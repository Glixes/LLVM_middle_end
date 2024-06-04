#include "llvm/Transforms/Utils/LoopFusion.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Instructions.h"
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/PostDominators.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/DependenceAnalysis.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

#define DEBUG

using namespace llvm;

bool areAdjacent (Loop *l1, Loop *l2)
{
    // check for all the exiting blocks of l1
    SmallVector<BasicBlock*, 4> exit_blocks;
    l1->getUniqueNonLatchExitBlocks(exit_blocks);
    for (BasicBlock *BB : exit_blocks)
    {
        if (BB != (l2->isGuarded() ? dyn_cast<BasicBlock>(l2->getLoopGuardBranch()) : l2->getLoopPreheader()))
            return false;
    }
    return true;
}


bool haveSameIterationsNumber (Loop *l1, Loop *l2, ScalarEvolution *SE)
{
    auto getTripCount = [SE] (Loop *l) -> const SCEV *
    {
        const SCEV *trip_count = SE->getBackedgeTakenCount(l);

        if (isa<SCEVCouldNotCompute>(trip_count))
        {
            outs() << "Trip count of loop " << l->getName() << " could not be computed.";
            return nullptr;
        }

        return trip_count;
    };

    return getTripCount(l1) == getTripCount(l2);
}


bool areFlowEquivalent (Loop *l1, Loop *l2, DominatorTree *DT, PostDominatorTree *PDT)
{
    BasicBlock *B1 = l1->getHeader();
    BasicBlock *B2 = l2->getHeader();
    
    return (DT->dominates(B1, B2) && PDT->dominates(B2, B1));
}


bool isDistanceNegative (Instruction *inst1, Instruction *inst2, Loop *loop1, Loop *loop2, ScalarEvolution &SE, DependenceInfo DI){

    // This lambda returns CanonicalAddExpr (or something better if it exists)
    auto getSCEVExpr = [&SE](Instruction *instToAnalyze, Loop *loop) -> const SCEVAddRecExpr* {
        
        Value *instArguments = getLoadStorePointerOperand(instToAnalyze);        
        const SCEV *scevPtr = SE.getSCEVAtScope(instArguments, loop);   

        #ifdef DEBUG
            outs() << "SCEV: " << *scevPtr << "\n";
            outs() << "Type: " << scevPtr->getSCEVType() << "\n";
        #endif

        if ((scevPtr->getSCEVType() != SCEVTypes::scAddRecExpr && 
                scevPtr->getSCEVType() != SCEVTypes::scAddExpr))
            return nullptr;
        
        std::vector<const SCEV *> Operands = scevPtr->operands();
        
        #ifdef DEBUG
            for (auto op: Operands)
                outs() << "Operand: " << *op << "\n";
        #endif
        
        //const SCEV *ConstantOfSCEV = Operands[0];
        //const SCEV *StrideOfSCEV = Operands[1];  

        SmallPtrSet<const SCEVPredicate *, 4> Preds;
        const SCEVAddRecExpr *CanonicalAddExpr = SE.convertSCEVToAddRecWithPredicates(scevPtr, loop, Preds);       
        outs() << *CanonicalAddExpr << "\n";

        return CanonicalAddExpr;
    };

    const SCEVAddRecExpr *loadSCEV = getSCEVExpr(inst1, loop1); 
    const SCEVAddRecExpr *storeSCEV = getSCEVExpr(inst2, loop2);
    
    if (!(loadSCEV && storeSCEV)){
        #ifdef DEBUG
            outs() << "Can't find a Canonical Add Expression for inst!" << "\n";
        #endif
        return true;
    }

    // dependence analysis
    auto instructionDependence = DI.depends(inst1, inst2, true);

    outs() << "isDirectionNegative()? " << instructionDependence->isDirectionNegative() << "\n";
    outs() << "normalize()? " << instructionDependence->normalize(&SE) << "\n";

    // strong SIV test
    const SCEV* C1 = storeSCEV->getStart();
    const SCEV* C2 = loadSCEV->getStart();
    const SCEV* stride1 = storeSCEV->getStepRecurrence(SE);
    const SCEV* stride2 = loadSCEV->getStepRecurrence(SE);

    #ifdef DEBUG
        outs() << "Store start: " << *C1 << "\n";
        outs() << "Load start: " << *C2 << "\n";
        outs() << "Store step recurrence: " << *stride1 << "\n";
        outs() << "Load step recurrence: " << *stride2 << "\n";
    #endif

    if (!SE.isKnownNonZero(stride1) || stride1 != stride2){
        outs() << "Cannot compute distance\n";
        return true;
    }

    const SCEV *stride = stride1;
    const SCEV *delta = SE.getMinusSCEV(C1, C2);
    const SCEV *dependence_dist = nullptr;
    
    // can we compute distance?
    if (isa<SCEVConstant>(delta) && isa<SCEVConstant>(stride)) {
        outs() << "Stride: " << *stride << ", delta: " << *delta << "\n";
        // TODO find a method to compute 1/stride, for now the multiplication just allows to keep track of the stride sign 
        dependence_dist = SE.getMulExpr(delta, stride);
        outs() << "Dependence distance: " << *dependence_dist << "\n";
    }
    else{
        outs() << "Cannot compute distance\n";
        return true;
    }
        
    bool IsAlwaysGE = SE.isKnownPredicate(ICmpInst::ICMP_SGE, storeSCEV, loadSCEV);
    bool IsDistLT0 = SE.isKnownPredicate(ICmpInst::ICMP_SLT, dependence_dist, SE.getZero(stride->getType()));
    
    #ifdef DEBUG
        outs() << "Predicate 'always store >= load': " << (IsAlwaysGE ? "True" : "False") << "\n";
        outs() << "Predicate 'dependence dist < 0': " << (IsDistLT0 ? "True" : "False") << "\n";
    #endif

    return IsDistLT0;
}


bool areDistanceIndependent (Loop *l1, Loop *l2, ScalarEvolution &SE, DependenceInfo &DI)
{
    // get all the loads and stores
    std::vector<std::pair<Value*, Loop*>> loadsvector;
    std::vector<std::pair<Value*, Loop*>> storesvector;

    //Lambda function. This collect loads and stores in vectors 
    auto collectLoadStores = [&loadsvector, &storesvector] (Loop *l) {
        for (auto BI = l->block_begin(); BI != l->block_end(); ++BI) {
            
            BasicBlock *BB = *BI;

            for (auto i = BB->begin(); i != BB->end(); i++) {
                Instruction *inst = dyn_cast<Instruction>(i);

                if (inst){
                    if (isa<StoreInst>(inst))
                        storesvector.push_back(std::pair(inst, l));
                    if (isa<LoadInst>(inst))
                        loadsvector.push_back(std::pair(inst,l));
                }
                else
                    continue;

            }}
    };
    
    collectLoadStores(l1);
    collectLoadStores(l2);

    #ifdef DEBUG        
        outs() << "\n Loads dump \n";
        for(auto i : loadsvector)   
            {outs() << *i.first << "\n";}
        
        outs() << "\n Stores dump \n";    
        for(auto i : storesvector)  
            {outs() << *i.first << "\n";}
    #endif

    for (auto val1: loadsvector){
        Instruction *inst1 = dyn_cast<Instruction>(val1.first);
        for (auto val2: storesvector){
            Instruction *inst2 = dyn_cast<Instruction>(val2.first);
            
            auto instructionDependence = DI.depends(inst1, inst2, true);

            #ifdef DEBUG
                outs() << "Checking " << *val1.first << " " << *val2.first << " dep? " <<
                    (instructionDependence ? "True" : "False") << "\n";
            #endif

            if (instructionDependence
                && !instructionDependence->isInput()
                && !instructionDependence->isOutput()) {
                
                // If isDistanceNegative, then there is a negative distance dependency, so return false
                if (isDistanceNegative(inst1, inst2, val1.second, val2.second, SE, DI)){
                    // outs() << "isDirectionNegative()? " << instructionDependence->isDirectionNegative() << "\n";
                    
                    return false;
                }

            }
        }
    }
    return true;
}


void fuseLoop (Loop *l1, Loop *l2)
{
    BasicBlock *l2_entry_block = l2->isGuarded() ? l2->getLoopGuardBranch()->getParent() : l2->getLoopPreheader(); 

    SmallVector<BasicBlock *> exits_blocks;
    
    /*
    Replace the uses of the induction variable of the second loop with 
    the induction variable of the first loop.
    */
    PHINode *index1 = l1->getCanonicalInductionVariable();
    PHINode *index2 = l2->getCanonicalInductionVariable();
    index2->replaceAllUsesWith(index1);

    /*
    Get reference to the basic blocks that will undergo relocation.
    */
    struct LoopStructure
    {
        BasicBlock *header;
        BasicBlock *latch;
        BasicBlock *body_head;
        BasicBlock *body_tail;

        LoopStructure (Loop *l)
        {
            this->header = l->getHeader();
            this->latch = l->getLoopLatch();
            this->body_head = getBodyHead(l, header);
            this->body_tail = latch->getUniquePredecessor();
        }

        BasicBlock *getBodyHead (Loop *l, BasicBlock *header)
        {
            for (auto sit = succ_begin(header); sit != succ_end(header); sit++)
            {
                BasicBlock *successor = dyn_cast<BasicBlock>(*sit);
                if (l->contains(successor))
                    return successor;
            }
            return nullptr;
        }
    };
    
    LoopStructure *first_loop = new LoopStructure(l1);
    LoopStructure *second_loop = new LoopStructure(l2);

    l2->getExitBlocks(exits_blocks);
    for (BasicBlock *BB : exits_blocks)
    {
        for (pred_iterator pit = pred_begin(BB); pit != pred_end(BB); pit++)
        {
            BasicBlock *predecessor = dyn_cast<BasicBlock>(*pit);
            if (predecessor == l2->getHeader())
            {
                l1->getHeader()->getTerminator()->replaceUsesOfWith(l2_entry_block, BB);
            }
        }
    }

    BranchInst *new_branch = BranchInst::Create(second_loop->latch);
    ReplaceInstWithInst(second_loop->header->getTerminator(), new_branch);

    first_loop->body_tail->getTerminator()->replaceUsesOfWith(first_loop->latch, second_loop->body_head);
    second_loop->body_tail->getTerminator()->replaceUsesOfWith(second_loop->latch, first_loop->latch);

    delete first_loop;
    delete second_loop;

    return;
}

PreservedAnalyses LoopFusion::run (Function &F,FunctionAnalysisManager &AM)
{
    LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
    ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
    DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
    PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);
    DependenceInfo &DI = AM.getResult<DependenceAnalysis>(F);

    SmallVector<Loop *, 4> loops_forest = LI.getLoopsInPreorder();

    if (loops_forest.size() <= 1)
        return PreservedAnalyses::all();

    std::unordered_map<unsigned, Loop*> last_loop_at_level;
    last_loop_at_level[loops_forest[0]->getLoopDepth()] = loops_forest[0];


    bool fusion_happened = false;
    for (size_t i = 1; i < loops_forest.size(); i++)
    {
        unsigned loop_depth = loops_forest[i]->getLoopDepth();
        Loop *l1 = last_loop_at_level[loop_depth];
        Loop *l2 = loops_forest[i];

        // check whether l1 exists, i.e. there is a loop at the current loop level that has been visited before
        // check for the same parent
        if (l1 && l1->getParentLoop() == l2->getParentLoop())
        {
            /*
            Expoliting the logical short-circuit, as soon as one of th functions returns false, 
            the others remaining checks are not executed and the if statement condition become false.
            */ 
            if (areAdjacent(l1, l2) && 
                haveSameIterationsNumber(l1, l2, &SE) && 
                areFlowEquivalent(l1, l2, &DT, &PDT) && 
                areDistanceIndependent(l1, l2, SE, DI))
            {
                outs() << "Starting fusion ...\n";
                fuseLoop(l1, l2);
                fusion_happened = true;
                outs() << "Fusion done\n";
                break;
            }
        }
        
        last_loop_at_level[loop_depth] = loops_forest[i];
    }

    return fusion_happened ? PreservedAnalyses::none() : PreservedAnalyses::all();
}