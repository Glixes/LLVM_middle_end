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

/** Returns true if the loops are adjacent, i.e. the exit block of the first loop is the preheader 
 * of the second one (or the guard block if the loop is guarded). Otherwise, it returns false.
 * 
 * @param l1 loop 1
 * @param l2 loop 2
 * @return bool
*/
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


/** @brief Returns true if the loops have the same number of iterations.
 * Otherwise, it returns false. The number of iterations is computed based on the number of backedges taken.
 * 
 * @param l1 loop 1
 * @param l2 loop 2
 * @param SE scalar evolution
 * @return bool
*/
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
        outs() << "Trip count: " << *trip_count << "\n";
        return trip_count;
    };

    return getTripCount(l1) == getTripCount(l2);
}


/** @brief Returns true if the loops are control flow equivalent.
 * I.e. when l1 executes, also l2 executes and when l2 executes also l1 executes.
 * Otherwise, it returns false.
 * 
 * @param l1 loop 1
 * @param l2 loop 2
 * @param DT domiator tree
 * @param PDT post dominator tree
 * @return bool
*/
bool areFlowEquivalent (Loop *l1, Loop *l2, DominatorTree *DT, PostDominatorTree *PDT)
{
    BasicBlock *B1 = l1->getHeader();
    BasicBlock *B2 = l2->getHeader();
    
    return (DT->dominates(B1, B2) && PDT->dominates(B2, B1));
}

/**
 * This function returns True if the distance between inst1 and inst2 is Negative. 
 * 
 * @param inst1 first instruction to analyze
 * @param inst2 second instruction to analyze
 * @param Loop1 Loop that contains first instruction
 * @param Loop2 Loop that contains second instruction
 * @param ScalarEvolution
 * @param DependenceInfo
*/
bool isDistanceNegative (Instruction *inst1, Instruction *inst2, Loop *loop1, Loop *loop2, 
    ScalarEvolution &SE, DependenceInfo DI)
{   
    // This lambda returns CanonicalAddExpr (or something better if it exists)
    auto getSCEVExpr = [&SE](Instruction *instToAnalyze, Loop *loop) -> const SCEVAddRecExpr* {
        
        Value *instArguments = getLoadStorePointerOperand(instToAnalyze);        
        const SCEV *scevPtr = SE.getSCEVAtScope(instArguments, loop);   

        #ifdef DEBUG
            outs() << "SCEV: " << *scevPtr << " with type " << scevPtr->getSCEVType() << "\n";
        #endif

        if ((scevPtr->getSCEVType() != SCEVTypes::scAddRecExpr && scevPtr->getSCEVType() != SCEVTypes::scAddExpr))
            return nullptr;
        
        std::vector<const SCEV *> SCEVOperands = scevPtr->operands();
        
        #ifdef DEBUG
            for (auto op: SCEVOperands)
                outs() << "Operand: " << *op << "\n";
        #endif

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

    // TODO: dependence analysis TOBEREMOVED?
    auto instructionDependence = DI.depends(inst1, inst2, true);

    #ifdef DEBUG
        outs() << "isDirectionNegative()? " << instructionDependence->isDirectionNegative() << "\n";
        outs() << "normalize()? " << instructionDependence->normalize(&SE) << "\n";
    #endif

    // based on strong SIV test
    const SCEV* baseAddressFirstInstruction = storeSCEV->getStart();
    const SCEV* baseAddressSecondInstruction = loadSCEV->getStart();
    const SCEV* strideStore = storeSCEV->getStepRecurrence(SE);
    const SCEV* strideLoad = loadSCEV->getStepRecurrence(SE);

    #ifdef DEBUG
        outs() << "Store start: " << *baseAddressFirstInstruction << "\n";
        outs() << "Load start: " << *baseAddressSecondInstruction << "\n";
        outs() << "Store step recurrence: " << *strideStore << "\n";
        outs() << "Load step recurrence: " << *strideLoad << "\n";
    #endif

    if (!SE.isKnownNonZero(strideStore) || strideStore != strideLoad){
        outs() << "Cannot compute distance\n";
        return true;
    }

    const SCEV *instructionsDelta = SE.getMinusSCEV(baseAddressFirstInstruction, baseAddressSecondInstruction);
    const SCEV *dependence_dist = nullptr;
    
    // can we compute distance?
    if (isa<SCEVConstant>(instructionsDelta) && isa<SCEVConstant>(strideStore)) {
  
        // The following lines of code return the product of stride and delta. Since we are working with int, there is no way to obtain d = i' - i = (c1 - c2) / stride, the result will be always 0. We left diagnostic print to show how we tried to compute the formula.
        #ifdef DEBUG
            //const SCEV *divisionWithStride = SE.getUDivExpr(SE.getOne(strideStore->getType()), strideStore);
            outs() << "Stride: " << *strideStore << ", delta: " << *instructionsDelta << ". Stride type: "<< *strideStore->getType();
        #endif
        
        //We use the mul to compute the sign. This result is given considered type size too. To obtain a better result, we should divide by 4 to "remove" integer data type size
        dependence_dist = SE.getMulExpr(instructionsDelta, strideStore);
        outs() << "Dependence distance: " << *dependence_dist << "\n";

    }
    else{
        outs() << "Cannot compute distance\n";
        return true;
    }
    
    //Only for diagnostic purposes
    bool isStoreGELoad = SE.isKnownPredicate(ICmpInst::ICMP_SGE, storeSCEV, loadSCEV);
    
    bool isLoadGELoad = SE.isKnownPredicate(ICmpInst::ICMP_SLT, dependence_dist, SE.getZero(strideStore->getType()));
    
    #ifdef DEBUG
        outs() << "Predicate 'always store >= load': " << (isStoreGELoad ? "True" : "False") << "\n";
        outs() << "Predicate 'dependence dist < 0': " << (isLoadGELoad ? "True" : "False") << "\n";
    #endif

    return isLoadGELoad;
}


bool areDistanceIndependent (Loop *l1, Loop *l2, ScalarEvolution &SE, DependenceInfo &DI, LoopInfo &LI)
{
    // get all the loads and stores
    std::vector<Value*> loads1;
    std::vector<Value*> stores1;
    std::vector<Value*> loads2;
    std::vector<Value*> stores2;

    //Lambda function. This collect loads and stores in vectors 
    auto collectLoadStores = [] (std::vector<Value*> *loads, std::vector<Value*> *stores, Loop *l) {
        for (auto BI = l->block_begin(); BI != l->block_end(); ++BI) {
            
            BasicBlock *BB = *BI;

            for (auto i = BB->begin(); i != BB->end(); i++) {
                Instruction *inst = dyn_cast<Instruction>(i);

                if (inst){
                    if (isa<StoreInst>(inst))
                        stores->push_back(inst);
                    if (isa<LoadInst>(inst))
                        loads->push_back(inst);
                }
                else
                    continue;

            }}
    };
    
    collectLoadStores(&loads1, &stores1, l1);
    collectLoadStores(&loads2, &stores2, l2);

    #ifdef DEBUG        
        outs() << "\n Loads dump \n";
        for(auto i : loads1)   
            {outs() << *i << "\n";}
        for(auto i : loads2)   
            {outs() << *i << "\n";}
        
        outs() << "\n Stores dump \n";    
        for(auto i : stores1)  
            {outs() << *i << "\n";}
        for(auto i : stores2)  
            {outs() << *i << "\n";}
    #endif

    for (auto store: stores1){
        Instruction *storeInst = dyn_cast<Instruction>(store);
        for (auto load: loads2){
            Instruction *loadInst = dyn_cast<Instruction>(load);
            
            auto instructionDependence = DI.depends(storeInst, loadInst, true);

            #ifdef DEBUG
                outs() << "Checking " << *load << " " << *store << " dep? " <<
                    (instructionDependence ? "True" : "False") << "\n";
            #endif

            if (instructionDependence
                && !instructionDependence->isInput()
                && !instructionDependence->isOutput()) {
                
                if(LI.getLoopFor(loadInst->getParent()) != l2 || LI.getLoopFor(storeInst->getParent()) != l1){
                    return false;
                }

                // If isDistanceNegative, then there is a negative distance dependency, so return false
                if (isDistanceNegative(loadInst, storeInst, l2, l1, SE, DI)){
                    // outs() << "isDirectionNegative()? " << instructionDependence->isDirectionNegative() << "\n";
                    
                    return false;
                }
            }
        }
    }
    return true;
}


/** @brief Fuses the given loops.
 * The body of the second loop, after beeing unlinked, is connected after the body of the first loop.
 * 
 * @param l1 loop 1
 * @param l2 loop 2
*/
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
    Data structure to get reference to the basic blocks that will undergo relocation.
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
            Expoliting the logical short-circuit, as soon as one of the functions returns false, 
            the others remaining checks are not executed and the if statement condition becomes false.
            */ 
            if (areAdjacent(l1, l2) && 
                haveSameIterationsNumber(l1, l2, &SE) && 
                areFlowEquivalent(l1, l2, &DT, &PDT) && 
                areDistanceIndependent(l1, l2, SE, DI, LI))
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