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
    // check for all the exit blocks of l1
    SmallVector<BasicBlock*, 4> exit_blocks;

    l1->getUniqueNonLatchExitBlocks(exit_blocks);

    for (BasicBlock *BB : exit_blocks)
    {
        #ifdef DEBUG
            outs() << *BB << "\n";
            outs() << "BB instruction number " << BB->size() << "\n";
        #endif

        if (l2->isGuarded() && BB != dyn_cast<BasicBlock>(l2->getLoopGuardBranch()))
            return false;

        if (BB != l2->getLoopPreheader() || BB->size() > 1)
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
    auto getTripCount = [SE] (Loop *l) -> const SCEV * {
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
*/
bool isDistanceNegative (Instruction *inst1, Instruction *inst2, Loop *loop1, Loop *loop2, ScalarEvolution &SE)
{   

    // This lambda returns a polynomial recurrence on the trip count, an object of type SCEVAddRecExpr*,
    // the reason is that this class offers more utilities than a regular SCEV*
    auto getSCEVExpr = [&SE](Instruction *instructionToAnalyze, Loop *loopOfTheInstruction) -> const SCEVAddRecExpr* {
        
        Value *instructionArguments = getLoadStorePointerOperand(instructionToAnalyze);        
        const SCEV *SCEVFromInstruction = SE.getSCEVAtScope(instructionArguments, loopOfTheInstruction);   

        #ifdef DEBUG
            outs() << "SCEV: " << *SCEVFromInstruction << " with type " << SCEVFromInstruction->getSCEVType() << "\n";
        #endif

        // only convert "compatible" types of SCEV
        if ((SCEVFromInstruction->getSCEVType() != SCEVTypes::scAddRecExpr && SCEVFromInstruction->getSCEVType() != SCEVTypes::scAddExpr))
          return nullptr;
        
        std::vector<const SCEV *> SCEVOperands = SCEVFromInstruction->operands();
        
        #ifdef DEBUG
            outs() << "Operand: ";
            for (auto op: SCEVOperands)
                outs() << *op << ", ";
            outs() << "\n";
        #endif

        SmallPtrSet<const SCEVPredicate *, 4> Preds;

        const SCEVAddRecExpr *polinomial_recurrence = SE.convertSCEVToAddRecWithPredicates(SCEVFromInstruction, loopOfTheInstruction, Preds);       
    
        #ifdef DEBUG
            if (polinomial_recurrence)
                outs() << "Polynomial recurrence " << *polinomial_recurrence << "\n";
        #endif
        
        return polinomial_recurrence;


    };

    const SCEVAddRecExpr *inst1AddRec = getSCEVExpr(inst1, loop1); 
    const SCEVAddRecExpr *inst2AddRec = getSCEVExpr(inst2, loop2);
    
    if (!(inst1AddRec && inst2AddRec)){
        #ifdef DEBUG
            outs() << "Can't find a polynomial recurrence for inst!\n";
        #endif
        return true;
    }

    const SCEV* base_address_first_instruction = inst2AddRec->getStart();
    const SCEV* base_address_second_instruction = inst1AddRec->getStart();
    const SCEV* stride_store = inst2AddRec->getStepRecurrence(SE);
    const SCEV* stride_load = inst1AddRec->getStepRecurrence(SE);

    #ifdef DEBUG
        outs() << "Store start: " << *base_address_first_instruction << "\n";
        outs() << "Load start: " << *base_address_second_instruction << "\n";
        outs() << "Store step recurrence: " << *stride_store << "\n";
        outs() << "Load step recurrence: " << *stride_load << "\n";
    #endif

    if (!SE.isKnownNonZero(stride_store) || stride_store != stride_load){
        outs() << "Cannot compute distance\n";
        return true;
    }

    // delta represents the distance, in number of memory cells, between the starting addresses which are used to access memory
    // in instruction 1 and 2
    const SCEV *instructions_delta = SE.getMinusSCEV(base_address_first_instruction, base_address_second_instruction);
    const SCEV *dependence_dist = nullptr;
    
    // can we compute distance?
    if (isa<SCEVConstant>(instructions_delta) && isa<SCEVConstant>(stride_store)) {

        // The dependence distance between the two instructions is computed from delta and stride,
        // using a method inspired from strong SIV tests.
        //
        // The formula to apply should be the following:
        // d = i' - i = (c1 - c2) / stride, as indicated by Absar in "Scalar Evolution Demystified",
        // but it was decided to skip the division for implementation difficulties,
        // it was used a multiplication instead, so that the "distance" would keep into consideration sign difference
        // between delta and stride;
        // this way, the distance is not actually a distance between indexes in access to memory (e.g. A[i] compared to A[i']),
        // but it is just the delta between starting addresses of the two arrays, but inflated by the absolute value of the stride,
        // with a sign that is the result of the sign concordance between stride and delta
      
        #ifdef DEBUG
            outs() << "Stride: " << *stride_store << ", delta: " << *instructions_delta << ". Stride type: "<< *stride_store->getType();
        #endif
        
        dependence_dist = SE.getMulExpr(instructions_delta, stride_store);
        outs() << "Dependence distance: " << *dependence_dist << "\n";

    }
    else{
        outs() << "Cannot compute distance\n";
        return true;
    }
    

    bool isDistLT0 = SE.isKnownPredicate(ICmpInst::ICMP_SLT, dependence_dist, SE.getZero(stride_store->getType()));
    
    #ifdef DEBUG
        outs() << "Predicate 'dependence dist < 0': " << (isDistLT0 ? "True" : "False") << "\n";
    #endif

    return isDistLT0;
}


bool areDistanceIndependent (Loop *l1, Loop *l2, ScalarEvolution &SE, DependenceInfo &DI, LoopInfo &LI)
{
    // get all the loads and stores
    std::vector<Value*> loads_first_loop, stores_first_loop, loads_second_loop, stores_second_loop;

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
    
    collectLoadStores(&loads_first_loop, &stores_first_loop, l1);
    collectLoadStores(&loads_second_loop, &stores_second_loop, l2);

    #ifdef DEBUG        
        outs() << "\n Loads dump \n";
        for(auto i : loads_first_loop)   
            outs() << *i << "\n";
        for(auto i : loads_second_loop)   
            outs() << *i << "\n";
        
        outs() << "\n Stores dump \n";    
        for(auto i : stores_first_loop)  
            outs() << *i << "\n";
        for(auto i : stores_second_loop)  
            outs() << *i << "\n";
    #endif

    auto checkStoreAndLoadDependence = [&DI, &LI, &SE](std::vector<Value*> *store_vector, std::vector<Value*> *load_vector, Loop *store_loop, Loop *load_loop) {
        for (auto store: *store_vector){

            Instruction *store_inst = dyn_cast<Instruction>(store);
            
            for (auto load: *load_vector){
                
                Instruction *load_inst = dyn_cast<Instruction>(load);
                auto instruction_dependence = DI.depends(store_inst, load_inst, true);

                #ifdef DEBUG
                    outs() << "Checking " << *load << " " << *store << " dep? " << (instruction_dependence ? "True" : "False") << "\n";
                #endif

                if (instruction_dependence) {
                    
                    // Check that load and store inst are not part of a nested loop
                    if(LI.getLoopFor(load_inst->getParent()) != load_loop || LI.getLoopFor(store_inst->getParent()) != store_loop)
                        return false;

                    // If isDistanceNegative, then there is a negative distance dependency, so return false

                    if (isDistanceNegative(load_inst, store_inst, load_loop, store_loop, SE))
                        return false;
                    
                }
            }
        }
        return true;
    };
    
    if (!checkStoreAndLoadDependence(&stores_first_loop, &loads_second_loop, l1, l2) || 
        !checkStoreAndLoadDependence(&stores_second_loop, &loads_first_loop, l2, l1) )
        return false;

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
        BasicBlock *header, *latch, *body_head, *body_tail;

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

    delete first_loop; delete second_loop;

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

    std::unordered_map<unsigned, Loop*> last_loop_at_level = {{loops_forest[0]->getLoopDepth(), loops_forest[0]}};

    bool fusion_happened = false;

    for (size_t i = 1; i < loops_forest.size(); i++)
    {
        unsigned loop_depth = loops_forest[i]->getLoopDepth();
        Loop *l1 = last_loop_at_level[loop_depth];
        Loop *l2 = loops_forest[i];

        // check whether l1 exists (i.e. there is a loop at the current loop level that has been visited before) and check for the same parent
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