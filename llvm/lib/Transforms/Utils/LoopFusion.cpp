#include "llvm/Transforms/Utils/LoopFusion.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Instructions.h"
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/PostDominators.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>

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


const SCEV *getTripCount (Loop *l, ScalarEvolution *SE)
{
    const SCEV *trip_count = SE->getBackedgeTakenCount(l);

    if (isa<SCEVCouldNotCompute>(trip_count))
    {
        outs() << "Trip count of loop " << l->getName() << " could not be computed.";
        return nullptr;
    }

    return trip_count;
}


bool haveSameIterationsNumber (Loop *l1, Loop *l2, ScalarEvolution *SE)
{
    return getTripCount(l1, SE) == getTripCount(l2, SE);
}


bool areFlowEquivalent (Loop *l1, Loop *l2, DominatorTree *DT, PostDominatorTree *PDT)
{
    BasicBlock *B1 = l1->getHeader();
    BasicBlock *B2 = l2->getHeader();
    
    return (DT->dominates(B1, B2) && PDT->dominates(B2, B1));
}

/*
bool areDistanceIndependent (const SCEV *stride, const SCEV *c1, const SCEV *c2, ScalarEvolution *SE)
{
    const SCEV *delta = SE->getMinusSCEV(c1, c2);

    if (isa<SCEVConstant>(*delta) && isa<SCEVConstant>(*stride))
    {
        // get dependece distance and return true if it is positive, otherwise return false
        return SE->isKnownPositive(delta);
    }
}
*/

bool areDistanceIndependent (Loop *l1, Loop *l2, ScalarEvolution &SE)
{
    // we only analyze loops in simplified form, so with a single entry and a single exit
    if (!l1->isLoopSimplifyForm() || !l2->isLoopSimplifyForm())
        return false;

    // get all the loads and stores
    std::vector<Value*> loadsStores1;
    std::vector<Value*> loadsStores2;
    for (auto BI = l1->block_begin(); BI != l1->block_end(); ++BI)
    {
        BasicBlock *BB = *BI;
        for (auto i = BB->begin(); i != BB->end(); i++)
        {
            Instruction *inst = dyn_cast<Instruction>(i);
            if (!inst)
                continue;
            Value *ls = getLoadStorePointerOperand(inst);
            if (!ls)
                continue;
            loadsStores1.push_back(ls);
        }
    }
    
    for (auto BI = l2->block_begin(); BI != l2->block_end(); ++BI)
    {
        BasicBlock *BB = *BI;
        for (auto i = BB->begin(); i != BB->end(); i++)
        {
            Instruction *inst = dyn_cast<Instruction>(i);
            if (!inst)
                continue;
            Value *ls = getLoadStorePointerOperand(inst);
            if (!ls)
                continue;
            loadsStores2.push_back(ls);
        }
    }
    ICmpInst::Predicate Pred = ICmpInst::ICMP_SGE;

    for (auto val1: loadsStores1){
        const SCEV *scevPtr1 = SE.getSCEVAtScope(val1, l1);
        outs() << *val1 << "\n";
        outs() << *scevPtr1 << "\n";

        std::vector<const SCEV *> Operands1 = scevPtr1->operands();
        for (auto op: Operands1)
            outs() << "Operand: " << *op << "\n";
        const SCEV * C1 = Operands1[0];
        const SCEV * Stride = Operands1[1];

        if ((scevPtr1->getSCEVType() != SCEVTypes::scAddRecExpr))
            continue;
        const SCEV *AddRec1 = SE.getAddExpr(C1, Stride);
        outs() << *AddRec1 << "\n";

        for (auto val2: loadsStores2){
            const SCEV *scevPtr2 = SE.getSCEVAtScope(val2, l2);
            bool IsAlwaysGE = SE.isKnownPredicate(Pred, scevPtr1, scevPtr2);
            outs() << "Predicate: " << (IsAlwaysGE?"True":"False") << "\n";
        }
    }

    return true;
}


Value *getBaseAddress (Instruction *inst)
{
    if (isa<AllocaInst>(inst) || isa<Argument>(inst))
        return inst;
    
    Value *i;
    for (Value::use_iterator iter = inst->use_begin(); iter != inst->use_end(); ++iter)
    {
        Use *use_of_inst = &(*iter);
        Instruction *user_inst = dyn_cast<Instruction>(iter->getUser());

        i = getBaseAddress(user_inst);
        if (i)
            return i;
    }
    return nullptr;
}

bool fuseLoop (Loop *l1, Loop *l2, ScalarEvolution *SE)
{
    outs() << "1\n";
    SmallVector<BasicBlock *> exits_blocks;
    
    /*
    Replace the uses of the induction variable of the second loop with 
    the induction variable of the first loop.
    */
    PHINode *index1 = l1->getInductionVariable(*SE);
    PHINode *index2 = l2->getInductionVariable(*SE);
    outs() << *index1 << "\n";
    outs() << *index2 << "\n";
    index2->replaceAllUsesWith(index1);
    outs() << "2\n";

    /*
    Get reference to the basic blocks that will undergo relocation.
    */
    BasicBlock *first_body = l1->getHeader()->getSingleSuccessor();
    BasicBlock *first_latch = first_body->getSingleSuccessor();
    BasicBlock *second_body = l2->getHeader()->getSingleSuccessor();
    BasicBlock *second_latch = second_body->getSingleSuccessor();
    outs() << "3\n";
    l2->getExitBlocks(exits_blocks);
    outs() << "4\n";
    for (BasicBlock *BB : exits_blocks)
    {
        outs() << "5\n";
        if (BB->getSinglePredecessor() == l2->getHeader())
        {
            outs() << "6\n";
            BB->removeFromParent();
            BB->moveAfter(l1->getHeader());
            outs() << "7\n";
        }
    }

    outs() << "8\n";
    second_latch->removeFromParent();
    first_latch->removeFromParent();
    second_body->removeFromParent();
    second_body->moveAfter(first_body);
    first_latch->moveAfter(second_body);
    second_latch->moveAfter(l2->getHeader());
    outs() << "9\n";

    return true;
}

PreservedAnalyses LoopFusion::run (Function &F,FunctionAnalysisManager &AM)
{
    outs() << "before all\n";
    LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
    ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
    DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
    PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);

    SmallVector<Loop *, 4> loops_forest = LI.getLoopsInPreorder();

    outs() << "before all\n";

    if (loops_forest.size() <= 1)
        return PreservedAnalyses::all();

    std::unordered_map<unsigned, Loop*> last_loop_at_level;
    last_loop_at_level[loops_forest[0]->getLoopDepth()] = loops_forest[0];

    outs() << "before loop\n";

    for (size_t i = 1; i < loops_forest.size(); i++)
    {
        unsigned loop_depth = loops_forest[i]->getLoopDepth();
        Loop *l1 = last_loop_at_level[loop_depth];
        Loop *l2 = loops_forest[i];
        outs() << "before fuse\n";
        fuseLoop(l1, l2, &SE);
        outs() << "after fuse\n";

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
                areDistanceIndependent(l1, l2, SE))
            {
                // Loop Fusion
                continue;
            }
        }
        
        last_loop_at_level[loop_depth] = loops_forest[i];
    }

    return PreservedAnalyses::all();
}