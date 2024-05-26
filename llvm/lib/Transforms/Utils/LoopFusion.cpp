#include "llvm/Transforms/Utils/LoopFusion.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/PostDominators.h>
#include <llvm/Analysis/LoopInfo.h>

using namespace llvm;

bool isAdjacent (Loop *l1, Loop *l2)
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


bool haveSameNumberIterations (Loop *l1, Loop *l2, ScalarEvolution *SE)
{
    int c1 = SE->getSmallConstantMaxTripCount(l1);
    int c2 = SE->getSmallConstantMaxTripCount(l2);
    return (c1 == c2);
}


bool isFlowEquivalent (Loop *l1, Loop *l2, DominatorTree *DT, PostDominatorTree *PDT)
{
    BasicBlock *B1 = l1->getHeader();
    BasicBlock *B2 = l2->getHeader();
    
    return (DT->dominates(B1, B2) && PDT->dominates(B2, B1));
}


bool areDistanceIndependent (Loop *l1, Loop *l2)
{
    std::unordered_map<Value*, std::vector<std::vector<int, int>>> index_map;
    for (auto BI = l1->block_begin(); BI != l2->block_end(); ++BI)
    {
        BasicBlock *BB = *BI;
        for (auto i = BB->begin(); i != BB->end(); i++)
        {
            Instruction *inst = dyn_cast<Instruction>(i);
            //index_map[dyn_cast<Value>(inst)].push_back()
        }
    }
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

PreservedAnalyses LoopFusion::run (Function &F,FunctionAnalysisManager &AM)
{
    LoopInfo &LI = AM.getResult<LoopAnalysis>(F);

    ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
    DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
    PostDominatorTree &PDT = AM.getResult<PostDominatorTreeAnalysis>(F);

    for (Loop *L : LI)
    {
        outs() << *L << "\n"; 
    }

    return PreservedAnalyses::all();
}