#include "llvm/Transforms/Utils/LoopFusion.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/PostDominators.h>
#include <llvm/Analysis/LoopInfo.h>

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


int getNormalizedIterationsNumber (Loop *l, ScalarEvolution *SE)
{
    int iterations_number = SE->getSmallConstantMaxTripCount(l);
    return (l->isGuarded() ? iterations_number++ : iterations_number);
}


bool haveSameNumberIterations (Loop *l1, Loop *l2, ScalarEvolution *SE)
{
    return getNormalizedIterationsNumber(l1, SE) == getNormalizedIterationsNumber(l2, SE);
}


bool areFlowEquivalent (Loop *l1, Loop *l2, DominatorTree *DT, PostDominatorTree *PDT)
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

    SmallVector<Loop *, 4> loops_forest = LI.getLoopsInPreorder();

    if (loops_forest.size() <= 1)
        return PreservedAnalyses::all();

    std::unordered_map<unsigned, Loop*> last_loop_at_level;
    last_loop_at_level[loops_forest[0]->getLoopDepth()] = loops_forest[0];

    for (int i = 1; i < loops_forest.size(); i++)
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
                haveSameNumberIterations(l1, l2, &SE) && 
                areFlowEquivalent(l1, l2, &DT, &PDT) && 
                areDistanceIndependent(l1, l2))
            {
                // Loop Fusion
                continue;
            }
        }
        
        last_loop_at_level[loop_depth] = loops_forest[i];
        //(A(DE(F(H)G))BC(IJ(L(O)MN)K))
        // ADEFHGBCIJLOMNK
    }

    return PreservedAnalyses::all();
}