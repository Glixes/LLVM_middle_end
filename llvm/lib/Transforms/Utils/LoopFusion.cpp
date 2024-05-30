#include "llvm/Transforms/Utils/LoopFusion.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Instructions.h"
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/PostDominators.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/DependenceAnalysis.h>

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


bool areDistanceIndependent (const SCEV *stride, const SCEV *c1, const SCEV *c2, ScalarEvolution *SE)
{
    const SCEV *delta = SE->getMinusSCEV(c1, c2);

    if (isa<SCEVConstant>(*delta) && isa<SCEVConstant>(*stride))
    {
        // get dependece distance and return true if it is positive, otherwise return false
        //SE->isKnownPositive()
    }
}


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
    //std::unordered_map<Value*, std::vector<std::vector<int, int>>> index_map;
    for (auto BI = l1->block_begin(); BI != l2->block_end(); ++BI)
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

        const SCEV *AddRec1 =SE.getAddExpr(C1, Stride);
        if (!AddRec1)
            continue;
        outs() << *AddRec1 << "\n";

        for (auto val2: loadsStores2){
            const SCEV *scevPtr2 = SE.getSCEVAtScope(val1, l1);
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
                haveSameNumberIterations(l1, l2, &SE) && 
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