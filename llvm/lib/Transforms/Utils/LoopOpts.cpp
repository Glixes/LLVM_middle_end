#include "llvm/Transforms/Utils/LoopOpts.h"
#include "llvm/IR/Dominators.h"

using namespace llvm;

bool isAlreadyLoopInvariant(Instruction *inst)
{
    return inst->getMetadata("invariant");
}

bool isLoopInvariant(Value *v, Loop* L)
{
    Instruction *v_inst = dyn_cast<Instruction>(v);
    // v_inst is NULL when v is an argument of the function
    if (!v_inst || isAlreadyLoopInvariant(v_inst) || !L->contains(v_inst))
        return true;
    
    outs() << "Is value " << *v_inst << " invariant?\n";
    
    Constant *c_inst = dyn_cast<Constant>(v);
    outs() << "Is the value " << c_inst << " constant?\n";
    if (c_inst)
        return true;
    
    return false;
}

bool isLoopInvariant(const Instruction *inst, Loop* L)
{
    if (!inst->isBinaryOp())
        return false;
    Value *val1 = inst->getOperand(0);
    Value *val2 = inst->getOperand(1);
    outs() << "Analyzing operands: " << *val1 << ", " << *val2 << "\n";
    
    return isLoopInvariant(val1, L) && isLoopInvariant(val2, L);
}

void markExitsDominatorBlocks(Loop &L, DominatorTree *DT)
{
    SmallVector<BasicBlock*> exiting_blocks;
    for (auto BI = L.block_begin(); BI != L.block_end(); ++BI)
    {
        BasicBlock *BB = *BI;
        if (L.isLoopExiting(BB))
            exiting_blocks.push_back(BB);
    }

    for (auto BI = L.block_begin(); BI != L.block_end(); ++BI)
    {
        BasicBlock *BB = *BI;
        LLVMContext &C = BB->getContext();
        outs() << "Basic block: " << *BB << "\n";

        bool is_dominator = true;
        for (auto EB: exiting_blocks)
        {
            if (!DT->dominates(BB, EB))
            {
                is_dominator = false;
                break;
            }
        }

        if (is_dominator)
        {
            MDNode *N = MDNode::get(C, MDString::get(C, ""));
            Instruction *terminator = BB->getTerminator();
            terminator->setMetadata("exits dominator", N);
            outs() << "Basic block: marked as exits dominator\n";
        }
    }
}

void markIfUseDominator(Instruction *inst, DominatorTree *DT)
{
    for (Value::use_iterator iter = inst->use_begin(); iter != inst->use_end(); iter++)
    {
        Use *use_of_inst = &(*iter);
        Value *val = dyn_cast<Value>(inst);
        if(!DT->dominates(val, *use_of_inst))
            return;
    }
    LLVMContext &C = inst->getContext();
    MDNode *N = MDNode::get(C, MDString::get(C, ""));
    inst->setMetadata("use dominator", N);
    outs() << "Instruction: marked as use dominator\n";
    return;
}

PreservedAnalyses LoopOpts::run (Loop &L, LoopAnalysisManager &LAM, 
                                    LoopStandardAnalysisResults &LAR, LPMUpdater &LU)
{
    DominatorTree *DT = &LAR.DT;
    BasicBlock *root_DT = (DT->getRootNode())->getBlock();
    
    outs() << "Pre-header: " << *(L.getLoopPreheader()) << "\n";
    outs() << "Header: " << *(L.getHeader()) << "\n";
    // outs() << L.getBlocks() << "\n";
    Loop *Loop = &L;
    for (auto BI = L.block_begin(); BI != L.block_end(); ++BI)
    {
        BasicBlock *BB = *BI;
        outs() << "Basic block: " << *BB << "\n";
        for (auto i = BB->begin(); i != BB->end(); i++)
        {
            Instruction *inst = dyn_cast<Instruction>(i);
            outs() << "Instruction: " << *inst << "\n";
            if (isLoopInvariant(inst, Loop))
            {   
                LLVMContext &C = inst->getContext();
                MDNode *N = MDNode::get(C, MDString::get(C, ""));
                inst->setMetadata("invariant", N);
                
                outs() << "Loop invariant instruction detected: " << *inst << "\n";
            }
            markIfUseDominator(inst, DT);
        }
    }

    markExitsDominatorBlocks(L, DT);

    return PreservedAnalyses::all();
}