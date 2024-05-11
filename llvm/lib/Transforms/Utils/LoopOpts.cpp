#include "llvm/Transforms/Utils/LoopOpts.h"
#include "llvm/IR/Dominators.h"

using namespace llvm;

bool isAlreadyLoopInvariant(Instruction *inst)
{
    //outs() << "Analyzing map: " << invariant_map[inst] << "\n";
    //return invariant_map[inst];
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

void markIfUseDominator(Instruction *inst, DominatorTree *DT)
{
    for (Value::use_iterator iter = inst->use_begin(); iter != inst->use_end(); iter++)
    {
        Use *use_of_inst = &(*iter);
        Value *val = dyn_cast<Value>(inst);
        if(DT->dominates(val, *use_of_inst))
        {
            LLVMContext &C = inst->getContext();
            MDNode *N = MDNode::get(C, MDString::get(C, ""));
            inst->setMetadata("use dominator", N);
        }
    }
}

PreservedAnalyses LoopOpts::run (Loop &L, LoopAnalysisManager &LAM, 
                                    LoopStandardAnalysisResults &LAR, LPMUpdater &LU)
{
    //std::unordered_map<const Instruction*, bool> invariant_map;
    DominatorTree *DT = &LAR.DT;
    BasicBlock *root_DT = (DT->getRootNode())->getBlock();
    SmallVector<BasicBlock*> exiting_blocks;
    
    /*
    for (auto i = root_DT->begin(); i != root_DT->end(); i++)
    {
        Instruction *inst = dyn_cast<Instruction>(i);
        outs() << *inst << "\n";
    }
    */
    
    outs() << "Pre-header: " << *(L.getLoopPreheader()) << "\n";
    outs() << "Header: " << *(L.getHeader()) << "\n";
    // outs() << L.getBlocks() << "\n";
    Loop *Loop = &L;
    for (auto BI = L.block_begin(); BI != L.block_end(); ++BI)
    {
        BasicBlock *BB = *BI;
        if (L.isLoopExiting(BB))
            exiting_blocks.push_back(BB);
        outs() << "Basic block: " << *BB << "\n";
        for (auto i = BB->begin(); i != BB->end(); i++)
        {
            // const_cast translate a const object into a non constant one
            // in this case const Instruction into Instruction.
            Instruction *inst = dyn_cast<Instruction>(i);
            outs() << "Instruction: " << *inst << "\n";
            if (isLoopInvariant(inst, Loop))
            {
                //invariant_map[inst] = true;
                
                LLVMContext &C = inst->getContext();
                MDNode *N = MDNode::get(C, MDString::get(C, ""));
                inst->setMetadata("invariant", N);
                
                outs() << "Loop invariant instruction detected: " << *inst << "\n";
            }
            markIfUseDominator(inst, DT);
        }
    }

    return PreservedAnalyses::all();
}