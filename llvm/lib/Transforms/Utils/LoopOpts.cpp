#include "llvm/Transforms/Utils/LoopOpts.h"
#include "llvm/IR/Dominators.h"

using namespace llvm;


const std::string invariant_tag = "invariant";
const std::string use_dominator = "use_dominator";
const std::string exits_dominator = "exits_dominator";
const std::string dead_inst = "dead";
SmallVector<std::string> tags = {invariant_tag, use_dominator, exits_dominator, dead_inst};

void clearMetadata (Instruction *inst) 
{
    for (auto type: tags)
        inst->setMetadata(type, NULL);
}

bool isAlreadyLoopInvariant (Instruction *inst)
{
    return inst->getMetadata(invariant_tag);
}

bool isLoopInvariant (Value *v, Loop* L)
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

bool isLoopInvariant (const Instruction *inst, Loop* L)
{
    Value *val1 = inst->getOperand(0);
    Value *val2 = inst->getOperand(1);
    outs() << "Analyzing operands: " << *val1 << ", " << *val2 << "\n";
    
    return isLoopInvariant(val1, L) && isLoopInvariant(val2, L);
}

void markExitsDominatorBlocks (Loop &L, DominatorTree *DT)
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
            terminator->setMetadata(exits_dominator, N);
            outs() << "Basic block: marked as exits dominator\n";
        }
    }
}

std::vector<Use*> getUses (Instruction *inst)
{
    std::vector<Use*> uses_to_check;
    for (Value::use_iterator iter = inst->use_begin(); iter != inst->use_end(); ++iter)
    {
        Use *use_of_inst = &(*iter);
        Instruction *user_inst = dyn_cast<Instruction>(iter->getUser());
        outs() << "Use: " << *(user_inst) << "\n";
        if (isa<PHINode>(user_inst))
        {
            std::vector<Use*> res = getUses(user_inst);
            uses_to_check.insert(uses_to_check.end(), res.begin(), res.end());
        }
        else
            uses_to_check.push_back(use_of_inst);
    }
    return uses_to_check;
};

void markIfUseDominator (Instruction *inst, DominatorTree *DT)
{
    std::function<std::vector<Use*>(Instruction*)> getUses = [&](Instruction *inst) -> std::vector<Use*>
    {
        std::vector<Use*> uses_to_check;
        for (Value::use_iterator iter = inst->use_begin(); iter != inst->use_end(); ++iter)
        {
            Use *use_of_inst = &(*iter);
            Instruction *user_inst = dyn_cast<Instruction>(iter->getUser());
            outs() << "Use: " << *(user_inst) << "\n";
            if (isa<PHINode>(user_inst))
            {
                std::vector<Use*> res = getUses(user_inst);
                uses_to_check.insert(uses_to_check.end(), res.begin(), res.end());
            }
            else
                uses_to_check.push_back(use_of_inst);
        }
        return uses_to_check;
    };

    std::vector<Use*> uses = getUses(inst);
    Value *inst_val = dyn_cast<Value>(inst);

    for (Use *use : uses)
    {
        outs() << DT->dominates(inst_val, *use) << "\n";
        if (!DT->dominates(inst_val, *use))
            return;
    }
    LLVMContext &C = inst->getContext();
    MDNode *N = MDNode::get(C, MDString::get(C, ""));
    inst->setMetadata(use_dominator, N);
    outs() << "Instruction: marked as use dominator\n";
    return;
}

bool markDeadInstructions (Loop *L)
{
    for (auto BI = L->block_begin(); BI != L->block_end(); ++BI)
    {
        BasicBlock *BB = *BI;
        for (BasicBlock::iterator i = BB->begin(); i != BB->end(); i++)
        { 
            Instruction *inst = dyn_cast<Instruction>(i);
            LLVMContext &C = inst->getContext();
            std::vector<Use*> uses = getUses(inst);
            bool isDead = true;
            for (Use *use : uses)
            {
                if (!L->contains(use->getUser()))
                {
                    isDead = false;
                    break;
                }
            }

            if (isDead = true)
            {
                MDNode *N = MDNode::get(C, MDString::get(C, ""));
                inst->setMetadata(dead_inst, N);
                outs() << "Instruction: marked as dead\n";
            }
            return true;
        }
    }
}


void codeMotion (DomTreeNode *node_DT, BasicBlock *preheader)
{
    SmallVector<Instruction*> toBeMoved;
    outs() << "1\n";
    if (!node_DT)
        return;
    BasicBlock *node = node_DT->getBlock();
    outs() << "BB : " << *node << "\n";
    outs() << "2\n";
    
    outs() << "3\n";
    for (auto inst = node->begin(); inst != node->end(); inst++)
    {
        outs() << *inst << "\n";
        outs() << "4\n";
        bool move = ((!inst->getMetadata(dead_inst) && !node->getTerminator()->getMetadata(exits_dominator)) || !inst->getMetadata(use_dominator) || !inst->getMetadata(invariant_tag));
        clearMetadata(&(*inst));
        if (move)
            continue;
        toBeMoved.push_back(&(*inst));
        outs() << "5\n";   
    }
    outs() << "6\n";

    outs() << "7\n";

    Instruction *last_preheader_inst = &(*(preheader->getTerminator()));

    for (auto inst: toBeMoved){
        // move inst in preheader
        outs() << "To be deleted inst " << *inst << "\n";
        outs() << "Trying to insert before inst " << *last_preheader_inst << "\n";
        inst->removeFromParent();
        inst->insertBefore(last_preheader_inst);
        outs() << "Newly inserted inst " << *inst << "\n";
    }

    for (DomTreeNode *child : node_DT->children())
    {
        codeMotion(child, preheader);
    }

    outs() << "8\n";
}


PreservedAnalyses LoopOpts::run (Loop &L, LoopAnalysisManager &LAM, 
                                    LoopStandardAnalysisResults &LAR, LPMUpdater &LU)
{
    DominatorTree *DT = &LAR.DT;
    //BasicBlock *root_DT = (DT->getRootNode())->getBlock();
    
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
            if (!inst->isBinaryOp())
                continue;
            outs() << "Instruction: " << *inst << "\n";
            if (isLoopInvariant(inst, Loop))
            {   
                LLVMContext &C = inst->getContext();
                MDNode *N = MDNode::get(C, MDString::get(C, "h"));
                inst->setMetadata("invariant", N);
                
                outs() << "Loop invariant instruction detected: " << *inst << "\n";
            }
            markIfUseDominator(inst, DT);
            //markDead(inst,L);
        }
    }

    markExitsDominatorBlocks(L, DT);

    codeMotion(DT->getRootNode(), L.getLoopPreheader());

    return PreservedAnalyses::all();
}