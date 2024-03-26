//===-- LocalOpts.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/LocalOpts.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"
#include <llvm/IR/Constants.h>

using namespace llvm;

bool runOnBasicBlock(BasicBlock &B) 
{
  for (auto &inst : B)
  {
    // check on mul operations
    if (inst.getOpcode() != BinaryOperator::Mul)
      continue;
    // get both operand
    Value *fact1 = inst.getOperand(0);
    Value *fact2 = inst.getOperand(1);
    // check if one of the operands is a power of 2 constant
    ConstantInt *C1 = dyn_cast<ConstantInt>(fact1);
    ConstantInt *C2 = dyn_cast<ConstantInt>(fact2);
    Instruction *NewShl = nullptr;
    if (C1 && C1->getValue().isPowerOf2())
    {
      // create shift constant
      ConstantInt *shift = ConstantInt::get(C1->getType(), C1->getValue().logBase2());
      // create a new instruction shl instruction
      NewShl = BinaryOperator::Create(BinaryOperator::Shl, fact2, shift);
    }
    else if (C2 && C2->getValue().isPowerOf2())
    {
      // create shift constant
      ConstantInt *shift = ConstantInt::get(C2->getType(), C2->getValue().logBase2());
      // create a new instruction shl instruction
      NewShl = BinaryOperator::Create(BinaryOperator::Shl, fact1, shift);
    }
    else
      continue;
    // isert the new shift instruction after the considered mul instruction
    NewShl->insertAfter(&inst);
    // replace every the mul instruction use with a shift instruction use
    inst.replaceAllUsesWith(NewShl);
  }

  return true;
}

/*
bool runOnBasicBlock(BasicBlock &B) 
{
  for (auto i = B.begin(); i != B.end(); i++)
  {
    Instruction &inst = *i;
    if (inst.getOpcode() != BinaryOperator::Mul)
      continue;

    ConstantInt *C = dyn_cast<ConstantInt>(i->getOperand(1));
    if (!C) 
      continue;

    const APInt value = C->getValue();
    if (!value.isPowerOf2())
      continue;

    int factor = value.logBase2();

    LLVMContext &context = i->getParent()->getContext();
    Value *shift_val = ConstantInt::get(llvm::Type::getInt32Ty(context), factor);

    Instruction *NewInst = BinaryOperator::Create(BinaryOperator::Shl, i->getOperand(0), shift_val);

    NewInst->insertAfter(&inst);
    inst.replaceAllUsesWith(NewInst);
  }


  return true;
  }
*/

bool runOnFunction(Function &F) {
  bool Transformed = false;

  for (auto Iter = F.begin(); Iter != F.end(); ++Iter) {
    if (runOnBasicBlock(*Iter)) {
      Transformed = true;
    }
  }

  return Transformed;
}


PreservedAnalyses LocalOpts::run(Module &M,
                                      ModuleAnalysisManager &AM) {
  for (auto Fiter = M.begin(); Fiter != M.end(); ++Fiter)
    if (runOnFunction(*Fiter))
      return PreservedAnalyses::none();
  
  return PreservedAnalyses::all();
}

