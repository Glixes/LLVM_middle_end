//===-- LocalOpts.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/LocalOpts.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
// #include <llvm/IR/Constants.h>

using namespace llvm;

/** @brief Check a pair of values for one constant.
* If both parameters are constants, it casts only the first one.
*
* @param val1 first value
* @param val2 second value
* @return a pair containing the constant and the value.
*/
std::pair<ConstantInt*, Value*> getConstant (Value *val1, Value *val2)
{
  ConstantInt *C1 = dyn_cast<ConstantInt>(val1);
  ConstantInt *C2 = dyn_cast<ConstantInt>(val2);

  if (C1)
    return std::pair<ConstantInt*, Value*> (C1, val2);
  else if (C2)
    return std::pair<ConstantInt*, Value*> (C2, val1);

  return std::pair<ConstantInt*, Value*> (nullptr, nullptr);
}

/** @brief Check for algebraic identity optimizations.
 * 
 * @param c constant operand
 * @param op opcode
 * @return true if it is an algebraic identity, false otherwise
*/
bool algebraic_identity (ConstantInt* c, unsigned int op)
{
  switch (op)
  {
    case BinaryOperator::Mul:
      if (c->isOne())
        return true;
      break;

    case BinaryOperator::Add:
      if (c->isZero())
        return true;
      break;

    default:
      return false;
      break;
  }
}

bool runOnBasicBlock(BasicBlock &B) {
  for (auto &inst : B) 
  {
    // check on mul operations
    if (!inst.isBinaryOp())
      continue;

    std::pair<ConstantInt*, Value*> operands = getConstant(inst.getOperand(0), inst.getOperand(1));
    if (!operands.first)
      continue;

    // optimized instruction
    Instruction * i = nullptr;
    
    if (Instruction *a = (algebraic_identity(operands.first, inst.getOpcode()) ? 
          dyn_cast<Instruction> (operands.second) : nullptr))
    {
      i = a;
    }
    else if (operands.first->getValue().isPowerOf2()) 
    {
      // create shift constant
      ConstantInt *shift =
          ConstantInt::get(operands.first->getType(), operands.first->getValue().logBase2());
      // create a new instruction shl instruction
      i = BinaryOperator::Create(BinaryOperator::Shl, operands.second, shift);
      // isert the new shift instruction after the considered mul instruction
      i->insertAfter(&inst);
    } 
    // replace the non-optimized instruction uses with the optimized ones
    if (i)
      inst.replaceAllUsesWith(i);
  }

  return true;
}

bool runOnFunction(Function &F) {
  bool Transformed = false;

  for (auto Iter = F.begin(); Iter != F.end(); ++Iter) {
    if (runOnBasicBlock(*Iter)) {
      Transformed = true;
    }
  }

  return Transformed;
}

PreservedAnalyses LocalOpts::run(Module &M, ModuleAnalysisManager &AM) {
  for (auto Fiter = M.begin(); Fiter != M.end(); ++Fiter)
    if (runOnFunction(*Fiter))
      return PreservedAnalyses::none();

  return PreservedAnalyses::all();
}
