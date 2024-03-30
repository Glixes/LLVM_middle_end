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

Operation::Operation(Instruction &inst) : register1(inst.getOperand(0)), register2(inst.getOperand(1)), 
  inst(&inst), C1(dyn_cast<ConstantInt>(register1)), C2(dyn_cast<ConstantInt>(register2)), 
  op(inst.getOpcode()) {}

size_t Operation::getNConstants ()
{
  size_t counter = 0;
  if (C1)
    counter++;
  if (C2)
    counter++;
  return counter;
}

Value* Operation::getOpposite (ConstantInt *C)
{
  if (C == C1)
    return register2;
  else if (C == C2)
    return register1;
  return nullptr;
}

ConstantInt* Operation::getFirstConstantInt ()
{
  return (C1) ? C1 : C2;
}

/** @brief Compute constant folding optimization.
 * 
 * @param o operation examined
 * @return Add instruction containing the result as first operand, and 0 as second operand.
*/
Instruction* getConstantFolding (Operation *o)
{
  APInt fact1 = o->C1->getValue();
  APInt fact2 = o->C2->getValue();

  switch (o->op)
  {
    case BinaryOperator::Add:
      fact1 += fact2;
      break;
    
    case BinaryOperator::Sub:
      fact1 -= fact2;
      break;

    case BinaryOperator::Mul:
      fact1 *= fact2;
      break;

    case BinaryOperator::SDiv:
      fact1.udiv(fact2);
      break;

    case BinaryOperator::UDiv:
      fact1.udiv(fact2);
      break;

    case BinaryOperator::Shl:
      fact1<<=fact2;

    case BinaryOperator::LShr:
      fact1.lshr(fact2);

    default:
      return nullptr;
  }

  ConstantInt *result = ConstantInt::get(o->C1->getType(), fact1.getSExtValue());
  return BinaryOperator::Create(Instruction::Shl, result, 0);
}

/** @brief Check for algebraic identity and in positive cases, return the instruction to replace.
 * 
 * @param operands ConstantInt operands
 * @param inst instruction examined
 * @return Value containing the intruction to replace, nullptr otherwise.
*/
Value* getAlgebraicIdentity (Operation *o)
{
  ConstantInt* C = nullptr;
  switch (o->op)
  {
    case BinaryOperator::Add:
      if (o->C1 && o->C1->isZero())
        C = o->C1;
        LLVM_FALLTHROUGH;
    case BinaryOperator::Sub:
      if (o->C2 && o->C2->isZero())
        C = o->C2;
      break;

    case BinaryOperator::Mul:
      if (o->C1 && o->C1->isOne())
        C = o->C1;
        LLVM_FALLTHROUGH;
    case BinaryOperator::UDiv:
    case BinaryOperator::SDiv:
      if (o->C2 && o->C2->isOne())
        C = o->C2;
      break;
  }

  return (C) ? o->getOpposite(C) : nullptr;
}

Instruction* getStrengthReduction (Operation *o)
{
  ConstantInt *C = o->getFirstConstantInt();
  // Negative constants are not handled
  unsigned int shiftVal = C->getValue().ceilLogBase2();
  ConstantInt *shift = ConstantInt::get(C->getType(), shiftVal);

  Instruction* newinst = nullptr;
  switch (o->op)
  {
      case BinaryOperator::Mul:
      {
        Instruction *shli = BinaryOperator::Create(Instruction::Shl, o->getOpposite(C), shift);
        shli->insertAfter(o->inst);
        unsigned int restVal = (1 << shiftVal) - C->getValue().getSExtValue();
        ConstantInt *rest = ConstantInt::get(C->getType(), restVal);
        if (restVal == 0)
        {
          newinst = shli;
        }
        else if (restVal == 1)
        {
          newinst = BinaryOperator::Create(BinaryOperator::Sub, shli, o->getOpposite(C));
          newinst->insertAfter(shli);
        }
        else if (restVal > 1)
        {
          Instruction *muli = BinaryOperator::Create(BinaryOperator::Mul, o->getOpposite(C), rest);
          muli->insertAfter(shli);
          newinst = BinaryOperator::Create(BinaryOperator::Sub, shli, muli);
          newinst->insertAfter(muli);
        }
        break;
      }

      case BinaryOperator::UDiv:
      case BinaryOperator::SDiv:
      {
        if (C == o->C2 && C->getValue().isPowerOf2())
        {
          newinst = BinaryOperator::Create(Instruction::LShr, o->getOpposite(C), shift);
          newinst->insertAfter(o->inst);
        }
        break;
      }
  }
  return newinst;
}

bool runOnBasicBlock(BasicBlock &B) 
{
  bool optimizedLastCycle = false;
  do 
  {
    optimizedLastCycle = false;
    for (auto &inst : B) 
    {
      // check for binary operations
      if (!inst.isBinaryOp())
        continue;

      Operation *o = new Operation (inst);
      size_t nConstants = o->getNConstants();
      if (nConstants == 0)
        continue;

      /* Optimized instruction.
      * The Value type is necessary in order to include also the Argument objects (representig
      * function's arguments).
      */
      Value *i = (nConstants == 2) ? getConstantFolding(o) : getAlgebraicIdentity(o);
      if (!i)
        i = getStrengthReduction(o);

      // replace the non-optimized instruction uses with the optimized ones
      if (i)
      {
        inst.replaceAllUsesWith(i);
        optimizedLastCycle = true;
      }
    }
  }
  while (optimizedLastCycle && false);

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