/*********************                                                        */
/*! \file lean_rules.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of lean rules
 **/

#include "proof/lean/lean_rules.h"

#include <iostream>

#include "expr/proof_checker.h"

namespace cvc5 {
namespace proof {

const char* toString(LeanRule id)
{
  switch (id)
  {
    case LeanRule::SCOPE: return "scope";
    case LeanRule::CL_ASSUME: return "clAssume";
    case LeanRule::CL_OR: return "clOr";
    case LeanRule::TH_ASSUME: return "thAssume";
    case LeanRule::LIFT_N_OR_TO_IMP: return "liftNOrToImp";
    case LeanRule::LIFT_N_OR_TO_NEG: return "liftNOrToNeg";

    case LeanRule::R0: return "R0";
    case LeanRule::R0_PARTIAL: return "R0";
    case LeanRule::R1: return "R1";
    case LeanRule::R1_PARTIAL: return "R1";

    case LeanRule::FACTORING: return "factoring";
    case LeanRule::REORDER: return "reorder";
    case LeanRule::EQ_RESOLVE: return "eqResolve";
    case LeanRule::MODUS_PONENS: return "modusPonens";
    case LeanRule::NOT_NOT_ELIM: return "notNotElim";
    case LeanRule::CONTRADICTION: return "contradiction";
    case LeanRule::AND_ELIM: return "andElim";
    case LeanRule::NOT_OR_ELIM: return "notOrElim";
    case LeanRule::AND_INTRO: return "andIntro";
    case LeanRule::AND_INTRO_PARTIAL: return "andIntro";
    case LeanRule::IMPLIES_ELIM: return "impliesElim";
    case LeanRule::NOT_IMPLIES1: return "notImplies1";
    case LeanRule::NOT_IMPLIES2: return "notImplies2";
    case LeanRule::EQUIV_ELIM1: return "equivElim1";
    case LeanRule::EQUIV_ELIM2: return "equivElim2";
    case LeanRule::NOT_EQUIV_ELIM1: return "notEquivElim1";
    case LeanRule::NOT_EQUIV_ELIM2: return "notEquivElim2";
    case LeanRule::XOR_ELIM1: return "xorElim1";
    case LeanRule::XOR_ELIM2: return "xorElim2";
    case LeanRule::NOT_XOR_ELIM1: return "notXorElim1";
    case LeanRule::NOT_XOR_ELIM2: return "notXorElim2";
    case LeanRule::ITE_ELIM1: return "iteElim1";
    case LeanRule::ITE_ELIM2: return "iteElim2";
    case LeanRule::NOT_ITE_ELIM1: return "notIteElim1";
    case LeanRule::NOT_ITE_ELIM2: return "notIteElim2";
    case LeanRule::NOT_AND: return "notAnd";
    case LeanRule::CNF_AND_POS: return "@cnfAndPos";
    case LeanRule::CNF_AND_NEG: return "@cnfAndNeg";
    case LeanRule::CNF_OR_POS: return "@cnfOrPos";
    case LeanRule::CNF_OR_NEG: return "@cnfOrNeg";

    case LeanRule::CNF_IMPLIES_POS: return "cnfImpliesPos";
    case LeanRule::CNF_IMPLIES_NEG1: return "cnfImpliesNeg1";
    case LeanRule::CNF_IMPLIES_NEG2: return "cnfImpliesNeg2";
    case LeanRule::CNF_EQUIV_POS1: return "cnfEquivPos1";
    case LeanRule::CNF_EQUIV_POS2: return "cnfEquivPos2";
    case LeanRule::CNF_EQUIV_NEG1: return "cnfEquivNeg1";
    case LeanRule::CNF_EQUIV_NEG2: return "cnfEquivNeg2";
    case LeanRule::CNF_XOR_POS1: return "cnfXorPos1";
    case LeanRule::CNF_XOR_POS2: return "cnfXorPos2";
    case LeanRule::CNF_XOR_NEG1: return "cnfXorNeg1";
    case LeanRule::CNF_XOR_NEG2: return "cnfXorNeg2";
    case LeanRule::CNF_ITE_POS1: return "cnfItePos1";
    case LeanRule::CNF_ITE_POS2: return "cnfItePos2";
    case LeanRule::CNF_ITE_POS3: return "cnfItePos3";
    case LeanRule::CNF_ITE_NEG1: return "cnfIteNeg1";
    case LeanRule::CNF_ITE_NEG2: return "cnfIteNeg2";
    case LeanRule::CNF_ITE_NEG3: return "cnfIteNeg3";
    case LeanRule::TRUST: return "trust";
    case LeanRule::TH_TRUST: return "thTrust";
    case LeanRule::TH_TRUST_VALID: return "thTrustValid";

    case LeanRule::CONG: return "cong";
    case LeanRule::CONG_PARTIAL: return "cong";
    case LeanRule::REFL: return "@refl";
    case LeanRule::REFL_PARTIAL: return "@refl";
    case LeanRule::TRANS: return "trans";
    case LeanRule::TRANS_PARTIAL: return "trans";
    case LeanRule::SYMM: return "symm";
    case LeanRule::NEG_SYMM: return "negSymm";

    case LeanRule::TRUE_INTRO: return "trueIntro";
    case LeanRule::TRUE_ELIM: return "trueElim";
    case LeanRule::FALSE_INTRO: return "falseIntro";
    case LeanRule::FALSE_ELIM: return "falseElim";

    case LeanRule::STRING_LENGTH_POS: return "stringLengthPos";
    case LeanRule::ARITH_SUM_UB: return "arithSumUb";
    case LeanRule::ARITH_MULT_POS: return "arithMultPos";
    case LeanRule::ARITH_MULT_NEG: return "arithMultNeg";
    case LeanRule::EVALUATE: return "evaluate";

    case LeanRule::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, LeanRule id)
{
  out << toString(id);
  return out;
}

LeanRule getLeanRule(Node n)
{
  // Trace("test-lean") << "getLeanRule::converting " << n;
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    // Trace("test-lean") << ", getting rule " << static_cast<LeanRule>(id)
    //                    << "\n";
    return static_cast<LeanRule>(id);
  }
  // Trace("test-lean") << ", failed get  int\n";
  return LeanRule::UNKNOWN;
}

}  // namespace proof
}  // namespace cvc5
