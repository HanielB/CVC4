/*********************                                                        */
/*! \file eq_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A proof as produced by the equality engine.
 **
 **/

#include "cvc4_private.h"

#pragma once

#include <deque>
#include <memory>
#include <queue>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/proof.h"
#include "theory/uf/equality_engine_types.h"

namespace CVC4 {
namespace theory {
namespace eq {

class EqProof
{
 public:
  class PrettyPrinter
  {
   public:
    virtual ~PrettyPrinter() {}
    virtual std::string printTag(unsigned tag) = 0;
  };

  EqProof() : d_id(MERGED_THROUGH_REFLEXIVITY) {}
  unsigned d_id;
  Node d_node;
  std::vector<std::shared_ptr<EqProof>> d_children;
  /**
   * Debug print this proof on debug trace c with tabulation tb and pretty
   * printer prettyPrinter.
   */
  void debug_print(const char* c,
                   unsigned tb = 0,
                   PrettyPrinter* prettyPrinter = nullptr) const;
  /**
   * Debug print this proof on output stream os with tabulation tb and pretty
   * printer prettyPrinter.
   */
  void debug_print(std::ostream& os,
                   unsigned tb = 0,
                   PrettyPrinter* prettyPrinter = nullptr) const;

  /** Add to proof
   *
   * This method adds all of its steps to p via calls to CDProof::addStep.
   *
   * This method can be seen as a translation from EqProof to ProofNode. It is
   * temporary until we update the EqualityEngine to the new proof
   * infrastructure.
   *
   * It returns the node that is the conclusion of the proof as added to p.
   */
  Node addToProof(CDProof* p) const;

 private:
  void maybeFoldTransitivityChildren(std::vector<Node>& premises,
                                     CDProof* p) const;

  void maybeAddSymmOrTrueIntroToProof(unsigned i,
                                      std::vector<Node>& premises,
                                      bool first,
                                      Node termInEq,
                                      CDProof* p) const;

}; /* class EqProof */

}  // Namespace eq
}  // Namespace theory
}  // Namespace CVC4
