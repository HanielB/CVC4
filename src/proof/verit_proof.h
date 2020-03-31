/*********************                                                        */
/*! \file veriT_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A proof to be output in the veriT proof format.
 **/

#include "cvc4_private.h"
#include "expr/node.h"
#include "proof/new_proof.h"
#include "theory/theory.h"

#ifndef CVC4__VERIT_PROOF_H
#define CVC4__VERIT_PROOF_H

namespace CVC4 {

class VeritProofStep : public ProofStep
{
 public:
  VeritProofStep(unsigned id, NewProofRule rule = RULE_UNDEF);
  ~VeritProofStep() override {}

  void addRule(NewProofRule rule);
  void addPremises(std::vector<unsigned>& reasons);
  void addPremises(unsigned reason);
  void addConclusion(Node conclusion);
  void addConclusion(std::vector<Node>& conclusion);

  const std::vector<Node>& getConclusion() const;
  const std::vector<unsigned>& getPremises() const;

 private:
  std::vector<Node> d_conclusion;
  std::vector<unsigned> d_premises;
};

class VeritProof : public NewProof
{
 public:
  ~VeritProof() override {}
  void toStream(std::ostream& out) const override;
  void finishProof() override {}
  ClauseId addProofStep(NewProofRule rule) override;
  ClauseId addProofStep();

  ClauseId addProofStep(NewProofRule rule,
                        std::vector<unsigned>& reasons,
                        Node conclusion);
  ClauseId addProofStep(NewProofRule rule,
                        std::vector<unsigned>& reasons,
                        std::vector<Node>& conclusion);

  ClauseId addProofStep(NewProofRule rule, Node conclusion);
  // add to last created proof step
  void addToLastProofStep(Node conclusion);
  void addToLastProofStep(std::vector<unsigned>& reasons, Node conclusion);

  // add to proof step of the given id
  void addToProofStep(ClauseId id, Node conclusion);
  void addToProofStep(ClauseId id, NewProofRule rule, Node conclusion);
  void addToProofStep(ClauseId id,
                      NewProofRule rule,
                      std::vector<Node>& conclusion);
  void addToProofStep(ClauseId id,
                      NewProofRule rule,
                      std::vector<ClauseId>& reasons,
                      std::vector<Node>& conclusion);
  ClauseId addTheoryProof(theory::EqProof* proof);

  const std::vector<VeritProofStep>& getProofSteps() const;

  ClauseId getId() { return d_nextId; }

 private:
  unsigned getNextId() { return d_nextId++; }

  ClauseId processTheoryProof(theory::EqProof* proof);
  /** traverse proof recursively and for every congruence rule with a non-null
   * conclusion, flatten all congruence application in children with nullary
   * conclusions */
  // void flattenBinCongs(theory::EqProof* proof,
  //                      std::vector<theory::EqProof*>& premises);

  void printRule(std::ostream& out, NewProofRule r) const;
  void printStep(std::ostream& out, VeritProofStep* s) const;

  std::vector<VeritProofStep> d_proofSteps;
};

}  // namespace CVC4

#endif /* CVC4__VERIT_PROOF_H */
