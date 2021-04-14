/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proof manager of SmtEngine.
 */

#include "cvc4_private.h"

#ifndef CVC5__SMT__PROOF_MANAGER_H
#define CVC5__SMT__PROOF_MANAGER_H

#include "context/cdhashmap.h"
#include "expr/node.h"

namespace cvc5 {

class ProofChecker;
class ProofNode;
class ProofNodeManager;
class SmtEngine;

namespace smt {

class Assertions;
class DefinedFunction;
class PreprocessProofGenerator;
class ProofPostproccess;

/**
 * This class is responsible for managing the proof output of SmtEngine, as
 * well as setting up the global proof checker and proof node manager.
 *
 * The proof production of an SmtEngine is directly impacted by whether, and
 * how, we are producing unsat cores:
 *
 * - If we are producing unsat cores using the old proof infrastructure, then
 *   SmtEngine will not have proofs in the sense of this proof manager.
 *
 * - If we are producing unsat cores using this proof infrastructure, then the
 *   SmtEngine will have proofs using this proof manager (if --produce-proofs
 *   was not passed by the user it will be activated), but these proofs will
 *   only cover preprocessing and the prop engine, i.e., the theory engine will
 *   not have proofs.
 *
 * - If we are not producing unsat cores then the SmtEngine will have proofs as
 *   long as --produce-proofs was given.
 *
 * - If SmtEngine has been configured in a way that is incompatible with proofs
 *   and it was set to produce unsat cores using proofs, then unsat core
 *   production will be disabled.
 */
class PfManager
{
  /** The type of our internal map of defined functions */
  using DefinedFunctionMap =
      context::CDHashMap<Node, smt::DefinedFunction, NodeHashFunction>;

 public:
  PfManager(context::UserContext* u, SmtEngine* smte);
  ~PfManager();
  /**
   * Print the proof on the given output stream.
   *
   * The argument pfn is the proof for false in the current context.
   *
   * Throws an assertion failure if pg cannot provide a closed proof with
   * respect to assertions in as and df. For the latter, entries in the defined
   * function map correspond to equalities of the form (= f (lambda (...) t)),
   * which are considered assertions in the final proof.
   */
  void printProof(std::ostream& out,
                  std::shared_ptr<ProofNode> pfn,
                  Assertions& as,
                  DefinedFunctionMap& df);
  /**
   * Check proof, same as above, without printing.
   */
  void checkProof(std::shared_ptr<ProofNode> pfn,
                  Assertions& as,
                  DefinedFunctionMap& df);

  /**
   * Get final proof.
   *
   * The argument pfn is the proof for false in the current context.
   */
  std::shared_ptr<ProofNode> getFinalProof(std::shared_ptr<ProofNode> pfn,
                                           Assertions& as,
                                           DefinedFunctionMap& df);
  //--------------------------- access to utilities
  /** Get a pointer to the ProofChecker owned by this. */
  ProofChecker* getProofChecker() const;
  /** Get a pointer to the ProofNodeManager owned by this. */
  ProofNodeManager* getProofNodeManager() const;
  /** Get the proof generator for proofs of preprocessing. */
  smt::PreprocessProofGenerator* getPreprocessProofGenerator() const;
  //--------------------------- end access to utilities
 private:
  /**
   * Set final proof, which initializes d_finalProof to the given proof node of
   * false, postprocesses it, and stores it in d_finalProof.
   */
  void setFinalProof(std::shared_ptr<ProofNode> pfn,
                     Assertions& as,
                     DefinedFunctionMap& df);
  /**
   * Get assertions from the assertions
   */
  void getAssertions(Assertions& as,
                     DefinedFunctionMap& df,
                     std::vector<Node>& assertions);
  /** The false node */
  Node d_false;
  /** For the new proofs module */
  std::unique_ptr<ProofChecker> d_pchecker;
  /** A proof node manager based on the above checker */
  std::unique_ptr<ProofNodeManager> d_pnm;
  /** The preprocess proof generator. */
  std::unique_ptr<smt::PreprocessProofGenerator> d_pppg;
  /** The proof post-processor */
  std::unique_ptr<smt::ProofPostproccess> d_pfpp;
  /**
   * The final proof produced by the SMT engine.
   * Combines the proofs of preprocessing, prop engine and theory engine, to be
   * connected by setFinalProof().
   */
  std::shared_ptr<ProofNode> d_finalProof;
}; /* class SmtEngine */

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__PROOF_MANAGER_H */
