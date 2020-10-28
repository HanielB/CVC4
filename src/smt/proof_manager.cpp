/*********************                                                        */
/*! \file proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof manager of the SMT engine
 **/

#include "smt/proof_manager.h"

#include "expr/proof_node_algorithm.h"
#include "options/base_options.h"
#include "options/smt_options.h"
#include "proof/lean/lean_post_processor.h"
#include "proof/lean/lean_printer.h"
#include "smt/assertions.h"

namespace CVC4 {
namespace smt {

PfManager::PfManager(context::UserContext* u, SmtEngine* smte)
    : d_pchecker(new ProofChecker(options::proofNewPedantic())),
      d_pnm(new ProofNodeManager(d_pchecker.get())),
      d_rewriteDb(new theory::RewriteDb),
      d_pppg(new PreprocessProofGenerator(
          d_pnm.get(), u, "smt::PreprocessProofGenerator")),
      d_pfpp(new ProofPostproccess(d_pnm.get(), smte, d_pppg.get())),
      d_lpfpp(new proof::LeanProofPostprocess(d_pnm.get())),
      d_finalProof(nullptr)
{
  // add rules to eliminate here
  if (options::proofGranularityMode() != options::ProofGranularityMode::OFF)
  {
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_EQ_INTRO);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_INTRO);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_ELIM);
    d_pfpp->setEliminateRule(PfRule::MACRO_SR_PRED_TRANSFORM);
    d_pfpp->setEliminateRule(PfRule::MACRO_RESOLUTION);
    if (options::proofGranularityMode()
        != options::ProofGranularityMode::REWRITE)
    {
      d_pfpp->setEliminateRule(PfRule::SUBS);
      d_pfpp->setEliminateRule(PfRule::REWRITE);
      if (options::proofGranularityMode()
          != options::ProofGranularityMode::THEORY_REWRITE)
      {
        // this eliminates theory rewriting steps with finer-grained DSL rules
        d_pfpp->setEliminateRule(PfRule::THEORY_REWRITE);
      }
    }
  }
  d_false = NodeManager::currentNM()->mkConst(false);
}

PfManager::~PfManager() {}

void PfManager::setFinalProof(std::shared_ptr<ProofNode> pfn,
                              context::CDList<Node>* al)
{
  Assert(al != nullptr);
  // Note this assumes that setFinalProof is only called once per unsat
  // response. This method would need to cache its result otherwise.
  Trace("smt-proof") << "SmtEngine::setFinalProof(): get proof body...\n";

  if (Trace.isOn("smt-proof-debug"))
  {
    Trace("smt-proof-debug")
        << "SmtEngine::setFinalProof(): Proof node for false:\n";
    Trace("smt-proof-debug") << *pfn.get() << std::endl;
    Trace("smt-proof-debug") << "=====" << std::endl;
  }

  if (Trace.isOn("smt-proof"))
  {
    Trace("smt-proof") << "SmtEngine::setFinalProof(): get free assumptions..."
                       << std::endl;
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(pfn.get(), fassumps);
    Trace("smt-proof")
        << "SmtEngine::setFinalProof(): initial free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("smt-proof") << "- " << a << std::endl;
    }
  }

  std::vector<Node> assertions;
  Trace("smt-proof") << "SmtEngine::setFinalProof(): assertions are:\n";
  for (context::CDList<Node>::const_iterator i = al->begin(); i != al->end();
       ++i)
  {
    Node n = *i;
    Trace("smt-proof") << "- " << n << std::endl;
    assertions.push_back(n);
  }
  Trace("smt-proof") << "=====" << std::endl;

  Trace("smt-proof") << "SmtEngine::setFinalProof(): postprocess...\n";
  Assert(d_pfpp != nullptr);
  d_pfpp->setAssertions(assertions);
  d_pfpp->process(pfn);

  Trace("smt-proof") << "SmtEngine::setFinalProof(): make scope...\n";

  // Now make the final scope, which ensures that the only open leaves
  // of the proof are the assertions.
  d_finalProof = d_pnm->mkScope(pfn, assertions);
  Trace("smt-proof") << "SmtEngine::setFinalProof(): finished.\n";
}

void PfManager::printProof(std::shared_ptr<ProofNode> pfn, Assertions& as)
{
  Trace("smt-proof") << "PfManager::printProof: start" << std::endl;
  std::shared_ptr<ProofNode> fp = getFinalProof(pfn, as);
  // TODO (proj #37) according to the proof format, post process the proof node
  // TODO (proj #37) according to the proof format, print the proof node
  // leanPrinter(out, fp.get());
  std::ostream& out = *options::out();
  if (options::proofFormatMode() == options::ProofFormatMode::LEAN)
  {
    d_lpfpp->process(fp);
    proof::leanPrinter(out, fp);
  }
  out << "(proof\n";
  out << *fp;
  out << "\n)\n";
}

void PfManager::checkProof(std::shared_ptr<ProofNode> pfn, Assertions& as)
{
  Trace("smt-proof") << "PfManager::checkProof: start" << std::endl;
  std::shared_ptr<ProofNode> fp = getFinalProof(pfn, as);
  Trace("smt-proof-debug") << "PfManager::checkProof: returned " << *fp.get()
                           << std::endl;
}

ProofChecker* PfManager::getProofChecker() const { return d_pchecker.get(); }

ProofNodeManager* PfManager::getProofNodeManager() const { return d_pnm.get(); }

theory::RewriteDb* PfManager::getRewriteDatabase() const
{
  return d_rewriteDb.get();
}

smt::PreprocessProofGenerator* PfManager::getPreprocessProofGenerator() const
{
  return d_pppg.get();
}

std::shared_ptr<ProofNode> PfManager::getFinalProof(
    std::shared_ptr<ProofNode> pfn, Assertions& as)
{
  context::CDList<Node>* al = as.getAssertionList();
  setFinalProof(pfn, al);
  Assert(d_finalProof);
  return d_finalProof;
}

}  // namespace smt
}  // namespace CVC4
