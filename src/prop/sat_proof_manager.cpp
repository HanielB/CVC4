/*********************                                                        */
/*! \file sat_proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the proof manager for Minisat
 **/

#include "prop/sat_proof_manager.h"

#include "expr/proof_node_algorithm.h"
#include "options/smt_options.h"
#include "prop/cnf_stream.h"
#include "prop/minisat/minisat.h"
#include "theory/theory_proof_step_buffer.h"

namespace CVC4 {
namespace prop {

SatProofManager::SatProofManager(Minisat::Solver* solver,
                                 CnfStream* cnfStream,
                                 context::UserContext* userContext,
                                 ProofNodeManager* pnm)
    : d_solver(solver),
      d_cnfStream(cnfStream),
      d_pnm(pnm),
      d_resChains(pnm, true, userContext),
      d_resChainPg(userContext, pnm),
      d_assumptions(userContext),
      d_conflictLit(undefSatVariable)
{
  d_false = NodeManager::currentNM()->mkConst(false);
  d_true = NodeManager::currentNM()->mkConst(true);
}

void SatProofManager::printClause(const Minisat::Clause& clause)
{
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    SatLiteral satLit = MinisatSatSolver::toSatLiteral(clause[i]);
    Trace("sat-proof") << satLit << " ";
  }
}

Node SatProofManager::getClauseNode(SatLiteral satLit)
{
  Assert(d_cnfStream->getNodeCache().find(satLit)
         != d_cnfStream->getNodeCache().end())
      << "SatProofManager::getClauseNode: literal " << satLit
      << " undefined.\n";
  return d_cnfStream->getNodeCache()[satLit];
}

Node SatProofManager::getClauseNode(const Minisat::Clause& clause)
{
  std::vector<Node> clauseNodes;
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    SatLiteral satLit = MinisatSatSolver::toSatLiteral(clause[i]);
    Assert(d_cnfStream->getNodeCache().find(satLit)
           != d_cnfStream->getNodeCache().end())
        << "SatProofManager::getClauseNode: literal " << satLit
        << " undefined\n";
    clauseNodes.push_back(d_cnfStream->getNodeCache()[satLit]);
  }
  // order children by node id
  std::sort(clauseNodes.begin(), clauseNodes.end());
  return NodeManager::currentNM()->mkNode(kind::OR, clauseNodes);
}

void SatProofManager::startResChain(const Minisat::Clause& start)
{
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::startResChain: ";
    printClause(start);
    Trace("sat-proof") << "\n";
  }
  d_resLinks.push_back(
      std::make_tuple(getClauseNode(start), Node::null(), true));
}

void SatProofManager::addResolutionStep(Minisat::Lit lit, bool redundant)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(lit);
  Node litNode = d_cnfStream->getNodeCache()[satLit];
  bool negated = satLit.isNegated();
  Assert(!negated || litNode.getKind() == kind::NOT);
  if (!redundant)
  {
    Trace("sat-proof") << "SatProofManager::addResolutionStep: {"
                       << satLit.isNegated() << "} [" << satLit << "] "
                       << ~satLit << "\n";
    // if lit is negated then the chain resolution construction will use it as a
    // pivot occurring as is in the second clause and the node under the
    // negation in the first clause
    d_resLinks.push_back(std::make_tuple(d_cnfStream->getNodeCache()[~satLit],
                                         negated ? litNode[0] : litNode,
                                         !satLit.isNegated()));
  }
  else
  {
    Trace("sat-proof") << "SatProofManager::addResolutionStep: redundant lit "
                       << satLit << " stored\n";
    d_redundantLits.push_back(satLit);
  }
}

void SatProofManager::addResolutionStep(const Minisat::Clause& clause,
                                        Minisat::Lit lit)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(lit);
  Node litNode = d_cnfStream->getNodeCache()[satLit];
  bool negated = satLit.isNegated();
  Assert(!negated || litNode.getKind() == kind::NOT);
  Node clauseNode = getClauseNode(clause);
  // if lit is negative then the chain resolution construction will use it as a
  // pivot occurring as is in the second clause and the node under the
  // negation in the first clause, which means that the third argument of the
  // tuple must be false
  d_resLinks.push_back(
      std::make_tuple(clauseNode, negated ? litNode[0] : litNode, negated));
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::addResolutionStep: {"
                       << satLit.isNegated() << "} [" << ~satLit << "] ";
    printClause(clause);
    Trace("sat-proof") << "\nSatProofManager::addResolutionStep:\t"
                       << clauseNode << "\n";
  }
}

void SatProofManager::endResChain(Minisat::Lit lit)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(lit);
  Trace("sat-proof") << "SatProofManager::endResChain: chain_res for "
                     << satLit;
  endResChain(getClauseNode(satLit), {satLit});
}

void SatProofManager::endResChain(const Minisat::Clause& clause)
{
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::endResChain: chain_res for ";
    printClause(clause);
  }
  std::multiset<SatLiteral> clauseLits;
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    clauseLits.insert(MinisatSatSolver::toSatLiteral(clause[i]));
  }
  endResChain(getClauseNode(clause), clauseLits);
}

void SatProofManager::endResChain(
    Node conclusion, const std::multiset<SatLiteral>& conclusionLits)
{
  Trace("sat-proof") << ", " << conclusion << "\n";
  // first process redundant literals
  std::set<SatLiteral> visited;
  unsigned pos = d_resLinks.size();
  for (SatLiteral satLit : d_redundantLits)
  {
    processRedundantLit(satLit, conclusionLits, visited, pos);
  }
  d_redundantLits.clear();
  // build resolution chain
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> children, args;
  for (unsigned i = 0, size = d_resLinks.size(); i < size; ++i)
  {
    Node clause, pivot;
    bool posFirst;
    std::tie(clause, pivot, posFirst) = d_resLinks[i];
    children.push_back(clause);
    Trace("sat-proof") << "SatProofManager::endResChain:   ";
    if (i > 0)
    {
      Trace("sat-proof") << "{" << posFirst << "} ["
                         << d_cnfStream->getTranslationCache()[pivot] << "] ";
    }
    // special case for clause (or l1 ... ln) being a single literal
    // corresponding itself to a clause, which is indicated by the pivot being
    // of the form (not (or l1 ... ln))
    if (clause.getKind() == kind::OR
        && !(pivot.getKind() == kind::NOT && pivot[0].getKind() == kind::OR
             && pivot[0] == clause))
    {
      for (unsigned j = 0, sizeJ = clause.getNumChildren(); j < sizeJ; ++j)
      {
        Trace("sat-proof") << d_cnfStream->getTranslationCache()[clause[j]];
        if (j < sizeJ - 1)
        {
          Trace("sat-proof") << ", ";
        }
      }
    }
    else
    {
      Assert(d_cnfStream->getTranslationCache().find(clause)
             != d_cnfStream->getTranslationCache().end())
          << "clause node " << clause
          << " treated as unit has no literal. Pivot is " << pivot << "\n";
      Trace("sat-proof") << d_cnfStream->getTranslationCache()[clause];
    }
    Trace("sat-proof") << " : ";
    if (i > 0)
    {
      args.push_back(posFirst ? d_true : d_false);
      args.push_back(pivot);
      Trace("sat-proof") << "{" << posFirst << "} [" << pivot << "] ";
    }
    Trace("sat-proof") << clause << "\n";
  }
  // whether no-op
  if (children.size() == 1)
  {
    Trace("sat-proof") << "SatProofManager::endResChain: no-op. The conclusion "
                       << conclusion << " is set-equal to premise "
                       << children[0] << "\n";
    return;
  }
  if (Trace.isOn("sat-proof") && d_resChains.hasGenerator(conclusion))
  {
    Trace("sat-proof") << "SatProofManager::endResChain: replacing proof of "
                       << conclusion << "\n";
  }
  // buffer for steps
  theory::TheoryProofStepBuffer psb;
  // since the conclusion can be both reordered and without duplicates and the
  // SAT solver does not record this information, we must recompute it here so
  // the proper CHAIN_RESOLUTION step can be created
  //
  // compute initial chain resolution conclusion
  Node chainConclusion = d_pnm->getChecker()->checkDebug(
      PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "");
  if (chainConclusion != conclusion)
  {
    // there are three differences that may exist between the computed
    // conclusion above and the actual conclusion:
    //
    // 1 - chainConclusion may contains literals not in the conclusion, which
    //     means that some resolution links are being used more than once to
    //     eliminate such literals.
    // 2 - duplicates
    // 3 - order.
    //
    // Both 2 and 3 are handled by factorReorderElimDoubleNeg.
    //
    // To fix 1 we get the literals in chainCoclusion not in conclusion, look
    // for the resolution link that eliminates it and add that clause as a
    // premise as many times as the offending literal occurs. Note that if this
    // link contains literals not in chainConclusion, we have to repeat this
    // process, recursively, for all such literals.
    std::vector<Node> chainConclusionLits{chainConclusion.begin(),
                                          chainConclusion.end()};
    std::vector<Node> conclusionLitsVec;
    // whether conclusion is unit
    if (conclusionLits.size() == 1)
    {
      conclusionLitsVec.push_back(conclusion);
    }
    else
    {
      conclusionLitsVec.insert(
          conclusionLitsVec.end(), conclusion.begin(), conclusion.end());
    }
    if (processCrowdingLits(
            chainConclusionLits, conclusionLitsVec, children, args))
    {
      // added more resolution steps, so recompute conclusion
      chainConclusion = d_pnm->getChecker()->checkDebug(
          PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "");
      Trace("sat-proof") << "SatProofManager::endResChain: previous conclusion "
                            "crowded, new steps:\n";
      if (Trace.isOn("sat-proof"))
      {
        for (unsigned i = 0, size = children.size(); i < size; ++i)
        {
          Trace("sat-proof") << "SatProofManager::endResChain:   ";
          if (i > 0)
          {
            Trace("sat-proof") << "{" << (args[2 * (i - 1)] == d_true ? 1 : 0)
                               << "} [" << args[(2 * i) - 1] << "] ";
          }
          Trace("sat-proof") << children[i] << "\n";
        }
      }
      Trace("sat-proof")
          << "SatProofManager::endResChain: new computed conclusion: "
          << chainConclusion << "\n";
    }
    Trace("sat-proof") << "SatProofManager::endResChain: creating step for "
                          "computed conclusion "
                       << chainConclusion << "\n";
    psb.addStep(PfRule::CHAIN_RESOLUTION, children, args, chainConclusion);
    // if this happens that chainConclusion needs to be factored and/or
    // reordered, which in either case can be done only if it's not a unit
    // clause.
    CVC4_UNUSED Node reducedChainConclusion =
        psb.factorReorderElimDoubleNeg(chainConclusion);
    Assert(reducedChainConclusion == conclusion)
        << "original conclusion " << conclusion
        << "\nis different from computed conclusion " << chainConclusion
        << "\nafter factorReorderElimDoubleNeg " << reducedChainConclusion;
  }
  else
  {
    Trace("sat-proof") << "SatProofManager::endResChain: creating step for "
                          "computed conclusion "
                       << chainConclusion << "\n";
    psb.addStep(PfRule::CHAIN_RESOLUTION, children, args, chainConclusion);
  }
  // buffer the steps in the resolution chain proof generator
  const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
  for (const std::pair<Node, ProofStep>& step : steps)
  {
    Trace("sat-proof") << "SatProofManager::endResChain: adding for "
                       << step.first << " step " << step.second << "\n";
    d_resChainPg.addStep(step.first, step.second);
    // the premises of this resolution may not have been justified yet, so we do
    // not pass assumptions to check closedness
    d_resChains.addLazyStep(step.first, &d_resChainPg);
  }
  // clearing
  d_resLinks.clear();
}

unsigned SatProofManager::findLastInclusion(Node lit)
{
  // find the last link that introduces the offending literal
  for (unsigned i = d_resLinks.size(); i > 0; --i)
  {
    Node clause, pivot;
    bool posFirst;
    std::tie(clause, pivot, posFirst) = d_resLinks[i-1];
    // notice that only non-unit clauses may be introducing the offending
    // literal, so we don't need to differentiate unit from non-unit
    if (clause.getKind() != kind::OR)
    {
      continue;
    }
    if (std::find(clause.begin(), clause.end(), lit) != clause.end())
    {
      return i - 1;
    }
  }
  return d_resLinks.size();
}

bool SatProofManager::processCrowdingLits(
    const std::vector<Node>& clauseLits,
    const std::vector<Node>& targetClauseLits,
    std::vector<Node>& premises,
    std::vector<Node>& pivots)
{
  // offending lits and how many times they occur
  std::map<Node, unsigned> offending;
  for (unsigned i = 0, size = clauseLits.size(); i < size; ++i)
  {
    if (std::find(
            targetClauseLits.begin(), targetClauseLits.end(), clauseLits[i])
        == targetClauseLits.end())
    {
      offending[clauseLits[i]]++;
    }
  }
  if (offending.empty())
  {
    return false;
  }
  Trace("sat-proof") << push;
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof")
        << "SatProofManager::processCrowdingLits: offending lits:\n";
    for (const std::pair<const Node&, unsigned>& pair : offending)
    {
      Trace("sat-proof") << "\t- " << pair.first << " {" << pair.second
                         << "}\n";
    }
  }
  // for each offending literal, which link last included it?
  std::vector<std::pair<Node, unsigned>> lastInclusion;
  std::map<Node, unsigned> lastInclusionMap;
  // for each offending lit, get the link in which it is eliminated
  for (const std::pair<const Node&, unsigned>& offn : offending)
  {
    unsigned index = findLastInclusion(offn.first);
    Assert(index < d_resLinks.size());
    lastInclusion.push_back(std::make_pair(offn.first, index));
    lastInclusionMap[offn.first] = index;
  }
  // order map so that we process offending literals in the order of the clauses
  // that introduce them
  auto cmp = [=](std::pair<Node, unsigned>& a, std::pair<Node, unsigned>& b) {
    return a.second < b.second;
  };
  std::sort(lastInclusion.begin(), lastInclusion.end(), cmp);
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::processCrowdingLits: offending "
                          "lits last inclusion:\n";
    for (const std::pair<const Node&, unsigned>& pair : lastInclusion)
    {
      Trace("sat-proof") << "\t- [" << pair.second << "] : " << pair.first
                         << "\n";
    }
  }
  std::set<Node> processed;
  // for each offending lit, get the link in which it is eliminated. The size is
  // *not* cached because we add elements to this vector
  for (unsigned i = 0; i < lastInclusion.size(); ++i)
  {
    Assert(lastInclusion[i].second < d_resLinks.size() - 1);
    Node offLit = lastInclusion[i].first;
    Trace("sat-proof") << "SatProofManager::processCrowdingLits: eliminate {"
                       << offending[offLit] << "} " << offLit << " from link "
                       << lastInclusion[i].second + 1 << " on\n";
    AlwaysAssert(!processed.count(offLit));
    processed.insert(offLit);
    // find the last link that eliminates the offending literal. A literal l is
    // eliminated by a link if it contains a literal l' with opposito polarity
    // to l.
    for (unsigned j = lastInclusion[i].second + 1, sizeResL = d_resLinks.size();
         j < sizeResL;
         ++j)
    {
      Node clause, pivot;
      bool posFirst;
      std::tie(clause, pivot, posFirst) = d_resLinks[j];
      // To eliminate offLit, the clause must contain it with oposity
      // polarity. There are three successful cases, according to the pivot and
      // its sign
      //
      // - offLit is the same as the pivot and posFirst is true, which means
      //   that the clause contains its negation and eliminates it
      //
      // - the pivot is equal to offLit negated and posFirst is false, which
      //   means that the clause contains the negation of offLit
      //
      // - offLit is the negation of the pivot and posFirst is false, so the
      //   clause contains the node whose negation is offLit
      if ((offLit == pivot && posFirst)
          || (offLit.notNode() == pivot && !posFirst)
          || (pivot.notNode() == offLit && !posFirst))
      {
        Node posFirstNode = posFirst ? d_true : d_false;
        // get respective position for clause/pivot to double
        unsigned k;
        for (k = premises.size() - 1; k > 0; --k)
        {
          if (premises[k] == clause)
          {
            Assert(pivots[2 * (k - 1)] == posFirstNode
                   && pivots[(2 * k) - 1] == pivot)
                << posFirstNode << ", " << pivot << "\n"
                << pivots[2 * (k - 1)] << ", " << pivots[(2 * k) - 1];
            break;
          }
        }
        Assert(k > 0);
        Trace("sat-proof") << "SatProofManager::processCrowdingLits: found "
                              "killer of offending lit "
                           << offLit << " as " << k << "-th premise "
                           << premises[k] << "\n";
        // get number of occurrences of offending literal
        unsigned occurrences = offending[offLit];
        // literals introduced by resolving against clause are its literals
        // minus pivot. If the clause is itself the literal to eliminate,
        // nothing to be done
        Node elim = posFirst ? pivot.notNode() : pivot;
        if (clause != elim)
        {
          // for each literal that is not the one to be eliminated and that is
          // not in the conclusion, we increment its count in offending
          // multiplied by the number of times this clause will be introduced,
          // which is offending[offLit]. Note that this literal may not be in
          // current set, in which case it's added.
          for (const Node& lit : clause)
          {
            if (lit == elim
                || std::find(
                       targetClauseLits.begin(), targetClauseLits.end(), lit)
                       != targetClauseLits.end())
            {
              continue;
            }
            auto it = lastInclusionMap.find(lit);
            if (it == lastInclusionMap.end())
            {
              Trace("sat-proof") << push;
              unsigned index = findLastInclusion(lit);
              Assert(index < d_resLinks.size());
              Trace("sat-proof")
                  << "SatProofManager::processCrowdingLits: new offending lit "
                  << lit << " from link " << index << "\n";
              lastInclusionMap[lit] = index;
              offending[lit] = 0;
              // insert in correct position in vector
              for (unsigned l = lastInclusion.size(); l > 0; --l)
              {
                if (index > lastInclusion[l-1].second)
                {
                  lastInclusion.insert(lastInclusion.begin() + l,
                                       std::make_pair(lit, index));
                  Trace("sat-proof")
                      << "SatProofManager::processCrowdingLits: adding after "
                      << lastInclusion[l - 1].second << "\n";
                  break;
                }
              }
              Trace("sat-proof")  << pop;
            }
            Assert(lastInclusionMap[lit] > lastInclusionMap[offLit])
                << "lit [" << lastInclusionMap[lit] << "] " << lit
                << " previous to offLit [" << lastInclusionMap[offLit] << "] "
                << offLit;
            Trace("sat-proof")
                << "SatProofManager::processCrowdingLits: adding "
                << occurrences << " to lit " << lit << " current "
                << offending[lit] << "\n";
            offending[lit] += occurrences;
          }
        }
        // for each occurrence, replicate the link in the premises/pivots
        while (occurrences-- > 0)
        {
          premises.insert(premises.begin() + k, clause);
          pivots.insert(pivots.begin() + 2 * (k - 1), {posFirstNode, pivot});
        }
        break;
      }
    }
  }
  Trace("sat-proof") << pop;
  return true;
}

void SatProofManager::processRedundantLit(
    SatLiteral lit,
    const std::multiset<SatLiteral>& conclusionLits,
    std::set<SatLiteral>& visited,
    unsigned pos)
{
  Trace("sat-proof") << push
                     << "SatProofManager::processRedundantLit: Lit: " << lit
                     << "\n";
  if (visited.count(lit))
  {
    Trace("sat-proof") << "already visited\n" << pop;
    return;
  }
  Minisat::Solver::TCRef reasonRef =
      d_solver->reason(Minisat::var(MinisatSatSolver::toMinisatLit(lit)));
  if (reasonRef == Minisat::Solver::TCRef_Undef)
  {
    Trace("sat-proof") << "unit, add link to lit " << lit << " at pos: " << pos
                       << "\n"
                       << pop;
    visited.insert(lit);
    Node litNode = d_cnfStream->getNodeCache()[lit];
    bool negated = lit.isNegated();
    Assert(!negated || litNode.getKind() == kind::NOT);

    d_resLinks.insert(d_resLinks.begin() + pos,
                      std::make_tuple(d_cnfStream->getNodeCache()[~lit],
                                      negated ? litNode[0] : litNode,
                                      !negated));
    return;
  }
  Assert(reasonRef >= 0 && reasonRef < d_solver->ca.size())
      << "reasonRef " << reasonRef << " and d_satSolver->ca.size() "
      << d_solver->ca.size() << "\n";
  const Minisat::Clause& reason = d_solver->ca[reasonRef];
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "reason: ";
    printClause(reason);
    Trace("sat-proof") << "\n";
  }
  // check if redundant literals in the reason. The first literal is the one we
  // will be eliminating, so we check the others
  for (unsigned i = 1, size = reason.size(); i < size; ++i)
  {
    SatLiteral satLit = MinisatSatSolver::toSatLiteral(reason[i]);
    // if literal does not occur in the conclusion we process it as well
    if (!conclusionLits.count(satLit))
    {
      processRedundantLit(satLit, conclusionLits, visited, pos);
    }
  }
  Assert(!visited.count(lit));
  visited.insert(lit);
  Trace("sat-proof") << "clause, add link to lit " << lit << " at pos: " << pos
                     << "\n"
                     << pop;
  // add the step before steps for children. Note that the step is with the
  // reason, not only with ~lit, since the learned clause is built under the
  // assumption that the redundant literal is removed via the resolution with
  // the explanation of its negation
  Node clauseNode = getClauseNode(reason);
  Node litNode = d_cnfStream->getNodeCache()[lit];
  bool negated = lit.isNegated();
  Assert(!negated || litNode.getKind() == kind::NOT);
  d_resLinks.insert(
      d_resLinks.begin() + pos,
      std::make_tuple(clauseNode, negated ? litNode[0] : litNode, !negated));
}

void SatProofManager::explainLit(
    SatLiteral lit, std::unordered_set<TNode, TNodeHashFunction>& premises)
{
  Node litNode = getClauseNode(lit);
  Trace("sat-proof") << push << "SatProofManager::explainLit: Lit: " << lit
                     << " [" << litNode << "]\n";
  Minisat::Solver::TCRef reasonRef =
      d_solver->reason(Minisat::var(MinisatSatSolver::toMinisatLit(lit)));
  if (reasonRef == Minisat::Solver::TCRef_Undef)
  {
    Trace("sat-proof") << "SatProofManager::explainLit: no SAT reason\n" << pop;
    return;
  }
  Assert(reasonRef >= 0 && reasonRef < d_solver->ca.size())
      << "reasonRef " << reasonRef << " and d_satSolver->ca.size() "
      << d_solver->ca.size() << "\n";
  const Minisat::Clause& reason = d_solver->ca[reasonRef];
  unsigned size = reason.size();
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::explainLit: with clause: ";
    printClause(reason);
    Trace("sat-proof") << "\n";
  }
  // pedantically check that the negation of the literal to explain *does not*
  // occur in the reason, otherwise we will loop forever
  for (unsigned i = 0; i < size; ++i)
  {
    AlwaysAssert(~MinisatSatSolver::toSatLiteral(reason[i]) != lit)
        << "cyclic justification\n";
  }
  // add the reason clause first
  std::vector<Node> children{getClauseNode(reason)}, args;
  // save in the premises
  premises.insert(children.back());
  NodeManager* nm = NodeManager::currentNM();
  Trace("sat-proof") << push;
  for (unsigned i = 0; i < size; ++i)
  {
    SatLiteral curr_lit = MinisatSatSolver::toSatLiteral(reason[i]);
    // ignore the lit we are trying to explain...
    if (curr_lit == lit)
    {
      continue;
    }
    std::unordered_set<TNode, TNodeHashFunction> childPremises;
    explainLit(~curr_lit, childPremises);
    // save to resolution chain premises / arguments
    Assert(d_cnfStream->getNodeCache().find(curr_lit)
           != d_cnfStream->getNodeCache().end());
    children.push_back(d_cnfStream->getNodeCache()[~curr_lit]);
    Node currLitNode = d_cnfStream->getNodeCache()[curr_lit];
    bool negated = curr_lit.isNegated();
    Assert(!negated || currLitNode.getKind() == kind::NOT);
    // note this is the opposite of what is done in addResolutionStep. This is
    // because here the clause, which contains the literal being analyzed, is
    // the first clause rather than the second
    args.push_back(!negated ? d_true : d_false);
    args.push_back(negated ? currLitNode[0] : currLitNode);
    // add child premises and the child itself
    premises.insert(childPremises.begin(), childPremises.end());
    premises.insert(d_cnfStream->getNodeCache()[~curr_lit]);
  }
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << pop << "SatProofManager::explainLit: chain_res for "
                       << lit << ", " << litNode << " with clauses:\n";
    for (unsigned i = 0, csize = children.size(); i < csize; ++i)
    {
      Trace("sat-proof") << "SatProofManager::explainLit:   " << children[i];
      if (i > 0)
      {
        Trace("sat-proof") << " [" << args[i - 1] << "]";
      }
      Trace("sat-proof") << "\n";
    }
  }
  // if justification of children contains the expected conclusion, avoid the
  // cyclic proof by aborting.
  if (premises.count(litNode))
  {
    Trace("sat-proof") << "SatProofManager::explainLit: CYCLIC PROOF of " << lit
                       << " [" << litNode << "], ABORT\n"
                       << pop;
    return;
  }
  Trace("sat-proof") << pop;
  // create step
  ProofStep ps(PfRule::CHAIN_RESOLUTION, children, args);
  d_resChainPg.addStep(litNode, ps);
  // the premises in the limit of the justification may correspond to other
  // links in the chain which have, themselves, literals yet to be justified. So
  // we are not ready yet to check closedness w.r.t. CNF transformation of the
  // preprocessed assertions
  d_resChains.addLazyStep(litNode, &d_resChainPg);
}

void SatProofManager::finalizeProof(Node inConflictNode,
                                    const std::vector<SatLiteral>& inConflict)
{
  Trace("sat-proof")
      << "SatProofManager::finalizeProof: conflicting clause node: "
      << inConflictNode << "\n";
  // nothing to do
  if (inConflictNode == d_false)
  {
    return;
  }
  if (Trace.isOn("sat-proof-debug2"))
  {
    Trace("sat-proof-debug2")
        << push << "SatProofManager::finalizeProof: saved proofs in chain:\n";
    std::map<Node, std::shared_ptr<ProofNode>> links = d_resChains.getLinks();
    std::unordered_set<Node, NodeHashFunction> skip;
    for (const std::pair<const Node, std::shared_ptr<ProofNode>>& link : links)
    {
      if (skip.count(link.first))
      {
        continue;
      }
      auto it = d_cnfStream->getTranslationCache().find(link.first);
      if (it != d_cnfStream->getTranslationCache().end())
      {
        Trace("sat-proof-debug2")
            << "SatProofManager::finalizeProof:  " << it->second;
      }
      // a refl step added due to double elim negation, ignore
      else if (link.second->getRule() == PfRule::REFL)
      {
        continue;
      }
      // a clause
      else
      {
        Trace("sat-proof-debug2") << "SatProofManager::finalizeProof:";
        Assert(link.first.getKind() == kind::OR) << link.first;
        for (const Node& n : link.first)
        {
          it = d_cnfStream->getTranslationCache().find(n);
          Assert(it != d_cnfStream->getTranslationCache().end());
          Trace("sat-proof-debug2") << it->second << " ";
        }
      }
      Trace("sat-proof-debug2") << "\n";
      Trace("sat-proof-debug2")
          << "SatProofManager::finalizeProof: " << link.first << "\n";
      // get resolution
      Node cur = link.first;
      std::shared_ptr<ProofNode> pfn = link.second;
      while (pfn->getRule() != PfRule::CHAIN_RESOLUTION)
      {
        Assert(pfn->getChildren().size() == 1
               && pfn->getChildren()[0]->getRule() == PfRule::ASSUME)
            << *link.second.get() << "\n"
            << *pfn.get();
        cur = pfn->getChildren()[0]->getResult();
        // retrieve justification of assumption in the links
        Assert(links.find(cur) != links.end());
        pfn = links[cur];
        // ignore it in the rest of the outside loop
        skip.insert(cur);
      }
      std::vector<Node> fassumps;
      expr::getFreeAssumptions(pfn.get(), fassumps);
      Trace("sat-proof-debug2") << push;
      for (const Node& fa : fassumps)
      {
        Trace("sat-proof-debug2") << "SatProofManager::finalizeProof:   - ";
        it = d_cnfStream->getTranslationCache().find(fa);
        if (it != d_cnfStream->getTranslationCache().end())
        {
          Trace("sat-proof-debug2") << it->second << "\n";
          continue;
        }
        // then it's a clause
        Assert(fa.getKind() == kind::OR);
        for (const Node& n : fa)
        {
          it = d_cnfStream->getTranslationCache().find(n);
          Assert(it != d_cnfStream->getTranslationCache().end());
          Trace("sat-proof-debug2") << it->second << " ";
        }
        Trace("sat-proof-debug2") << "\n";
      }
      Trace("sat-proof-debug2") << pop;
      Trace("sat-proof-debug2")
          << "SatProofManager::finalizeProof:  " << *pfn.get() << "\n=======\n";
      ;
    }
    Trace("sat-proof-debug2") << pop;
  }
  // We will resolve away of the literals l_1...l_n in inConflict. At this point
  // each ~l_i must be either explainable, the result of a previously saved
  // resolution chain, or an input. In account of it possibly being the first,
  // we call explainLit on each ~l_i while accumulating the children and
  // arguments for the resolution step to conclude false.
  std::vector<Node> children{inConflictNode}, args;
  std::unordered_set<TNode, TNodeHashFunction> premises;
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = inConflict.size(); i < size; ++i)
  {
    Assert(d_cnfStream->getNodeCache().find(inConflict[i])
           != d_cnfStream->getNodeCache().end());
    std::unordered_set<TNode, TNodeHashFunction> childPremises;
    explainLit(~inConflict[i], childPremises);
    Node negatedLitNode = d_cnfStream->getNodeCache()[~inConflict[i]];
    // save to resolution chain premises / arguments
    children.push_back(negatedLitNode);
    Node litNode = d_cnfStream->getNodeCache()[inConflict[i]];
    bool negated = inConflict[i].isNegated();
    Assert(!negated || litNode.getKind() == kind::NOT);
    // note this is the opposite of what is done in addResolutionStep. This is
    // because here the clause, which contains the literal being analyzed, is
    // the first clause rather than the second
    args.push_back(!negated ? d_true : d_false);
    args.push_back(negated ? litNode[0] : litNode);
    // add child premises and the child itself
    premises.insert(childPremises.begin(), childPremises.end());
    premises.insert(negatedLitNode);
    Trace("sat-proof") << "===========\n";
  }
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::finalizeProof: chain_res for false "
                          "with clauses:\n";
    for (unsigned i = 0, size = children.size(); i < size; ++i)
    {
      Trace("sat-proof") << "SatProofManager::finalizeProof:   " << children[i];
      if (i > 0)
      {
        Trace("sat-proof") << " [" << args[i - 1] << "]";
      }
      Trace("sat-proof") << "\n";
    }
  }
  // create step
  ProofStep ps(PfRule::CHAIN_RESOLUTION, children, args);
  d_resChainPg.addStep(d_false, ps);
  // not yet ready to check closedness because maybe only now we will justify
  // literals used in resolutions
  d_resChains.addLazyStep(d_false, &d_resChainPg);
  // Fix point justification of literals in leaves of the proof of false
  bool expanded;
  do
  {
    expanded = false;
    Trace("sat-proof") << "expand assumptions to prove false\n";
    std::shared_ptr<ProofNode> pfn = d_resChains.getProofFor(d_false);
    Assert(pfn);
    Trace("sat-proof-debug") << "sat proof of flase: " << *pfn.get() << "\n";
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(pfn.get(), fassumps);
    if (Trace.isOn("sat-proof"))
    {
      for (const Node& fa : fassumps)
      {
        Trace("sat-proof") << "- ";
        auto it = d_cnfStream->getTranslationCache().find(fa);
        if (it != d_cnfStream->getTranslationCache().end())
        {
          Trace("sat-proof") << it->second << "\n";
          Trace("sat-proof") << "- " << fa << "\n";
          continue;
        }
        // then it's a clause
        Assert(fa.getKind() == kind::OR);
        for (const Node& n : fa)
        {
          it = d_cnfStream->getTranslationCache().find(n);
          Assert(it != d_cnfStream->getTranslationCache().end());
          Trace("sat-proof") << it->second << " ";
        }
        Trace("sat-proof") << "\n";
        Trace("sat-proof") << "- " << fa << "\n";
      }
    }

    // for each assumption, see if it has a reason
    for (const Node& fa : fassumps)
    {
      // ignore already processed assumptions
      if (premises.count(fa))
      {
        Trace("sat-proof") << "already processed assumption " << fa << "\n";
        continue;
      }
      // ignore input assumptions. This is necessary to avoid rare collisions
      // between input clauses and literals that are equivalent at the node
      // level. In trying to justify the literal below if, it was previously
      // propagated (say, in a previous check-sat call that survived the
      // user-context changes) but no longer holds, then we may introduce a
      // bogus proof for it, rather than keeping it as an input.
      if (d_assumptions.contains(fa))
      {
        Trace("sat-proof") << "input assumption " << fa << "\n";
        continue;
      }
      // ignore non-literals
      auto it = d_cnfStream->getTranslationCache().find(fa);
      if (it == d_cnfStream->getTranslationCache().end())
      {
        Trace("sat-proof") << "no lit assumption " << fa << "\n";
        premises.insert(fa);
        continue;
      }
      Trace("sat-proof") << "lit assumption (" << it->second << "), " << fa
                         << "\n";
      // mark another iteration for the loop, as some resolution link may be
      // connected because of the new justifications
      expanded = true;
      std::unordered_set<TNode, TNodeHashFunction> childPremises;
      explainLit(it->second, childPremises);
      // add the premises used in the justification. We know they will have
      // been as expanded as possible
      premises.insert(childPremises.begin(), childPremises.end());
      // add free assumption itself
      premises.insert(fa);
    }
  } while (expanded);
  // now we should be able to close it
  if (options::proofNewEagerChecking())
  {
    std::vector<Node> assumptionsVec;
    for (const Node& a : d_assumptions)
    {
      assumptionsVec.push_back(a);
    }
    d_resChains.addLazyStep(d_false, &d_resChainPg, assumptionsVec);
  }
}

void SatProofManager::storeUnitConflict(Minisat::Lit inConflict)
{
  Assert(d_conflictLit == undefSatVariable);
  d_conflictLit = MinisatSatSolver::toSatLiteral(inConflict);
}

void SatProofManager::finalizeProof()
{
  Assert(d_conflictLit != undefSatVariable);
  Trace("sat-proof")
      << "SatProofManager::finalizeProof: conflicting (lazy) satLit: "
      << d_conflictLit << "\n";
  finalizeProof(getClauseNode(d_conflictLit), {d_conflictLit});
}

void SatProofManager::finalizeProof(Minisat::Lit inConflict, bool adding)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(inConflict);
  Trace("sat-proof") << "SatProofManager::finalizeProof: conflicting satLit: "
                     << satLit << "\n";
  Node clauseNode = getClauseNode(satLit);
  if (adding)
  {
    registerSatAssumptions({clauseNode});
  }
  finalizeProof(clauseNode, {satLit});
}

void SatProofManager::finalizeProof(const Minisat::Clause& inConflict,
                                    bool adding)
{
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof")
        << "SatProofManager::finalizeProof: conflicting clause: ";
    printClause(inConflict);
    Trace("sat-proof") << "\n";
  }
  std::vector<SatLiteral> clause;
  for (unsigned i = 0, size = inConflict.size(); i < size; ++i)
  {
    clause.push_back(MinisatSatSolver::toSatLiteral(inConflict[i]));
  }
  Node clauseNode = getClauseNode(inConflict);
  if (adding)
  {
    registerSatAssumptions({clauseNode});
  }
  finalizeProof(clauseNode, clause);
}

std::shared_ptr<ProofNode> SatProofManager::getProof()
{
  std::shared_ptr<ProofNode> pfn = d_resChains.getProofFor(d_false);
  if (!pfn)
  {
    pfn = d_pnm->mkAssume(d_false);
  }
  return pfn;
}

void SatProofManager::registerSatLitAssumption(Minisat::Lit lit)
{
  Trace("sat-proof") << "SatProofManager::registerSatLitAssumption: - "
                     << getClauseNode(MinisatSatSolver::toSatLiteral(lit))
                     << "\n";
  d_assumptions.insert(getClauseNode(MinisatSatSolver::toSatLiteral(lit)));
}

void SatProofManager::registerSatAssumptions(const std::vector<Node>& assumps)
{
  for (const Node& a : assumps)
  {
    Trace("sat-proof") << "SatProofManager::registerSatAssumptions: - " << a
                       << "\n";
    d_assumptions.insert(a);
  }
}

}  // namespace prop
}  // namespace CVC4
