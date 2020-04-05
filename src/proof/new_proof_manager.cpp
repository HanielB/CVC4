/*********************                                                        */
/*! \file new_proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A new manager for Proofs
 **/

#include "proof/new_proof_manager.h"

#include "base/check.h"
#include "context/context.h"
#include "options/bv_options.h"
#include "options/proof_options.h"
#include "proof/clause_id.h"
#include "proof/cnf_proof.h"
#include "proof/lean_proof.h"
#include "proof/lfsc_proof_printer.h"
#include "proof/proof_utils.h"
#include "proof/resolution_bitvector_proof.h"
#include "proof/sat_proof_implementation.h"
#include "proof/theory_proof.h"
#include "proof/verit_proof.h"
#include "prop/minisat/core/Solver.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/output_channel.h"
#include "theory/term_registration_visitor.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/proof.h"

namespace CVC4 {

NewProofManager::NewProofManager(options::ProofFormatMode format)
    : d_format(format)
{
  // TODO add LFSC
  if (format == options::ProofFormatMode::LEAN)
  {
    d_proof.reset(new LeanProof());
    return;
  }
  // default
  Assert(format == options::ProofFormatMode::VERIT);
  d_proof.reset(new VeritProof());
}

NewProofManager::~NewProofManager() {}

NewProofManager* NewProofManager::currentPM()
{
  return smt::currentNewProofManager();
}

NewProof& NewProofManager::getProof()
{
  NewProof* proof = d_proof.get();
  proof->finishProof();
  return *proof;
}

void NewProofManager::addInputAssertion(Node formula)
{
  ClauseId id = d_proof.get()->addProofStep(RULE_INPUT);
  Debug("newproof::pm") << "NewProofManager::addInputAssertion [id: " << id
                        << "]: " << formula << std::endl;

  if (d_format == options::ProofFormatMode::VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    vtproof->addToLastProofStep(formula);
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    leanproof->addToLastProofStep(formula);
  }
  d_assertionToClauseId[formula] = id;
}

void NewProofManager::addInputSubAssertion(Node formula, ClauseId id)
{
  // We can add the same formula from different assertions.  In this
  // case we keep the first assertion. For example asserting a /\ b
  // and then b /\ c where b is an atom, would assert b twice (note
  // that since b is top level, it is not cached by the CnfStream)
  auto it = d_assertionToClauseId.find(formula);
  if (it != d_assertionToClauseId.end())
  {
    Debug("newproof::sat::cnf")
        << "NewProofManager::addINputSubAssertion: formula " << formula
        << " already saved under id " << it->second << "\n";
    return;
  }
  Debug("newproof::sat::cnf")
      << "NewProofManager::addINputSubAssertion: formula " << formula
      << " assigned id " << id << "\n";
  d_assertionToClauseId[formula] = id;
}

void NewProofManager::addAssertionProofStep(Node src,
                                            Node dest,
                                            NewProofRule rule)
{
  Debug("newproof::pm") << "NewProofManager::addAssertionProofStep: [" << rule
                        << "] from " << src << " to " << dest << std::endl;
  Assert(d_assertionToClauseId.find(src) != d_assertionToClauseId.end());
  std::vector<ClauseId> reasons{d_assertionToClauseId[src]};
  ClauseId id;
  if (d_format == options::ProofFormatMode::VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    id = vtproof->addProofStep(rule, reasons, dest);
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    id = leanproof->addProofStep(rule, reasons, dest);
  }
  // update id of assertion
  d_assertionToClauseId[dest] = id;
}

void NewProofManager::addIteRemovalProofStep(Node src, Node dest)
{
  Debug("newproof::pm") << "NewProofManager::addIteRemovalProofStep: ["
                        << RULE_PREPROCESSING_ITE_REMOVAL << "] from " << src
                        << " to " << dest << std::endl;
  Assert(d_assertionToClauseId.find(src) != d_assertionToClauseId.end());
  std::vector<ClauseId> reasons{d_assertionToClauseId[src]};
  ClauseId id;
  if (d_format == options::ProofFormatMode::VERIT
      || d_format == options::ProofFormatMode::LEAN)
  {
    // nothing to be done
    id = d_assertionToClauseId[src];
  }
  // update id of assertion
  d_assertionToClauseId[dest] = id;
}

void NewProofManager::addIteDefProofStep(Node def)
{
  Debug("newproof::pm") << "NewProofManager::addItedDefProofStep: ["
                        << RULE_ITE_INTRO << "] " << def << "\n";
  ClauseId id;
  if (d_format == options::ProofFormatMode::VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    id = vtproof->addProofStep(RULE_ITE_INTRO, def);
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    id = leanproof->addIteIntroProofStep(def);
  }
  // update id of assertion
  d_assertionToClauseId[def] = id;
}

void NewProofManager::notifyIte(Node src, Node dest)
{
  Debug("newproof::pm") << "NewProofManager::notifyIte: from " << src << " to "
                        << dest << "\n";
  if (d_format == options::ProofFormatMode::VERIT)
  {
    // nothing for now
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    leanproof->notifyIte(src, dest);
  }
}

ClauseId NewProofManager::addCnfProofStep(NewProofRule rule,
                                          ClauseId id,
                                          Node src,
                                          std::vector<Node>& clauseNodes,
                                          unsigned ith)
{
  Debug("newproof::pm") << "NewProofManager::addCnfProofStep: [" << rule
                        << "], src " << src << ", [id: " << id << "], "
                        << " clauseNodes: " << clauseNodes << std::endl;
  // retrieve justification for src, which must have one, since it is an input
  Assert(d_assertionToClauseId.find(src) != d_assertionToClauseId.end())
      << "NewProofManager::addCnfProofStep: node " << src
      << " is not input or it is and was already processed in a conlfict\n";
  std::vector<ClauseId> reasons{d_assertionToClauseId[src]};

  if (d_format == options::ProofFormatMode::VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    // if id is not defined then create a new proof step
    if (id == ClauseIdUndef)
    {
      id = vtproof->addProofStep(rule, reasons, clauseNodes);
    }
    else
    {
      vtproof->addToProofStep(id, rule, reasons, clauseNodes);
    }
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    // TODO HB add this logic to the proof itself, out of the PM
    // if id is not defined then create a new proof step
    if (id == ClauseIdUndef)
    {
      id = ith == static_cast<unsigned>(-1)
               ? leanproof->addProofStep(rule, reasons, clauseNodes)
               : leanproof->addProofStep(rule, reasons, clauseNodes, ith);
    }
    else
    {
      if (ith == static_cast<unsigned>(-1))
      {
        leanproof->addToProofStep(id, rule, reasons, clauseNodes);
      }
      else
      {
        leanproof->addToProofStep(id, rule, reasons, clauseNodes, ith);
      }
    }
  }

  return id;
}

ClauseId NewProofManager::addCnfProofStep(NewProofRule rule,
                                          ClauseId id,
                                          Node src,
                                          prop::SatClause clause,
                                          unsigned ith)
{
  std::vector<Node> clauseNodes;
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    Assert(d_litToNode.find(clause[i]) != d_litToNode.end());
    // premises in conclusion are already negated in this case...
    clauseNodes.push_back(d_litToNode[clause[i]]);
  }
  return addCnfProofStep(rule, id, src, clauseNodes, ith);
}

ClauseId NewProofManager::addCnfProofStep(prop::SatLiteral lit, ClauseId id)
{
  Debug("newproof::pm") << "NewProofManager::addCnfProofStep: SatLit " << lit
                        << std::endl;
  // this guy must be an input, so I need to associate the input corresponding
  // to the input to the clause id of the input
  Assert(d_litToNode.find(lit) != d_litToNode.end());
  Node litDef = d_litToNode[lit];
  // It must be an input
  if (d_assertionToClauseId.find(litDef) == d_assertionToClauseId.end())
  {
    Debug("newproof::pm") << "NewProofManager::addCnfProofStep: node " << litDef
                          << " is not input or it is and was already processed "
                             "in a conlfict, I guess. It has id "
                          << id << "\n";
    return id;
  }
  // Associate input literal with his respective clause id
  ClauseId previous_id = d_assertionToClauseId[litDef];
  d_litToClauseId[lit] = previous_id;
  d_clauseIdToLit[previous_id] = lit;
  return previous_id;
}

void NewProofManager::addDefCnfProofStep(NewProofRule rule,
                                         ClauseId id,
                                         prop::SatClause clause,
                                         unsigned ith)
{
  Debug("newproof::pm") << "NewProofManager::addDefCnfProofStep: [" << rule
                        << "] clause: " << clause << std::endl;
  std::vector<Node> clauseNodes;
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    Assert(d_litToNode.find(clause[i]) != d_litToNode.end());
    // premises in conclusion are already negated in this case...
    clauseNodes.push_back(d_litToNode[clause[i]]);
  }
  if (d_format == options::ProofFormatMode::VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    vtproof->addToProofStep(id, rule, clauseNodes);
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    leanproof->addToCnfProofStep(id, rule, clauseNodes, ith);
  }
}

inline void NewProofManager::printLit(const Minisat::Solver::TLit lit)
{
  Debug("newproof::sat") << (Minisat::sign(lit) ? "-" : "")
                         << Minisat::var(lit) + 1 << " ";
}

inline void NewProofManager::printClause(const Minisat::Solver::TClause& clause)
{
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    Debug("newproof::sat") << (Minisat::sign(clause[i]) ? "-" : "")
                           << Minisat::var(clause[i]) + 1 << " ";
    if (Debug.isOn("newproof::sat::cnf"))
    {
      prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(clause[i]);
      Assert(d_litToNode.find(satLit) != d_litToNode.end());
      Debug("newproof::sat::cnf") << "[" << d_litToNode[satLit] << "] ";
    }
  }
}

void NewProofManager::addLitDef(prop::SatLiteral lit, Node litNode)
{
  Debug("newproof::sat") << "NewProofManager::addLitDef: lit/def: " << lit
                         << " / " << litNode << "\n";
  d_litToNode[lit] = litNode;
}

void NewProofManager::addClauseDef(ClauseId clause,
                                   Node clauseNode,
                                   Node clauseNodeDef)
{
  Debug("newproof::sat")
      << "NewProofManager::addClauseDef: clause/assertion/def: " << clause
      << " / " << clauseNode << " / " << clauseNodeDef << "\n";
  // I guess they have to be synched
  Assert(d_clauseToNode.find(clause) == d_clauseToNode.end()
         || d_clauseToNodeDef.find(clause) != d_clauseToNodeDef.end());

  // We can add the same clause from different assertions.  In this
  // case we keep the first assertion. For example asserting a /\ b
  // and then b /\ c where b is an atom, would assert b twice (note
  // that since b is top level, it is not cached by the CnfStream)
  //
  // For definitions the first is kept
  //
  // HB Need to grok the above
  if (d_clauseToNodeDef.find(clause) != d_clauseToNodeDef.end())
  {
    Debug("newproof::sat") << "NewProofManager::addClauseDef: clause " << clause
                           << " already had node  " << d_clauseToNode[clause]
                           << " and def  " << d_clauseToNodeDef[clause] << "\n";
    return;
  }
  d_clauseToNode[clause] = clauseNode;
  d_clauseToNodeDef[clause] = clauseNodeDef;
}

void NewProofManager::addClauseDef(ClauseId clause, Node clauseNodeDef)
{
  Debug("newproof::sat") << "NewProofManager::addClauseDef: clause/def: "
                         << clause << " / " << clauseNodeDef << "\n";
  // For definitions the first is kept
  if (d_clauseToNodeDef.find(clause) != d_clauseToNodeDef.end())
  {
    Debug("newproof::sat") << "NewProofManager::addClauseDef: clause " << clause
                           << " already had def " << d_clauseToNodeDef[clause]
                           << "\n";
    return;
  }
  d_clauseToNodeDef[clause] = clauseNodeDef;
}

ClauseId NewProofManager::registerClause(Minisat::Solver::TLit lit)
{
  ClauseId id;
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  auto it = d_litToClauseId.find(satLit);
  if (it != d_litToClauseId.end())
  {
    if (Debug.isOn("newproof::sat"))
    {
      Debug("newproof::sat")
          << "NewProofManager::registerClause: id " << it->second << ", TLit: ";
      printLit(lit);
      Debug("newproof::sat") << " already registered\n";
    }
    return it->second;
  }
  if (d_format == options::ProofFormatMode::VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    id = vtproof->addProofStep();
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    id = leanproof->addProofStep();
  }
  d_litToClauseId[satLit] = id;
  d_clauseIdToLit[id] = satLit;
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::registerClause: id " << id
                           << ", TLit: ";
    printLit(lit);
    Debug("newproof::sat") << "\n";
  }
  return id;
}

ClauseId NewProofManager::registerClause(Minisat::Solver::TLit lit,
                                         NewProofRule reason,
                                         Node litNodeDef)
{
  ClauseId id;
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  auto it = d_litToClauseId.find(satLit);
  if (it != d_litToClauseId.end())
  {
    if (Debug.isOn("newproof::sat"))
    {
      Debug("newproof::sat")
          << "NewProofManager::registerClause: id " << it->second << ", TLit: ";
      printLit(lit);
      Debug("newproof::sat") << " already registered\n";
    }
    return it->second;
  }
  if (!litNodeDef.isNull())
  {
    addLitDef(toSatLiteral<Minisat::Solver>(lit), litNodeDef);
  }
  else
  {
    // if I'm not giving a definition I must have saved this at some previous
    // point
    Assert(d_litToNode.find(satLit) != d_litToNode.end());
    litNodeDef = d_litToNode[satLit];
    Debug("newproof::sat::cnf")
        << "NewProofManager::registerClause: TLit def " << litNodeDef << "\n";
  }
  if (reason == RULE_INPUT)
  {
    Assert(d_assertionToClauseId.find(litNodeDef)
           != d_assertionToClauseId.end());
    id = d_assertionToClauseId[litNodeDef];
  }
  else if (reason == RULE_THEORY_LEMMA)
  {
    // since this is a theory lemma I may already have a proof for it, in which
    // case it will now be built
    auto itt = d_litToTheoryProof.find(toSatLiteral<Minisat::Solver>(lit));

    if (d_format == options::ProofFormatMode::VERIT)
    {
      VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
      if (itt != d_litToTheoryProof.end())
      {
        id = vtproof->addTheoryProof(itt->second);
      }
      else
      {
        id = vtproof->addProofStep(RULE_UNDEF, litNodeDef);
      }
    }
    else if (d_format == options::ProofFormatMode::LEAN)
    {
      LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
      if (itt != d_litToTheoryProof.end())
      {
        id = leanproof->addTheoryProof(itt->second);
      }
      else
      {
        id = leanproof->addProofStep(RULE_UNDEF, litNodeDef);
      }
    }
  }
  else
  {
    // placeholder
    if (d_format == options::ProofFormatMode::VERIT)
    {
      VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
      id = vtproof->addProofStep();
    }
    else if (d_format == options::ProofFormatMode::LEAN)
    {
      LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
      id = leanproof->addProofStep();
    }
  }
  d_litToClauseId[satLit] = id;
  d_clauseIdToLit[id] = satLit;

  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::registerClause: id " << id
                           << ", TLit: ";
    printLit(lit);
    Debug("newproof::sat") << "\n";
  }
  return id;
}

ClauseId NewProofManager::registerClause(Minisat::Solver::TClause& clause)
{
  ClauseId id;
  if (clause.proofId() != 0)
  {
    id = clause.proofId();
    Assert(d_clauseIdToClause.find(id) != d_clauseIdToClause.end());
    if (Debug.isOn("newproof::sat"))
    {
      Debug("newproof::sat")
          << "NewProofManager::registerClause: id " << id << ", TClause: ";
      printClause(clause);
      Debug("newproof::sat") << " already registered\n";
    }
    return id;
  }
  if (d_format == options::ProofFormatMode::VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    id = vtproof->addProofStep();
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    id = leanproof->addProofStep();
  }
  clause.setProofId(id);
  d_clauseIdToClause[id] = &clause;
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::registerClause: id " << id
                           << ", TClause: ";
    printClause(clause);
    Debug("newproof::sat") << "\n";
  }
  return id;
}

ClauseId NewProofManager::registerClause(Minisat::Solver::TClause& clause,
                                         NewProofRule reason,
                                         Node clauseNodeDef)
{
  ClauseId id;
  if (clause.proofId() != 0)
  {
    id = clause.proofId();
    Assert(d_clauseIdToClause.find(id) != d_clauseIdToClause.end());
    if (Debug.isOn("newproof::sat"))
    {
      Debug("newproof::sat")
          << "NewProofManager::registerClause: id " << id << ", TClause: ";
      printClause(clause);
      Debug("newproof::sat") << " already registered\n";
    }
    return id;
  }
  if (clauseNodeDef.isNull())
  {
    // if I'm not giving a definition then all literals must have been previous
    // defined. Use that to build a definition
    std::vector<Node> children;
    for (unsigned i = 0, size = clause.size(); i < size; ++i)
    {
      prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(clause[i]);
      Assert(d_litToNode.find(satLit) != d_litToNode.end());
      children.push_back(d_litToNode[satLit]);
    }
    clauseNodeDef = NodeManager::currentNM()->mkNode(kind::OR, children);
  }
  if (reason == RULE_THEORY_LEMMA)
  {
    // the propagated literal is always at the first position in the clause
    // TODO HB How to assert this?
    prop::SatLiteral lit = toSatLiteral<Minisat::Solver>(clause[0]);
    // since this is a theory lemma I may already have a proof for it, in which
    // case it will now be built
    auto itt = d_litToTheoryProof.find(lit);
    if (d_format == options::ProofFormatMode::VERIT)
    {
      VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
      if (itt != d_litToTheoryProof.end())
      {
        id = vtproof->addTheoryProof(itt->second);
      }
      else
      {
        // build clause if need be
        id = vtproof->addProofStep(RULE_UNDEF, clauseNodeDef);
      }
    }
    else if (d_format == options::ProofFormatMode::LEAN)
    {
      LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
      if (itt != d_litToTheoryProof.end())
      {
        id = leanproof->addTheoryProof(itt->second);
      }
      else
      {
        // build clause if need be
        id = leanproof->addProofStep(RULE_UNDEF, clauseNodeDef);
      }
    }
  }
  else
  {
    // placeholder
    if (d_format == options::ProofFormatMode::VERIT)
    {
      VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
      id = vtproof->addProofStep();
    }
    else if (d_format == options::ProofFormatMode::LEAN)
    {
      LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
      id = leanproof->addProofStep();
    }
    Assert(false) << "NewProofManager::registerClause can't handle non-unit "
                     "clause - RULE_LEMMA yet\n";
  }
  clause.setProofId(id);
  d_clauseIdToClause[id] = &clause;
  // now define it
  addClauseDef(id, clauseNodeDef);
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::registerClause: id " << id
                           << ", TClause: ";
    printClause(clause);
    Debug("newproof::sat") << "\n";
  }
  return id;
}

void NewProofManager::startResChain(Minisat::Solver::TClause& start)
{
  Assert(start.proofId() != 0);
  ClauseId id = start.proofId();
  Debug("newproof::sat") << "NewProofManager::startResChain " << id << "\n";
  // TODO what should I add here? Who is "start"???
}

void NewProofManager::addResolutionStep(Minisat::Solver::TLit lit,
                                        Minisat::Solver::TClause& clause,
                                        bool sign)
{
  ClauseId id = registerClause(clause);
  Debug("newproof::sat") << "NewProofManager::addResolutionStep: (" << id
                         << ", ";
  printLit(lit);
  Debug("newproof::sat") << "\n";
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Assert(d_litToNode.find(satLit) != d_litToNode.end());
  d_resolution.push_back(
      Resolution(registerClause(clause), d_litToNode[satLit], sign));
}

void NewProofManager::endResChain(Minisat::Solver::TLit lit)
{
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Assert(d_litToClauseId.find(satLit) != d_litToClauseId.end());
  endResChain(d_litToClauseId[satLit]);
}

// id is the conclusion
void NewProofManager::endResChain(ClauseId id)
{
  Debug("newproof::sat") << "NewProofManager::endResChain " << id << "\n";
  Assert(d_resolution.size() > 0);
  Debug("newproof::sat") << "========\n"
                         << "set .c" << id << "(resolution :clauses (";
  for (unsigned i = 0, size = d_resolution.size(); i < size; ++i)
  {
    Debug("newproof::sat") << ".c" << d_resolution[i].d_id;
    if (i < size - 1)
    {
      Debug("newproof::sat") << " ";
    }
  }
  Debug("newproof::sat") << "========\n";

  // saving for later printing
  d_resolutions.push_back(std::vector<Resolution>());
  d_resolutions.back().insert(
      d_resolutions.back().end(), d_resolution.begin(), d_resolution.end());
  // clearing
  d_resolution.clear();
}

ClauseId NewProofManager::justifyLit(Minisat::Solver::TLit lit)
{
  ClauseId id;
  Debug("newproof::sat") << "NewProofManager::justifyLit: lit: ";
  printLit(lit);
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Debug("newproof::sat") << "[" << d_litToNode[satLit] << "]\n";
  // see if already computed
  if (d_litToClauseId.find(satLit) != d_litToClauseId.end())
  {
    id = d_litToClauseId[satLit];
    Debug("newproof::sat") << "NewProofManager::justifyLit: already has id "
                           << id << "\n";
    return id;
  }
  Debug("newproof::sat")
      << "NewProofManager::justifyLit: computing justification...\n";
  Minisat::Solver::TCRef reason_ref = d_solver->reason(Minisat::var(lit));
  Assert(reason_ref != Minisat::Solver::TCRef_Undef);
  Assert(reason_ref >= 0 && reason_ref < d_solver->ca.size());
  // Here, the call to resolveUnit() can reallocate memory in the
  // clause allocator.  So reload reason ptr each time.
  const Minisat::Solver::TClause& initial_reason = d_solver->ca[reason_ref];
  unsigned current_reason_size = initial_reason.size();
  Debug("newproof::sat") << "NewProofManager::justifyLit: with clause: ";
  printClause(initial_reason);
  Debug("newproof::sat") << "\n";
  std::vector<Resolution> reason_resolutions;
  // add the reason clause first
  Assert(initial_reason.proofId() != 0);
  reason_resolutions.push_back(Resolution(initial_reason.proofId()));
  for (unsigned i = 0; i < current_reason_size; ++i)
  {
    const Minisat::Solver::TClause& current_reason = d_solver->ca[reason_ref];
    Assert(current_reason_size == static_cast<unsigned>(current_reason.size()));
    current_reason_size = current_reason.size();
    Minisat::Solver::TLit curr_lit = current_reason[i];
    // ignore the lit we are trying to justify...
    if (curr_lit == lit)
    {
      continue;
    }
    prop::SatLiteral curr_satLit = toSatLiteral<Minisat::Solver>(curr_lit);
    Assert(d_litToNode.find(curr_satLit) != d_litToNode.end());
    Resolution res(justifyLit(~curr_lit),
                   d_litToNode[curr_satLit],
                   Minisat::sign(curr_lit) ? 0 : 1);
    reason_resolutions.push_back(res);
  }
  // retrieve lit's node definition
  Assert(d_litToNode.find(satLit) != d_litToNode.end());
  Node litDef = d_litToNode[satLit];
  // generate resolution step that allows the derivation of lit
  if (d_format == options::ProofFormatMode::VERIT)
  {
    std::vector<unsigned> reason_ids;
    for (unsigned i = 0, size = reason_resolutions.size(); i < size; ++i)
    {
      reason_ids.push_back(reason_resolutions[i].d_id);
    }
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    id = vtproof->addProofStep(RULE_RESOLUTION, reason_ids, litDef);
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    id = leanproof->addResSteps(reason_resolutions, litDef);
  }
  d_litToClauseId[satLit] = id;
  d_clauseIdToLit[id] = satLit;
  return id;
}

void NewProofManager::finalizeProof(ClauseId conflict_id)
{
  std::vector<Resolution> reasons;
  reasons.push_back(Resolution(conflict_id));
  // retrive clause
  std::vector<Minisat::Solver::TLit> conflict_clause;
  auto it = d_clauseIdToClause.find(conflict_id);
  if (it != d_clauseIdToClause.end())
  {
    for (unsigned i = 0, size = it->second->size(); i < size; ++i)
    {
      conflict_clause.push_back((*it->second)[i]);
    }
  }
  else
  {
    Assert(d_clauseIdToLit.find(conflict_id) != d_clauseIdToLit.end());
    conflict_clause.push_back(
        prop::MinisatSatSolver::toMinisatLit(d_clauseIdToLit[conflict_id]));
  }
  Debug("newproof::sat") << "NewProofManager::finalizeProof: conflict_id: "
                         << conflict_id << "\n";
  // since this clause is conflicting, I must be able to resolve away each of
  // its literals l_1...l_n. Each literal ~l_i must be justifiable
  //
  // Either ~l_i is the conclusion of some previous, already built, step or from
  // a subproof to be computed.
  //
  // For each l_i, a resolution step is created with the id of the step allowing
  // the derivation of ~l_i, whose pivot in the conflict_clause will be l_i. All
  // resolution steps will be saved in the given reasons vector.
  for (unsigned i = 0, size = conflict_clause.size(); i < size; ++i)
  {
    prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(conflict_clause[i]);
    Assert(d_litToNode.find(satLit) != d_litToNode.end());
    Resolution res(justifyLit(~conflict_clause[i]),
                   d_litToNode[satLit],
                   Minisat::sign(conflict_clause[i]) ? 0 : 1);
    reasons.push_back(res);
  }
  if (d_format == options::ProofFormatMode::VERIT)
  {
    std::vector<unsigned> reason_ids;
    for (unsigned i = 0, size = reasons.size(); i < size; ++i)
    {
      reason_ids.push_back(reasons[i].d_id);
    }
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    vtproof->addProofStep(RULE_RESOLUTION, reason_ids, Node::null());
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    leanproof->addResSteps(reasons, Node::null());
  }
}

// case in which I addded a false unit clause
void NewProofManager::finalizeProof(Minisat::Solver::TLit lit)
{
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Debug("newproof::sat")
      << "NewProofManager::finalizeProof: conflicting satLit: " << satLit
      << "\n";
  auto it = d_litToClauseId.find(satLit);
  if (it != d_litToClauseId.end())
  {
    // for whatever reason I may already have a clause id for it...
    finalizeProof(it->second);
    return;
  }
  // must come from input then
  Assert(d_litToNode.find(satLit) != d_litToNode.end());
  Node litDef = d_litToNode[satLit];
  Assert(d_assertionToClauseId.find(litDef) != d_assertionToClauseId.end());
  ClauseId id = d_assertionToClauseId[litDef];
  // since I'm here update this already
  d_litToClauseId[satLit] = id;
  d_clauseIdToLit[id] = satLit;
  finalizeProof(id);
}

void NewProofManager::finalizeProof()
{
  // last added clause is the conflicting one
  ClauseId conflict_id;
  if (d_format == options::ProofFormatMode::VERIT)
  {
    VeritProof* vtproof = static_cast<VeritProof*>(d_proof.get());
    conflict_id = vtproof->getId() - 1;
  }
  else if (d_format == options::ProofFormatMode::LEAN)
  {
    LeanProof* leanproof = static_cast<LeanProof*>(d_proof.get());
    conflict_id = leanproof->getId() - 1;
  }
  finalizeProof(conflict_id);
}

void NewProofManager::queueTheoryProof(prop::SatLiteral lit,
                                       theory::EqProof* proof)
{
  Debug("newproof::pm::th")
      << "NewProofManager::queuing prood with satlit: " << lit << ":\n";
  proof->debug_print("newproof::pm::th", 1);
  Assert(d_litToTheoryProof.find(lit) == d_litToTheoryProof.end());
  d_litToTheoryProof[lit] = proof;
}

void NewProofManager::setLogic(const LogicInfo& logic) { d_logic = logic; }

NewProofManager::NewProofManagerStatistics::NewProofManagerStatistics()
    : d_proofProductionTime("proof::NewProofManager::proofProductionTime")
{
  smtStatisticsRegistry()->registerStat(&d_proofProductionTime);
}

NewProofManager::NewProofManagerStatistics::~NewProofManagerStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_proofProductionTime);
}

}  // namespace CVC4
