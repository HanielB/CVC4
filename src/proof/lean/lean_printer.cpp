/*********************                                                        */
/*! \file lean_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lean proof nodes
 **/

#include "proof/lean/lean_printer.h"

#include <iostream>
#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "options/expr_options.h"
#include "proof/lean/lean_rules.h"

namespace cvc5 {

namespace proof {

LetUpdaterPfCallback::LetUpdaterPfCallback(LetBinding& lbind,
                                           std::set<LeanRule>& letRules)
    : d_lbind(lbind), d_letRules(letRules)
{
}

LetUpdaterPfCallback::~LetUpdaterPfCallback() {}

bool LetUpdaterPfCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                        const std::vector<Node>& fa,
                                        bool& continueUpdate)
{
  // only process non-let rules
  return d_letRules.find(getLeanRule(pn->getArguments()[0]))
         == d_letRules.end();
}

bool LetUpdaterPfCallback::update(Node res,
                                  PfRule id,
                                  const std::vector<Node>& children,
                                  const std::vector<Node>& args,
                                  CDProof* cdp,
                                  bool& continueUpdate)
{
  d_lbind.process(res);
  return false;
}

LeanPrinter::LeanPrinter()
    : d_letRules({
          LeanRule::R0_PARTIAL,
          LeanRule::R1_PARTIAL,
          LeanRule::REFL_PARTIAL,
          LeanRule::CONG_PARTIAL,
          LeanRule::TRANS_PARTIAL,
          LeanRule::AND_INTRO_PARTIAL,
          LeanRule::CL_OR,
          LeanRule::CL_ASSUME,
          LeanRule::TH_ASSUME,
      }),
      d_lbind(options::defaultDagThresh() ? options::defaultDagThresh() + 1
                                          : 0),
      d_cb(new LetUpdaterPfCallback(d_lbind, d_letRules))
{
  d_false = NodeManager::currentNM()->mkConst(false);
}
LeanPrinter::~LeanPrinter() {}

void LeanPrinter::printOffset(std::ostream& out, uint64_t offset) const
{
  for (uint64_t i = 0; i < offset; ++i)
  {
    out << "  ";
  }
}

void LeanPrinter::printSort(std::ostream& out, TypeNode sort)
{
  // functional sort
  if (sort.isFunction())
  {
    out << "(arrowN [";
    // print each arg sort
    size_t size = sort.getNumChildren();
    for (size_t i = 0; i < size - 1; ++i)
    {
      printSort(out, sort[i]);
      out << ", ";
    }
    // print return sort
    printSort(out, sort[size - 1]);
    out << "])";
    return;
  }
  // boolean sort
  if (sort.isBoolean())
  {
    out << "boolSort";
    return;
  }
  if (sort.isInteger())
  {
    out << "intSort";
    return;
  }
  if (sort.isString())
  {
    out << "strSort";
    return;
  }
  // TODO HB will need to add cases for other theories

  // uninterpreted sort
  AlwaysAssert(sort.isSort()) << sort << "\n";
  out << sort;
}

void LeanPrinter::printConstant(std::ostream& out, TNode n)
{
  Kind k = n.getKind();
  if (k == kind::CONST_BOOLEAN)
  {
    out << (n.getConst<bool>() ? "top" : "bot");
    return;
  }
  else if (k == kind::CONST_STRING)
  {
    std::string str = n.getConst<String>().toString();
    out << "(mkValChars [";
    for (size_t i = 0; i < str.length(); ++i)
    {
      out << "\'" << str.at(i) << "\'";
      if (i != str.length() - 1) out << ", ";
    }
    out << "])";
  }
  else  // k == kind::BOUND_VARIABLE
  {
    out << n;
  }
}

void LeanPrinter::printTermList(std::ostream& out, TNode n)
{
  out << "[";
  for (size_t i = 0, size = n.getNumChildren(); i < size; ++i)
  {
    printTerm(out, n[i]);
    out << (i < size - 1 ? ", " : "]");
  }
}

void LeanPrinter::printBinary(std::ostream& out, TNode n)
{
  Kind k = n.getKind();
  out << kind::toString(k) << " ";
  printTerm(out, n[0]);
  out << " ";
  printTerm(out, n[1]);
}

void LeanPrinter::printTerm(std::ostream& out, TNode n, bool letTop)
{
  Node nc = d_lbind.convert(n, "let", letTop);
  size_t nChildren = nc.getNumChildren();
  // printing constant symbol
  if (nChildren == 0)
  {
    if (nc.getKind() == kind::CONST_RATIONAL)
    {
      out << "(mkValInt ";
      printConstant(out, nc);
      out << ")";
    } else
    {
      printConstant(out, nc);
    }
    return;
  }
  // printing applications / formulas
  out << "(";
  Kind k = nc.getKind();
  TypeNode tn = nc.getType();
  switch (k)
  {
    case kind::APPLY_UF:
    {
      Node op = nc.getOperator();
      Assert(nChildren >= 1);
      if (nChildren > 1)
      {
        out << "appN ";
        printTerm(out, op);
        out << " ";
        printTermList(out, nc);
      }
      else
      {
        out << "app ";
        printTerm(out, op);
        out << " ";
        printTerm(out, nc[0]);
      }
      break;
    }
    case kind::EQUAL:
    {
      // out << "mkEq ";
      out << "eq ";
      printTerm(out, nc[0]);
      out << " ";
      printTerm(out, nc[1]);
      break;
    }
    case kind::XOR:
    {
      // out << "mkXor ";
      out << "xor ";
      printTerm(out, nc[0]);
      out << " ";
      printTerm(out, nc[1]);
      break;
    }
    case kind::OR:
    {
      Assert(nChildren >= 2);
      if (nChildren > 2)
      {
        out << "orN ";
        printTermList(out, nc);
      }
      else
      {
        // out << "mkOr ";
        out << "term.or ";
        printTerm(out, nc[0]);
        out << " ";
        printTerm(out, nc[1]);
      }
      break;
    }
    case kind::AND:
    {
      Assert(nChildren >= 2);
      if (nChildren > 2)
      {
        out << "andN ";
        printTermList(out, nc);
      }
      else
      {
        // out << "mkAnd ";
        out << "term.and ";
        printTerm(out, nc[0]);
        out << " ";
        printTerm(out, nc[1]);
      }
      break;
    }
    case kind::IMPLIES:
    {
      out << "implies ";
      printTerm(out, nc[0]);
      out << " ";
      printTerm(out, nc[1]);
      break;
    }
    case kind::NOT:
    {
      out << "term.not ";
      printTerm(out, nc[0]);
      break;
    }
    case kind::ITE:
    {
      out << "fIte ";
      printTerm(out, nc[0]);
      out << " ";
      printTerm(out, nc[1]);
      out << " ";
      printTerm(out, nc[2]);
      break;
    }
    case kind::DISTINCT:
    {
      out << "distinct ";
      printTerm(out, nc[0]);
      out << " ";
      printTerm(out, nc[1]);
      break;
    }
    case kind::SEXPR:
    {
      out << "[";
      printTerm(out, nc[0]);
      for (size_t i = 1, size = nc.getNumChildren(); i < size; ++i)
      {
        out << ", ";
        printTerm(out, nc[i]);
      }
      out << "]";
      break;
    }
  case kind::STRING_LENGTH:
  {
    out << "mkLength ";
    printTerm(out, nc[0]);
    break;
  }
  case kind::LT:
  case kind::LEQ:
  case kind::GT:
  case kind::GEQ:
  case kind::MULT:
  case kind::PLUS:
  {
    printBinary(out, nc);
    break;
  }
    default: Unhandled() << " " << k;
  }
  out << ")" << (letTop ? "" : "\n");
}

void LeanPrinter::printTermList(std::ostream& out,
                                const std::vector<Node>& children)
{
  out << "[";
  for (size_t i = 0, size = children.size(); i < size; ++i)
  {
    printTerm(out, children[i]);
    out << (i < size - 1 ? ", " : "]");
  }
}

void LeanPrinter::printLetList(std::ostream& out)
{
  std::vector<Node> letList;
  d_lbind.letify(letList);
  std::map<Node, size_t>::const_iterator it;
  for (TNode n : letList)
  {
    size_t id = d_lbind.getId(n);
    Assert(id != 0);
    out << "def let" << id << " := ";
    printTerm(out, n, false);
  }
}

void LeanPrinter::printStepId(std::ostream& out,
                              const ProofNode* pfn,
                              const std::map<const ProofNode*, size_t>& pfMap,
                              const std::map<Node, size_t>& pfAssumpMap)
{
  if (pfn->getRule() == PfRule::ASSUME)
  {
    AlwaysAssert(pfAssumpMap.find(pfn->getResult()) != pfAssumpMap.end()) << pfn->getResult();
    out << "lean_a" << pfAssumpMap.find(pfn->getResult())->second;
  }
  else
  {
    AlwaysAssert(pfMap.find(pfn) != pfMap.end());
    out << "lean_s" << pfMap.find(pfn)->second;
  }
}

void LeanPrinter::printProof(std::ostream& out,
                             size_t& id,
                             uint64_t offset,
                             std::shared_ptr<ProofNode> pfn,
                             std::map<const ProofNode*, size_t>& pfMap,
                             std::map<Node, size_t>& pfAssumpMap)
{
  std::map<const ProofNode*, size_t>::const_iterator pfIt =
      pfMap.find(pfn.get());
  if (pfIt != pfMap.end())
  {
    return;
  }
  if (pfn->getRule() == PfRule::ASSUME)
  {
    return;
  }
  TNode res = pfn->getResult();
  // print rule specific lean syntax, traversing children before parents in
  // ProofNode tree
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  Trace("test-lean") << "printProof: offset " << offset << "\n";
  Trace("test-lean") << "printProof: args " << args << "\n";
  LeanRule rule = getLeanRule(args[0]);
  Trace("test-lean") << "printProof: rule " << rule << "\n";
  Trace("test-lean") << "printProof: result " << res << "\n";
  if (rule == LeanRule::UNKNOWN)
  {
    // save proof step in map
    pfMap[pfn.get()] = id++;
    out << "Unhandled: " << rule << " " << args << "\n";
    return;
  }
  // we handle scope differently because it starts a subproof
  if (rule == LeanRule::SCOPE)
  {
    printOffset(out, offset);
    out << "have lean_s" << id << " : thHolds ";
    // print conversion to a clause of the original scope's conclusion
    printTerm(out, res);
    out << " from\n";
    // each argument to the scope proof node corresponds to one scope to close
    // in the Lean proof. To avoid clashes, we shift the assumptions numbers by
    // current pfAssumpMap' size
    size_t assumptionsShift = pfAssumpMap.size();
    std::map<Node, size_t> backupMap;
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      auto it = pfAssumpMap.find(args[i]);
      if (it != pfAssumpMap.end())
      {
        backupMap[args[i]] = it->second;
      }
      pfAssumpMap[args[i]] = assumptionsShift + i - 3;
      // push and print offset
      printOffset(out, ++offset);
      out << "(scope (fun lean_a" << assumptionsShift + i - 3 << " : thHolds ";
      printTerm(out, args[i]);
      out << " =>\n";
    }
    // similarly, we shift step ids by the number of current steps
    size_t newId = pfMap.size();
    // use a new proof map for subproof
    // std::map<const ProofNode*, size_t> subpfMap{pfMap};
    Trace("test-lean") << pop;
    AlwaysAssert(children.size() == 1);
    printProof(out, newId, ++offset, children[0], pfMap, pfAssumpMap);
    Trace("test-lean") << pop;
    // print conclusion of scope's child. For now this is a redundant step
    // because the proof can't end with "have" but rather with "show"
    printOffset(out, offset);
    out << "show thHolds ";
    printTerm(out, children[0]->getResult());
    out << " from ";
    printStepId(out, children[0].get(), pfMap, pfAssumpMap);
    out << "\n";
    // now close. We have assumptions*2 parens
    std::stringstream cparens;
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      offset--;
      cparens << "))";
    }
    printOffset(out, offset);
    out << cparens.str() << "\n";
    // recover assumption map
    for (const auto& p : backupMap)
    {
      pfAssumpMap[p.first] = p.second;
    }
    // save proof step in map
    pfMap[pfn.get()] = id++;
    return;
  }
  Trace("test-lean") << push;
  for (const std::shared_ptr<ProofNode>& child : children)
  {
    printProof(out, id, offset, child, pfMap, pfAssumpMap);
  }
  Trace("test-lean") << pop;
  printOffset(out, offset);
  AlwaysAssert(args.size() >= 3);
  // print conclusion: proof node concludes `false`, print as show ... rather
  // than have s.... If the proof has a clausal conclusion (as argument), print
  // holds, otherwise thHolds and the result.
  bool hasClausalResult = args[2] != Node::null();
  if (d_letRules.find(rule) != d_letRules.end())
  {
    out << "let lean_s" << id << " := " << rule;
  }
  else
  {
    if (res == d_false)
    {
      out << "show " << (hasClausalResult ? "holds [] " : "thHolds bot");
    }
    else
    {
      out << "have lean_s" << id << " : ";
      if (hasClausalResult)
      {
        out << "holds ";
        printTerm(out, args[2]);
      }
      else
      {
        out << "thHolds ";
        printTerm(out, res);
      }
    }
    out << " from " << rule;
  }
  for (const std::shared_ptr<ProofNode>& child : children)
  {
    out << " ";
    printStepId(out, child.get(), pfMap, pfAssumpMap);
  }
  for (size_t i = 3, size = args.size(); i < size; ++i)
  {
    out << " ";
    printTerm(out, args[i]);
  }
  out << "\n";
  // save proof step in map
  pfMap[pfn.get()] = id++;
}

void LeanPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid Lean output from a ProofNode
  Trace("test-lean-pf") << "Post-processed proof " << *pfn.get() << "\n";
  // TODO preamble should be theory dependent
  out << "import Cdclt.Euf\n\n";
  // increase recursion depth and heartbeats
  out << "set_option maxRecDepth 1000\nset_option maxHeartbeats 500000\n\n";
  // do includes
  out << "open proof\nopen proof.sort proof.term\n";
  out << "open rules eufRules\n\n";

  // Print user defined sorts and constants of those sorts
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
  }
  int sortCount = 1000;
  int symCount = 1000;
  // uninterpreted sorts
  std::unordered_set<TypeNode> sts;
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    // only collect for declaration non predefined sorts
    if (st.isSort() && st.getKind() != kind::TYPE_CONSTANT)
    {
      Trace("test-lean") << "collecting sort " << st << " with kind "
                         << st.getKind() << "\n";
      sts.insert(st);
    }
    else if (st.isFunction())
    {
      for (const auto& stc : st)
      {
        // TODO get recursively for functional sorts under functional sorts
        if (stc.getKind() != kind::TYPE_CONSTANT)
        {
          sts.insert(stc);
        }
      }
    }
  }
  for (const auto& s : sts)
  {
    out << "def " << s << " := atom " << sortCount++ << "\n";
  }
  // uninterpreted functions
  for (const Node& s : syms)
  {
    out << "def " << s << " := const " << symCount++ << " ";
    printSort(out, s.getType());
    out << "\n";
  }
  // actual proof is below processed scope and possibly spurious thAssume
  AlwaysAssert(pfn->getChildren().size() == 1
               && pfn->getChildren()[0]->getChildren().size() == 1);
  std::shared_ptr<ProofNode> innerPf = pfn->getChildren()[0]->getChildren()[0];
  Trace("test-lean") << "innerPf rule: " << getLeanRule(innerPf->getArguments()[0]) << "\n";
  // compute the term lets. For this consider the assertions and the conclusions
  // of explicit proof steps
  for (const Node& a : assertions)
  {
    d_lbind.process(a);
  }
  ProofNodeUpdater updater(nullptr, *(d_cb.get()), false, false, false);
  updater.process(innerPf);

  const std::vector<Node>& assumptions = pfn->getChildren()[0]->getArguments();
  for (size_t i = 3, size = assumptions.size(); i < size; ++i)
  {
    d_lbind.process(assumptions[i]);
  }
  printLetList(out);

  // print theorem header, which is to get proofs of all the assumptions and
  // conclude a proof of []. The assumptions are args[2..]
  out << "\ntheorem th0 : ";
  Assert(assumptions.size() > 2);
  for (size_t i = 3, size = assumptions.size(); i < size; ++i)
  {
    out << "thHolds ";
    printTerm(out, assumptions[i]);
    out << " -> ";
  }
  // whether conclusion is "thHolds bot" or "holds []" depends on what the inner
  // proof term is concluding. So we check here:
  AlwaysAssert(innerPf->getArguments().size() >= 3);
  if (!innerPf->getArguments()[2].isNull())
  {
    out << "holds [] :=\n";
  }
  else
  {
    AlwaysAssert(innerPf->getResult() == d_false)
      << "conclusion with rule " << getLeanRule(innerPf->getArguments()[0])
        << " is actually " << innerPf->getResult();
    out << "thHolds bot :=\n";
  }
  // print initial assumptions
  std::map<Node, size_t> pfAssumpMap;
  for (size_t i = 3, size = assumptions.size(); i < size; ++i)
  {
    pfAssumpMap[assumptions[i]] = i - 3;
    out << "fun lean_a" << i - 3 << " : thHolds ";
    printTerm(out, assumptions[i]);
    out << " =>\n";
  }
  std::stringstream ss;
  ss << out.rdbuf();
  size_t id = 0;
  Trace("test-lean") << "Before getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  std::map<const ProofNode*, size_t> pfMap;
  printProof(out, id, 0, innerPf, pfMap, pfAssumpMap);
  ss.clear();
  ss << out.rdbuf();
  Trace("test-lean") << "After getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  out << "\n";
}

}  // namespace proof
}  // namespace cvc5
