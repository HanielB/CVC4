/*********************                                                        */
/*! \file verit_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes into veriT proof nodes
 **/

#include "proof/verit/verit_post_processor.h"

namespace CVC4 {

namespace proof {

VeritProofPostprocessCallback::VeritProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
{
  d_nm = NodeManager::currentNM();
  d_cl = d_nm->mkBoundVar("cl",d_nm->stringType());
}

bool VeritProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                 bool& continueUpdate)
{
  if(pn->getRule() == PfRule::VERIT_RULE){
    return false;
  }
  return true;
}

bool VeritProofPostprocessCallback::update(
    Node res,
    PfRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp,
    bool& continueUpdate)
{
  Trace("verit-proof") << "- veriT post process callback " << res << " " << id
                       << " " << children << " / " << args << std::endl;

  d_nm = NodeManager::currentNM();
  std::vector<Node> new_args = std::vector<Node>();

  //Basic rules (non-extended mode)
  switch (id)
  {
    //================================================= Core rules
    //======================== Assume and Scope
    // ======== Assumption (a leaf)
    // Children: none
    // Arguments: (F)
    // --------------
    // Conclusion: F
    //
    // proof rule: assume
    // proof node: (VP:F)
    // proof term: F
    // premises: ()
    // args: ()
    case PfRule::ASSUME:
    {
      return addVeritStep(res, VeritRule::ASSUME, children, {}, *cdp);
    }
    // ======== Scope (a binder for assumptions)
    // Children: (P:F)
    // Arguments: (F1, ..., Fn)
    // --------------
    // Conclusion: (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)) if F is false
    //
    // proof rule: anchor
    // proof node: (VP1:(cl (not F1) ... (not Fn) F))
    // proof term: (cl (not F1) ... (not Fn) F)
    // premises: P
    // args: (F1, ..., Fn)
    //
    // Repeat the following two step for i=1 to n:
    //
    // proof rule: and_pos
    // proof node: (VP2_i:(cl (not (and F1 ... Fn)) Fi))
    // proof term: (cl (not (and F1 ... Fn)) Fi)
    // premises: ()
    // args: ()
    //
    // Let (not (and F1 ... Fn))^i denote the repetition of (not (and F1 ...
    // Fn)) for i times
    //
    // proof rule: resolution
    // proof node: (VP2a:(cl F (not (and F1 ... Fn))^n))
    // proof term: (cl F (not (and F1 ... Fn))^n)
    // premises: VP1, VP2_i for all i in {1..n},
    // args: ()
    //
    // In extended mode add reordering step:
    //
    // proof rule: reorder
    // proof node: (VP2b:(cl (not (and F1 ... Fn))^n F))
    // proof term: (cl (not (and F1 ... Fn))^n F)
    // premises: VP2a
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (VP3:(cl (not (and F1 ... Fn)) F))
    // proof term: (cl (not (and F1 ... Fn)) F)
    // premises: VP2a or VP2b
    // args: ()
    //
    // proof rule: implies_neg1
    // proof node: (VP4:(cl (=> (and F1 ... Fn) F) (and F1 ... Fn)))
    // proof term: (cl (=> (and F1 ... Fn) F) (and F1 ... Fn))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP5:(cl (=> (and F1 ... Fn) F) F))
    // proof term: (cl (=> (and F1 ... Fn) F) F)
    // premises: VP4 VP3
    // args: ()
    //
    // proof rule: implies_neg2
    // proof node: (VP6:(cl (=> (and F1 ... Fn) F) (not F)))
    // proof term: (cl (=> (and F1 ... Fn) F) (not F))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP7:(cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F)))
    // proof term: (cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F))
    // premises: VP5 VP6
    // args: ()
    //
    // If F = false:
    //
    // proof rule: duplicated_literals
    // proof node: (VP8:(cl (=> (and F1 ... Fn) F)))
    // proof term: (cl (=> (and F1 ... Fn) F))
    // premises: VP7
    // args: ()
    //
    // proof rule: implies_simplify
    // proof node:
    //   (VP9:(cl (= (=> (and F1 ... Fn) false) (not (and F1 ...Fn)))))
    // proof term:
    //   (cl (= (=> (and F1 ... Fn) false) (not (and F1 ... Fn))))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof node:
    //   (VP10:(cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn))))
    // proof term:
    //   (cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn)))
    // premises: VP9
    // args: ()
    //
    // proof rule: resolution
    // proof node: (or (not (and F1 ... Fn)))
    // proof term: (cl (not (and F1 ... Fn)))
    // premises: VP8 VP10
    // args: ()
    //
    // Otherwise:
    //
    // proof rule: duplicated_literals
    // proof node: (or (=> (and F1 ... Fn) F))
    // proof term: (cl (=> (and F1 ... Fn) F))
    // premises: VP7
    // args: ()
    case PfRule::SCOPE:
    {
      bool success = true;

      //Build vp1
      std::vector<Node> negNode;
      for(Node arg:args){
        negNode.push_back(arg.notNode());     // (not F1) ... (not Fn)
      }
      negNode.push_back(children[0]);         // (not F1) ... (not Fn) F
      negNode.insert(negNode.begin(), d_cl);  // (cl (not F1) ... (not F) F)
      Node vp1 = d_nm->mkNode(kind::SEXPR, negNode);
      success &=
          addVeritStep(vp1, VeritRule::ANCHOR_SUBPROOF, children, args, *cdp);

      //Build vp2i
      Node andNode;
      if (args.size() != 1)
      {
        andNode = d_nm->mkNode(kind::AND, args);  // (and F1 ... Fn)
      }
      else
      {
        andNode = args[0];  // F1
      }
      std::vector<Node> premisesVP2 = {vp1};
      std::vector<Node> notAnd = {d_cl,children[0]}; // cl F
      Node vp2_i;
      for (long unsigned int i = 0; i < args.size(); i++)
      {
        vp2_i = d_nm->mkNode(kind::SEXPR,
                             d_cl,
                             andNode.notNode(),
                             args[i]);  // (cl (not (and F1 ... Fn)) Fi)
        success &= addVeritStep(vp2_i, VeritRule::AND_POS, {}, {}, *cdp);
        premisesVP2.push_back(vp2_i);
        notAnd.push_back(andNode.notNode());  // cl F (not (and F1 ... Fn))^i
      }

      Node vp2a = d_nm->mkNode(kind::SEXPR,notAnd); // (cl F (not (and F1 ... Fn))^n)
      success &=
          addVeritStep(vp2a, VeritRule::RESOLUTION, premisesVP2, {}, *cdp);
      Node vp2 = vp2a;
      if(d_extended){
   notAnd.erase(notAnd.begin()+1);  //(cl (not (and F1 ... Fn))^n F)
   notAnd.push_back(children[0]);   //(cl (not (and F1 ... Fn))^n F)
         Node vp2b = d_nm->mkNode(kind::SEXPR,notAnd);
         success &=
          addVeritStep(vp2b, VeritRule::REORDER, {vp2a}, {}, *cdp);
   vp2=vp2b;
      }

      Node vp3 =
          d_nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), children[0]);
      success &=
          addVeritStep(vp3, VeritRule::DUPLICATED_LITERALS, {vp2}, {}, *cdp);

      Node vp8 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::IMPLIES, andNode, children[0]));

      Node vp4 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], andNode);
      success &= addVeritStep(vp4, VeritRule::IMPLIES_NEG1, {}, {}, *cdp);

      Node vp5 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0]);
      success &= addVeritStep(vp5, VeritRule::RESOLUTION, {vp4, vp3}, {}, *cdp);

      Node vp6 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0].notNode());
      success &= addVeritStep(vp6, VeritRule::IMPLIES_NEG2, {}, {}, *cdp);

      Node vp7 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], vp8[1]);
      success &= addVeritStep(vp7, VeritRule::RESOLUTION, {vp5, vp6}, {}, *cdp);

      if (children[0] != d_nm->mkConst(false))
      {
        success &= addVeritStep(
            res, VeritRule::DUPLICATED_LITERALS, vp8, {vp7}, {}, *cdp);
      }
      else
      {
        success &=
            addVeritStep(vp8, VeritRule::DUPLICATED_LITERALS, {vp7}, {}, *cdp);

        Node vp9 =
            d_nm->mkNode(kind::SEXPR,
                         d_cl,
                         d_nm->mkNode(kind::EQUAL, vp8[1], andNode.notNode()));
        success &= addVeritStep(vp9, VeritRule::IMPLIES_SIMPLIFY, {}, {}, *cdp);

        Node vp10 = d_nm->mkNode(
            kind::SEXPR, d_cl, vp8[1].notNode(), andNode.notNode());
        success &= addVeritStep(vp10, VeritRule::EQUIV1, {vp9}, {}, *cdp);

        success &= addVeritStep(res,
                                VeritRule::RESOLUTION,
                                d_nm->mkNode(kind::SEXPR, d_cl, res),
                                {vp8, vp10},
                                {},
                                *cdp);
      }

      return success;
    }
    // ======== Theory Rewrite
    // Children: none
    // Arguments: (F, tid, rid)
    // ----------------------------------------
    // Conclusion: F
    // where F is an equality of the form (= t t') where t' is obtained by
    // applying the kind of rewriting given by the method identifier rid, which
    // is one of:
    //  { RW_REWRITE_THEORY_PRE, RW_REWRITE_THEORY_POST, RW_REWRITE_EQ_EXT }
    // Notice that the checker for this rule does not replay the rewrite to
    // ensure correctness, since theory rewriter methods are not static. For
    // example, the quantifiers rewriter involves constructing new bound
    // variables that are not guaranteed to be consistent on each call.
    //
    //
    // The rule is translated according to tid and the outermost connective of
    // t. This is not an exact translation but should work in most cases.
    //
    // E.g. if the F: (= (* 0 d) 0) and tid = THEORY_ARITH, then prod_simplify
    // is correctly guessed as the rule.
    case PfRule::THEORY_REWRITE:{
      theory::TheoryId tid = static_cast<theory::TheoryId>(std::stoul(args[1].toString()));
      VeritRule vrule = VeritRule::UNDEFINED;
      Node t = res[0];
      //std::cout << "tid " << tid << std::endl;
      //std::cout << "t kind " << t.getKind() << std::endl;
      //std::cout << "(= t t')" << res << std::endl;
      switch (tid){
        case theory::TheoryId::THEORY_BUILTIN:{
     switch(t.getKind()){
       case kind::ITE:{
         vrule = VeritRule::ITE_SIMPLIFY; break;
       }
       case kind::EQUAL:
             {  // Test equiv_simplify
                std::cout << "What happens here " << t << std::endl;
               vrule = VeritRule::EQ_SIMPLIFY; break;
             }
             case kind::AND:{
         vrule = VeritRule::AND_SIMPLIFY; break;
       }
       case kind::OR:{
         vrule = VeritRule::OR_SIMPLIFY; break;
       }
       case kind::NOT:{
         vrule = VeritRule::NOT_SIMPLIFY; break;
       }
       case kind::IMPLIES:{
         vrule = VeritRule::IMPLIES_SIMPLIFY; break;
       }
       default:{
               std::cout << "tid " << tid << std::endl;
               std::cout << "t kind " << t.getKind() << std::endl;
               std::cout << "(= t t')" << res << std::endl;
         break;
             }
    }
    break;
  }
        case theory::TheoryId::THEORY_BOOL:
        {
          vrule = VeritRule::BOOL_SIMPLIFY;
          break;
        }  // TODO: Should there be a case distinction with kinds here?
        case theory::TheoryId::THEORY_UF:{
    switch(t.getKind()){
            case kind::EQUAL:
            {  // A lot of these seem to be symmetry rules but not all....
              // std::cout << "What happens here2: " << std::endl;
              //    std::cout << "tid2 " << tid << std::endl;
              // std::cout << "t kind2 " << t.getKind() << std::endl;
              //  std::cout << "(= t t')2 " << res << std::endl;
              vrule = VeritRule::EQUIV_SIMPLIFY;
              break;
            }
             default:{
               // std::cout << "t kind 3" << t.getKind() << std::endl;
               // std::cout << "(= t t') 3" << res << std::endl;
             }
    }
    break;
  }
        case theory::TheoryId::THEORY_ARITH:{
     switch(t.getKind()){
       case kind::DIVISION:{
         vrule = VeritRule::DIV_SIMPLIFY; break;
       }
       case kind::PRODUCT:{ //What is this?
         vrule = VeritRule::PROD_SIMPLIFY; break;
             }
       case kind::MINUS:{
         vrule = VeritRule::MINUS_SIMPLIFY; break;
       }
       case kind::UMINUS:{
         vrule = VeritRule::UNARY_MINUS_SIMPLIFY; break;
       }
       case kind::PLUS:{
         vrule = VeritRule::NOT_SIMPLIFY; break;
       }
       case kind::MULT:{
         vrule = VeritRule::PROD_SIMPLIFY;break;
       }
       case kind::EQUAL:{}
       case kind::LT:{}
       case kind::GT:{}
       case kind::GEQ:{}
       case kind::LEQ:{
         vrule = VeritRule::COMP_SIMPLIFY; break;
       }
       case kind::CAST_TO_REAL:{
               return addVeritStep(res,
                                   VeritRule::LA_GENERIC,
                                   d_nm->mkNode(kind::SEXPR, d_cl, res),
                                   children,
                                   {d_nm->mkConst(Rational(1))},
                                   *cdp);
       }
       default:{
               // std::cout << "t kind " << t.getKind() << std::endl;
               // std::cout << "(= t t')" << res << std::endl;
             }
    }
    break;
  }
        case theory::TheoryId::THEORY_BV:{break;}
        case theory::TheoryId::THEORY_FP:{break;}
        case theory::TheoryId::THEORY_ARRAYS:{break;}
        case theory::TheoryId::THEORY_DATATYPES:{break;}
        case theory::TheoryId::THEORY_SEP:{break;}
        case theory::TheoryId::THEORY_SETS:{break;}
        case theory::TheoryId::THEORY_BAGS:{break;}
        case theory::TheoryId::THEORY_STRINGS:{break;}
  case theory::TheoryId::THEORY_QUANTIFIERS:{ vrule = VeritRule::QUANTIFIER_SIMPLIFY; break;}
        case theory::TheoryId::THEORY_LAST:{break;}
  default:{};
      }
      return addVeritStep(res,
                          vrule,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    //================================================= Boolean rules
    // ======== Resolution
    // Children:
    //  (P1:C1, P2:C2)
    // Arguments: (id, L)
    // ---------------------
    // Conclusion: C
    // where
    //   - C1 and C2 are nodes viewed as clauses, i.e., either an OR node with
    //     each children viewed as a literal or a node viewed as a literal. Note
    //     that an OR node could also be a literal.
    //   - id is either true or false
    //   - L is the pivot of the resolution, which occurs as is (resp. under a
    //     NOT) in C1 and negatively (as is) in C2 if id = true (id = false).
    //   C is a clause resulting from collecting all the literals in C1, minus
    //   the first occurrence of the pivot or its negation, and C2, minus the
    //   first occurrence of the pivot or its negation, according to the policy
    //   above. If the resulting clause has a single literal, that literal
    //   itself is the result; if it has no literals, then the result is false;
    //   otherwise it's an OR node of the resulting literals.
    //
    //
    // In case that C1 = (or F1 ... Fn) and C2 != (not (or F1 ... Fn)):
    //
    // proof rule: or
    // proof node: (VP1:(cl F1 ... Fn))
    // proof term: (cl F1 ... Fn)
    // premises: P1
    // args: ()
    //
    // Otherwise VP1 = P1
    //
    // In case that C2 = (or F1 ... Fn) and C1 != (not (or F1 ... Fn)):
    //
    // proof rule: or
    // proof node: (VP2:(cl F1 ... Fn))
    // proof term: (cl F1 ... Fn)
    // premises: P2
    // args: ()
    //
    // Otherwise VP2 = P2
    //
    // If C = (or G1 ... Gn) then except if id = true (false) and C1 = L or C2 =
    // not L (C2 = L and C1 = not L):
    //
    // proof rule: resolution
    // proof node: (or G1 ... Gn)
    // proof term: (cl G1 ... Gn)
    // premises: VP1 VP2
    // args: ()
    //
    // Otherwise if C = false
    //
    // proof rule: resolution
    // proof node: C
    // proof term: (cl)
    // premises: VP1 VP2
    // args: ()
    //
    // Otherwise,
    //
    // proof rule: resolution
    // proof node: C
    // proof term: (cl C)
    // premises: VP1 VP2
    // args: ()
    case PfRule::RESOLUTION:{
      bool success = true;
      Node vp1 = children[0];
      Node vp2 = children[1];

      std::vector<Node>
          current_resolvent;  // Needed to determine if (cl C) or (cl G1 ... Gn)
                              // should be added in the end.

       VeritRule vp1_rule =
       static_cast<VeritRule>(std::stoul(cdp->getProofFor(vp1)->getArguments()[0].toString()));
       VeritRule vp2_rule =
       static_cast<VeritRule>(std::stoul(cdp->getProofFor(vp2)->getArguments()[0].toString()));

      // TODO: Check if child rule is SYMM, use equal_Nodes


      // If the rule of the child is ASSUME or EQ_RESOLUTION and additional or
      // step might be needed. TODO: REPLACE EQ_RESOLUTION
      if ((vp1_rule == VeritRule::ASSUME
           || vp1_rule == VeritRule::EQ_RESOLUTION))
      {
        if (children[0].getKind() == kind::OR
            && !isSameModEqual(children[0], children[1].notNode())) //TODO: isSameModeEqual
        {
          success &= addVeritStepFromOr(
              children[0], VeritRule::OR, {children[0]}, {}, *cdp);
          vp1 = d_nm->mkNode(kind::SEXPR, d_cl, vp1);
          // If this is the case the literals in C1 are added to the
          // current_resolvent.
          current_resolvent.insert(
              current_resolvent.end(), children[0].begin(), children[0].end());
        }
        else
        {
          // Otherwise, the whole clause is added.
          current_resolvent.push_back(children[0]);
        }
      }
      // For all other rules it is easy to determine if the whole clause or the
      // literals in the clause should be added. If the node is an or node add
      // literals otherwise the whole clause.
      else
      {
        if (children[0].getKind() == kind::OR)
        {
          current_resolvent.insert(
              current_resolvent.end(), children[0].begin(), children[0].end());
        }
        else
        {
          current_resolvent.push_back(children[0]);
        }
      }
      // The same is done to the second child.
      if ((vp2_rule == VeritRule::ASSUME
           || vp2_rule == VeritRule::EQ_RESOLUTION))
      {
        if (children[1].getKind() == kind::OR
            && !isSameModEqual(children[1], children[0].notNode()))
        {  // TODO: vp1_rule == PfRule::ASSUME &&
          success &= addVeritStepFromOr(
              children[1], VeritRule::OR, {children[1]}, {}, *cdp);
          vp2 = d_nm->mkNode(kind::SEXPR, d_cl, vp2);
          current_resolvent.insert(
              current_resolvent.end(), children[1].begin(), children[1].end());
        }
        else
        {
          current_resolvent.push_back(children[1]);
        }
      }
      else
      {
        if (children[1].getKind() == kind::OR)
        {
          current_resolvent.insert(
              current_resolvent.end(), children[1].begin(), children[1].end());
        }
        else
        {
          current_resolvent.push_back(children[1]);
        }
      }

      // The pivot and its negation are deleted from the current_resolvent
      current_resolvent.erase(std::find(
          current_resolvent.begin(), current_resolvent.end(), args[1]));
      current_resolvent.erase(std::find(current_resolvent.begin(),
                                        current_resolvent.end(),
                                        args[1].notNode()));
      // If there is only one elment left C should be printed as (cl C)
      // otherwise as (cl G1 ... Gn)
      if (res.getKind() == kind::OR && current_resolvent.size() != 1)
      {
        return success &= addVeritStepFromOr(res,
                                             VeritRule::RESOLUTION,
                                             {vp1, vp2},
                                             {},
                                             *cdp);  //(cl G1 ... Gn)
      }
      if (res == d_nm->mkConst(false))
      {
        return success &= addVeritStep(res,
                                       VeritRule::RESOLUTION,
                                       d_nm->mkNode(kind::SEXPR, d_cl),
                                       {vp1, vp2},
                                       {},
                                       *cdp);
      }
      return success &= addVeritStep(res,
                                     VeritRule::RESOLUTION,
                                     d_nm->mkNode(kind::SEXPR, d_cl, res),
                                     {vp1, vp2},
                                     {},
                                     *cdp);  //(cl C)
    }
    // ======== N-ary Resolution
    // Children: (P1:C_1, ..., Pm:C_n)
    // Arguments: (id_1, L_1, ..., id_{n-1}, L_{n-1})
    // ---------------------
    // Conclusion: C
    // where
    //   - let C_1 ... C_n be nodes viewed as clauses, as defined above
    //   - let "C_1 <>_{L,id} C_2" represent the resolution of C_1 with C_2 with
    //     pivot L and policy id, as defined above
    //   - let C_1' = C_1 (from P1),
    //   - for each i > 1, let C_i' = C_{i-1}' <>_{L_{i-1}, id_{i-1}} C_i
    //   The result of the chain resolution is C = C_n'
    //
    // If for any Ci, Ci = (or F1 ... Fn) and Ci != L_{i-1} (for C1, C1 != L_1)
    // then:
    //
    // proof rule: or
    // proof node: (VPi:(cl F1 ... Fn))
    // proof term: (cl F1 ... Fn)
    // premises: Pi
    // args: ()
    //
    // Otherwise VPi = Ci
    //
    // proof rule: resolution
    // proof node: C
    // proof term: (cl C)
    // premises:
    // args: ()
    case PfRule::CHAIN_RESOLUTION:  // TODO
    {//TODO: check if id necessary
      bool success = true;
      Node trueNode = d_nm->mkConst(true);
      Node falseNode = d_nm->mkConst(false);

      Node pivot_id = args[0];
      Node L = args[1];
      std::vector<Node> current_resolvent;
      std::vector<Node> new_children = children;

      // First child handling
      VeritRule child_rule =
      static_cast<VeritRule>(std::stoul(cdp->getProofFor(children[0])->getArguments()[0].toString()));

      if ((child_rule == VeritRule::ASSUME
           || child_rule == VeritRule::EQ_RESOLUTION))
      {
        if (children[0].getKind() == kind::OR && children[0] != L)
        {
          // add cl step and update new_children
          std::vector<Node> clauses;
          clauses.push_back(d_cl);
          clauses.insert(clauses.end(), children[0].begin(), children[0].end());
          Node conclusion = d_nm->mkNode(kind::SEXPR,clauses);
          success &=
              addVeritStep(conclusion, VeritRule::OR, {children[0]}, {}, *cdp);
          new_children[0] = conclusion;
          current_resolvent.insert(
              current_resolvent.end(), children[0].begin(), children[0].end());
        }
        else
        {
          current_resolvent.push_back(children[0]);
        }
      }
      else
      {
        if (children[0].getKind() == kind::OR)
        {
          current_resolvent.insert(
              current_resolvent.end(), children[0].begin(), children[0].end());
        }
        else
        {
          current_resolvent.push_back(children[0]);
        }
      }
      // delete L (resp. L.notNode()) from current resolvent
      /*if(id == trueNode){
        current_resolvent.erase(std::find(current_resolvent.begin(),current_resolvent.end(),L));
      }
      else{
        current_resolvent.erase(std::find(current_resolvent.begin(),current_resolvent.end(),L.notNode()));
      }*/

      // All further children
      for (unsigned long int i = 1; i < children.size(); i++)
      {
        // Add cl step if children[i] has kind OR and the L before it is not
        // itself E.g. L_{i-1} = c and children[i] = (or a (not c)) -> add OR
        // step E.g. L_{i-1} = (or a (not c)) and children[i] = (or a (not c)) ->
        // don't add OR step
        child_rule = static_cast<VeritRule>(std::stoul(cdp->getProofFor(children[i])->getArguments()[0].toString()));
        if ((child_rule == VeritRule::ASSUME
             || child_rule == VeritRule::EQ_RESOLUTION))
        {
          if (children[i].getKind() == kind::OR && children[i] != L)
          {
            std::vector<Node> clauses;
            clauses.push_back(d_cl);
            clauses.insert(
                clauses.end(), children[i].begin(), children[i].end());
            Node conclusion = d_nm->mkNode(kind::SEXPR, clauses);
            success &= addVeritStep(
                conclusion, VeritRule::OR, {children[i]}, {}, *cdp);
            new_children[i] = conclusion;
            current_resolvent.insert(current_resolvent.begin(),
                                     children[i].begin(),
                                     children[i].end());
          }
          else
          {
            current_resolvent.push_back(children[i]);
          }
        }
        else
        {
          if (children[i].getKind() == kind::OR)
          {
            current_resolvent.insert(current_resolvent.end(),
                                     children[i].begin(),
                                     children[i].end());
          }
          else
          {
            current_resolvent.push_back(children[i]);
          }
        }
        current_resolvent.erase(
            std::find(current_resolvent.begin(), current_resolvent.end(), L));
        current_resolvent.erase(std::find(
            current_resolvent.begin(), current_resolvent.end(), L.notNode()));

        if (i < children.size() - 1)
        {
          pivot_id = args[2 * i];
          L = args[2 * i + 1];
        }
      }

      if (res.getKind() == kind::OR && current_resolvent.size() != 1)
      {
        return success &= addVeritStepFromOr(
                   res, VeritRule::RESOLUTION, new_children, {}, *cdp);
      }
      else if (res == d_nm->mkConst(false))
      {
        return success &= addVeritStep(res,
                                       VeritRule::RESOLUTION,
                                       d_nm->mkNode(kind::SEXPR, d_cl),
                                       new_children,
                                       {},
                                       *cdp);
      }
      return success &= addVeritStep(res,
                                     VeritRule::RESOLUTION,
                                     d_nm->mkNode(kind::SEXPR, d_cl, res),
                                     new_children,
                                     {},
                                     *cdp);
    }
    // ======== Factoring
    // Children: (P:C1)
    // Arguments: ()
    // ---------------------
    // Conclusion: C2
    // where
    //  Set representations of C1 and C2 is the same and the number of literals
    //  in C2 is smaller than that of C1
    //
    //  proof rule: duplicated_literals
    //  proof node: C2
    //  proof term: (cl F1 ... Fn)
    //  premises: P
    //  args: ()
    case PfRule::FACTORING:
    {
      if (res.getKind() == kind::OR)
      {
        return addVeritStepFromOr(
            res, VeritRule::DUPLICATED_LITERALS, children, {}, *cdp);
      }
      return addVeritStep(res,
                          VeritRule::DUPLICATED_LITERALS,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Split
    // Children: none
    // Arguments: (F)
    // ---------------------
    // Conclusion: (or F (not F))
    //
    // proof rule: not_not
    // proof node: (VP1:(cl (not (not (not F))) F))
    // proof term: (cl (not (not (not F))) F)
    // premises: ()
    // args: ()
    //
    // proof rule: not_not
    // proof node: (VP2:(cl (not (not (not (not F)))) (not F))
    // proof term: (cl (not (not (not (not F)))) (not F)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (or F (not F))
    // proof term: (cl F (not F))
    // premises: VP1 VP2
    // args: ()
    case PfRule::SPLIT:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, args[0].notNode().notNode().notNode(), args[0]);
      Node vp2 = d_nm->mkNode(kind::SEXPR,
                              d_cl,
                              args[0].notNode().notNode().notNode().notNode(),
                              args[0].notNode());

      return addVeritStep(vp2, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(vp1, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStepFromOr(
                 res, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp);
    }
    // ======== Equality resolution
    // Children: (P1:F1, P2:(= F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    // proof rule: equiv_pos2
    // proof node: (VP1:(cl (not (= F1 F2)) (not F1) (F2)))
    // proof term: (cl (not (= F1 F2)) (not F1) (F2))
    // premises: ()
    // args: ()
    //
    // There is a special case occurring here, if F1 = (or G1 ... Gn) because
    // then P1 will be printed as (cl G1 ... Gn) but needs to be printed as (cl
    // (or G1 ... Gn))
    //
    // Repeat the following two step for i=1 to n:
    //
    // for i=1 to n:
    //
    // proof rule: or_neg
    // proof node: (VP2i:(cl (or G1 ... Gn) (not Gi)))
    // proof term: (cl (or G1 ... Gn) (not Gi))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP3:(cl (or G1 ... Gn)^n))
    // proof term: (cl (or G1 ... Gn)^n)
    // premises: P1 VP21 ... VPn
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (VP4:(cl (or (G1 ... Gn)))
    // proof term: (cl (or G1 ... Gn))
    // premises: VP3
    // args: ()
    //
    // Set child1 = VP3
    //
    // Otherwise child1 = VP1
    //
    // Then,
    //
    // proof rule: resolution
    // proof node: F2
    // proof term: (cl F2)
    // premises: VP1 P2 P1
    // args: ()
    case PfRule::EQ_RESOLVE:
    {
      // TODO: Tidy up, look for all rules if assumptions have to be ruled out
      bool success = true;
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, children[1].notNode(), children[0].notNode(), res);
      Node child1 = children[0];

      VeritRule child1_rule =
        static_cast<VeritRule>(std::stoul(cdp->getProofFor(child1)->getArguments()[0].toString()));

      if (child1_rule != VeritRule::ASSUME
          && !isSameModEqual(children[0].notNode(), vp1[1])
          && children[0].getKind() == kind::OR)
      {
        std::vector<Node> clauses;
        clauses.push_back(d_cl);  // cl
        clauses.insert(clauses.end(),
                       children[0].begin(),
                       children[0].end());  //(cl G1 ... Gn)

        std::vector<Node> vp2Nodes = {children[0]};
        std::vector<Node> resNodes = {d_cl};
        for (int i = 0; i < children[0].end() - children[0].begin(); i++)
        {
          Node vp2i = d_nm->mkNode(
              kind::SEXPR,
              d_cl,
              children[0],
              children[0][i].notNode());  //(cl (or G1 ... Gn) (not Gi))
          success &= addVeritStep(vp2i, VeritRule::OR_NEG, {}, {}, *cdp);
          vp2Nodes.push_back(vp2i);
          resNodes.push_back(children[0]);
        }
        Node vp3 = d_nm->mkNode(kind::SEXPR, resNodes);
        success &= addVeritStep(vp3, VeritRule::RESOLUTION, vp2Nodes, {}, *cdp);

        Node vp4 = d_nm->mkNode(kind::SEXPR, d_cl, children[0]);
        success &=
            addVeritStep(vp4, VeritRule::DUPLICATED_LITERALS, {vp3}, {}, *cdp);
        child1 = vp4;
      }

      /*if(res.getKind() == kind::OR){
        Node vp5 = d_nm->mkNode(kind::SEXPR,d_cl,res);
        return success
             && addVeritStep(vp1, VeritRule::EQUIV_POS2, {}, {}, *cdp)
             && addVeritStep(vp5,
                             VeritRule::RESOLUTION,
                             {vp1,children[1],child1},
                             {},
                             *cdp)
             && addVeritStepFromOr(res,VeritRule::OR,{vp5},{},*cdp);

      }*/
      return success && addVeritStep(vp1, VeritRule::EQUIV_POS2, {}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::EQ_RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp1, children[1], child1},
                             {},
                             *cdp);
    }
    // ======== Modus ponens
    // Children: (P1:F1, P2:(=> F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    //
    // proof rule: implies
    // proof term: (VP1:(cl (not F1) F2))
    // proof term: (cl (not F1) F2)
    // premises: P2
    // args: ()
    //
    // proof rule: resolution
    // proof node: F2
    // proof term: (cl F2)
    // premises: VP1 P1
    // args: ()
    case PfRule::MODUS_PONENS:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addVeritStep(vp1, VeritRule::IMPLIES, {children[1]}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
           {vp1,children[0]},
                             {},
                             *cdp);
    }
    // ======== Double negation elimination
    // Children: (P:(not (not F)))
    // Arguments: none
    // ---------------------
    // Conclusion: (F)
    //
    // proof rule: not_not
    // proof node: (VP1:(cl (not (not (not F))) F))
    // proof term: (cl (not (not (not F))) F)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: F
    // proof term: (cl F)
    // premises: VP1 P
    // args: ()
    case PfRule::NOT_NOT_ELIM:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addVeritStep(vp1, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp1, children[0]},
                             {},
                             *cdp);
    }
    // ======== Contradiction
    // Children: (P1:F P2:(not F))
    // Arguments: ()
    // ---------------------
    // Conclusion: false
    //
    // proof rule: resolution
    // proof node: false
    // proof term: (cl)
    // premises: P1 P2
    // args: ()
    case PfRule::CONTRA:
    {
      return addVeritStep(res, VeritRule::RESOLUTION, d_nm->mkNode(kind::SEXPR,d_cl), children, {}, *cdp);
    }
    // ======== And elimination
    // Children: (P:(and F1 ... Fn))
    // Arguments: (i)
    // ---------------------
    // Conclusion: (Fi)
    //
    // proof rule: and
    // proof node: (VP:Fi)
    // proof term: (cl Fi)
    // premises: P
    // args: ()
    case PfRule::AND_ELIM:
    {
      return addVeritStep(res,
                          VeritRule::AND,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== And introduction
    // Children: (P1:F1 ... Pn:Fn))
    // Arguments: ()
    // ---------------------
    // Conclusion: (and F1 ... Fn)
    //
    // proof rule: and_neg
    // proof node: (VP1:(cl (and F1 ... Fn) (not F1) ... (not Fn)))
    // proof term: (cl (and F1 ... Fn) (not F1) ... (not Fn))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (and F1 ... Fn)
    // proof term: (cl (and F1 ... Fn))
    // premises: VP1 P1 ... Pn
    // args: ()
    case PfRule::AND_INTRO:
    {
      std::vector<Node> neg_Nodes;
      neg_Nodes.push_back(d_cl);
      neg_Nodes.push_back(res);
      for (unsigned long int i = 0; i < children.size(); i++)
      {
        neg_Nodes.push_back(children[i].notNode());
      }
      Node vp1 = d_nm->mkNode(kind::SEXPR, neg_Nodes);

      std::vector<Node> new_children;
      new_children.push_back(vp1);
      new_children.insert(new_children.end(), children.begin(), children.end());

      return addVeritStep(vp1, VeritRule::AND_NEG, {}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             new_children,
                             {},
                             *cdp);
    }
    // ======== Not Or elimination
    // Children: (P:(not (or F1 ... Fn)))
    // Arguments: (i)
    // ---------------------
    // Conclusion: (not Fi)
    //
    // proof rule: not_or
    // proof node: (not Fi)
    // proof term: (cl (not Fi))
    // premises: P
    // args: ()
    case PfRule::NOT_OR_ELIM:
    {
      return addVeritStep(res, VeritRule::NOT_OR, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
    }
    // ======== Implication elimination
    // Children: (P:(=> F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: implies
    // proof node: (or (not F1) F2)
    // proof term: (cl (not F1) F2)
    // premises: P
    // args: ()
    case PfRule::IMPLIES_ELIM:
    {
      return addVeritStepFromOr(res, VeritRule::IMPLIES, children, {}, *cdp);
    }
    // ======== Not Implication elimination version 1
    // Children: (P:(not (=> F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (F1)
    //
    // proof rule: not_implies1
    // proof node: (VP:F1)
    // proof term: (cl F1)
    // premises: P
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM1:
    {
      return addVeritStep(res,
                          VeritRule::NOT_IMPLIES1,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Not Implication elimination version 2
    // Children: (P:(not (=> F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (not F2)
    //
    // proof rule: not_implies2
    // proof node: (not F2)
    // proof term: (cl (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM2:
    {
      return addVeritStep(res, VeritRule::NOT_IMPLIES2, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
    }
    // ======== Equivalence elimination version 1
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: equiv1
    // proof node: (or (not F1) F2)
    // proof term: (cl (not F1) F2)
    // premises: P
    // args: ()
    case PfRule::EQUIV_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV1, children, {}, *cdp);
    }
    // ======== Equivalence elimination version 2
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: equiv2
    // proof node: (or F1 (not F2))
    // proof term: (cl F1 (not F2))
    // premises: P
    // args: ()
    case PfRule::EQUIV_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV2, children, {}, *cdp);
    }
    // ======== Not Equivalence elimination version 1
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // proof rule: not_equiv1
    // proof node: (or F1 F2)
    // proof term: (cl F1 F2)
    // premises: P
    // args: ()
    case PfRule::NOT_EQUIV_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_EQUIV1, children, {}, *cdp);
    }
    // ======== Not Equivalence elimination version 2
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) (not F2))
    //
    // proof rule: not_equiv2
    // proof node: (or (not F1) (not F2))
    // proof term: (cl (not F1) (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_EQUIV_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_EQUIV2, children, {}, *cdp);
    }
    // ======== XOR elimination version 1
    // Children: (P:(xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // proof rule: XOR1
    // proof node: (or F1 F2)
    // proof term: (cl F1 F2)
    // premises: P
    // args: ()
    case PfRule::XOR_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::XOR1, children, {}, *cdp);
    }
    // ======== XOR elimination version 2
    // Children: (P:(not (xor F1 F2))))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: XOR2
    // proof node: (or F1 (not F2))
    // proof term: (cl F1 (not F2))
    // premises: P
    // args: ()
    case PfRule::XOR_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::XOR2, children, {}, *cdp);
    }
    // ======== Not XOR elimination version 1
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: NOT_XOR1
    // proof node: (or F1 (not F2))
    // proof term: (cl F1 (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_XOR_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_XOR1, children, {}, *cdp);
    }
    // ======== Not XOR elimination version 2
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: NOT_XOR1
    // proof node: (or (not F1) F2)
    // proof term: (cl (not F1) F2)
    // premises: P
    // args: ()
    case PfRule::NOT_XOR_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_XOR2, children, {}, *cdp);
    }
    // ======== ITE elimination version 1
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) F1)
    //
    // proof rule: ite2
    // proof node: (or (not C) F1)
    // proof term: (cl (not C) F1)
    // premises: P
    // args: ()
    case PfRule::ITE_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::ITE2, children, {}, *cdp);
    }
    // ======== ITE elimination version 2
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C F2)
    //
    // proof rule: ite1
    // proof node: (or C F2)
    // proof term: (cl C F2)
    // premises: P
    // args: ()
    case PfRule::ITE_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::ITE1, children, {}, *cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) (not F1))
    //
    // proof rule: not_ite2
    // proof node: (or (not C) (not F1))
    // proof term: (cl (not C) (not F1))
    // premises: P
    // args: ()
    case PfRule::NOT_ITE_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_ITE2, children, {}, *cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C (not F2))
    //
    // proof rule: not_ite1
    // proof node: (or C (not F2))
    // proof term: (cl C (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_ITE_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_ITE1, children, {}, *cdp);
    }

    //================================================= De Morgan rules
    // ======== Not And
    // Children: (P:(not (and F1 ... Fn))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) ... (not Fn))
    //
    // proof rule: not_and
    // proof node: (or (not F1) ... (not Fn))
    // proof term: (cl (not F1) ... (not Fn))
    // premises: P
    // args: ()
    case PfRule::NOT_AND:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_AND, children, {}, *cdp);
    }

    //================================================= CNF rules
    // ======== CNF And Pos
    // Children: ()
    // Arguments: ((and F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (not (and F1 ... Fn)) Fi)
    //
    // proof rule: and_pos
    // proof node: (or (not (and F1 ... Fn)) Fi)
    // proof term: (cl (not (and F1 ... Fn)) Fi)
    // premises: ()
    // args: ()
    case PfRule::CNF_AND_POS:
    {
      return addVeritStepFromOr(res, VeritRule::AND_POS, children, {}, *cdp);
    }
    // ======== CNF And Neg
    // Children: ()
    // Arguments: ((and F1 ... Fn))
    // ---------------------
    // Conclusion: (or (and F1 ... Fn) (not F1) ... (not Fn))
    //
    // proof rule: and_neg
    // proof node: (or (and F1 ... Fn) (not F1) ... (not Fn))
    // proof term: (cl (and F1 ... Fn) (not F1) ... (not Fn))
    // premises: ()
    // args: ()
    case PfRule::CNF_AND_NEG:
    {
      return addVeritStepFromOr(res, VeritRule::AND_NEG, children, {}, *cdp);
    }
    // ======== CNF Or Pos
    // Children: ()
    // Arguments: ((or F1 ... Fn))
    // ---------------------
    // Conclusion: (or (not (or F1 ... Fn)) F1 ... Fn)
    //
    // proof rule: or_pos
    // proof node: (or (not (or F1 ... Fn)) F1 ... Fn)
    // proof term: (cl (not (or F1 ... Fn)) F1 ... Fn)
    // premises: ()
    // args: ()
    case PfRule::CNF_OR_POS:
    {
      return addVeritStepFromOr(res, VeritRule::OR_POS, children, {}, *cdp);
    }
    // ======== CNF Or Neg
    // Children: ()
    // Arguments: ((or F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (or F1 ... Fn) (not Fi))
    //
    // proof rule: or_neg
    // proof node: (or (or F1 ... Fn) (not Fi))
    // proof term: (cl (or F1 ... Fn) (not Fi))
    // premises: ()
    // args: ()
    case PfRule::CNF_OR_NEG:
    {
      return addVeritStepFromOr(res, VeritRule::OR_NEG, children, {}, *cdp);
    }
    // ======== CNF Implies Pos
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (not (implies F1 F2)) (not F1) F2)
    //
    // proof rule: implies_pos
    // proof node: (or (not (implies F1 F2)) (not F1) F2)
    // proof term: (cl (not (implies F1 F2)) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_POS:
    {
      return addVeritStepFromOr(
          res, VeritRule::IMPLIES_POS, children, {}, *cdp);
    }
    // ======== CNF Implies Neg version 1
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) F1)
    //
    // proof rule: implies_neg1
    // proof node: (or (implies F1 F2) F1)
    // proof term: (cl (implies F1 F2) F1)
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_NEG1:
    {
      return addVeritStepFromOr(
          res, VeritRule::IMPLIES_NEG1, children, {}, *cdp);
    }
    // ======== CNF Implies Neg version 2
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) (not F2))
    //
    // proof rule: implies_neg2
    // proof node: (or (implies F1 F2) (not F2))
    // proof term: (cl (implies F1 F2) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_NEG2:
    {
      return addVeritStepFromOr(
          res, VeritRule::IMPLIES_NEG2, children, {}, *cdp);
    }
    // ======== CNF Equiv Pos version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) (not F1) F2)
    //
    // proof rule: equiv_pos2
    // proof node: (or (not (= F1 F2)) (not F1) F2)
    // proof term: (cl (not (= F1 F2)) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_POS1:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_POS2, children, {}, *cdp);
    }
    // ======== CNF Equiv Pos version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) F1 (not F2))
    //
    // proof rule: equiv_pos1
    // proof node: (or (not (= F1 F2)) F1 (not F2))
    // proof term: (cl (not (= F1 F2)) F1 (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_POS2:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_POS1, children, {}, *cdp);
    }
    // ======== CNF Equiv Neg version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) F1 F2)
    //
    // proof rule: equiv_neg2
    // proof node: (or (= F1 F2) F1 F2)
    // proof term: (cl (= F1 F2) F1 F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_NEG1:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_NEG2, children, {}, *cdp);
    }
    // ======== CNF Equiv Neg version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) (not F1) (not F2))
    //
    // proof rule: equiv_neg1
    // proof node: (or (= F1 F2) (not F1) (not F2))
    // proof term: (cl (= F1 F2) (not F1) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_NEG2:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_NEG1, children, {}, *cdp);
    }
    // ======== CNF Xor Pos version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) F1 F2)
    //
    // proof rule: xor_pos1
    // proof node: (or (not (xor F1 F2)) F1 F2)
    // proof term: (cl (not (xor F1 F2)) F1 F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_POS1:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_POS1, children, {}, *cdp);
    }
    // ======== CNF Xor Pos version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) (not F1) (not F2))
    //
    // proof rule: xor_pos2
    // proof node: (or (not (xor F1 F2)) (not F1) (not F2))
    // proof term: (cl (not (xor F1 F2)) (not F1) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_POS2:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_POS2, children, {}, *cdp);
    }
    // ======== CNF Xor Neg version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) (not F1) F2)
    //
    // proof rule: xor_neg2
    // proof node: (or (xor F1 F2) (not F1) F2)
    // proof term: (cl (xor F1 F2) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_NEG1:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_NEG2, children, {}, *cdp);
    }
    // ======== CNF Xor Neg version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) F1 (not F2))
    //
    // proof rule: xor_neg1
    // proof node: (or (xor F1 F2) F1 (not F2))
    // proof term: (cl (xor F1 F2) F1 (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_NEG2:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_NEG1, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) (not C) F1)
    //
    // proof rule: ite_pos2
    // proof node: (or (not (ite C F1 F2)) (not C) F1)
    // proof term: (cl (not (ite C F1 F2)) (not C) F1)
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_POS1:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_POS2, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) C F2)
    //
    // proof rule: ite_pos1
    // proof node: (or (not (ite C F1 F2)) C F2)
    // proof term: (cl (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_POS2:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_POS1, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 3
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) F1 F2)
    //
    // proof rule: ite_pos1
    // proof node: (VP1:(cl (not (ite C F1 F2)) C F2))
    // proof term: (cl (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    //
    // proof rule: ite_pos2
    // proof node: (VP2:(cl (not (ite C F1 F2)) (not C) F1))
    // proof term: (cl (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP3:(cl (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2))
    // proof term: (cl (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2)
    // premises: VP1 VP2
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (or (not (ite C F1 F2)) F1 F2)
    // proof term: (cl (not (ite C F1 F2)) F1 F2)
    // premises: VP3
    // args: ()
    case PfRule::CNF_ITE_POS3:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0], res[2]);
      Node vp2 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0].notNode(), res[1]);
      Node vp3 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], res[1], res[0], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_POS1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_POS2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
             && addVeritStepFromOr(
                 res, VeritRule::DUPLICATED_LITERALS, {vp3}, {}, *cdp);
    }
    // ======== CNF ITE Neg version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not C) (not F1))
    //
    // proof rule: ite_neg2
    // proof node: (or (ite C F1 F2) (not C) (not F1))
    // proof term: (cl (ite C F1 F2) (not C) (not F1))
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_NEG1:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_NEG2, children, {}, *cdp);
    }
    // ======== CNF ITE Neg version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) C (not F2))
    //
    // proof rule: ite_neg1
    // proof node: (or (ite C F1 F2) C (not F2))
    // proof term: (cl (ite C F1 F2) C (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_NEG2:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_NEG1, children, {}, *cdp);
    }
    // ======== CNF ITE Neg version 3
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not F1) (not F2))
    //
    // proof rule: ite_neg1
    // proof term: (VP1:(cl (ite C F1 F2) C (not F2)))
    // premises: ()
    // args: ()
    //
    // proof rule: ite_neg2
    // proof term: (VP2:(cl (ite C F1 F2) (not C) (not F1)))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof term: (VP3:(cl (ite C F1 F2) (not F2) (ite C F1 F2) (not F1)))
    // premises: VP1 VP2
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof term: (cl (ite C F1 F2) C (not F2))
    // premises: VP3
    // args: ()
    case PfRule::CNF_ITE_NEG3:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0], res[2]);
      Node vp2 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0].notNode(), res[1]);
      Node vp3 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], res[1], res[0], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_NEG1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_NEG2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
             && addVeritStepFromOr(
                 res, VeritRule::DUPLICATED_LITERALS, {vp3}, {}, *cdp);
    }
    //================================================= Equality rules
    // ======== Reflexive
    // Children: none
    // Arguments: (t)
    // ---------------------
    // Conclusion: (= t t)
    //
    // proof rule: refl
    // proof term: (cl (= t t))
    // premises: ()
    // args: ()
    case PfRule::REFL:
    {
      return addVeritStep(res, VeritRule::REFL, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
    }
    // ======== Transitivity
    // Children: (P1:(= t1 t2), ..., Pn:(= t{n-1} tn))
    // Arguments: none
    // -----------------------
    // Conclusion: (= t1 tn)
    //
    // proof rule: trans
    // proof node: (= t1 tn)
    // proof term: (cl (= t1 tn))
    // premises: P1, ..., Pn
    // args: ()
    case PfRule::TRANS:
    {
      return addVeritStep(res, VeritRule::TRANS, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
    }
    // ======== Congruence
    // Children: (P1:(= t1 s1), ..., Pn:(= tn sn))
    // Arguments: (<kind> f?)
    // ---------------------------------------------
    // Conclusion: (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn))
    // Notice that f must be provided iff <kind> is a parameterized kind, e.g.
    // APPLY_UF. The actual node for <kind> is constructible via
    // ProofRuleChecker::mkKindNode.
    //
    // proof rule: cong
    // proof node: (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn))
    // proof term: (cl (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn)))
    // premises: P1, ..., Pn
    // args: ()
    case PfRule::CONG:
    {
      return addVeritStep(res, VeritRule::CONG, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
    }
    // ======== True intro
    // Children: (P:F)
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= F true)
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F true) F)))
    // proof term: (cl (= (= F true) F))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv2
    // proof node: (VP2:(cl (= F true) (not F)))
    // proof term: (cl (= F true) (not F))
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: (= F true)
    // proof term: (cl (= F true))
    // premises: VP2 P
    // args: ()
    case PfRule::TRUE_INTRO:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, res, children[0]));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    // ======== True elim
    // Children: (P:(= F true))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: F
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F true) F)))
    // proof term: (cl (= (= F true) F))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof node: (VP2:(cl (not (= F true)) F))
    // proof term: (cl (not (= F true)) F)
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: (F)
    // proof term: (cl F)
    // premises: VP2
    // args: ()
    //
    case PfRule::TRUE_ELIM:
    {
      bool success = true;
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, children[0], res));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      success &= addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
                 && addVeritStep(vp2, VeritRule::EQUIV1, {vp1}, {}, *cdp);
      return success
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    // ======== False intro
    // Children: (P:(not F))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= F false)
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F false) (not F))))
    // proof term: (cl (= (= F false) (not F)))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv2
    // proof node: (VP2:(cl (= F false) (not (not F))))
    // proof term: (cl (= F false) (not (not F)))
    // premises: VP1
    // args: ()
    //
    // proof rule: not_not
    // proof node: (VP3:(cl (not (not (not F))) F))
    // proof term: (cl (not (not (not F))) F)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP4:(cl (= F false) F))
    // proof term: (cl (= F false) F)
    // premises: VP2 VP3
    // args: ()
    //
    // proof rule: resolution
    // proof node: (= F false)
    // proof term: (cl (= F false))
    // premises: VP4 P
    // args: ()
    case PfRule::FALSE_INTRO:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, res, children[0]));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      Node vp3 = d_nm->mkNode(
          kind::SEXPR, d_cl, children[0].notNode().notNode(), children[0][0]);
      Node vp4 = d_nm->mkNode(kind::SEXPR, d_cl, res, children[0][0]);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(vp4, VeritRule::RESOLUTION, {vp2, vp3}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp4, children[0]},
                             {},
                             *cdp);
    }
    // ======== False elim
    // Children: (P:(= F false))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (not F)
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F false) (not F))))
    // proof term: (cl (= (= F false) (not F)))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof node: (VP2:(cl (not (= F false)) (not F)))
    // proof term: (cl (not (= F false)) (not F))
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: (not F)
    // proof term: (cl (not F))
    // premises: VP2 P
    // args: ()
    case PfRule::FALSE_ELIM:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, children[0], res));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV1, {vp1}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    //================================================= Quantifiers rules
    // ======== Witness intro
    // Children: (P:(exists ((x T)) F[x]))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= k (witness ((x T)) F[x]))
    // where k is the Skolem form of (witness ((x T)) F[x]).
    /*case PfRule::WITNESS_INTRO:
    {
      return false;
    }*/
    // ======== Exists intro
    // Children: (P:F[t])
    // Arguments: ((exists ((x T)) F[x]))
    // ----------------------------------------
    // Conclusion: (exists ((x T)) F[x])
    // This rule verifies that F[x] indeed matches F[t] with a substitution
    // over x.
    /*case PfRule::EXISTS_INTRO:
    {
      return false;
    }*/
    // ======== Skolemize
    // Children: (P:(exists ((x1 T1) ... (xn Tn)) F))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: F*sigma
    // sigma maps x1 ... xn to their representative skolems obtained by
    // SkolemManager::mkSkolemize, returned in the skolems argument of that
    // method. Alternatively, can use negated forall as a premise.
    /*case PfRule::SKOLEMIZE:
    {
    }*/
    // ======== Instantiate
    // Children: (P:(forall ((x1 T1) ... (xn Tn)) F))
    // Arguments: (t1 ... tn)
    // ----------------------------------------
    // Conclusion: F*sigma
    // sigma maps x1 ... xn to t1 ... tn.
    //
    // proof rule: forall_inst
    // proof node: (VP1:(cl (or (not (forall ((x1 T1) ... (xn Tn)) F))
    // F*sigma)))
    // proof term: (cl (or (not (forall ((x1 T1) ... (xn Tn)) F))
    // F*sigma))
    // premises: ()
    // args: (= x1 t1) ... (= xn tn)
    //
    // proof rule: or
    // proof node: (VP2:(cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma))
    // proof term: (cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma)
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: F*sigma
    // proof term: (cl F*sigma)
    // premises: VP2 P
    // args: ()
    case PfRule::INSTANTIATE:
    {
      for (unsigned long int i = 0; i < args.size(); i++)
      {
        new_args.push_back(
            d_nm->mkNode(kind::EQUAL, children[0][0][i], args[i]));
      }
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::OR, children[0].notNode(), res));
      bool success =
          addVeritStep(vp1, VeritRule::FORALL_INST, {}, new_args, *cdp);
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      success &= addVeritStep(vp2, VeritRule::OR, {vp1}, {}, *cdp);
      return success
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    //================================================= Arithmetic rules
  // ======== Adding Inequalities
  // Note: an ArithLiteral is a term of the form (>< poly const)
  // where
  //   >< is >=, >, ==, <, <=, or not(== ...).
  //   poly is a polynomial
  //   const is a rational constant

    // Children: (P1:l1, ..., Pn:ln)
    //           where each li is an ArithLiteral
    //           not(= ...) is dis-allowed!
    //
    // Arguments: (k1, ..., kn), non-zero reals
    // ---------------------
    // Conclusion: (>< (* k t1) (* k t2))
    //    where >< is the fusion of the combination of the ><i, (flipping each
    //    it its ki is negative). >< is always one of <, <= NB: this implies
    //    that lower bounds must have negative ki,
    //                      and upper bounds must have positive ki.
    //    t1 is the sum of the polynomials.
    //    t2 is the sum of the constants.
    // case PfRule::ARITH_SCALE_SUM_UPPER_BOUNDS:{
    //
    //}
    // ======== Tightening Strict Integer Upper Bounds
    // Children: (P:(< i c))
    //         where i has integer type.
    // Arguments: none
    // ---------------------
    // Conclusion: (<= i greatestIntLessThan(c)})
    // INT_TIGHT_UB,
    // ======== Tightening Strict Integer Lower Bounds
    // Children: (P:(> i c))
    //         where i has integer type.
    // Arguments: none
    // ---------------------
    // Conclusion: (>= i leastIntGreaterThan(c)})
    // INT_TIGHT_LB,
    // ======== Trichotomy of the reals
    // Children: (A B)
    // Arguments: (C)
    // ---------------------
    // Conclusion: (C),
    //                 where (not A) (not B) and C
    //                   are (> x c) (< x c) and (= x c)
    //                   in some order
    //                 note that "not" here denotes arithmetic negation,
    //                 flipping
    //                 >= to <, etc.
    //
    // If C = (= x c) or C = (> x c) pre-processing has to transform (>= x c)
    // into (<= c x)
    //
    // proof rule: la_disequality
    // proof node: (VP1: (or (= x c) (not (<= x c)) (not (<= c x))))
    // proof term: (cl (or (= x c) (not (<= x c)) (not (<= c x))))
    // premises: ()
    // args: ()
    //
    // proof rule: or
    // proof node: (VP2: (cl (= x c) (not (<= x c)) (not (<= c x))))
    // proof term: (cl (= x c) (not (<= x c)) (not (<= c x)))
    // premises: ()
    // args: ()
    //
    // If C = (> x c) or C = (< x c) post-processing has to be added. In these
    // cases resolution on VP2 A B yields (not (<=x c)) or (not (<= c x)) and
    // comp_simplify is used to transform it into C. Otherwise,
    //
    // proof rule: resolution
    // proof node: C
    // proof term: (cl C)
    // premises: VP2 A B
    // args: ()
    //
    // TODO:
    // isabelle-mirabelle/Green_cvc42/x2020_07_31_11_27_36_291_7704406.smt_in
    /*case PfRule::ARITH_TRICHOTOMY:{
      bool success = true;
      Node equal;
      Node lesser;
      Node greater;

      if(res.getKind() == kind::EQUAL){equal = res;}
      else if(children[0].getKind() == kind::NOT){equal = children[0];}
      else if(children[1].getKind() == kind::NOT){equal = children[1];}

      if(res.getKind() == kind::GT){greater = res;}
      else if(children[0].getKind() == kind::LEQ){greater = children[0];}
      else if(children[1].getKind() == kind::LEQ){greater = children[1];}

      if(res.getKind() == kind::LT){lesser = res;}
      else if(children[0].getKind() == kind::GEQ){lesser = children[0];}
      else if(children[1].getKind() == kind::GEQ){lesser = children[1];}

      Node x = equal[0][0];
      Node c = equal[0][1];
      Node vp_child1 = children[0];
      Node vp_child2 = children[1];

      //Preprocessing
      if(res == equal || res == greater){ // C = (= x c) or C = (> x c)
        // lesser = (>= x c)
        Node vpc2 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::EQUAL,d_nm->mkNode(kind::GEQ,x,c),d_nm->mkNode(kind::LEQ,c,x)));
    // (cl (= (>= x c) (<= c x))) Node vpc1 =
    d_nm->mkNode(kind::SEXPR,d_cl,vpc2[1].notNode(),d_nm->mkNode(kind::GEQ,x,c).notNode(),d_nm->mkNode(kind::LEQ,c,x));
    // (cl (not(= (>= x c) (<= c x))) (not (>= x c)) (<= c x)) vp_child1 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::LEQ,c,x)); // (cl (<= c x))

        success &= addVeritStep(vpc1,VeritRule::EQUIV_POS2,{},{},*cdp)
                && addVeritStep(vpc2,VeritRule::COMP_SIMPLIFY,{},{},*cdp)
                &&
    addVeritStep(vp_child1,VeritRule::RESOLUTION,{vpc1,vpc2,lesser},{},*cdp);
        // greater = (<= x c) or greater = (not (= x c)) -> no preprocessing
    necessary if(res == equal){vp_child2 = greater;} else{vp_child2 = equal;}
      }

      //Process
      Node vp1 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::OR,d_nm->mkNode(kind::EQUAL,x,c),d_nm->mkNode(kind::LEQ,x,c).notNode(),d_nm->mkNode(kind::LEQ,c,x).notNode()));
    // (cl (or (= x c) (not (<= x c)) (not (<= c x)))) Node vp2 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::EQUAL,x,c),d_nm->mkNode(kind::LEQ,x,c).notNode(),d_nm->mkNode(kind::LEQ,c,x).notNode());
    // (cl (= x c) (not (<= x c)) (not (<= c x))) success &=
    addVeritStep(vp1,VeritRule::LA_DISEQUALITY,{},{},*cdp)
              && addVeritStep(vp2,VeritRule::OR,{vp1},{},*cdp);

      //Postprocessing
      if (res == equal){ //no postprocessing necessary
        return success &&
    addVeritStep(res,VeritRule::RESOLUTION,d_nm->mkNode(kind::SEXPR,d_cl,res),{vp2,vp_child1,vp_child2},{},*cdp);
      }
      else if(res == greater){ //have (not (<= x c)) but result should be (> x
    c) Node vp3 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::LEQ,x,c).notNode()); // (cl
    (not (<= x c))) Node vp4 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::EQUAL,d_nm->mkNode(kind::GT,x,c),d_nm->mkNode(kind::LEQ,x,c).notNode()).notNode(),d_nm->mkNode(kind::GT,x,c),d_nm->mkNode(kind::LEQ,x,c).notNode().notNode());
    // (cl (not(= (> x c) (not (<= x c)))) (> x c) (not (not (<= x c)))) Node
    vp5 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::EQUAL,d_nm->mkNode(kind::GT,x,c),d_nm->mkNode(kind::LEQ,x,c).notNode()));
    // (cl (= (> x c) (not (<= x c))))

        return success
                &&
    addVeritStep(vp3,VeritRule::RESOLUTION,{vp2,vp_child1,vp_child2},{},*cdp)
                && addVeritStep(vp4,VeritRule::EQUIV_POS1,{},{},*cdp)
                && addVeritStep(vp5,VeritRule::COMP_SIMPLIFY,{},{},*cdp)
                &&
    addVeritStep(res,VeritRule::RESOLUTION,d_nm->mkNode(kind::SEXPR,d_cl,res),{vp3,vp4,vp5},{},*cdp);
      }
      else{ //have (not (<= c x)) but result should be (< x c)
        Node vp3 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::LEQ,c,x).notNode()); // (cl
    (not (<= c x))) Node vp4 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::EQUAL,d_nm->mkNode(kind::LT,x,c),d_nm->mkNode(kind::LEQ,c,x).notNode()).notNode(),d_nm->mkNode(kind::LT,x,c),d_nm->mkNode(kind::LEQ,c,x).notNode().notNode());
    // (cl (not(= (< x c) (not (<= c x)))) (< x c) (not (not (<= c x)))) Node
    vp5 =
    d_nm->mkNode(kind::SEXPR,d_cl,d_nm->mkNode(kind::EQUAL,d_nm->mkNode(kind::LT,x,c),d_nm->mkNode(kind::LEQ,c,x).notNode()));
    // (cl (= (< x c) (not (<= c x))))

        return success
                &&
    addVeritStep(vp3,VeritRule::RESOLUTION,{vp2,vp_child1,vp_child2},{},*cdp)
                && addVeritStep(vp4,VeritRule::EQUIV_POS1,{},{},*cdp)
                && addVeritStep(vp5,VeritRule::COMP_SIMPLIFY,{},{},*cdp)
                &&
    addVeritStep(res,VeritRule::RESOLUTION,d_nm->mkNode(kind::SEXPR,d_cl,res),{vp3,vp4,vp5},{},*cdp);
      }

    }*/
    // ======== Arithmetic operator elimination
    // Children: none
    // Arguments: (t)
    // ---------------------
    // Conclusion: arith::OperatorElim::getAxiomFor(t)
    // ARITH_OP_ELIM_AXIOM,
    // ======== Int Trust
    // Children: (P1 ... Pn)
    // Arguments: (Q)
    // ---------------------
    // Conclusion: (Q)
    // INT_TRUST,
    //======== Multiplication sign inference
    // Children: none
    // Arguments: (f1, ..., fk, m)
    // ---------------------
    // Conclusion: (=> (and f1 ... fk) (~ m 0))
    // Where f1, ..., fk are variables compared to zero (less, greater or not
    // equal), m is a monomial from these variables, and ~ is the comparison
    // (less or greater) that results from the signs of the variables. All
    // variables with even exponent in m should be given as not equal to zero
    // while all variables with odd exponent in m should be given as less or
    // greater than zero.
    // ARITH_MULT_SIGN,
    //======== Multiplication with positive factor
    // Children: none
    // Arguments: (m, orig, lhs, rel, rhs)
    // ---------------------
    // Conclusion: (=> (and (> m 0) (rel lhs rhs)) (rel (* m lhs) (* m rhs)))
    // Where orig is the origin that implies (rel lhs rhs) and rel is a relation
    // symbol.
    // ARITH_MULT_POS,
    //======== Multiplication with negative factor
    // Children: none
    // Arguments: (m, orig, (rel lhs rhs))
    // ---------------------
    // Conclusion: (=> (and (< m 0) (rel lhs rhs)) (rel_inv (* m lhs) (* m
    // rhs))) Where orig is the origin that implies (rel lhs rhs) and rel is a
    // relation symbol and rel_inv the inverted relation symbol.
    // ARITH_MULT_NEG,
    //======== Multiplication tangent plane
    // Children: none
    // Arguments: (t, x, y, a, b, sgn)
    // ---------------------
    // Conclusion:
    //   sgn=-1: (= (<= t tplane) (or (and (<= x a) (>= y b)) (and (>= x a) (<=
    //   y b))) sgn= 1: (= (>= t tplane) (or (and (<= x a) (<= y b)) (and (>= x
    //   a)
    //   (>= y b)))
    // Where x,y are real terms (variables or extended terms), t = (* x y)
    // (possibly under rewriting), a,b are real constants, and sgn is either -1
    // or 1. tplane is the tangent plane of x*y at (a,b): b*x + a*y - a*b
    // ARITH_MULT_TANGENT,

    default://TBD
    {
      if(!d_extended){
        std::cout << "Not implemented yet " << id << std::endl;
        return addVeritStep(res, VeritRule::UNDEFINED, d_nm->mkNode(kind::SEXPR,d_cl,res),children, args, *cdp);
      }
    }
  }

  if(!d_extended){
    return false;
  }

  //Extended rules
  switch (id)
  {
    // ======== Symmetric
    // Children: (P:(= t1 t2)) or (P:(not (= t1 t2)))
    // Arguments: none
    // -----------------------
    // Conclusion: (= t2 t1) or (not (= t2 t1))
    //
    //
    // proof rule: symm
    // proof node: (= t2 t1) or (not (= t2 t1))
    // proof term: (cl (= t2 t1)) or (cl (not (= t2 t1)))
    // premises: ((P:(= t1 t2)) or (P:(not (= t1 t2))
    // args: ()
    case PfRule::SYMM:
    {
      return addVeritStep(res,
                          VeritRule::SYMM,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);

    }
    // ======== Reordering
    // Children: (P:C1)
    // Arguments: (C2)
    // ---------------------
    // Conclusion: C2
    // where
    //  Set representations of C1 and C2 is the same but the number of literals
    //  in C2 is the same of that of C1
    //
    //
    // Let C2 = (or F1 ... Fn)
    //
    // proof rule: reordering
    // proof node: C2
    // proof term: (cl F1 ... Fn)
    // premises: P
    // args: ()
    case PfRule::REORDERING:
    {
      return addVeritStepFromOr(res, VeritRule::REORDER, children, {}, *cdp);
    }
    default://TBD
    {
      std::cout << "Not implemented yet " << id << std::endl;
      return addVeritStep(res, VeritRule::UNDEFINED, d_nm->mkNode(kind::SEXPR,d_cl,res),children, args, *cdp);
    }
  }

  Trace("verit-proof") << "... error translating rule "
                       << id << " / "
                       << res << " "
                       << children << " " << args << std::endl;
  return false;
}

VeritProofPostprocessFinalCallback::VeritProofPostprocessFinalCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
{
  d_nm = NodeManager::currentNM();
  d_cl = d_nm->mkBoundVar("cl",d_nm->stringType());
}

bool VeritProofPostprocessFinalCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                 bool& continueUpdate)
{
  if((pn->getArguments()[2].end()-pn->getArguments()[2].begin()) > 1){
    if (pn->getArguments()[2][1].toString() == d_nm->mkConst(false).toString()){
      return true;
    }
  }
  return false;
}

bool VeritProofPostprocessFinalCallback::update(
    Node res,
    PfRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp,
    bool& continueUpdate)
{
  bool success = true;
  d_nm = NodeManager::currentNM();
  Node falseNotNode = d_nm->mkConst(false).notNode();

  Node res2 = d_nm->mkNode(kind::SEXPR, d_cl);
  Node res3 = d_nm->mkNode(kind::SEXPR, res);
  std::vector<Node> new_args = std::vector<Node>();
  VeritRule vrule =
        static_cast<VeritRule>(std::stoul(args[0].toString()));
  new_args.push_back(d_nm->mkConst<Rational>(static_cast<unsigned>(vrule)));
  new_args.push_back(d_nm->mkNode(kind::SEXPR, res));  //(false)
  if (vrule == VeritRule::ASSUME)
  {
    new_args.push_back(res);
  }
  else
  {
    new_args.push_back(d_nm->mkNode(kind::SEXPR, d_cl, res));
  }  // (cl false)
  Trace("verit-proof") << "... add veriT step "
                       << d_nm->mkNode(kind::SEXPR, res) << " / "
                       << d_nm->mkNode(kind::SEXPR, d_cl, res) << " "
                       << children << " / {}" << std::endl;
  success &= cdp->addStep(d_nm->mkNode(kind::SEXPR, res),
                          PfRule::VERIT_RULE,
                          children,
                          new_args,
                          true,
                          CDPOverwrite::ALWAYS);

  new_args.clear();
  new_args.push_back(
      d_nm->mkConst<Rational>(static_cast<unsigned>(VeritRule::FALSE)));
  new_args.push_back(falseNotNode);  // (not false)
  new_args.push_back(
      d_nm->mkNode(kind::SEXPR, d_cl, falseNotNode));  // (cl (not false))
  Trace("verit-proof") << "... add veriT step " << falseNotNode << " / "
                       << d_nm->mkNode(kind::SEXPR, d_cl, falseNotNode)
                       << " {} / {}" << std::endl;
  success &= cdp->addStep(falseNotNode,
                          PfRule::VERIT_RULE,
                          {},
                          new_args,
                          true,
                          CDPOverwrite::ALWAYS);

  new_args.clear();
  new_args.push_back(
      d_nm->mkConst<Rational>(static_cast<unsigned>(VeritRule::RESOLUTION)));
  new_args.push_back(res);
  new_args.push_back(res2);
  Trace("verit-proof") << "... add veriT step " << res << " / " << res2 << " {"
                       << falseNotNode << ", " << d_nm->mkNode(kind::SEXPR, res)
                       << " / {}" << std::endl;
  success &= cdp->addStep(res,
                          PfRule::VERIT_RULE,
                          {falseNotNode, d_nm->mkNode(kind::SEXPR, res)},
                          new_args,
                          true,
                          CDPOverwrite::ALWAYS);
  return success;
}

bool VeritProofPostprocessCallback::addVeritStep(
    Node res,
    VeritRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  return addVeritStep(res,rule,res,children,args,cdp);
}

bool VeritProofPostprocessCallback::addVeritStep(
    Node res,
    VeritRule rule,
    Node conclusion,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{  // TODO: use *cdp, unify
  std::vector<Node> new_args = std::vector<Node>();
  new_args.push_back(d_nm->mkConst<Rational>(static_cast<unsigned>(rule)));
  new_args.push_back(res);
  new_args.push_back(conclusion);
  new_args.insert(new_args.end(),args.begin(),args.end());
  Trace("verit-proof") << "... add veriT step " << res << " / "  << conclusion << " " << children << " / " << new_args << std::endl;
  return cdp.addStep(res,PfRule::VERIT_RULE,children,new_args);
}

//Replace a node (or F1 ... Fn) by (cl F1 ... Fn)
bool VeritProofPostprocessCallback::addVeritStepFromOr(
    Node res,
    VeritRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> clauses;
  clauses.push_back(d_cl);
  clauses.insert(clauses.end(),res.begin(),res.end());
  Node conclusion = d_nm->mkNode(kind::SEXPR,clauses);
  return addVeritStep(res,rule,conclusion,children,args,cdp);
}

bool VeritProofPostprocessCallback::isSameModEqual(Node vp1, Node vp2)
{
  if (vp1.getKind() != vp2.getKind())
  {
    return false;
  }
  else if (vp1 == vp2)
  {
    return true;
  }
  else if (vp1.getKind() == kind::EQUAL)
  {
    return (isSameModEqual(vp1[0], vp2[1]) && isSameModEqual(vp1[1], vp2[0]))
           || (isSameModEqual(vp1[0], vp2[0])
               && isSameModEqual(vp1[1], vp2[1]));
  }
  std::vector<Node> vp1s(vp1.begin(), vp1.end());
  std::vector<Node> vp2s(vp2.begin(), vp2.end());
  if (vp1s.size() != vp2s.size())
  {
    return false;
  }
  bool equal = true;
  for (unsigned long int i = 0; i < vp1s.size(); i++)
  {
    equal &= isSameModEqual(vp1s[i], vp2s[i]);
  }
  return equal;
}

MyVeritProofPostprocessCallback::MyVeritProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
{
  NodeManager* nm = NodeManager::currentNM();
  d_cl = nm->mkBoundVar("cl", nm->stringType());
}

bool MyVeritProofPostprocessCallback::shouldUpdate(
    std::shared_ptr<ProofNode> pn, bool& continueUpdate)
{
  if (pn->getRule() == PfRule::VERIT_RULE)
  {
    return false;
  }
  return true;
}

bool MyVeritProofPostprocessCallback::update(Node res,
                                             PfRule id,
                                             const std::vector<Node>& children,
                                             const std::vector<Node>& args,
                                             CDProof* cdp,
                                             bool& continueUpdate)
{
  Trace("verit-proof") << "- veriT post process callback " << res << " " << id
                       << " " << children << " / " << args << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> new_args = std::vector<Node>();

  // Basic rules (non-extended mode)
  switch (id)
  {
    //================================================= Core rules
    //======================== Assume and Scope
    // ======== Assumption (a leaf)
    // Children: none
    // Arguments: (F)
    // --------------
    // Conclusion: F
    //
    // proof rule: assume
    // proof node: (VP:F)
    // proof term: F
    // premises: ()
    // args: ()
    case PfRule::ASSUME:
    {
      return addVeritStep(res, VeritRule::ASSUME, children, {}, *cdp);
    }
    // ======== Scope (a binder for assumptions)
    // Children: (P:F)
    // Arguments: (F1, ..., Fn)
    // --------------
    // Conclusion: (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)) if F is false
    //
    // proof rule: anchor
    // proof node: (VP1:(cl (not F1) ... (not Fn) F))
    // proof term: (cl (not F1) ... (not Fn) F)
    // premises: P
    // args: (F1, ..., Fn)
    //
    // Repeat the following two step for i=1 to n:
    //
    // proof rule: and_pos
    // proof node: (VP2_i:(cl (not (and F1 ... Fn)) Fi))
    // proof term: (cl (not (and F1 ... Fn)) Fi)
    // premises: ()
    // args: ()
    //
    // Let (not (and F1 ... Fn))^i denote the repetition of (not (and F1 ...
    // Fn)) for i times
    //
    // proof rule: resolution
    // proof node: (VP2a:(cl F (not (and F1 ... Fn))^n))
    // proof term: (cl F (not (and F1 ... Fn))^n)
    // premises: VP1, VP2_i for all i in {1..n},
    // args: ()
    //
    // In extended mode add reordering step:
    //
    // proof rule: reorder
    // proof node: (VP2b:(cl (not (and F1 ... Fn))^n F))
    // proof term: (cl (not (and F1 ... Fn))^n F)
    // premises: VP2a
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (VP3:(cl (not (and F1 ... Fn)) F))
    // proof term: (cl (not (and F1 ... Fn)) F)
    // premises: VP2a or VP2b
    // args: ()
    //
    // proof rule: implies_neg1
    // proof node: (VP4:(cl (=> (and F1 ... Fn) F) (and F1 ... Fn)))
    // proof term: (cl (=> (and F1 ... Fn) F) (and F1 ... Fn))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP5:(cl (=> (and F1 ... Fn) F) F))
    // proof term: (cl (=> (and F1 ... Fn) F) F)
    // premises: VP4 VP3
    // args: ()
    //
    // proof rule: implies_neg2
    // proof node: (VP6:(cl (=> (and F1 ... Fn) F) (not F)))
    // proof term: (cl (=> (and F1 ... Fn) F) (not F))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP7:(cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F)))
    // proof term: (cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F))
    // premises: VP5 VP6
    // args: ()
    //
    // If F = false:
    //
    // proof rule: duplicated_literals
    // proof node: (VP8:(cl (=> (and F1 ... Fn) F)))
    // proof term: (cl (=> (and F1 ... Fn) F))
    // premises: VP7
    // args: ()
    //
    // proof rule: implies_simplify
    // proof node:
    //   (VP9:(cl (= (=> (and F1 ... Fn) false) (not (and F1 ...Fn)))))
    // proof term:
    //   (cl (= (=> (and F1 ... Fn) false) (not (and F1 ... Fn))))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof node:
    //   (VP10:(cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn))))
    // proof term:
    //   (cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn)))
    // premises: VP9
    // args: ()
    //
    // proof rule: resolution
    // proof node: (or (not (and F1 ... Fn)))
    // proof term: (cl (not (and F1 ... Fn)))
    // premises: VP8 VP10
    // args: ()
    //
    // Otherwise:
    //
    // proof rule: duplicated_literals
    // proof node: (or (=> (and F1 ... Fn) F))
    // proof term: (cl (=> (and F1 ... Fn) F))
    // premises: VP7
    // args: ()
    case PfRule::SCOPE:
    {
      bool success = true;

      // Build vp1
      std::vector<Node> negNode;
      for (Node arg : args)
      {
        negNode.push_back(arg.notNode());  // (not F1) ... (not Fn)
      }
      negNode.push_back(children[0]);         // (not F1) ... (not Fn) F
      negNode.insert(negNode.begin(), d_cl);  // (cl (not F1) ... (not F) F)
      Node vp1 = nm->mkNode(kind::SEXPR, negNode);
      success &=
          addVeritStep(vp1, VeritRule::ANCHOR_SUBPROOF, children, args, *cdp);

      // Build vp2i
      Node andNode;
      if (args.size() != 1)
      {
        andNode = nm->mkNode(kind::AND, args);  // (and F1 ... Fn)
      }
      else
      {
        andNode = args[0];  // F1
      }
      std::vector<Node> premisesVP2 = {vp1};
      std::vector<Node> notAnd = {d_cl, children[0]};  // cl F
      Node vp2_i;
      for (long unsigned int i = 0; i < args.size(); i++)
      {
        vp2_i = nm->mkNode(kind::SEXPR,
                           d_cl,
                           andNode.notNode(),
                           args[i]);  // (cl (not (and F1 ... Fn)) Fi)
        success &= addVeritStep(vp2_i, VeritRule::AND_POS, {}, {}, *cdp);
        premisesVP2.push_back(vp2_i);
        notAnd.push_back(andNode.notNode());  // cl F (not (and F1 ... Fn))^i
      }

      Node vp2a =
          nm->mkNode(kind::SEXPR, notAnd);  // (cl F (not (and F1 ... Fn))^n)
      success &=
          addVeritStep(vp2a, VeritRule::RESOLUTION, premisesVP2, {}, *cdp);
      Node vp2 = vp2a;
      notAnd.erase(notAnd.begin() + 1);  //(cl (not (and F1 ... Fn))^n F)
      notAnd.push_back(children[0]);     //(cl (not (and F1 ... Fn))^n F)
      Node vp2b = nm->mkNode(kind::SEXPR, notAnd);
      success &= addVeritStep(vp2b, VeritRule::REORDER, {vp2a}, {}, *cdp);
      vp2 = vp2b;

      Node vp3 = nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), children[0]);
      success &=
          addVeritStep(vp3, VeritRule::DUPLICATED_LITERALS, {vp2}, {}, *cdp);

      Node vp8 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::IMPLIES, andNode, children[0]));

      Node vp4 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], andNode);
      success &= addVeritStep(vp4, VeritRule::IMPLIES_NEG1, {}, {}, *cdp);

      Node vp5 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0]);
      success &= addVeritStep(vp5, VeritRule::RESOLUTION, {vp4, vp3}, {}, *cdp);

      Node vp6 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0].notNode());
      success &= addVeritStep(vp6, VeritRule::IMPLIES_NEG2, {}, {}, *cdp);

      Node vp7 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], vp8[1]);
      success &= addVeritStep(vp7, VeritRule::RESOLUTION, {vp5, vp6}, {}, *cdp);

      if (children[0] != nm->mkConst(false))
      {
        success &= addVeritStep(
            res, VeritRule::DUPLICATED_LITERALS, vp8, {vp7}, {}, *cdp);
      }
      else
      {
        success &=
            addVeritStep(vp8, VeritRule::DUPLICATED_LITERALS, {vp7}, {}, *cdp);

        Node vp9 =
            nm->mkNode(kind::SEXPR,
                       d_cl,
                       nm->mkNode(kind::EQUAL, vp8[1], andNode.notNode()));
        success &= addVeritStep(vp9, VeritRule::IMPLIES_SIMPLIFY, {}, {}, *cdp);

        Node vp10 =
            nm->mkNode(kind::SEXPR, d_cl, vp8[1].notNode(), andNode.notNode());
        success &= addVeritStep(vp10, VeritRule::EQUIV1, {vp9}, {}, *cdp);

        success &= addVeritStep(res,
                                VeritRule::RESOLUTION,
                                nm->mkNode(kind::SEXPR, d_cl, res),
                                {vp8, vp10},
                                {},
                                *cdp);
      }

      return success;
    }
    // ======== Theory Rewrite
    // Children: none
    // Arguments: (F, tid, rid)
    // ----------------------------------------
    // Conclusion: F
    // where F is an equality of the form (= t t') where t' is obtained by
    // applying the kind of rewriting given by the method identifier rid, which
    // is one of:
    //  { RW_REWRITE_THEORY_PRE, RW_REWRITE_THEORY_POST, RW_REWRITE_EQ_EXT }
    // Notice that the checker for this rule does not replay the rewrite to
    // ensure correctness, since theory rewriter methods are not static. For
    // example, the quantifiers rewriter involves constructing new bound
    // variables that are not guaranteed to be consistent on each call.
    //
    //
    // The rule is translated according to tid and the outermost connective of
    // t. This is not an exact translation but should work in most cases.
    //
    // E.g. if the F: (= (* 0 d) 0) and tid = THEORY_ARITH, then prod_simplify
    // is correctly guessed as the rule.
    case PfRule::THEORY_REWRITE:
    {
      theory::TheoryId tid =
          static_cast<theory::TheoryId>(std::stoul(args[1].toString()));
      VeritRule vrule = VeritRule::UNDEFINED;
      Node t = res[0];
      // std::cout << "tid " << tid << std::endl;
      // std::cout << "t kind " << t.getKind() << std::endl;
      // std::cout << "(= t t')" << res << std::endl;
      switch (tid)
      {
        case theory::TheoryId::THEORY_BUILTIN:
        {
          switch (t.getKind())
          {
            case kind::ITE:
            {
              vrule = VeritRule::ITE_SIMPLIFY;
              break;
            }
            case kind::EQUAL:
            {  // Test equiv_simplify
              std::cout << "What happens here " << t << std::endl;
              vrule = VeritRule::EQ_SIMPLIFY;
              break;
            }
            case kind::AND:
            {
              vrule = VeritRule::AND_SIMPLIFY;
              break;
            }
            case kind::OR:
            {
              vrule = VeritRule::OR_SIMPLIFY;
              break;
            }
            case kind::NOT:
            {
              vrule = VeritRule::NOT_SIMPLIFY;
              break;
            }
            case kind::IMPLIES:
            {
              vrule = VeritRule::IMPLIES_SIMPLIFY;
              break;
            }
            default:
            {
              std::cout << "tid " << tid << std::endl;
              std::cout << "t kind " << t.getKind() << std::endl;
              std::cout << "(= t t')" << res << std::endl;
              break;
            }
          }
          break;
        }
        case theory::TheoryId::THEORY_BOOL:
        {
          vrule = VeritRule::BOOL_SIMPLIFY;
          break;
        }  // TODO: Should there be a case distinction with kinds here?
        case theory::TheoryId::THEORY_UF:
        {
          switch (t.getKind())
          {
            case kind::EQUAL:
            {  // A lot of these seem to be symmetry rules but not all....
              // std::cout << "What happens here2: " << std::endl;
              //    std::cout << "tid2 " << tid << std::endl;
              // std::cout << "t kind2 " << t.getKind() << std::endl;
              //  std::cout << "(= t t')2 " << res << std::endl;
              vrule = VeritRule::EQUIV_SIMPLIFY;
              break;
            }
            default:
            {
              // std::cout << "t kind 3" << t.getKind() << std::endl;
              // std::cout << "(= t t') 3" << res << std::endl;
            }
          }
          break;
        }
        case theory::TheoryId::THEORY_ARITH:
        {
          switch (t.getKind())
          {
            case kind::DIVISION:
            {
              vrule = VeritRule::DIV_SIMPLIFY;
              break;
            }
            case kind::PRODUCT:
            {  // What is this?
              vrule = VeritRule::PROD_SIMPLIFY;
              break;
            }
            case kind::MINUS:
            {
              vrule = VeritRule::MINUS_SIMPLIFY;
              break;
            }
            case kind::UMINUS:
            {
              vrule = VeritRule::UNARY_MINUS_SIMPLIFY;
              break;
            }
            case kind::PLUS:
            {
              vrule = VeritRule::NOT_SIMPLIFY;
              break;
            }
            case kind::MULT:
            {
              vrule = VeritRule::PROD_SIMPLIFY;
              break;
            }
            case kind::EQUAL:
            {
            }
            case kind::LT:
            {
            }
            case kind::GT:
            {
            }
            case kind::GEQ:
            {
            }
            case kind::LEQ:
            {
              vrule = VeritRule::COMP_SIMPLIFY;
              break;
            }
            case kind::CAST_TO_REAL:
            {
              return addVeritStep(res,
                                  VeritRule::LA_GENERIC,
                                  nm->mkNode(kind::SEXPR, d_cl, res),
                                  children,
                                  {nm->mkConst(Rational(1))},
                                  *cdp);
            }
            default:
            {
              // std::cout << "t kind " << t.getKind() << std::endl;
              // std::cout << "(= t t')" << res << std::endl;
            }
          }
          break;
        }
        case theory::TheoryId::THEORY_BV:
        {
          break;
        }
        case theory::TheoryId::THEORY_FP:
        {
          break;
        }
        case theory::TheoryId::THEORY_ARRAYS:
        {
          break;
        }
        case theory::TheoryId::THEORY_DATATYPES:
        {
          break;
        }
        case theory::TheoryId::THEORY_SEP:
        {
          break;
        }
        case theory::TheoryId::THEORY_SETS:
        {
          break;
        }
        case theory::TheoryId::THEORY_BAGS:
        {
          break;
        }
        case theory::TheoryId::THEORY_STRINGS:
        {
          break;
        }
        case theory::TheoryId::THEORY_QUANTIFIERS:
        {
          vrule = VeritRule::QUANTIFIER_SIMPLIFY;
          break;
        }
        case theory::TheoryId::THEORY_LAST:
        {
          break;
        }
        default:
        {
        };
      }
      return addVeritStep(
          res, vrule, nm->mkNode(kind::SEXPR, d_cl, res), children, {}, *cdp);
    }
    //================================================= Boolean rules
    // ======== Resolution
    // Children:
    //  (P1:C1, P2:C2)
    // Arguments: (id, L)
    // ---------------------
    // Conclusion: C
    // where
    //   - C1 and C2 are nodes viewed as clauses, i.e., either an OR node with
    //     each children viewed as a literal or a node viewed as a literal. Note
    //     that an OR node could also be a literal.
    //   - id is either true or false
    //   - L is the pivot of the resolution, which occurs as is (resp. under a
    //     NOT) in C1 and negatively (as is) in C2 if id = true (id = false).
    //   C is a clause resulting from collecting all the literals in C1, minus
    //   the first occurrence of the pivot or its negation, and C2, minus the
    //   first occurrence of the pivot or its negation, according to the policy
    //   above. If the resulting clause has a single literal, that literal
    //   itself is the result; if it has no literals, then the result is false;
    //   otherwise it's an OR node of the resulting literals.
    //
    //
    // In case that C1 = (or F1 ... Fn) and C2 != (not (or F1 ... Fn)):
    //
    // proof rule: or
    // proof node: (VP1:(cl F1 ... Fn))
    // proof term: (cl F1 ... Fn)
    // premises: P1
    // args: ()
    //
    // Otherwise VP1 = P1
    //
    // In case that C2 = (or F1 ... Fn) and C1 != (not (or F1 ... Fn)):
    //
    // proof rule: or
    // proof node: (VP2:(cl F1 ... Fn))
    // proof term: (cl F1 ... Fn)
    // premises: P2
    // args: ()
    //
    // Otherwise VP2 = P2
    //
    // If C = (or G1 ... Gn) then except if id = true (false) and C1 = L or C2 =
    // not L (C2 = L and C1 = not L):
    //
    // proof rule: resolution
    // proof node: (or G1 ... Gn)
    // proof term: (cl G1 ... Gn)
    // premises: VP1 VP2
    // args: ()
    //
    // Otherwise if C = false
    //
    // proof rule: resolution
    // proof node: C
    // proof term: (cl)
    // premises: VP1 VP2
    // args: ()
    //
    // Otherwise,
    //
    // proof rule: resolution
    // proof node: C
    // proof term: (cl C)
    // premises: VP1 VP2
    // args: ()
    case PfRule::RESOLUTION:
    {
      bool success = true;
      Node vp1 = children[0];
      Node vp2 = children[1];

      std::vector<Node>
          current_resolvent;  // Needed to determine if (cl C) or (cl G1 ... Gn)
                              // should be added in the end.

      VeritRule vp1_rule = static_cast<VeritRule>(
          std::stoul(cdp->getProofFor(vp1)->getArguments()[0].toString()));
      VeritRule vp2_rule = static_cast<VeritRule>(
          std::stoul(cdp->getProofFor(vp2)->getArguments()[0].toString()));

      // TODO: Check if child rule is SYMM, use equal_Nodes

      // If the rule of the child is ASSUME or EQ_RESOLUTION and additional or
      // step might be needed. TODO: REPLACE EQ_RESOLUTION
      if ((vp1_rule == VeritRule::ASSUME
           || vp1_rule == VeritRule::EQ_RESOLUTION))
      {
        if (children[0].getKind() == kind::OR
            && !isSameModEqual(children[0],
                               children[1].notNode()))  // TODO: isSameModeEqual
        {
          success &= addVeritStepFromOr(
              children[0], VeritRule::OR, {children[0]}, {}, *cdp);
          vp1 = nm->mkNode(kind::SEXPR, d_cl, vp1);
          // If this is the case the literals in C1 are added to the
          // current_resolvent.
          current_resolvent.insert(
              current_resolvent.end(), children[0].begin(), children[0].end());
        }
        else
        {
          // Otherwise, the whole clause is added.
          current_resolvent.push_back(children[0]);
        }
      }
      // For all other rules it is easy to determine if the whole clause or the
      // literals in the clause should be added. If the node is an or node add
      // literals otherwise the whole clause.
      else
      {
        if (children[0].getKind() == kind::OR)
        {
          current_resolvent.insert(
              current_resolvent.end(), children[0].begin(), children[0].end());
        }
        else
        {
          current_resolvent.push_back(children[0]);
        }
      }
      // The same is done to the second child.
      if ((vp2_rule == VeritRule::ASSUME
           || vp2_rule == VeritRule::EQ_RESOLUTION))
      {
        if (children[1].getKind() == kind::OR
            && !isSameModEqual(children[1], children[0].notNode()))
        {  // TODO: vp1_rule == PfRule::ASSUME &&
          success &= addVeritStepFromOr(
              children[1], VeritRule::OR, {children[1]}, {}, *cdp);
          vp2 = nm->mkNode(kind::SEXPR, d_cl, vp2);
          current_resolvent.insert(
              current_resolvent.end(), children[1].begin(), children[1].end());
        }
        else
        {
          current_resolvent.push_back(children[1]);
        }
      }
      else
      {
        if (children[1].getKind() == kind::OR)
        {
          current_resolvent.insert(
              current_resolvent.end(), children[1].begin(), children[1].end());
        }
        else
        {
          current_resolvent.push_back(children[1]);
        }
      }

      // The pivot and its negation are deleted from the current_resolvent
      current_resolvent.erase(std::find(
          current_resolvent.begin(), current_resolvent.end(), args[1]));
      current_resolvent.erase(std::find(current_resolvent.begin(),
                                        current_resolvent.end(),
                                        args[1].notNode()));
      // If there is only one elment left C should be printed as (cl C)
      // otherwise as (cl G1 ... Gn)
      if (res.getKind() == kind::OR && current_resolvent.size() != 1)
      {
        return success &= addVeritStepFromOr(res,
                                             VeritRule::RESOLUTION,
                                             {vp1, vp2},
                                             {},
                                             *cdp);  //(cl G1 ... Gn)
      }
      if (res == nm->mkConst(false))
      {
        return success &= addVeritStep(res,
                                       VeritRule::RESOLUTION,
                                       nm->mkNode(kind::SEXPR, d_cl),
                                       {vp1, vp2},
                                       {},
                                       *cdp);
      }
      return success &= addVeritStep(res,
                                     VeritRule::RESOLUTION,
                                     nm->mkNode(kind::SEXPR, d_cl, res),
                                     {vp1, vp2},
                                     {},
                                     *cdp);  //(cl C)
    }
    // ======== N-ary Resolution
    // Children: (P1:C_1, ..., Pm:C_n)
    // Arguments: (id_1, L_1, ..., id_{n-1}, L_{n-1})
    // ---------------------
    // Conclusion: C
    // where
    //   - let C_1 ... C_n be nodes viewed as clauses, as defined above
    //   - let "C_1 <>_{L,id} C_2" represent the resolution of C_1 with C_2 with
    //     pivot L and policy id, as defined above
    //   - let C_1' = C_1 (from P1),
    //   - for each i > 1, let C_i' = C_{i-1}' <>_{L_{i-1}, id_{i-1}} C_i
    //   The result of the chain resolution is C = C_n'
    //
    // If for any Ci, Ci = (or F1 ... Fn) and Ci != L_{i-1} (for C1, C1 != L_1)
    // then:
    //
    // proof rule: or
    // proof node: (VPi:(cl F1 ... Fn))
    // proof term: (cl F1 ... Fn)
    // premises: Pi
    // args: ()
    //
    // Otherwise VPi = Ci
    //
    // proof rule: resolution
    // proof node: C
    // proof term: (cl C)
    // premises:
    // args: ()
    case PfRule::CHAIN_RESOLUTION:
    {
      Node trueNode = nm->mkConst(true);
      Node falseNode = nm->mkConst(false);
      std::vector<Node> newChildren = children;

      // we need to get the children to proof to know if we need to eagerly
      // procces them, which is the case for ASSUME/EQ_RESOLUTION steps whose
      // conclusion (OR t1 ... tn) is used as (cl t1 ... tn) rather than as (cl
      // (OR t1 ... tn)). In such cases we will, we apply the veriT "or" rule as
      // an extra step, which generates the necessary (cl t1 ... tn) from (OR t1
      // ... tn) / (cl (OR t1 ... tn))
      //
      // We populate a set of proof nodes to eagerly process
      Trace("test-verit-debug")
          << "Look for candidates with\n\tchildren:" << children
          << "\n\targs: " << args << "\n";

      std::vector<std::shared_ptr<ProofNode>> childrenPfs;
      // The first child is used as a OR non-singleton clause if it is not equal
      // to its pivot. Since it's the first clause in the resolution it can only
      // be equal to the pivot in the case the polarity is true.
      if (children[0].getKind() == kind::OR
          && (args[0] != trueNode || children[0] != args[1]))
      {
        // get its proof
        std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
        if (childPf->getRule() == PfRule::ASSUME
            || childPf->getRule() == PfRule::EQ_RESOLVE)
        {
          Trace("test-verit-debug")
              << "Add or steps to 0-th child " << children[0] << ": "
              << *childPf.get() << "\n";
          // build "or" conclusion
          std::vector<Node> lits{d_cl};
          lits.insert(lits.end(), children[0].begin(), children[0].end());
          Node conclusion = nm->mkNode(kind::SEXPR, lits);
          addVeritStep(conclusion, VeritRule::OR, {children[0]}, {}, *cdp);
          newChildren[0] = conclusion;
        }
      }
      for (std::size_t i = 1, size = children.size(); i < size; ++i)
      {
        // any OR node that is viewed as a non-singleton clause, i.e., the
        // resolution is not directly with it. The children[i] OR node is used
        // as a singleton clause only in the case in which the (i-1)-th
        // resolution is with false polarity and the pivot is equal to it. We
        // are interested in all the other cases.
        if (children[i].getKind() == kind::OR
            && (args[2 * (i - 1)] != falseNode
                || args[2 * (i - 1) + 1] != children[i]))
        {
          // get its proof
          std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[i]);
          if (childPf->getRule() == PfRule::ASSUME
              || childPf->getRule() == PfRule::EQ_RESOLVE)
          {
            Trace("test-verit-debug")
                << "Add or steps to " << i << "-th child " << children[i]
                << ": " << *childPf.get() << "\n";
            // build "or" conclusion
            std::vector<Node> lits{d_cl};
            lits.insert(lits.end(), children[i].begin(), children[i].end());
            Node conclusion = nm->mkNode(kind::SEXPR, lits);
            addVeritStep(conclusion, VeritRule::OR, {children[0]}, {}, *cdp);
            newChildren[i] = conclusion;
          }
        }
      }
      // now we need to determine what if res, the original chain resolution
      // conclusion, if it's of the form (OR t1 ... tn), corresponds to the
      // clause (cl t1 ... tn) or to (cl (OR t1 ... tn)). The *only* way in
      // which the latter can happen is if res occurs as a child in one of the
      // premises, and is *not* eliminated afterwards. So we search for res as a
      // subterm of some children, which would mark its last insertion into the
      // resolution result. If res does not occur as the pivot to be eliminated
      // in a subsequent premise, then, and only then, it is a singleton clause.
      //
      // If res is not an OR node, then it's necessarily a singleton clause.
      bool isSingletonClause = res.getKind() != kind::OR;
      if (!isSingletonClause)
      {
        size_t i;
        for (i = children.size(); i > 0; --i)
        {
          // only non-singleton clauses may be introducing
          // res, so we only care about non-singleton OR nodes. We check then
          // against the kind and whether the whole OR node occurs as a pivot of
          // the respective resolution
          if (children[i - 1].getKind() != kind::OR)
          {
            continue;
          }
          size_t pivotIndex = 2 * (i - 1);
          if (args[pivotIndex] == children[i - 1]
              || args[pivotIndex].notNode() == children[i - 1])
          {
            continue;
          }
          // if res occurs as a subterm of a non-singleton premise
          if (std::find(children[i - 1].begin(), children[i - 1].end(), res)
              != children[i - 1].end())
          {
            break;
          }
        }
        // now see if any subsequent premise eliminates it
        for (; i < children.size(); ++i)
        {
          bool posFirst = args[(2 * i) - 1] == trueNode;
          Node pivot = args[(2 * i)];
          // To eliminate res, the clause must contain it with opposite
          // polarity. There are three successful cases, according to the pivot
          // and its sign
          //
          // - res is the same as the pivot and posFirst is true, which means
          //   that the clause contains its negation and eliminates it
          //
          // - res is the negation of the pivot and posFirst is false, so the
          //   clause contains the node whose negation is res. Note that this
          //   case may either be res.notNode() == pivot or res ==
          //   pivot.notNode().
          if ((res == pivot && posFirst)
              || (res.notNode() == pivot && !posFirst)
              || (pivot.notNode() == res && !posFirst))
          {
            break;
          }
        }
        // if not eliminated (loop went to the end), then it's a singleton
        // clause
        isSingletonClause = i == children.size();
      }
      if (!isSingletonClause)
      {
        return addVeritStepFromOr(
            res, VeritRule::RESOLUTION, newChildren, {}, *cdp);
      }
      if (res == falseNode)
      {
        return addVeritStep(res,
                            VeritRule::RESOLUTION,
                            nm->mkNode(kind::SEXPR, d_cl),
                            newChildren,
                            {},
                            *cdp);
      }
      return addVeritStep(res,
                          VeritRule::RESOLUTION,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          newChildren,
                          {},
                          *cdp);
    }
    // ======== Factoring
    // Children: (P:C1)
    // Arguments: ()
    // ---------------------
    // Conclusion: C2
    // where
    //  Set representations of C1 and C2 is the same and the number of literals
    //  in C2 is smaller than that of C1
    //
    //  proof rule: duplicated_literals
    //  proof node: C2
    //  proof term: (cl F1 ... Fn)
    //  premises: P
    //  args: ()
    case PfRule::FACTORING:
    {
      if (res.getKind() == kind::OR)
      {
        return addVeritStepFromOr(
            res, VeritRule::DUPLICATED_LITERALS, children, {}, *cdp);
      }
      return addVeritStep(res,
                          VeritRule::DUPLICATED_LITERALS,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Split
    // Children: none
    // Arguments: (F)
    // ---------------------
    // Conclusion: (or F (not F))
    //
    // proof rule: not_not
    // proof node: (VP1:(cl (not (not (not F))) F))
    // proof term: (cl (not (not (not F))) F)
    // premises: ()
    // args: ()
    //
    // proof rule: not_not
    // proof node: (VP2:(cl (not (not (not (not F)))) (not F))
    // proof term: (cl (not (not (not (not F)))) (not F)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (or F (not F))
    // proof term: (cl F (not F))
    // premises: VP1 VP2
    // args: ()
    case PfRule::SPLIT:
    {
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, args[0].notNode().notNode().notNode(), args[0]);
      Node vp2 = nm->mkNode(kind::SEXPR,
                            d_cl,
                            args[0].notNode().notNode().notNode().notNode(),
                            args[0].notNode());

      return addVeritStep(vp2, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(vp1, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStepFromOr(
                 res, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp);
    }
    // ======== Equality resolution
    // Children: (P1:F1, P2:(= F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    // proof rule: equiv_pos2
    // proof node: (VP1:(cl (not (= F1 F2)) (not F1) (F2)))
    // proof term: (cl (not (= F1 F2)) (not F1) (F2))
    // premises: ()
    // args: ()
    //
    // There is a special case occurring here, if F1 = (or G1 ... Gn) because
    // then P1 will be printed as (cl G1 ... Gn) but needs to be printed as (cl
    // (or G1 ... Gn))
    //
    // Repeat the following two step for i=1 to n:
    //
    // for i=1 to n:
    //
    // proof rule: or_neg
    // proof node: (VP2i:(cl (or G1 ... Gn) (not Gi)))
    // proof term: (cl (or G1 ... Gn) (not Gi))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP3:(cl (or G1 ... Gn)^n))
    // proof term: (cl (or G1 ... Gn)^n)
    // premises: P1 VP21 ... VPn
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (VP4:(cl (or (G1 ... Gn)))
    // proof term: (cl (or G1 ... Gn))
    // premises: VP3
    // args: ()
    //
    // Set child1 = VP3
    //
    // Otherwise child1 = VP1
    //
    // Then,
    //
    // proof rule: resolution
    // proof node: F2
    // proof term: (cl F2)
    // premises: VP1 P2 P1
    // args: ()
    case PfRule::EQ_RESOLVE:
    {
      // build the valid clause (cl (not (= F1 F2)) (not F1) F2)
      Node equivPos2Cl = nm->mkNode(
          kind::SEXPR, d_cl, children[1].notNode(), children[0].notNode(), res);
      addVeritStep(equivPos2Cl, VeritRule::EQUIV_POS2, {}, {}, *cdp);
      return addVeritStep(res,
                          VeritRule::RESOLUTION,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          {equivPos2Cl, children[1], children[0]},
                          {},
                          *cdp);
    }
    // ======== Modus ponens
    // Children: (P1:F1, P2:(=> F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    //
    // proof rule: implies
    // proof term: (VP1:(cl (not F1) F2))
    // proof term: (cl (not F1) F2)
    // premises: P2
    // args: ()
    //
    // proof rule: resolution
    // proof node: F2
    // proof term: (cl F2)
    // premises: VP1 P1
    // args: ()
    case PfRule::MODUS_PONENS:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addVeritStep(vp1, VeritRule::IMPLIES, {children[1]}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp1, children[0]},
                             {},
                             *cdp);
    }
    // ======== Double negation elimination
    // Children: (P:(not (not F)))
    // Arguments: none
    // ---------------------
    // Conclusion: (F)
    //
    // proof rule: not_not
    // proof node: (VP1:(cl (not (not (not F))) F))
    // proof term: (cl (not (not (not F))) F)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: F
    // proof term: (cl F)
    // premises: VP1 P
    // args: ()
    case PfRule::NOT_NOT_ELIM:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addVeritStep(vp1, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp1, children[0]},
                             {},
                             *cdp);
    }
    // ======== Contradiction
    // Children: (P1:F P2:(not F))
    // Arguments: ()
    // ---------------------
    // Conclusion: false
    //
    // proof rule: resolution
    // proof node: false
    // proof term: (cl)
    // premises: P1 P2
    // args: ()
    case PfRule::CONTRA:
    {
      return addVeritStep(res,
                          VeritRule::RESOLUTION,
                          nm->mkNode(kind::SEXPR, d_cl),
                          children,
                          {},
                          *cdp);
    }
    // ======== And elimination
    // Children: (P:(and F1 ... Fn))
    // Arguments: (i)
    // ---------------------
    // Conclusion: (Fi)
    //
    // proof rule: and
    // proof node: (VP:Fi)
    // proof term: (cl Fi)
    // premises: P
    // args: ()
    case PfRule::AND_ELIM:
    {
      return addVeritStep(res,
                          VeritRule::AND,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== And introduction
    // Children: (P1:F1 ... Pn:Fn))
    // Arguments: ()
    // ---------------------
    // Conclusion: (and F1 ... Fn)
    //
    // proof rule: and_neg
    // proof node: (VP1:(cl (and F1 ... Fn) (not F1) ... (not Fn)))
    // proof term: (cl (and F1 ... Fn) (not F1) ... (not Fn))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (and F1 ... Fn)
    // proof term: (cl (and F1 ... Fn))
    // premises: VP1 P1 ... Pn
    // args: ()
    case PfRule::AND_INTRO:
    {
      std::vector<Node> neg_Nodes;
      neg_Nodes.push_back(d_cl);
      neg_Nodes.push_back(res);
      for (unsigned long int i = 0; i < children.size(); i++)
      {
        neg_Nodes.push_back(children[i].notNode());
      }
      Node vp1 = nm->mkNode(kind::SEXPR, neg_Nodes);

      std::vector<Node> new_children;
      new_children.push_back(vp1);
      new_children.insert(new_children.end(), children.begin(), children.end());

      return addVeritStep(vp1, VeritRule::AND_NEG, {}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             new_children,
                             {},
                             *cdp);
    }
    // ======== Not Or elimination
    // Children: (P:(not (or F1 ... Fn)))
    // Arguments: (i)
    // ---------------------
    // Conclusion: (not Fi)
    //
    // proof rule: not_or
    // proof node: (not Fi)
    // proof term: (cl (not Fi))
    // premises: P
    // args: ()
    case PfRule::NOT_OR_ELIM:
    {
      return addVeritStep(res,
                          VeritRule::NOT_OR,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Implication elimination
    // Children: (P:(=> F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: implies
    // proof node: (or (not F1) F2)
    // proof term: (cl (not F1) F2)
    // premises: P
    // args: ()
    case PfRule::IMPLIES_ELIM:
    {
      return addVeritStepFromOr(res, VeritRule::IMPLIES, children, {}, *cdp);
    }
    // ======== Not Implication elimination version 1
    // Children: (P:(not (=> F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (F1)
    //
    // proof rule: not_implies1
    // proof node: (VP:F1)
    // proof term: (cl F1)
    // premises: P
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM1:
    {
      return addVeritStep(res,
                          VeritRule::NOT_IMPLIES1,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Not Implication elimination version 2
    // Children: (P:(not (=> F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (not F2)
    //
    // proof rule: not_implies2
    // proof node: (not F2)
    // proof term: (cl (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM2:
    {
      return addVeritStep(res,
                          VeritRule::NOT_IMPLIES2,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Equivalence elimination version 1
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: equiv1
    // proof node: (or (not F1) F2)
    // proof term: (cl (not F1) F2)
    // premises: P
    // args: ()
    case PfRule::EQUIV_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV1, children, {}, *cdp);
    }
    // ======== Equivalence elimination version 2
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: equiv2
    // proof node: (or F1 (not F2))
    // proof term: (cl F1 (not F2))
    // premises: P
    // args: ()
    case PfRule::EQUIV_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV2, children, {}, *cdp);
    }
    // ======== Not Equivalence elimination version 1
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // proof rule: not_equiv1
    // proof node: (or F1 F2)
    // proof term: (cl F1 F2)
    // premises: P
    // args: ()
    case PfRule::NOT_EQUIV_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_EQUIV1, children, {}, *cdp);
    }
    // ======== Not Equivalence elimination version 2
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) (not F2))
    //
    // proof rule: not_equiv2
    // proof node: (or (not F1) (not F2))
    // proof term: (cl (not F1) (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_EQUIV_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_EQUIV2, children, {}, *cdp);
    }
    // ======== XOR elimination version 1
    // Children: (P:(xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // proof rule: XOR1
    // proof node: (or F1 F2)
    // proof term: (cl F1 F2)
    // premises: P
    // args: ()
    case PfRule::XOR_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::XOR1, children, {}, *cdp);
    }
    // ======== XOR elimination version 2
    // Children: (P:(not (xor F1 F2))))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: XOR2
    // proof node: (or F1 (not F2))
    // proof term: (cl F1 (not F2))
    // premises: P
    // args: ()
    case PfRule::XOR_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::XOR2, children, {}, *cdp);
    }
    // ======== Not XOR elimination version 1
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: NOT_XOR1
    // proof node: (or F1 (not F2))
    // proof term: (cl F1 (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_XOR_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_XOR1, children, {}, *cdp);
    }
    // ======== Not XOR elimination version 2
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: NOT_XOR1
    // proof node: (or (not F1) F2)
    // proof term: (cl (not F1) F2)
    // premises: P
    // args: ()
    case PfRule::NOT_XOR_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_XOR2, children, {}, *cdp);
    }
    // ======== ITE elimination version 1
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) F1)
    //
    // proof rule: ite2
    // proof node: (or (not C) F1)
    // proof term: (cl (not C) F1)
    // premises: P
    // args: ()
    case PfRule::ITE_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::ITE2, children, {}, *cdp);
    }
    // ======== ITE elimination version 2
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C F2)
    //
    // proof rule: ite1
    // proof node: (or C F2)
    // proof term: (cl C F2)
    // premises: P
    // args: ()
    case PfRule::ITE_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::ITE1, children, {}, *cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) (not F1))
    //
    // proof rule: not_ite2
    // proof node: (or (not C) (not F1))
    // proof term: (cl (not C) (not F1))
    // premises: P
    // args: ()
    case PfRule::NOT_ITE_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_ITE2, children, {}, *cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C (not F2))
    //
    // proof rule: not_ite1
    // proof node: (or C (not F2))
    // proof term: (cl C (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_ITE_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_ITE1, children, {}, *cdp);
    }

    //================================================= De Morgan rules
    // ======== Not And
    // Children: (P:(not (and F1 ... Fn))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) ... (not Fn))
    //
    // proof rule: not_and
    // proof node: (or (not F1) ... (not Fn))
    // proof term: (cl (not F1) ... (not Fn))
    // premises: P
    // args: ()
    case PfRule::NOT_AND:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_AND, children, {}, *cdp);
    }

    //================================================= CNF rules
    // ======== CNF And Pos
    // Children: ()
    // Arguments: ((and F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (not (and F1 ... Fn)) Fi)
    //
    // proof rule: and_pos
    // proof node: (or (not (and F1 ... Fn)) Fi)
    // proof term: (cl (not (and F1 ... Fn)) Fi)
    // premises: ()
    // args: ()
    case PfRule::CNF_AND_POS:
    {
      return addVeritStepFromOr(res, VeritRule::AND_POS, children, {}, *cdp);
    }
    // ======== CNF And Neg
    // Children: ()
    // Arguments: ((and F1 ... Fn))
    // ---------------------
    // Conclusion: (or (and F1 ... Fn) (not F1) ... (not Fn))
    //
    // proof rule: and_neg
    // proof node: (or (and F1 ... Fn) (not F1) ... (not Fn))
    // proof term: (cl (and F1 ... Fn) (not F1) ... (not Fn))
    // premises: ()
    // args: ()
    case PfRule::CNF_AND_NEG:
    {
      return addVeritStepFromOr(res, VeritRule::AND_NEG, children, {}, *cdp);
    }
    // ======== CNF Or Pos
    // Children: ()
    // Arguments: ((or F1 ... Fn))
    // ---------------------
    // Conclusion: (or (not (or F1 ... Fn)) F1 ... Fn)
    //
    // proof rule: or_pos
    // proof node: (or (not (or F1 ... Fn)) F1 ... Fn)
    // proof term: (cl (not (or F1 ... Fn)) F1 ... Fn)
    // premises: ()
    // args: ()
    case PfRule::CNF_OR_POS:
    {
      return addVeritStepFromOr(res, VeritRule::OR_POS, children, {}, *cdp);
    }
    // ======== CNF Or Neg
    // Children: ()
    // Arguments: ((or F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (or F1 ... Fn) (not Fi))
    //
    // proof rule: or_neg
    // proof node: (or (or F1 ... Fn) (not Fi))
    // proof term: (cl (or F1 ... Fn) (not Fi))
    // premises: ()
    // args: ()
    case PfRule::CNF_OR_NEG:
    {
      return addVeritStepFromOr(res, VeritRule::OR_NEG, children, {}, *cdp);
    }
    // ======== CNF Implies Pos
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (not (implies F1 F2)) (not F1) F2)
    //
    // proof rule: implies_pos
    // proof node: (or (not (implies F1 F2)) (not F1) F2)
    // proof term: (cl (not (implies F1 F2)) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_POS:
    {
      return addVeritStepFromOr(
          res, VeritRule::IMPLIES_POS, children, {}, *cdp);
    }
    // ======== CNF Implies Neg version 1
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) F1)
    //
    // proof rule: implies_neg1
    // proof node: (or (implies F1 F2) F1)
    // proof term: (cl (implies F1 F2) F1)
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_NEG1:
    {
      return addVeritStepFromOr(
          res, VeritRule::IMPLIES_NEG1, children, {}, *cdp);
    }
    // ======== CNF Implies Neg version 2
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) (not F2))
    //
    // proof rule: implies_neg2
    // proof node: (or (implies F1 F2) (not F2))
    // proof term: (cl (implies F1 F2) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_NEG2:
    {
      return addVeritStepFromOr(
          res, VeritRule::IMPLIES_NEG2, children, {}, *cdp);
    }
    // ======== CNF Equiv Pos version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) (not F1) F2)
    //
    // proof rule: equiv_pos2
    // proof node: (or (not (= F1 F2)) (not F1) F2)
    // proof term: (cl (not (= F1 F2)) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_POS1:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_POS2, children, {}, *cdp);
    }
    // ======== CNF Equiv Pos version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) F1 (not F2))
    //
    // proof rule: equiv_pos1
    // proof node: (or (not (= F1 F2)) F1 (not F2))
    // proof term: (cl (not (= F1 F2)) F1 (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_POS2:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_POS1, children, {}, *cdp);
    }
    // ======== CNF Equiv Neg version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) F1 F2)
    //
    // proof rule: equiv_neg2
    // proof node: (or (= F1 F2) F1 F2)
    // proof term: (cl (= F1 F2) F1 F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_NEG1:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_NEG2, children, {}, *cdp);
    }
    // ======== CNF Equiv Neg version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) (not F1) (not F2))
    //
    // proof rule: equiv_neg1
    // proof node: (or (= F1 F2) (not F1) (not F2))
    // proof term: (cl (= F1 F2) (not F1) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_NEG2:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_NEG1, children, {}, *cdp);
    }
    // ======== CNF Xor Pos version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) F1 F2)
    //
    // proof rule: xor_pos1
    // proof node: (or (not (xor F1 F2)) F1 F2)
    // proof term: (cl (not (xor F1 F2)) F1 F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_POS1:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_POS1, children, {}, *cdp);
    }
    // ======== CNF Xor Pos version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) (not F1) (not F2))
    //
    // proof rule: xor_pos2
    // proof node: (or (not (xor F1 F2)) (not F1) (not F2))
    // proof term: (cl (not (xor F1 F2)) (not F1) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_POS2:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_POS2, children, {}, *cdp);
    }
    // ======== CNF Xor Neg version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) (not F1) F2)
    //
    // proof rule: xor_neg2
    // proof node: (or (xor F1 F2) (not F1) F2)
    // proof term: (cl (xor F1 F2) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_NEG1:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_NEG2, children, {}, *cdp);
    }
    // ======== CNF Xor Neg version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) F1 (not F2))
    //
    // proof rule: xor_neg1
    // proof node: (or (xor F1 F2) F1 (not F2))
    // proof term: (cl (xor F1 F2) F1 (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_NEG2:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_NEG1, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) (not C) F1)
    //
    // proof rule: ite_pos2
    // proof node: (or (not (ite C F1 F2)) (not C) F1)
    // proof term: (cl (not (ite C F1 F2)) (not C) F1)
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_POS1:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_POS2, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) C F2)
    //
    // proof rule: ite_pos1
    // proof node: (or (not (ite C F1 F2)) C F2)
    // proof term: (cl (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_POS2:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_POS1, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 3
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) F1 F2)
    //
    // proof rule: ite_pos1
    // proof node: (VP1:(cl (not (ite C F1 F2)) C F2))
    // proof term: (cl (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    //
    // proof rule: ite_pos2
    // proof node: (VP2:(cl (not (ite C F1 F2)) (not C) F1))
    // proof term: (cl (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP3:(cl (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2))
    // proof term: (cl (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2)
    // premises: VP1 VP2
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (or (not (ite C F1 F2)) F1 F2)
    // proof term: (cl (not (ite C F1 F2)) F1 F2)
    // premises: VP3
    // args: ()
    case PfRule::CNF_ITE_POS3:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0], res[2]);
      Node vp2 =
          nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0].notNode(), res[1]);
      Node vp3 = nm->mkNode(kind::SEXPR, d_cl, res[0], res[1], res[0], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_POS1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_POS2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
             && addVeritStepFromOr(
                 res, VeritRule::DUPLICATED_LITERALS, {vp3}, {}, *cdp);
    }
    // ======== CNF ITE Neg version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not C) (not F1))
    //
    // proof rule: ite_neg2
    // proof node: (or (ite C F1 F2) (not C) (not F1))
    // proof term: (cl (ite C F1 F2) (not C) (not F1))
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_NEG1:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_NEG2, children, {}, *cdp);
    }
    // ======== CNF ITE Neg version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) C (not F2))
    //
    // proof rule: ite_neg1
    // proof node: (or (ite C F1 F2) C (not F2))
    // proof term: (cl (ite C F1 F2) C (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_NEG2:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_NEG1, children, {}, *cdp);
    }
    // ======== CNF ITE Neg version 3
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not F1) (not F2))
    //
    // proof rule: ite_neg1
    // proof term: (VP1:(cl (ite C F1 F2) C (not F2)))
    // premises: ()
    // args: ()
    //
    // proof rule: ite_neg2
    // proof term: (VP2:(cl (ite C F1 F2) (not C) (not F1)))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof term: (VP3:(cl (ite C F1 F2) (not F2) (ite C F1 F2) (not F1)))
    // premises: VP1 VP2
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof term: (cl (ite C F1 F2) C (not F2))
    // premises: VP3
    // args: ()
    case PfRule::CNF_ITE_NEG3:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0], res[2]);
      Node vp2 =
          nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0].notNode(), res[1]);
      Node vp3 = nm->mkNode(kind::SEXPR, d_cl, res[0], res[1], res[0], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_NEG1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_NEG2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
             && addVeritStepFromOr(
                 res, VeritRule::DUPLICATED_LITERALS, {vp3}, {}, *cdp);
    }
    //================================================= Equality rules
    // ======== Reflexive
    // Children: none
    // Arguments: (t)
    // ---------------------
    // Conclusion: (= t t)
    //
    // proof rule: refl
    // proof term: (cl (= t t))
    // premises: ()
    // args: ()
    case PfRule::REFL:
    {
      return addVeritStep(res,
                          VeritRule::REFL,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Transitivity
    // Children: (P1:(= t1 t2), ..., Pn:(= t{n-1} tn))
    // Arguments: none
    // -----------------------
    // Conclusion: (= t1 tn)
    //
    // proof rule: trans
    // proof node: (= t1 tn)
    // proof term: (cl (= t1 tn))
    // premises: P1, ..., Pn
    // args: ()
    case PfRule::TRANS:
    {
      return addVeritStep(res,
                          VeritRule::TRANS,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Congruence
    // Children: (P1:(= t1 s1), ..., Pn:(= tn sn))
    // Arguments: (<kind> f?)
    // ---------------------------------------------
    // Conclusion: (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn))
    // Notice that f must be provided iff <kind> is a parameterized kind, e.g.
    // APPLY_UF. The actual node for <kind> is constructible via
    // ProofRuleChecker::mkKindNode.
    //
    // proof rule: cong
    // proof node: (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn))
    // proof term: (cl (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn)))
    // premises: P1, ..., Pn
    // args: ()
    case PfRule::CONG:
    {
      return addVeritStep(res,
                          VeritRule::CONG,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== True intro
    // Children: (P:F)
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= F true)
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F true) F)))
    // proof term: (cl (= (= F true) F))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv2
    // proof node: (VP2:(cl (= F true) (not F)))
    // proof term: (cl (= F true) (not F))
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: (= F true)
    // proof term: (cl (= F true))
    // premises: VP2 P
    // args: ()
    case PfRule::TRUE_INTRO:
    {
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::EQUAL, res, children[0]));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    // ======== True elim
    // Children: (P:(= F true))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: F
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F true) F)))
    // proof term: (cl (= (= F true) F))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof node: (VP2:(cl (not (= F true)) F))
    // proof term: (cl (not (= F true)) F)
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: (F)
    // proof term: (cl F)
    // premises: VP2
    // args: ()
    //
    case PfRule::TRUE_ELIM:
    {
      bool success = true;
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::EQUAL, children[0], res));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      success &= addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
                 && addVeritStep(vp2, VeritRule::EQUIV1, {vp1}, {}, *cdp);
      return success
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    // ======== False intro
    // Children: (P:(not F))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= F false)
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F false) (not F))))
    // proof term: (cl (= (= F false) (not F)))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv2
    // proof node: (VP2:(cl (= F false) (not (not F))))
    // proof term: (cl (= F false) (not (not F)))
    // premises: VP1
    // args: ()
    //
    // proof rule: not_not
    // proof node: (VP3:(cl (not (not (not F))) F))
    // proof term: (cl (not (not (not F))) F)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP4:(cl (= F false) F))
    // proof term: (cl (= F false) F)
    // premises: VP2 VP3
    // args: ()
    //
    // proof rule: resolution
    // proof node: (= F false)
    // proof term: (cl (= F false))
    // premises: VP4 P
    // args: ()
    case PfRule::FALSE_INTRO:
    {
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::EQUAL, res, children[0]));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      Node vp3 = nm->mkNode(
          kind::SEXPR, d_cl, children[0].notNode().notNode(), children[0][0]);
      Node vp4 = nm->mkNode(kind::SEXPR, d_cl, res, children[0][0]);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(vp4, VeritRule::RESOLUTION, {vp2, vp3}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp4, children[0]},
                             {},
                             *cdp);
    }
    // ======== False elim
    // Children: (P:(= F false))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (not F)
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F false) (not F))))
    // proof term: (cl (= (= F false) (not F)))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof node: (VP2:(cl (not (= F false)) (not F)))
    // proof term: (cl (not (= F false)) (not F))
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: (not F)
    // proof term: (cl (not F))
    // premises: VP2 P
    // args: ()
    case PfRule::FALSE_ELIM:
    {
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::EQUAL, children[0], res));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV1, {vp1}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    //================================================= Quantifiers rules
    // ======== Witness intro
    // Children: (P:(exists ((x T)) F[x]))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= k (witness ((x T)) F[x]))
    // where k is the Skolem form of (witness ((x T)) F[x]).
    /*case PfRule::WITNESS_INTRO:
    {
      return false;
    }*/
    // ======== Exists intro
    // Children: (P:F[t])
    // Arguments: ((exists ((x T)) F[x]))
    // ----------------------------------------
    // Conclusion: (exists ((x T)) F[x])
    // This rule verifies that F[x] indeed matches F[t] with a substitution
    // over x.
    /*case PfRule::EXISTS_INTRO:
    {
      return false;
    }*/
    // ======== Skolemize
    // Children: (P:(exists ((x1 T1) ... (xn Tn)) F))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: F*sigma
    // sigma maps x1 ... xn to their representative skolems obtained by
    // SkolemManager::mkSkolemize, returned in the skolems argument of that
    // method. Alternatively, can use negated forall as a premise.
    /*case PfRule::SKOLEMIZE:
    {
    }*/
    // ======== Instantiate
    // Children: (P:(forall ((x1 T1) ... (xn Tn)) F))
    // Arguments: (t1 ... tn)
    // ----------------------------------------
    // Conclusion: F*sigma
    // sigma maps x1 ... xn to t1 ... tn.
    //
    // proof rule: forall_inst
    // proof node: (VP1:(cl (or (not (forall ((x1 T1) ... (xn Tn)) F))
    // F*sigma)))
    // proof term: (cl (or (not (forall ((x1 T1) ... (xn Tn)) F))
    // F*sigma))
    // premises: ()
    // args: (= x1 t1) ... (= xn tn)
    //
    // proof rule: or
    // proof node: (VP2:(cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma))
    // proof term: (cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma)
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: F*sigma
    // proof term: (cl F*sigma)
    // premises: VP2 P
    // args: ()
    case PfRule::INSTANTIATE:
    {
      for (unsigned long int i = 0; i < args.size(); i++)
      {
        new_args.push_back(nm->mkNode(kind::EQUAL, children[0][0][i], args[i]));
      }
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::OR, children[0].notNode(), res));
      bool success =
          addVeritStep(vp1, VeritRule::FORALL_INST, {}, new_args, *cdp);
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      success &= addVeritStep(vp2, VeritRule::OR, {vp1}, {}, *cdp);
      return success
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
      //================================================= Arithmetic rules
      // ======== Adding Inequalities
      // Note: an ArithLiteral is a term of the form (>< poly const)
      // where
      //   >< is >=, >, ==, <, <=, or not(== ...).
      //   poly is a polynomial
      //   const is a rational constant

      // Children: (P1:l1, ..., Pn:ln)
      //           where each li is an ArithLiteral
      //           not(= ...) is dis-allowed!
      //
      // Arguments: (k1, ..., kn), non-zero reals
      // ---------------------
      // Conclusion: (>< (* k t1) (* k t2))
      //    where >< is the fusion of the combination of the ><i, (flipping each
      //    it its ki is negative). >< is always one of <, <= NB: this implies
      //    that lower bounds must have negative ki,
      //                      and upper bounds must have positive ki.
      //    t1 is the sum of the polynomials.
      //    t2 is the sum of the constants.
      // case PfRule::ARITH_SCALE_SUM_UPPER_BOUNDS:{
      //
      //}
      // ======== Tightening Strict Integer Upper Bounds
      // Children: (P:(< i c))
      //         where i has integer type.
      // Arguments: none
      // ---------------------
      // Conclusion: (<= i greatestIntLessThan(c)})
      // INT_TIGHT_UB,
      // ======== Tightening Strict Integer Lower Bounds
      // Children: (P:(> i c))
      //         where i has integer type.
      // Arguments: none
      // ---------------------
      // Conclusion: (>= i leastIntGreaterThan(c)})
      // INT_TIGHT_LB,
      // ======== Trichotomy of the reals
      // Children: (A B)
      // Arguments: (C)
      // ---------------------
      // Conclusion: (C),
      //                 where (not A) (not B) and C
      //                   are (> x c) (< x c) and (= x c)
      //                   in some order
      //                 note that "not" here denotes arithmetic negation,
      //                 flipping
      //                 >= to <, etc.
      //
      // If C = (= x c) or C = (> x c) pre-processing has to transform (>= x c)
      // into (<= c x)
      //
      // proof rule: la_disequality
      // proof node: (VP1: (or (= x c) (not (<= x c)) (not (<= c x))))
      // proof term: (cl (or (= x c) (not (<= x c)) (not (<= c x))))
      // premises: ()
      // args: ()
      //
      // proof rule: or
      // proof node: (VP2: (cl (= x c) (not (<= x c)) (not (<= c x))))
      // proof term: (cl (= x c) (not (<= x c)) (not (<= c x)))
      // premises: ()
      // args: ()
      //
      // If C = (> x c) or C = (< x c) post-processing has to be added. In these
      // cases resolution on VP2 A B yields (not (<=x c)) or (not (<= c x)) and
      // comp_simplify is used to transform it into C. Otherwise,
      //
      // proof rule: resolution
      // proof node: C
      // proof term: (cl C)
      // premises: VP2 A B
      // args: ()
      //
      // TODO:
      // isabelle-mirabelle/Green_cvc42/x2020_07_31_11_27_36_291_7704406.smt_in
      /*case PfRule::ARITH_TRICHOTOMY:{
        bool success = true;
        Node equal;
        Node lesser;
        Node greater;

        if(res.getKind() == kind::EQUAL){equal = res;}
        else if(children[0].getKind() == kind::NOT){equal = children[0];}
        else if(children[1].getKind() == kind::NOT){equal = children[1];}

        if(res.getKind() == kind::GT){greater = res;}
        else if(children[0].getKind() == kind::LEQ){greater = children[0];}
        else if(children[1].getKind() == kind::LEQ){greater = children[1];}

        if(res.getKind() == kind::LT){lesser = res;}
        else if(children[0].getKind() == kind::GEQ){lesser = children[0];}
        else if(children[1].getKind() == kind::GEQ){lesser = children[1];}

        Node x = equal[0][0];
        Node c = equal[0][1];
        Node vp_child1 = children[0];
        Node vp_child2 = children[1];

        //Preprocessing
        if(res == equal || res == greater){ // C = (= x c) or C = (> x c)
          // lesser = (>= x c)
          Node vpc2 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::EQUAL,nm->mkNode(kind::GEQ,x,c),nm->mkNode(kind::LEQ,c,x)));
      // (cl (= (>= x c) (<= c x))) Node vpc1 =
      nm->mkNode(kind::SEXPR,d_cl,vpc2[1].notNode(),nm->mkNode(kind::GEQ,x,c).notNode(),nm->mkNode(kind::LEQ,c,x));
      // (cl (not(= (>= x c) (<= c x))) (not (>= x c)) (<= c x)) vp_child1 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::LEQ,c,x)); // (cl (<= c
      x))

          success &= addVeritStep(vpc1,VeritRule::EQUIV_POS2,{},{},*cdp)
                  && addVeritStep(vpc2,VeritRule::COMP_SIMPLIFY,{},{},*cdp)
                  &&
      addVeritStep(vp_child1,VeritRule::RESOLUTION,{vpc1,vpc2,lesser},{},*cdp);
          // greater = (<= x c) or greater = (not (= x c)) -> no preprocessing
      necessary if(res == equal){vp_child2 = greater;} else{vp_child2 = equal;}
        }

        //Process
        Node vp1 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::OR,nm->mkNode(kind::EQUAL,x,c),nm->mkNode(kind::LEQ,x,c).notNode(),nm->mkNode(kind::LEQ,c,x).notNode()));
      // (cl (or (= x c) (not (<= x c)) (not (<= c x)))) Node vp2 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::EQUAL,x,c),nm->mkNode(kind::LEQ,x,c).notNode(),nm->mkNode(kind::LEQ,c,x).notNode());
      // (cl (= x c) (not (<= x c)) (not (<= c x))) success &=
      addVeritStep(vp1,VeritRule::LA_DISEQUALITY,{},{},*cdp)
                && addVeritStep(vp2,VeritRule::OR,{vp1},{},*cdp);

        //Postprocessing
        if (res == equal){ //no postprocessing necessary
          return success &&
      addVeritStep(res,VeritRule::RESOLUTION,nm->mkNode(kind::SEXPR,d_cl,res),{vp2,vp_child1,vp_child2},{},*cdp);
        }
        else if(res == greater){ //have (not (<= x c)) but result should be (> x
      c) Node vp3 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::LEQ,x,c).notNode()); //
      (cl (not (<= x c))) Node vp4 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::EQUAL,nm->mkNode(kind::GT,x,c),nm->mkNode(kind::LEQ,x,c).notNode()).notNode(),nm->mkNode(kind::GT,x,c),nm->mkNode(kind::LEQ,x,c).notNode().notNode());
      // (cl (not(= (> x c) (not (<= x c)))) (> x c) (not (not (<= x c)))) Node
      vp5 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::EQUAL,nm->mkNode(kind::GT,x,c),nm->mkNode(kind::LEQ,x,c).notNode()));
      // (cl (= (> x c) (not (<= x c))))

          return success
                  &&
      addVeritStep(vp3,VeritRule::RESOLUTION,{vp2,vp_child1,vp_child2},{},*cdp)
                  && addVeritStep(vp4,VeritRule::EQUIV_POS1,{},{},*cdp)
                  && addVeritStep(vp5,VeritRule::COMP_SIMPLIFY,{},{},*cdp)
                  &&
      addVeritStep(res,VeritRule::RESOLUTION,nm->mkNode(kind::SEXPR,d_cl,res),{vp3,vp4,vp5},{},*cdp);
        }
        else{ //have (not (<= c x)) but result should be (< x c)
          Node vp3 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::LEQ,c,x).notNode()); //
      (cl (not (<= c x))) Node vp4 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::EQUAL,nm->mkNode(kind::LT,x,c),nm->mkNode(kind::LEQ,c,x).notNode()).notNode(),nm->mkNode(kind::LT,x,c),nm->mkNode(kind::LEQ,c,x).notNode().notNode());
      // (cl (not(= (< x c) (not (<= c x)))) (< x c) (not (not (<= c x)))) Node
      vp5 =
      nm->mkNode(kind::SEXPR,d_cl,nm->mkNode(kind::EQUAL,nm->mkNode(kind::LT,x,c),nm->mkNode(kind::LEQ,c,x).notNode()));
      // (cl (= (< x c) (not (<= c x))))

          return success
                  &&
      addVeritStep(vp3,VeritRule::RESOLUTION,{vp2,vp_child1,vp_child2},{},*cdp)
                  && addVeritStep(vp4,VeritRule::EQUIV_POS1,{},{},*cdp)
                  && addVeritStep(vp5,VeritRule::COMP_SIMPLIFY,{},{},*cdp)
                  &&
      addVeritStep(res,VeritRule::RESOLUTION,nm->mkNode(kind::SEXPR,d_cl,res),{vp3,vp4,vp5},{},*cdp);
        }

      }*/
      // ======== Arithmetic operator elimination
      // Children: none
      // Arguments: (t)
      // ---------------------
      // Conclusion: arith::OperatorElim::getAxiomFor(t)
      // ARITH_OP_ELIM_AXIOM,
      // ======== Int Trust
      // Children: (P1 ... Pn)
      // Arguments: (Q)
      // ---------------------
      // Conclusion: (Q)
      // INT_TRUST,
      //======== Multiplication sign inference
      // Children: none
      // Arguments: (f1, ..., fk, m)
      // ---------------------
      // Conclusion: (=> (and f1 ... fk) (~ m 0))
      // Where f1, ..., fk are variables compared to zero (less, greater or not
      // equal), m is a monomial from these variables, and ~ is the comparison
      // (less or greater) that results from the signs of the variables. All
      // variables with even exponent in m should be given as not equal to zero
      // while all variables with odd exponent in m should be given as less or
      // greater than zero.
      // ARITH_MULT_SIGN,
      //======== Multiplication with positive factor
      // Children: none
      // Arguments: (m, orig, lhs, rel, rhs)
      // ---------------------
      // Conclusion: (=> (and (> m 0) (rel lhs rhs)) (rel (* m lhs) (* m rhs)))
      // Where orig is the origin that implies (rel lhs rhs) and rel is a
      // relation symbol. ARITH_MULT_POS,
      //======== Multiplication with negative factor
      // Children: none
      // Arguments: (m, orig, (rel lhs rhs))
      // ---------------------
      // Conclusion: (=> (and (< m 0) (rel lhs rhs)) (rel_inv (* m lhs) (* m
      // rhs))) Where orig is the origin that implies (rel lhs rhs) and rel is a
      // relation symbol and rel_inv the inverted relation symbol.
      // ARITH_MULT_NEG,
      //======== Multiplication tangent plane
      // Children: none
      // Arguments: (t, x, y, a, b, sgn)
      // ---------------------
      // Conclusion:
      //   sgn=-1: (= (<= t tplane) (or (and (<= x a) (>= y b)) (and (>= x a)
      //   (<= y b))) sgn= 1: (= (>= t tplane) (or (and (<= x a) (<= y b)) (and
      //   (>= x a)
      //   (>= y b)))
      // Where x,y are real terms (variables or extended terms), t = (* x y)
      // (possibly under rewriting), a,b are real constants, and sgn is either
      // -1 or 1. tplane is the tangent plane of x*y at (a,b): b*x + a*y - a*b
      // ARITH_MULT_TANGENT,

    default:  // TBD
    {
    }
  }

  // Extended rules
  switch (id)
  {
    // ======== Symmetric
    // Children: (P:(= t1 t2)) or (P:(not (= t1 t2)))
    // Arguments: none
    // -----------------------
    // Conclusion: (= t2 t1) or (not (= t2 t1))
    //
    //
    // proof rule: symm
    // proof node: (= t2 t1) or (not (= t2 t1))
    // proof term: (cl (= t2 t1)) or (cl (not (= t2 t1)))
    // premises: ((P:(= t1 t2)) or (P:(not (= t1 t2))
    // args: ()
    case PfRule::SYMM:
    {
      return addVeritStep(res,
                          VeritRule::SYMM,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Reordering
    // Children: (P:C1)
    // Arguments: (C2)
    // ---------------------
    // Conclusion: C2
    // where
    //  Set representations of C1 and C2 is the same but the number of literals
    //  in C2 is the same of that of C1
    //
    //
    // Let C2 = (or F1 ... Fn)
    //
    // proof rule: reordering
    // proof node: C2
    // proof term: (cl F1 ... Fn)
    // premises: P
    // args: ()
    case PfRule::REORDERING:
    {
      return addVeritStepFromOr(res, VeritRule::REORDER, children, {}, *cdp);
    }
    default:  // TBD
    {
      std::cout << "Not implemented yet " << id << std::endl;
      return addVeritStep(res,
                          VeritRule::UNDEFINED,
                          nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          args,
                          *cdp);
    }
  }

  Trace("verit-proof") << "... error translating rule " << id << " / " << res
                       << " " << children << " " << args << std::endl;
  return false;
}

bool MyVeritProofPostprocessCallback::addVeritStep(
    Node res,
    VeritRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  return addVeritStep(res, rule, res, children, args, cdp);
}

bool MyVeritProofPostprocessCallback::addVeritStep(
    Node res,
    VeritRule rule,
    Node conclusion,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{  // TODO: use *cdp, unify
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> new_args = std::vector<Node>();
  new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(rule)));
  new_args.push_back(res);
  new_args.push_back(conclusion);
  new_args.insert(new_args.end(), args.begin(), args.end());
  Trace("verit-proof") << "... add veriT step " << res << " / " << conclusion
                       << " " << children << " / " << new_args << std::endl;
  return cdp.addStep(res, PfRule::VERIT_RULE, children, new_args);
}

// Replace a node (or F1 ... Fn) by (cl F1 ... Fn)
bool MyVeritProofPostprocessCallback::addVeritStepFromOr(
    Node res,
    VeritRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> lits{d_cl};
  lits.insert(lits.end(), res.begin(), res.end());
  return addVeritStep(
      res, rule, nm->mkNode(kind::SEXPR, lits), children, args, cdp);
}

bool MyVeritProofPostprocessCallback::isSameModEqual(Node vp1, Node vp2)
{
  if (vp1.getKind() != vp2.getKind())
  {
    return false;
  }
  else if (vp1 == vp2)
  {
    return true;
  }
  else if (vp1.getKind() == kind::EQUAL)
  {
    return (isSameModEqual(vp1[0], vp2[1]) && isSameModEqual(vp1[1], vp2[0]))
           || (isSameModEqual(vp1[0], vp2[0])
               && isSameModEqual(vp1[1], vp2[1]));
  }
  std::vector<Node> vp1s(vp1.begin(), vp1.end());
  std::vector<Node> vp2s(vp2.begin(), vp2.end());
  if (vp1s.size() != vp2s.size())
  {
    return false;
  }
  bool equal = true;
  for (unsigned long int i = 0; i < vp1s.size(); i++)
  {
    equal &= isSameModEqual(vp1s[i], vp2s[i]);
  }
  return equal;
}

VeritProofPostprocess::VeritProofPostprocess(ProofNodeManager* pnm,
                                             bool extended)
    : d_pnm(pnm),
      d_cb0(d_pnm),
      d_cb(new VeritProofPostprocessCallback(d_pnm)),
      d_fcb(new VeritProofPostprocessFinalCallback(d_pnm)),
      // d_updater(d_pnm, d_cb,false,false), //TODO: Look up parameters
      //d_fcb(d_pnm),
      //d_finalize(d_pnm, d_fcb,false,false),
      d_extended(extended)
{
}

VeritProofPostprocess::~VeritProofPostprocess() {}

void VeritProofPostprocess::myProcess(std::shared_ptr<ProofNode> pf)
{
  Trace("test-verit-debug") << "Original proof node: " << *pf.get() << "\n";
  // now, process
  ProofNodeUpdater updater(d_pnm, d_cb0, false, false);
  updater.process(pf);
  Trace("test-verit-debug") << "Converted proof node with updater: " << *pf.get()
                      << "\n";
}

void VeritProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  CDProof* cdp = new CDProof(d_pnm, nullptr, "CDProof", false);
  processInternal(pf,cdp);

  // In veriT the last step is always (cl). However, after the translate the final step might be (cl false). In that case additional steps are required.
  //d_finalize.process(pf);
  //CDProof* cdp = new CDProof(d_pnm, nullptr, "CDProof", false);
  VeritProofPostprocessFinalCallback* fcb = new VeritProofPostprocessFinalCallback(d_pnm);
  bool continueUpdate = true;
  if (fcb->shouldUpdate(pf,continueUpdate))
  {
    std::vector<Node> children;
    for (auto c : pf->getChildren())
    {
      children.push_back(c->getResult());
    }
    if(fcb->update(pf->getResult(), PfRule::VERIT_RULE, children, pf->getArguments(), cdp, continueUpdate)){
      d_pnm->updateNode(pf.get(), cdp->getProofFor(pf->getResult()).get());
      Trace("verit-proof") << "... updated proof for " << pf->getResult() << std::endl;
    }
    else{
      Trace("verit-proof") << "... error updating proof for " << pf->getResult()
                           << std::endl;
    }
  }
}

void VeritProofPostprocess::processInternal(std::shared_ptr<ProofNode> pf, CDProof* cdp)
{
  //First, update children
  std::vector<Node> children;
  for (const std::shared_ptr<ProofNode>& child :pf->getChildren()){
    std::shared_ptr<ProofNode> next_child = child;
    //In non-extended mode symm and reordering should be skipped.
    if(!d_extended && (next_child->getRule() == PfRule::REORDERING || next_child->getRule() == PfRule::SYMM)){
      while (next_child->getRule() == PfRule::SYMM || next_child->getRule() == PfRule::REORDERING){
        next_child = next_child->getChildren()[0];
      }
    }
    processInternal(next_child,cdp);
    children.push_back(next_child->getResult());
  }

  // Then, update proof node
  bool continueUpdate = true;
  if (d_cb->shouldUpdate(pf, continueUpdate))
  {
    if (d_cb->update(pf->getResult(),
                     pf->getRule(),
                     children,
                     pf->getArguments(),
                     cdp,
                     continueUpdate))
    {
      d_pnm->updateNode(pf.get(), cdp->getProofFor(pf->getResult()).get());
      Trace("verit-proof") << "... updated proof for " << pf->getResult()
                           << std::endl;
    }
    else
    {
      Trace("verit-proof") << "... error updating proof for " << pf->getResult()
                           << std::endl;
    }
  }
}

}  // namespace proof

}  // namespace CVC4
