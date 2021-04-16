/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for single invocation partitioning.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SINGLE_INV_PARTITION_H
#define CVC5__THEORY__QUANTIFIERS__SINGLE_INV_PARTITION_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

/** single invocation partition
 *
 * This is a utility to group formulas into single invocation/non-single
 * invocation parts, relative to a set of "input functions".
 * It can be used when either the set of input functions is fixed,
 * or is unknown.
 *
 * (EX1) For example, if input functions are { f },
 * then the formula is ( f( x, y ) = g( y ) V f( x, y ) = b )
 * is single invocation since there is only one
 * unique application of f, that is, f( x, y ).
 * Notice that
 *   exists f. forall xy. f( x, y ) = g( y ) V f( x, y ) = b
 * is equivalent to:
 *   forall xy. exists z. z = g( y ) V z = b
 *
 * When handling multiple input functions, we only infer a formula
 * is single invocation if all (relevant) input functions have the
 * same argument types. An input function is relevant if it is
 * specified by the input in a call to init() or occurs in the
 * formula we are processing.
 *
 * Notice that this class may introduce auxiliary variables to
 * coerce a formula into being single invocation. For example,
 * see Example 5 of Reynolds et al. SYNT 2017.
 *
 */
class SingleInvocationPartition
{
 public:
  SingleInvocationPartition() : d_has_input_funcs(false) {}
  ~SingleInvocationPartition() {}
  /** initialize this partition for formula n, with input functions funcs
   *
   * This initializes this class to check whether formula n is single
   * invocation with respect to the input functions in funcs only.
   * Below, the "processed formula" is a formula generated by this
   * call that is equivalent to n (if this call is successful).
   *
   * This method returns true if all input functions have identical
   * argument types, and false otherwise. Notice that all
   * access functions below are only valid if this class is
   * successfully initialized.
   */
  bool init(std::vector<Node>& funcs, Node n);

  /** initialize this partition for formula n
   *
   * In contrast to the above method, this version assumes that
   * all uninterpreted functions are input functions. That is, this
   * method is equivalent to the above function with funcs containing
   * all uninterpreted functions occurring in n.
   */
  bool init(Node n);

  /** is the processed formula purely single invocation?
   *
   * A formula is purely single invocation if it is equivalent to:
   *   t[ f1( x ), ..., fn( x ), x ],
   * for some F, where f1...fn are the input functions.
   * Notice that the free variables of t are exactly x.
   */
  bool isPurelySingleInvocation() { return d_conjuncts[1].empty(); }
  /** is the processed formula non-ground single invocation?
   *
   * A formula is non-ground single invocation if it is equivalent to:
   *   F[ f1( x ), ..., fn( x ), x, y ],
   * for some F, where f1...fn are the input functions.
   */
  bool isNonGroundSingleInvocation()
  {
    return d_conjuncts[3].size() == d_conjuncts[1].size();
  }

  /** Get the (portion of) the processed formula that is single invocation
   *
   * Notice this method returns the anti-skolemized version of the input
   * formula. In (EX1), this method returns:
   *   z = g( y ) V z = b
   * where z is the first-order variable for f (see
   * getFirstOrderVariableForFunction).
   */
  Node getSingleInvocation() { return getConjunct(0); }
  /** Get the (portion of) the processed formula that is not single invocation
   *
   * This formula and the above form a partition of the conjuncts of the
   * processed formula, that is:
   *   getSingleInvocation() * sigma ^ getNonSingleInvocation()
   * is equivalent to the processed formula, where sigma is a substitution of
   * the form:
   *   z_1 -> f_1( x ) .... z_n -> f_n( x )
   * where z_i are the first-order variables for input functions f_i
   * for all i=1,...,n, and x are the single invocation arguments of the input
   * formulas (see d_si_vars).
   */
  Node getNonSingleInvocation() { return getConjunct(1); }
  /** get full specification
   *
   * This returns getSingleInvocation() * sigma ^ getNonSingleInvocation(),
   * which is equivalent to the processed formula, where sigma is the
   * substitution described above.
   */
  Node getFullSpecification() { return getConjunct(2); }
  /** get first order variable for input function f
   *
   * This corresponds to the variable that we used when anti-skolemizing
   * function f. For example, in (EX1), if getSingleInvocation() returns:
   *   z = g( y ) V z = b
   * Then, getFirstOrderVariableForFunction(f) = z.
   */
  Node getFirstOrderVariableForFunction(Node f) const;

  /** get function for first order variable
   *
   * Opposite direction of above, where:
   *   getFunctionForFirstOrderVariable(z) = f.
   */
  Node getFunctionForFirstOrderVariable(Node v) const;

  /** get function invocation for
   *
   * Returns f( x ) where x are the single invocation arguments of the input
   * formulas (see d_si_vars). If f is not an input function, it returns null.
   */
  Node getFunctionInvocationFor(Node f) const;

  /** get single invocation variables, appends them to sivars */
  void getSingleInvocationVariables(std::vector<Node>& sivars) const;

  /** get all variables
   *
   * Appends all free variables of the processed formula to vars.
   */
  void getAllVariables(std::vector<Node>& vars) const;

  /** get function variables
   *
   * Appends all first-order variables corresponding to input functions to
   * fvars.
   */
  void getFunctionVariables(std::vector<Node>& fvars) const;

  /** get functions
   *
   * Gets all input functions. This has the same order as the list of
   * function variables above.
   */
  void getFunctions(std::vector<Node>& fs) const;

  /** print debugging information on Trace c */
  void debugPrint(const char* c);

 private:
  /** map from input functions to whether they have an anti-skolemizable type
   * An anti-skolemizable type is one of the form:
   *   ( T1, ..., Tn ) -> T
   * where Ti = d_arg_types[i] for i = 1,...,n.
   */
  std::map<Node, bool> d_funcs;

  /** map from functions to the invocation we inferred for them */
  std::map<Node, Node> d_func_inv;

  /** the list of first-order variables for functions
   * In (EX1), this is the list { z }.
   */
  std::vector<Node> d_func_vars;

  /** the arguments that we based the anti-skolemization on.
   * In (EX1), this is the list { x, y }.
   */
  std::vector<Node> d_si_vars;

  /** every free variable of conjuncts[2] */
  std::unordered_set<Node, NodeHashFunction> d_all_vars;
  /** map from functions to first-order variables that anti-skolemized them */
  std::map<Node, Node> d_func_fo_var;
  /** map from first-order variables to the function it anti-skolemized */
  std::map<Node, Node> d_fo_var_to_func;

  /** The argument types for this single invocation partition.
   * These are the argument types of the input functions we are
   * processing, where notice that:
   *   d_si_vars[i].getType()==d_arg_types[i]
   */
  std::vector<TypeNode> d_arg_types;

  /** the list of conjuncts with various properties :
   * 0 : the single invocation conjuncts (stored in anti-skolemized form),
   * 1 : the non-single invocation conjuncts,
   * 2 : all conjuncts,
   * 3 : non-ground single invocation conjuncts.
   */
  std::vector<Node> d_conjuncts[4];

  /** did we initialize this class with input functions? */
  bool d_has_input_funcs;
  /** the input functions we initialized this class with */
  std::vector<Node> d_input_funcs;
  /** all input functions */
  std::vector<Node> d_all_funcs;
  /** skolem of the same type as input functions */
  std::vector<Node> d_input_func_sks;

  /** infer the argument types of uninterpreted function applications
   *
   * If this method returns true, then typs contains the list of types of
   * the arguments (in order) of all uninterpreted functions in n.
   * If this method returns false, then there exists (at least) two
   * uninterpreted functions in n whose argument types are not identical.
   */
  bool inferArgTypes(Node n,
                     std::vector<TypeNode>& typs,
                     std::map<Node, bool>& visited);

  /** is anti-skolemizable type
   *
   * This method returns true if f's argument types are equal to the
   * argument types we have fixed in this class (see d_arg_types).
   */
  bool isAntiSkolemizableType(Node f);

  /**
   * This is the entry point for initializing this class,
   * which is called by the public init(...) methods.
   *   funcs are the input functions (if any were explicitly provide),
   *   typs is the types of the arguments of funcs,
   *   n is the formula to process,
   *   has_funcs is whether input functions were explicitly provided.
   */
  bool init(std::vector<Node>& funcs,
            std::vector<TypeNode>& typs,
            Node n,
            bool has_funcs);

  /**
   * Collect the top-level conjuncts of the formula (equivalent to)
   * n or the negation of n if pol=false, and store them in conj.
   */
  bool collectConjuncts(Node n, bool pol, std::vector<Node>& conj);

  /** process conjunct n
   *
   * This function is called when n is a top-level conjunction in a
   * formula that is equivalent to the input formula given to this
   * class via init.
   *
   * args : stores the arguments (if any) that we have seen in an application
   *   of an application of an input function in this conjunct.
   * terms/subs : this stores a term substitution with entries of the form:
   *     f(args) -> z
   *   where z is the first-order variable for input function f.
   */
  bool processConjunct(Node n,
                       std::map<Node, bool>& visited,
                       std::vector<Node>& args,
                       std::vector<Node>& terms,
                       std::vector<Node>& subs);

  /** get the and node corresponding to d_conjuncts[index] */
  Node getConjunct(int index);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__SINGLE_INV_PARTITION_H */
