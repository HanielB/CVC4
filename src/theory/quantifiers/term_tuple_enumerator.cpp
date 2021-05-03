/******************************************************************************
 * Top contributors (to current version):
 *   MikolasJanota, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of an enumeration of tuples of terms for the purpose of
 * quantifier instantiation.
 */
#include "theory/quantifiers/term_tuple_enumerator.h"

#include <algorithm>
#include <functional>
#include <iterator>
#include <map>
#include <vector>

#include "base/map_util.h"
#include "base/output.h"
#include "options/quantifiers_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/index_trie.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_pools.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"
#include "util/statistics_stats.h"

namespace cvc5 {

template <typename T>
static Cvc5ostream& operator<<(Cvc5ostream& out, const std::vector<T>& v)
{
  out << "[ ";
  std::copy(v.begin(), v.end(), std::ostream_iterator<T>(out, " "));
  return out << "]";
}

/** Tracing purposes, printing a masked vector of indices. */
static void traceMaskedVector(const char* trace,
                              const char* name,
                              const std::vector<bool>& mask,
                              const std::vector<size_t>& values)
{
  Assert(mask.size() == values.size());
  Trace(trace) << name << " [ ";
  for (size_t variableIx = 0; variableIx < mask.size(); variableIx++)
  {
    if (mask[variableIx])
    {
      Trace(trace) << values[variableIx] << " ";
    }
    else
    {
      Trace(trace) << "_ ";
    }
  }
  Trace(trace) << "]" << std::endl;
}

namespace theory {
namespace quantifiers {
/** A general interface for producing a sequence of terms for each quantified
 * variable.*/
class ITermProducer
{
 public:
  virtual ~ITermProducer() = default;
  /** Set up terms for given variable.  */
  virtual size_t prepareTerms(size_t variableIx) = 0;
  /** Get a given term for a given variable.  */
  virtual Node getTerm(size_t variableIx,
                       size_t term_index) CVC5_WARN_UNUSED_RESULT = 0;
};
/**A term producer based on the term database and the current equivalent
 * classes, i.e. if 2 terms belong to the same equivalents class, only one of
 * them will be produced.*/
class BasicTermProducer : public ITermProducer
{
 public:
  BasicTermProducer(Node quantifier, QuantifiersState& qs, TermDb* td)
      : d_quantifier(quantifier),
        d_qs(qs),
        d_typeCache(quantifier[0].getNumChildren()),
        d_tdb(td)
  {
  }

  virtual ~BasicTermProducer() = default;

  virtual size_t prepareTerms(size_t variableIx) override;
  virtual Node getTerm(size_t variableIx,
                       size_t term_index) override CVC5_WARN_UNUSED_RESULT;

 protected:
  const Node d_quantifier;
  /**  a list of terms for each type */
  std::map<TypeNode, std::vector<Node> > d_termDbList;
  /** Reference to quantifiers state */
  QuantifiersState& d_qs;
  /** type for each variable */
  std::vector<TypeNode> d_typeCache;
  /** Pointer to term database */
  TermDb* d_tdb;
};

/**
 * Enumerate ground terms according to the relevant domain class.
 */
class RelevantDomainProducer : public ITermProducer
{
 public:
  RelevantDomainProducer(Node quantifier, RelevantDomain* rd)
      : d_quantifier(quantifier), d_rd(rd)
  {
  }
  virtual ~RelevantDomainProducer() = default;

  virtual size_t prepareTerms(size_t variableIx) override
  {
    return d_rd->getRDomain(d_quantifier, variableIx)->d_terms.size();
  }
  virtual Node getTerm(size_t variableIx, size_t term_index) override
  {
    return d_rd->getRDomain(d_quantifier, variableIx)->d_terms[term_index];
  }

 protected:
  const Node d_quantifier;
  /** The relevant domain */
  RelevantDomain* d_rd;
};

/**
 * Base class for enumerators of tuples of terms for the purpose of
 * quantification instantiation. The tuples are represented as tuples of
 * indices of  terms, where the tuple has as many elements as there are
 * quantified variables in the considered quantifier.
 *
 * Like so, we see a tuple as a number, where the digits may have different
 * ranges. The most significant digits are stored first.
 *
 * Tuples are enumerated  in a lexicographic order in stages. There are 2
 * possible strategies, either  all tuples in a given stage have the same sum of
 * digits, or, the maximum  over these digits is the same.
 * */
class TermTupleEnumeratorBase : public TermTupleEnumeratorInterface
{
 public:
  /** Initialize the class with the quantifier to be instantiated. */
  TermTupleEnumeratorBase(Node quantifier,
                          const TermTupleEnumeratorEnv* env,
                          ITermProducer* termProducer)
      : d_quantifier(quantifier),
        d_variableCount(d_quantifier[0].getNumChildren()),
        d_env(env),
        d_termProducer(termProducer),
        d_stepCounter(0),
        d_disabledCombinations(
            true)  // do not record combinations with no blanks

  {
    d_changePrefix = d_variableCount;
  }

  virtual ~TermTupleEnumeratorBase() = default;

  // implementation of the TermTupleEnumeratorInterface
  virtual void init() override;
  virtual bool hasNext() override;
  virtual void next(/*out*/ std::vector<Node>& terms) override;
  virtual void failureReason(const std::vector<bool>& mask) override;
  // end of implementation of the TermTupleEnumeratorInterface

 protected:
  /** the quantifier whose variables are being instantiated */
  const Node d_quantifier;
  /** number of variables in the quantifier */
  const size_t d_variableCount;
  /** env of structures with a longer lifespan */
  const TermTupleEnumeratorEnv* const d_env;
  /**term producer to be used to generate the individual terms*/
  std::unique_ptr<ITermProducer> d_termProducer;
  /** number of candidate terms for each variable */
  std::vector<size_t> d_termsSizes;
  /** tuple of indices of the current terms */
  std::vector<size_t> d_termIndex;
  /** total number of steps of the enumerator */
  uint32_t d_stepCounter;

  /**becomes false once the enumerator runs out of options*/
  bool d_hasNext;

  /** a data structure storing disabled combinations of terms */
  IndexTrie d_disabledCombinations;
  /** the length of the prefix that has to be changed in the next
  combination, i.e.  the number of the most significant digits that need to be
  changed in order to escape a  useless instantiation */
  size_t d_changePrefix;
  virtual bool nextCombinationAttempt() = 0;
  virtual void initializeAttempts() = 0;
  /** Move on in the current stage */
  bool nextCombination();
};

class SocialTupleEnumerator : public TermTupleEnumeratorBase
{
 public:
  using TermTupleEnumeratorBase::TermTupleEnumeratorBase;  // inherit
                                                           // constructor
 protected:
  size_t d_maxValue;
  std::vector<size_t> d_score;
  virtual bool nextCombinationAttempt() override;
  bool validatePermutation();
  bool increaseScore();
  /** Move onto the next combination. */
  bool nextPermutation();
  bool nextValidPermutation();
  /** Find the next lexicographically smallest combination of terms that change
   * on the change prefix, each digit is within the current state,  and there is
   * at least one digit not in the previous stage. */
  virtual void initializeAttempts() override;
};

bool SocialTupleEnumerator::nextCombinationAttempt()
{
  return nextValidPermutation() || increaseScore();
}

bool SocialTupleEnumerator::validatePermutation()
{
  do
  {
    bool okay = true;
    for (size_t varIx = 0; okay && varIx < d_variableCount; varIx++)
    {
      okay = d_termIndex[varIx] < d_termsSizes[varIx];
    }
    if (okay)
    {
      return true;
    }
  } while (nextPermutation());
  return false;
}

bool SocialTupleEnumerator::nextValidPermutation()
{
  return nextPermutation() && validatePermutation();
}
bool SocialTupleEnumerator::nextPermutation()
{
  return std::next_permutation(d_termIndex.begin(), d_termIndex.end());
}

void SocialTupleEnumerator::initializeAttempts()
{
  d_maxValue =
      std::max(*std::max_element(d_termsSizes.begin(), d_termsSizes.end()),
               static_cast<size_t>(1));
  d_score.resize(d_variableCount, 0);
}
class StagedTupleEnumerator : public TermTupleEnumeratorBase
{
 public:
  using TermTupleEnumeratorBase::TermTupleEnumeratorBase;  // inherit
                                                           // constructor
 protected:
  /** current sum/max  of digits, depending on the strategy */
  size_t d_currentStage;
  /**total number of stages*/
  size_t d_stageCount;
  /** Move onto the next stage */
  bool increaseStage();
  /** Move onto the next stage, sum strategy. */
  bool increaseStageSum();
  /** Move onto the next stage, max strategy. */
  bool increaseStageMax();
  virtual bool nextCombinationAttempt() override;
  /** Move onto the next combination. */
  bool nextCombinationInternal();
  /** Find the next lexicographically smallest combination of terms that
   * change on the change prefix, each digit is within the current state,  and
   * there is at least one digit not in the previous stage. */
  bool nextCombinationSum();
  /** Find the next lexicographically smallest combination of terms that
   * change on the change prefix and their sum is equal to d_currentStage. */
  bool nextCombinationMax();
  virtual void initializeAttempts() override;
};
void TermTupleEnumeratorBase::init()
{
  Trace("inst-alg-rd") << "Initializing enumeration " << d_quantifier
                       << std::endl;
  d_hasNext = true;

  if (d_variableCount == 0)
  {
    d_hasNext = false;
    return;
  }

  // prepare a sequence of terms for each quantified variable
  // additionally initialize the cache for variable types
  for (size_t variableIx = 0; variableIx < d_variableCount; variableIx++)
  {
    const size_t termsSize = d_termProducer->prepareTerms(variableIx);
    Trace("inst-alg-rd") << "Variable " << variableIx << " has " << termsSize
                         << " in relevant domain." << std::endl;
    if (termsSize == 0 && !d_env->d_fullEffort)
    {
      d_hasNext = false;
      return;  // give up on an empty dommain
    }
    d_termsSizes.push_back(termsSize);
  }
  d_termIndex.resize(d_variableCount, 0);
  initializeAttempts();
}

bool TermTupleEnumeratorBase::hasNext()
{
  if (!d_hasNext)
  {
    return false;
  }

  if (d_stepCounter++ == 0)
  {  // TODO:any (nice)  way of avoiding this special if?
    return true;
  }

  // try to find the next combination
  return d_hasNext = nextCombination();
}

void TermTupleEnumeratorBase::failureReason(const std::vector<bool>& mask)
{
  if (Trace.isOn("inst-alg"))
  {
    traceMaskedVector("inst-alg", "failureReason", mask, d_termIndex);
  }
  d_disabledCombinations.add(mask, d_termIndex);  // record failure
  // update change prefix accordingly
  for (d_changePrefix = mask.size();
       d_changePrefix && !mask[d_changePrefix - 1];
       d_changePrefix--)
    ;
}

void TermTupleEnumeratorBase::next(/*out*/ std::vector<Node>& terms)
{
  Trace("inst-alg-rd") << "Try instantiation: " << d_termIndex << std::endl;
  terms.resize(d_variableCount);
  for (size_t variableIx = 0; variableIx < d_variableCount; variableIx++)
  {
    const Node t =
        d_termsSizes[variableIx] == 0
            ? Node::null()
            : d_termProducer->getTerm(variableIx, d_termIndex[variableIx]);
    terms[variableIx] = t;
    Trace("inst-alg-rd") << t << "  ";
    Assert(terms[variableIx].isNull()
           || terms[variableIx].getType().isComparableTo(
               d_quantifier[0][variableIx].getType()));
  }
  Trace("inst-alg-rd") << std::endl;
}

bool TermTupleEnumeratorBase::nextCombination()
{
  while (true)
  {
    Trace("inst-alg-rd") << "changePrefix " << d_changePrefix << std::endl;
    if (!nextCombinationAttempt())
    {
      return false;  // ran out of combinations
    }
    if (!d_disabledCombinations.find(d_termIndex, d_changePrefix))
    {
      return true;  // current combination vetted by disabled combinations
    }
  }
}

bool SocialTupleEnumerator::increaseScore()
{
  size_t increaseDigit;
  bool found = false;
  for (increaseDigit = 0; increaseDigit < d_variableCount; increaseDigit++)
  {
    const bool last = increaseDigit + 1 == d_variableCount;
    found = (!last && d_score[increaseDigit] < d_score[increaseDigit + 1])
            || (last && d_score[increaseDigit] < d_maxValue);
    if (found)
    {
      break;
    }
  }
  if (!found)
  {
    return false;
  }
  d_score[increaseDigit]++;
  std::fill_n(d_score.begin(), increaseDigit, 0);
  d_termIndex = d_score;
  Trace("inst-alg-rd") << "increased score: " << d_score << std::endl;
  return validatePermutation();
}

void StagedTupleEnumerator::initializeAttempts()
{
  d_currentStage = 0;
  // in the case of full effort we do at least one stage
  d_stageCount =
      std::max(*std::max_element(d_termsSizes.begin(), d_termsSizes.end()),
               static_cast<size_t>(1));

  Trace("inst-alg-rd") << "Will do " << d_stageCount
                       << " stages of instantiation." << std::endl;
}

bool StagedTupleEnumerator::increaseStageSum()
{
  const size_t lowerBound = d_currentStage + 1;
  Trace("inst-alg-rd") << "Try sum " << lowerBound << "..." << std::endl;
  d_currentStage = 0;
  for (size_t digit = d_termIndex.size();
       d_currentStage < lowerBound && digit--;)
  {
    const size_t missing = lowerBound - d_currentStage;
    const size_t maxValue = d_termsSizes[digit] ? d_termsSizes[digit] - 1 : 0;
    d_termIndex[digit] = std::min(missing, maxValue);
    d_currentStage += d_termIndex[digit];
  }
  return d_currentStage >= lowerBound;
}

bool StagedTupleEnumerator::increaseStage()
{
  d_changePrefix = d_variableCount;  // simply reset upon increase stage
  return d_env->d_increaseSum ? increaseStageSum() : increaseStageMax();
}

bool StagedTupleEnumerator::increaseStageMax()
{
  d_currentStage++;
  if (d_currentStage >= d_stageCount)
  {
    return false;
  }
  Trace("inst-alg-rd") << "Try stage " << d_currentStage << "..." << std::endl;
  // skipping some elements that have already been definitely seen
  // find the least significant digit that can be set to the current stage
  // TODO: should we skip all?
  std::fill(d_termIndex.begin(), d_termIndex.end(), 0);
  bool found = false;
  for (size_t digit = d_termIndex.size(); !found && digit--;)
  {
    if (d_termsSizes[digit] > d_currentStage)
    {
      found = true;
      d_termIndex[digit] = d_currentStage;
    }
  }
  Assert(found);
  return found;
}

bool StagedTupleEnumerator::nextCombinationAttempt()
{
  return nextCombinationInternal() || increaseStage();
}
/** Move onto the next combination, depending on the strategy. */
bool StagedTupleEnumerator::nextCombinationInternal()
{
  return d_env->d_increaseSum ? nextCombinationSum() : nextCombinationMax();
}

/** Find the next lexicographically smallest combination of terms that change
 * on the change prefix and their sum is equal to d_currentStage. */
bool StagedTupleEnumerator::nextCombinationMax()
{
  // look for the least significant digit, within change prefix,
  // that can be increased
  bool found = false;
  size_t increaseDigit = d_changePrefix;
  while (!found && increaseDigit--)
  {
    const size_t new_value = d_termIndex[increaseDigit] + 1;
    if (new_value < d_termsSizes[increaseDigit] && new_value <= d_currentStage)
    {
      d_termIndex[increaseDigit] = new_value;
      // send everything after the increased digit to 0
      std::fill(d_termIndex.begin() + increaseDigit + 1, d_termIndex.end(), 0);
      found = true;
    }
  }
  if (!found)
  {
    return false;  // nothing to increase
  }
  // check if the combination has at least one digit in the current stage,
  // since at least one digit was increased, no need for this in stage 1
  bool inStage = d_currentStage <= 1;
  for (size_t i = increaseDigit + 1; !inStage && i--;)
  {
    inStage = d_termIndex[i] >= d_currentStage;
  }
  if (!inStage)  // look for a digit that can increase to current stage
  {
    for (increaseDigit = d_variableCount, found = false;
         !found && increaseDigit--;)
    {
      found = d_termsSizes[increaseDigit] > d_currentStage;
    }
    if (!found)
    {
      return false;  // nothing to increase to the current stage
    }
    Assert(d_termsSizes[increaseDigit] > d_currentStage
           && d_termIndex[increaseDigit] < d_currentStage);
    d_termIndex[increaseDigit] = d_currentStage;
    // send everything after the increased digit to 0
    std::fill(d_termIndex.begin() + increaseDigit + 1, d_termIndex.end(), 0);
  }
  return true;
}

/** Find the next lexicographically smallest combination of terms that change
 * on the change prefix, each digit is within the current state,  and there is
 * at least one digit not in the previous stage. */
bool StagedTupleEnumerator::nextCombinationSum()
{
  size_t suffixSum = 0;
  bool found = false;
  size_t increaseDigit = d_termIndex.size();
  while (increaseDigit--)
  {
    const size_t newValue = d_termIndex[increaseDigit] + 1;
    found = suffixSum > 0 && newValue < d_termsSizes[increaseDigit]
            && increaseDigit < d_changePrefix;
    if (found)
    {
      // digit can be increased and suffix can be decreased
      d_termIndex[increaseDigit] = newValue;
      break;
    }
    suffixSum += d_termIndex[increaseDigit];
    d_termIndex[increaseDigit] = 0;
  }
  if (!found)
  {
    return false;
  }
  Assert(suffixSum > 0);
  // increaseDigit went up by one, hence, distribute (suffixSum - 1) in the
  // least significant digits
  suffixSum--;
  for (size_t digit = d_termIndex.size(); suffixSum > 0 && digit--;)
  {
    const size_t maxValue = d_termsSizes[digit] ? d_termsSizes[digit] - 1 : 0;
    d_termIndex[digit] = std::min(suffixSum, maxValue);
    suffixSum -= d_termIndex[digit];
  }
  Assert(suffixSum == 0);  // everything should have been distributed
  return true;
}

size_t BasicTermProducer::prepareTerms(size_t variableIx)
{
  Assert(variableIx < d_typeCache.size())
      << "mismatch " << variableIx << ":" << d_typeCache.size() << "\n";
  const TypeNode type_node = d_quantifier[0][variableIx].getType();
  d_typeCache[variableIx] = type_node;
  if (!ContainsKey(d_termDbList, type_node))
  {
    const size_t ground_terms_count = d_tdb->getNumTypeGroundTerms(type_node);
    std::map<Node, Node> repsFound;
    for (size_t j = 0; j < ground_terms_count; j++)
    {
      Node gt = d_tdb->getTypeGroundTerm(type_node, j);
      if (!options::cegqi() || !quantifiers::TermUtil::hasInstConstAttr(gt))
      {
        Node rep = d_qs.getRepresentative(gt);
        if (repsFound.find(rep) == repsFound.end())
        {
          repsFound[rep] = gt;
          d_termDbList[type_node].push_back(gt);
        }
      }
    }
  }

  Trace("inst-alg-rd") << "Instantiation Terms for child " << variableIx << ": "
                       << d_termDbList[type_node] << std::endl;
  return d_termDbList[type_node].size();
}

Node BasicTermProducer::getTerm(size_t variableIx, size_t term_index)
{
  const TypeNode type_node = d_typeCache[variableIx];
  Assert(term_index < d_termDbList[type_node].size());
  return d_termDbList[type_node][term_index];
}

/**
 * Enumerate ground terms as they come from a user-provided term pool
 */
class PoolTermProducer : public ITermProducer
{
 public:
  PoolTermProducer(Node quantifier, TermPools* tp, Node pool)
      : d_quantifier(quantifier), d_tp(tp), d_pool(pool)
  {
    Assert(d_pool.getKind() == kind::INST_POOL);
  }

  virtual ~PoolTermProducer() = default;

  /** gets the terms from the pool */
  size_t prepareTerms(size_t variableIx) override
  {
    Assert(d_pool.getNumChildren() > variableIx);
    // prepare terms from pool
    d_poolList[variableIx].clear();
    d_tp->getTermsForPool(d_pool[variableIx], d_poolList[variableIx]);
    Trace("pool-inst") << "Instantiation Terms for child " << variableIx << ": "
                       << d_poolList[variableIx] << std::endl;
    return d_poolList[variableIx].size();
  }
  Node getTerm(size_t variableIx, size_t term_index) override
  {
    Assert(term_index < d_poolList[variableIx].size());
    return d_poolList[variableIx][term_index];
  }

 protected:
  Node d_quantifier;
  /** Pointer to the term pool utility */
  TermPools* d_tp;
  /** The pool annotation */
  Node d_pool;
  /**  a list of terms for each id */
  std::map<size_t, std::vector<Node> > d_poolList;
};

TermTupleEnumeratorInterface* mkTermTupleEnumeratorLeximin(
    Node q, const TermTupleEnumeratorEnv* env, QuantifiersState& qs, TermDb* td)
{
  auto* termProducer = new BasicTermProducer(q, qs, td);
  return static_cast<TermTupleEnumeratorInterface*>(
      new SocialTupleEnumerator(q, env, termProducer));
}

TermTupleEnumeratorInterface* mkTermTupleEnumerator(
    Node q, const TermTupleEnumeratorEnv* env, QuantifiersState& qs, TermDb* td)
{
  auto* termProducer = new BasicTermProducer(q, qs, td);
  return static_cast<TermTupleEnumeratorInterface*>(
      new StagedTupleEnumerator(q, env, termProducer));
}
TermTupleEnumeratorInterface* mkTermTupleEnumeratorRd(
    Node q, const TermTupleEnumeratorEnv* env, RelevantDomain* rd)
{
  auto* termProducer = new RelevantDomainProducer(q, rd);
  return static_cast<TermTupleEnumeratorInterface*>(
      new StagedTupleEnumerator(q, env, termProducer));
}

TermTupleEnumeratorInterface* mkTermTupleEnumeratorPool(
    Node q, const TermTupleEnumeratorEnv* env, TermPools* tp, Node pool)
{
  auto* termProducer = new PoolTermProducer(q, tp, pool);
  return static_cast<TermTupleEnumeratorInterface*>(
      new StagedTupleEnumerator(q, env, termProducer));
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
