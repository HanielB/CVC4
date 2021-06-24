/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generated rewrites
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY_REWRITER_REWRITES_H
#define CVC5__THEORY_REWRITER_REWRITES_H

#include "expr/node.h"

namespace cvc5 {
namespace theory {

class RewriteDb;

namespace rewriter {

enum class DslPfRule : uint32_t
{
  FAIL = 0,
  REFL,
  EVAL,
  ${rule_ids}$
};

void addRules(RewriteDb& db);

/**
 * Converts a DSL proof rule to a string.
 * @param drule The DSL proof rule
 * @return The name of the DSL proof rule
 */
const char* toString(DslPfRule drule);
/**
 * Writes a DSL proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param drule The DSL proof rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, DslPfRule drule);
}
}  // namespace theory
}  // namespace cvc5

#endif
