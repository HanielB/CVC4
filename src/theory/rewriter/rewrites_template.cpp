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

#include "theory/rewriter/rewrites.h"

#include "expr/node.h"
#include "expr/node_manager.h"
#include "theory/rewrite_db.h"
#include "util/string.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace rewriter {

void addRules(RewriteDb& db)
{
  NodeManager* nm = NodeManager::currentNM();

// Declarations
${decls}$

// Definitions
${defns}$

// Rules
${rules}$
}

const char* toString(DslPfRule drule)
{
  switch (drule)
  {
    case DslPfRule::FAIL: return "FAIL";
    case DslPfRule::REFL: return "REFL";
    case DslPfRule::EVAL: return "EVAL";
${printer}$
    default: Unreachable();
  }
}

std::ostream& operator<<(std::ostream& out, DslPfRule drule)
{
  out << toString(drule);
  return out;
}

}  // namespace rewriter
}  // namespace theory
}  // namespace cvc5
