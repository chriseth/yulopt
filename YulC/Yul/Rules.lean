import YulC.Syntax.Yul

/-!
# Algebraic rewrite rules

Shared rule list (`x+0 → x`, `mul(x,1) → x`, `iszero(iszero(b)) → b`
when boolean, `and(x, ~0) → x`, …) — mirrors Solidity's
`libsolutil`/`libevmasm` `RuleList.h`. Used by both the Yul
`ExpressionSimplifier` and the assembly-level CSE.

See `PLAN.md` §4.3.
-/
namespace YulC.Yul.Rules

end YulC.Yul.Rules
