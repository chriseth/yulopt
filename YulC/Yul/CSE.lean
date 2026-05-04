import YulC.Syntax.Yul

/-!
# Common Subexpression Elimination (Yul level)

`CommonSubexpressionEliminator` (`c`). See `PLAN.md` §4.4.
-/
namespace YulC.Yul.CSE
open YulC.Syntax

def run (p : Program) : Program := p  -- TODO

end YulC.Yul.CSE
