import YulC.Syntax.Yul
import YulC.Yul.Rules

/-!
# Simplification passes

* `ExpressionSimplifier` (`s`)
* `ConditionalSimplifier` (`C`) / `ConditionalUnsimplifier` (`U`)
* `StructuralSimplifier` (`t`)
* `ControlFlowSimplifier` (`n`)

See `PLAN.md` §4.3.
-/
namespace YulC.Yul.Simplify
open YulC.Syntax

def expressionSimplifier    (p : Program) : Program := p  -- TODO
def conditionalSimplifier   (p : Program) : Program := p  -- TODO
def conditionalUnsimplifier (p : Program) : Program := p  -- TODO
def structuralSimplifier    (p : Program) : Program := p  -- TODO
def controlFlowSimplifier   (p : Program) : Program := p  -- TODO

end YulC.Yul.Simplify
