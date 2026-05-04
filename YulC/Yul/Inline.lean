import YulC.Syntax.Yul

/-!
# Inlining and specialisation

* `ExpressionInliner` (`e`)
* `FullInliner` (`i`)
* `FunctionSpecializer` (`F`)
* `EquivalentFunctionCombiner` (`v`)

See `PLAN.md` §4.5.
-/
namespace YulC.Yul.Inline
open YulC.Syntax

def expressionInliner           (p : Program) : Program := p  -- TODO
def fullInliner                 (p : Program) : Program := p  -- TODO
def functionSpecializer         (p : Program) : Program := p  -- TODO
def equivalentFunctionCombiner  (p : Program) : Program := p  -- TODO

end YulC.Yul.Inline
