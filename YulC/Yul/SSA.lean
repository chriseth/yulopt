import YulC.Syntax.Yul

/-!
# Pseudo-SSA layer

* `ExpressionSplitter` (`x`)
* `SSATransform` (`a`) / `SSAReverser` (`V`)
* `Rematerialiser` (`m`) / `LiteralRematerialiser` (`T`)
* `ExpressionJoiner` (`j`)

See `PLAN.md` §4.2.
-/
namespace YulC.Yul.SSA
open YulC.Syntax

def expressionSplitter      (p : Program) : Program := p  -- TODO
def ssaTransform            (p : Program) : Program := p  -- TODO
def ssaReverser             (p : Program) : Program := p  -- TODO
def rematerialiser          (p : Program) : Program := p  -- TODO
def literalRematerialiser   (p : Program) : Program := p  -- TODO
def expressionJoiner        (p : Program) : Program := p  -- TODO

end YulC.Yul.SSA
