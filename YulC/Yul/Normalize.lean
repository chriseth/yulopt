import YulC.Syntax.Yul

/-!
# Normal-form passes

* `FunctionHoister` (`h`)
* `FunctionGrouper` (`g`)
* `ForLoopInitRewriter` (`o`)
* `ForLoopConditionIntoBody` (`I`) / `ForLoopConditionOutOfBody` (`O`)
* `VarDeclInitializer` (`d`)
* `BlockFlattener` (`f`)

See `PLAN.md` §4.1.
-/
namespace YulC.Yul.Normalize
open YulC.Syntax

def hoistFunctions          (p : Program) : Program := p  -- TODO
def groupFunctions          (p : Program) : Program := p  -- TODO
def rewriteForInit          (p : Program) : Program := p  -- TODO
def forCondIntoBody         (p : Program) : Program := p  -- TODO
def forCondOutOfBody        (p : Program) : Program := p  -- TODO
def varDeclInitializer      (p : Program) : Program := p  -- TODO
def flattenBlocks           (p : Program) : Program := p  -- TODO

end YulC.Yul.Normalize
