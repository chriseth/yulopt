import YulC.Syntax.Yul

/-!
# Dead-code & data-flow passes

* `DeadCodeEliminator` (`D`)
* `UnusedPruner` (`u`) — always run, even with empty user sequence
* `UnusedAssignEliminator` (`r`)
* `UnusedStoreEliminator` (`S`)
* `EqualStoreEliminator` (`E`)
* `UnusedFunctionParameterPruner` (`p`)
* `CircularReferencesPruner` (`l`)

See `PLAN.md` §4.3 / §4.4.
-/
namespace YulC.Yul.DCE
open YulC.Syntax

def deadCodeEliminator              (p : Program) : Program := p  -- TODO
def unusedPruner                    (p : Program) : Program := p  -- TODO
def unusedAssignEliminator          (p : Program) : Program := p  -- TODO
def unusedStoreEliminator           (p : Program) : Program := p  -- TODO
def equalStoreEliminator            (p : Program) : Program := p  -- TODO
def unusedFunctionParameterPruner   (p : Program) : Program := p  -- TODO
def circularReferencesPruner        (p : Program) : Program := p  -- TODO

end YulC.Yul.DCE
