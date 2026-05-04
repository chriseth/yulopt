import YulC.Syntax.Yul

/-!
# LoadResolver

`LoadResolver` (`L`) — alias-aware propagation of known
`mload`/`sload` values. See `PLAN.md` §4.4.
-/
namespace YulC.Yul.LoadResolver
open YulC.Syntax

def run (p : Program) : Program := p  -- TODO

end YulC.Yul.LoadResolver
