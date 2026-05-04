import YulC.Codegen.Asm

/-!
# JumpdestRemover

Drops `JUMPDEST` nodes whose tag is never referenced by any
`PUSHTAG`. Proof difficulty: easy.
-/
namespace YulC.Asm.JumpdestRemover
open YulC.Codegen

def run (a : Asm) : Asm := a  -- TODO

end YulC.Asm.JumpdestRemover
