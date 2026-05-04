import YulC.Codegen.Asm

/-!
# BlockDeduplicator

Hash basic blocks under canonical tag-renaming, merge equal blocks
behind a single tag, redirect references.
-/
namespace YulC.Asm.BlockDeduplicator
open YulC.Codegen

def run (a : Asm) : Asm := a  -- TODO

end YulC.Asm.BlockDeduplicator
