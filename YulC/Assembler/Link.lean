import YulC.Codegen.Asm

/-!
# Assembler / linker

Resolve symbolic tags to byte offsets (iterative push-size resolution
because PUSH widths grow with offsets), emit final EVM bytecode and
auxdata. See `PLAN.md` Phase J.
-/
namespace YulC.Assembler
open YulC.Codegen

def link (_a : Asm) : ByteArray := .empty  -- TODO

end YulC.Assembler
