import YulC.Codegen.Asm

/-!
# Basic-block / CFG construction over Asm

Splits an `Asm` into basic blocks at `JUMP`/`JUMPI`/`JUMPDEST`. Used by
JumpdestRemover, BlockDeduplicator, Inliner and per-block CSE.
-/
namespace YulC.Asm.Cfg

end YulC.Asm.Cfg
