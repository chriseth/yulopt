import YulC.Codegen.Asm

/-!
# Peephole optimizer

Local rewrites over the `Asm` opcode stream:
`PUSH x POP → ε`, `SWAP1 SWAP1 → ε`, `ISZERO ISZERO ISZERO → ISZERO`,
`tag JUMP JUMPDEST(tag) → JUMPDEST(tag)`, etc. Mirrors solc's
`PeepholeOptimiser.cpp`.
-/
namespace YulC.Asm.Peephole
open YulC.Codegen

def run (a : Asm) : Asm := a  -- TODO

end YulC.Asm.Peephole
