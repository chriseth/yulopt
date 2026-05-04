import YulC.Codegen.Asm

/-!
# ConstantOptimiser

Replace expensive literal pushes (`PUSH 0xFFFFFFFF…`) with cheaper
arithmetic equivalents (`PUSH N SHL`, `NOT`, etc.) when the
`bytes + runs * gas` score is lower.
-/
namespace YulC.Asm.ConstantOptimiser
open YulC.Codegen

def run (_runs : Nat) (a : Asm) : Asm := a  -- TODO

end YulC.Asm.ConstantOptimiser
