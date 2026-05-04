import YulC.Syntax.Parser
import YulC.Yul.Pipeline
import YulC.Codegen.YulToAsm
import YulC.Asm.Pipeline
import YulC.Assembler.Link

/-!
# Driver / CLI

Mirrors `solc --strict-assembly --optimize [--yul-optimizations …]
[--optimize-runs N]`. Wires Parser → Yul Pipeline → Codegen → Asm
Pipeline → Assembler.
-/
namespace YulC.Driver

def compileSource (src : String) (runs : Nat := 200) : Except String ByteArray := do
  let prog ← YulC.Syntax.Parser.parse src
  -- TODO: take user --yul-optimizations sequence
  let prog := prog
  let asm := YulC.Codegen.compile prog
  let asm := YulC.Asm.Pipeline.run runs asm
  pure (YulC.Assembler.link asm)

end YulC.Driver
