import YulC.Syntax.Yul
import YulC.Syntax.Parser
import YulC.Semantics.YulSem
import YulC.Semantics.EvmSem
import YulC.Yul.Pipeline
import YulC.Codegen.Asm
import YulC.Codegen.YulToAsm
import YulC.Asm.Pipeline
import YulC.Assembler.Link
import YulC.Driver.Main
import YulC.Mini

/-!
# YulC

Optimizing compiler from Yul to EVM bytecode, written in Lean 4. See
`PLAN.md` for the design and per-pass implementation/proof notes.
-/
