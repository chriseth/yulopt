import YulC.Mini.Util
import YulC.Mini.Syntax
import YulC.Mini.Semantics
import YulC.Mini.Evm
import YulC.Mini.Compiler
import YulC.Mini.Correctness
import YulC.Mini.Parser
import YulC.Mini.Optim.ConstFold
import YulC.Mini.Optim.Algebraic
import YulC.Mini.Optim.Flatten
import YulC.Mini.Optim.Peephole
import YulC.Mini.Optim
import YulC.Mini.Examples

/-!
# Verified mini Yul → mini-EVM compiler

A small but **proven correct** compiler from a subset of Yul to a
subset of the EVM stack machine. See `PLAN.md` §"Verified mini
compiler" for the high-level design.

## Subset

* **Expressions:** literals, variables, the binary builtins
  `add sub mul div mod and or xor lt gt eq`, and the unary builtin
  `iszero`.
* **Statements:** `let x := e` (declare a fresh local) and
  `x := e` (overwrite an existing local).

Distinct binders required (no shadowing). Programs are flat sequences
of statements.

## Mini-EVM target

A stack machine over `Word = BitVec 256` with `PUSH`, the binary
opcodes above, `ISZERO`, `DUPi`, `SWAPi` and `POP`. Arithmetic wraps
mod 2²⁵⁶ and division/modulo are unsigned with `n / 0 = n % 0 = 0`,
matching real EVM semantics.

## Module layout

| Module                       | Contents                                            |
|------------------------------|-----------------------------------------------------|
| `YulC.Mini.Util`             | Generic `List.setOpt` and lemmas.                   |
| `YulC.Mini.Syntax`           | Yul AST and `Env.lookup` / `Env.update`.            |
| `YulC.Mini.Semantics`        | Big-step evaluator + lemmas on `Env.update`.        |
| `YulC.Mini.Evm`              | Mini-EVM target language and interpreter.           |
| `YulC.Mini.Compiler`         | `Layout`, codegen, layout lemmas.                   |
| `YulC.Mini.Correctness`      | `Matches` invariant + `compile_correct` theorems.   |
| `YulC.Mini.Parser`           | Yul concrete-syntax recursive-descent parser.       |
| `YulC.Mini.Optim.ConstFold`  | Verified constant-folding optimizer pass.           |
| `YulC.Mini.Optim.Algebraic`  | Safe algebraic identities (Yul level).              |
| `YulC.Mini.Optim.Flatten`    | Block-flattening (Yul level).                       |
| `YulC.Mini.Optim.Peephole`   | `PUSH; POP` cancellation on bytecode.               |
| `YulC.Mini.Optim`            | Composed `optimize` pipeline.                       |
| `YulC.Mini.Examples`         | Worked examples discharged with `decide`.           |

## Main theorems

* `YulC.Mini.Program.compile_correct` — a closed program whose source
  semantics succeeds with environment `env'` compiles to bytecode
  which, run on the empty stack, terminates with a stack `Matches`-ing
  `env'`.
* `YulC.Mini.compileOptimized_correct` — same guarantee for the full
  optimised pipeline (`optimize` → `Program.compile` →
  `Bytecode.peephole`).
-/
