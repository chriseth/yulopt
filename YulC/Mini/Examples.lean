import YulC.Mini.Syntax
import YulC.Mini.Semantics
import YulC.Mini.Compiler
import YulC.Mini.Correctness
import YulC.Mini.Parser
import YulC.Mini.Optim.ConstFold
import YulC.Mini.Optim.Algebraic
import YulC.Mini.Optim.Flatten
import YulC.Mini.Optim

/-!
# Worked examples

Every example is checked twice:

1. The source semantics evaluates to the expected environment.
2. The compiler succeeds and the resulting bytecode runs to a stack
   that matches the expected environment.

Both proofs are discharged by `decide`, providing a fully checked
witness that the verified pipeline works on concrete inputs.
-/

namespace YulC.Mini

/-- `let a := 2; let b := 3; let c := add(mul(a, a), b)` -/
def example1 : Program :=
  [ .letDecl "a" (.lit 2),
    .letDecl "b" (.lit 3),
    .letDecl "c" (.bin .add (.bin .mul (.var "a") (.var "a")) (.var "b")) ]

example : Program.exec example1 [] =
    some [("c", 7), ("b", 3), ("a", 2)] := by decide

example :
    ∃ ops layout' stack',
      Program.compile example1 [] = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches [("c", 7), ("b", 3), ("a", 2)] layout' stack' := by
  apply Program.compile_correct
  decide

/-- `let a := 5; let b := 10; a := add(a, b); let c := iszero(sub(a, 15))` -/
def example2 : Program :=
  [ .letDecl "a" (.lit 5),
    .letDecl "b" (.lit 10),
    .assign  "a" (.bin .add (.var "a") (.var "b")),
    .letDecl "c" (.un .iszero (.bin .sub (.var "a") (.lit 15))) ]

example : Program.exec example2 [] =
    some [("c", 1), ("b", 10), ("a", 15)] := by decide

example :
    ∃ ops layout' stack',
      Program.compile example2 [] = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches [("c", 1), ("b", 10), ("a", 15)] layout' stack' := by
  apply Program.compile_correct
  decide

/-- Demonstrates `div`, `mod`, `lt`, `eq`, bitwise `and`. -/
def example3 : Program :=
  [ .letDecl "x"   (.lit 23),
    .letDecl "y"   (.lit 5),
    .letDecl "q"   (.bin .div (.var "x") (.var "y")),
    .letDecl "r"   (.bin .mod (.var "x") (.var "y")),
    .letDecl "lt"  (.bin .lt  (.var "r") (.var "y")),
    .letDecl "eq"  (.bin .eq  (.var "q") (.lit 4)),
    .letDecl "msk" (.bin .and (.var "x") (.lit 0xF)) ]

example :
    ∃ ops layout' stack',
      Program.compile example3 [] = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches
        [("msk", Nat.land 23 0xF), ("eq", 1), ("lt", 1), ("r", 3),
         ("q", 4), ("y", 5), ("x", 23)] layout' stack' := by
  apply Program.compile_correct
  decide

end YulC.Mini

/-! ## Parser examples

The parser is exercised on concrete Yul source: we round-trip through
`Program.parse` and then drive the verified compiler on the result.
-/

namespace YulC.Mini

/-- Same program as `example1`, written in concrete Yul syntax. -/
def example1Src : String :=
  "{
     let a := 2
     let b := 3
     let c := add(mul(a, a), b)
   }"

def example1ParsedOK : Bool :=
  match Program.parse example1Src with
  | .ok p   => p == example1
  | .error _ => false

example : example1ParsedOK = true := by native_decide

def example1ParsedExec : Bool :=
  match Program.parse example1Src with
  | .ok p  => Program.exec p [] == some [("c", 7), ("b", 3), ("a", 2)]
  | .error _ => false

example : example1ParsedExec = true := by native_decide

/-- Same program as `example2`, in concrete syntax with comments. -/
def example2Src : String :=
  "// fresh let-bindings
   let a := 5
   let b := 10
   /* in-place update */
   a := add(a, b)
   let c := iszero(sub(a, 15))"

def example2ParsedOK : Bool :=
  match Program.parse example2Src with
  | .ok p   => p == example2
  | .error _ => false

example : example2ParsedOK = true := by native_decide

/-- Demonstrate the full source-to-bytecode pipeline. The compiled
bytecode is non-empty and the layout has the expected size. -/
def example1CompiledOK : Bool :=
  match Program.compileSource example1Src with
  | .ok (some (ops, layout')) =>
      !ops.isEmpty && layout'.length == 3
  | _ => false

example : example1CompiledOK = true := by native_decide

/-! ### Block example

Demonstrates nested blocks (`Stmt.block`). Under the post-disambiguator
semantics we adopt, a block is just a sequencing construct: any
`let` it introduces lives in the enclosing scope (and the
no-shadowing `letDecl` rule prevents accidental capture).
-/

/-- `let a := 1; { let b := 2; let c := add(a, b) }`. -/
def exampleBlock : Program :=
  [ .letDecl "a" (.lit 1),
    .block [ .letDecl "b" (.lit 2),
             .letDecl "c" (.bin .add (.var "a") (.var "b")) ] ]

example : Program.exec exampleBlock [] =
    some [("c", 3), ("b", 2), ("a", 1)] := by decide

example :
    ∃ ops layout' stack',
      Program.compile exampleBlock [] = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches [("c", 3), ("b", 2), ("a", 1)] layout' stack' := by
  apply Program.compile_correct
  decide

/-- Concrete-syntax counterpart of `exampleBlock`, exercising the
parser's nested-block support. -/
def exampleBlockSrc : String :=
  "{
     let a := 1
     {
       let b := 2
       let c := add(a, b)
     }
   }"

def exampleBlockParsedOK : Bool :=
  match Program.parse exampleBlockSrc with
  | .ok p   => p == exampleBlock
  | .error _ => false

example : exampleBlockParsedOK = true := by native_decide

/-! ### Constant folding

The `Expr.fold` pass collapses constant subexpressions, and is proven
to preserve the semantics of any program. -/

/-- Pre-folding: contains the fully-constant arithmetic
`add(mul(2, 3), sub(10, 4))`. -/
def foldDemo : Program :=
  [ Stmt.letDecl "v" (.bin .add (.bin .mul (.lit 2) (.lit 3))
                                (.bin .sub (.lit 10) (.lit 4))) ]

/-- Post-folding: the entire expression collapses to `lit 12`. -/
example : (progFold foldDemo == [Stmt.letDecl "v" (.lit 12)]) = true := by
  native_decide

/-- Folded program executes identically to the unfolded one. -/
example : Program.exec (progFold foldDemo) [] = Program.exec foldDemo [] :=
  progFold_exec foldDemo []

/-! ### Algebraic simplification

The `progAlg` pass rewrites `add(x, 0) → x`, `mul(x, 1) → x`, etc. -/

/-- `let v := add(mul(a, 1), sub(0, 0))` — both arms simplify away. -/
def algDemo : Program :=
  [ Stmt.letDecl "a" (.lit 5),
    Stmt.letDecl "v" (.bin .add (.bin .mul (.var "a") (.lit 1))
                                (.bin .sub (.lit 0) (.lit 0))) ]

example : (progAlg algDemo ==
    [ Stmt.letDecl "a" (.lit 5),
      Stmt.letDecl "v" (.var "a") ]) = true := by
  native_decide

example : Program.exec (progAlg algDemo) [] = Program.exec algDemo [] :=
  progAlg_exec algDemo []

/-! ### Block flattening

The `progFlatten` pass splices nested blocks into the surrounding
sequence and drops outer block wrappers. -/

/-- A program with a redundantly nested block. -/
def flattenDemo : Program :=
  [ Stmt.block [Stmt.letDecl "a" (.lit 1),
                Stmt.block [Stmt.letDecl "b" (.lit 2)]] ]

example : (progFlatten flattenDemo ==
    [ Stmt.letDecl "a" (.lit 1), Stmt.letDecl "b" (.lit 2) ]) = true := by
  native_decide

example : Program.exec (progFlatten flattenDemo) [] =
          Program.exec flattenDemo [] :=
  progFlatten_exec flattenDemo []

/-! ### Composed pipeline

`optimize = progAlg ∘ progFold ∘ progFlatten`, end-to-end verified. -/

example : Program.exec (optimize foldDemo) [] = Program.exec foldDemo [] :=
  optimize_exec foldDemo []

example : Program.exec (optimize flattenDemo) [] =
          Program.exec flattenDemo [] :=
  optimize_exec flattenDemo []

/-- Demonstrate the verified runtime invariant on `example1`: the
compiled bytecode, run on the empty stack, yields a stack matching the
expected environment. (Uses `Program.compile` directly so the
`compile_correct` lemma applies cleanly.) -/
example :
    ∃ ops layout' stack',
      Program.compile example1 [] = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches [("c", 7), ("b", 3), ("a", 2)] layout' stack' := by
  apply Program.compile_correct
  decide

/-! ### End-to-end optimised pipeline (`compileOptimized`)

Source → `optimize` (Yul-level passes) → `Program.compile` (codegen)
→ `Bytecode.peephole`. The resulting bytecode is provably equivalent
to compiling the original source. -/

example :
    ∃ ops layout' stack',
      compileOptimized example1 = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches [("c", 7), ("b", 3), ("a", 2)] layout' stack' := by
  apply compileOptimized_correct
  decide

/-- A program where the algebraic pass exposes peephole opportunities
in the codegen output. The end-to-end pipeline still produces a stack
matching the source semantics. -/
example :
    ∃ ops layout' stack',
      compileOptimized algDemo = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches [("v", 5), ("a", 5)] layout' stack' := by
  apply compileOptimized_correct
  decide

/-! ### Bytecode showcase: optimizer in action

A short, human-readable pretty-printer for `Op`, plus an end-to-end
demo that prints the bytecode emitted by both the unoptimised and the
optimised pipelines on the same source program. The two produce
different opcode sequences, but both are provably correct against the
same source semantics. -/

/-- Compact textual rendering of a single opcode. -/
def Op.pretty : Op → String
  | .push n  => s!"PUSH {n.toNat}"
  | .bin .add => "ADD"
  | .bin .sub => "SUB"
  | .bin .mul => "MUL"
  | .bin .div => "DIV"
  | .bin .mod => "MOD"
  | .bin .and => "AND"
  | .bin .or  => "OR"
  | .bin .xor => "XOR"
  | .bin .lt  => "LT"
  | .bin .gt  => "GT"
  | .bin .eq  => "EQ"
  | .un  .iszero => "ISZERO"
  | .dup i   => s!"DUP{i}"
  | .swap i  => s!"SWAP{i}"
  | .pop     => "POP"

/-- Render a bytecode sequence as a newline-separated listing. -/
def prettyBytecode (ops : List Op) : String :=
  String.intercalate "\n" (ops.map Op.pretty)

/-- Helper that runs a (possibly failing) compilation and returns just
the opcode list, pretty-printed. -/
def showCompile (mr : Option (List Op × Layout)) : String :=
  match mr with
  | none           => "<compilation failed>"
  | some (ops, _)  => prettyBytecode ops

/-- A program that exercises both Yul-level passes and the bytecode
peephole pass:

* `mul(2, 3)` is **constant-folded** to `6`.
* `mul(a, 1)` is **algebraically simplified** to `a`.
* The resulting `add(6, a)` becomes a small straight-line snippet,
  and the `peephole` pass collapses any spurious `PUSH; POP` pairs
  the codegen happens to emit. -/
def demoOpt : Program :=
  [ .letDecl "a" (.lit 4),
    .letDecl "x" (.bin .add (.bin .mul (.lit 2) (.lit 3))
                            (.bin .mul (.var "a") (.lit 1))) ]

/-- Naive (unoptimised) bytecode for `demoOpt`. -/
example : showCompile (Program.compile demoOpt []) =
"PUSH 4
PUSH 2
PUSH 3
MUL
DUP2
PUSH 1
MUL
ADD" := by native_decide

/-- Optimised bytecode for `demoOpt`: the multiplications are gone. -/
example : showCompile (compileOptimized demoOpt) =
"PUSH 4
PUSH 6
DUP2
ADD" := by native_decide

/-- Both versions agree with the source semantics — and `compileOptimized`
is verified to do so for *every* program (`compileOptimized_correct`). -/
example :
    ∃ ops layout' stack',
      compileOptimized demoOpt = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches [("x", 10), ("a", 4)] layout' stack' := by
  apply compileOptimized_correct
  decide

-- Inspect the two outputs interactively:
--   #eval IO.println (showCompile (Program.compile demoOpt []))
--   #eval IO.println (showCompile (compileOptimized demoOpt))

end YulC.Mini
