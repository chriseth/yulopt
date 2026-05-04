import YulC.Mini.Util
import YulC.Mini.Syntax
import YulC.Mini.Semantics

/-!
# Mini-EVM: target language

A simplified stack machine inspired by the EVM:

* operands are `Word`s (= `BitVec 256`);
* the stack is a `List Word` (head is the top);
* `Op.bin` / `Op.un` reuse the source-level `BinOp` / `UnOp` tags
  rather than introducing redundant opcode constructors;
* `dup i` / `swap i` use 1-based indices like real `DUPi` / `SWAPi`.

`Bytecode.run` is the deterministic small-step interpreter; we expose
the single algebraic property the compiler needs (`run_append`).
-/

namespace YulC.Mini

inductive Op where
  | push (n : Word)
  | bin  (op : BinOp)
  | un   (op : UnOp)
  | dup  (i : Nat)        -- 1-based, like EVM DUPi
  | swap (i : Nat)        -- 1-based, like EVM SWAPi (top with i-th below)
  | pop
  deriving Repr, Inhabited

abbrev Stack := List Word

namespace Op

@[simp] def step : Op → Stack → Option Stack
  | .push n,  s            => some (n :: s)
  | .bin bop, b :: a :: s  => some (bop.apply a b :: s)
  | .un  uop, a :: s       => some (uop.apply a :: s)
  | .dup i,   s            =>
    match s[i - 1]? with
    | some v => some (v :: s)
    | none   => none
  | .swap i,  v :: s       =>
    match s[i - 1]? with
    | some w =>
      match List.setOpt s (i - 1) v with
      | some s' => some (w :: s')
      | none    => none
    | none => none
  | .pop,     _ :: s       => some s
  | _, _ => none

end Op

namespace Bytecode

@[simp] def run : List Op → Stack → Option Stack
  | [],         s => some s
  | op :: rest, s =>
    match op.step s with
    | some s' => run rest s'
    | none    => none

/-- Sequencing distributes over bytecode concatenation. The single
algebraic identity on which the compiler's correctness rests. -/
theorem run_append (a b : List Op) (s : Stack) :
    Bytecode.run (a ++ b) s =
      match Bytecode.run a s with
      | some s' => Bytecode.run b s'
      | none    => none := by
  induction a generalizing s with
  | nil => simp
  | cons op rest ih =>
    simp only [List.cons_append, Bytecode.run]
    cases op.step s with
    | none    => rfl
    | some s' => simp [ih s']

end Bytecode

end YulC.Mini
