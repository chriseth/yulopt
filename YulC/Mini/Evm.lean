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
  /-- Structured conditional. Pops the cond from the top of the stack;
  if non-zero, runs `body` (which must be **stack-balanced**: same
  height in/out). A separate lowering pass to flat EVM `JUMPI`/
  `JUMPDEST` is intended as future work. -/
  | iff  (body : List Op)
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
  -- `Op.iff` is multi-step: handled by `Bytecode.run` directly.
  | _, _ => none

end Op

namespace Bytecode

/-- Bytecode interpreter. Linear ops are dispatched to `Op.step`;
`Op.iff body` pops the condition and conditionally runs `body`,
requiring it to be stack-balanced. -/
def run : List Op → Stack → Option Stack
  | [],                s  => some s
  | (.iff body) :: rest, [] => none
  | (.iff body) :: rest, c :: s =>
    if c = 0 then run rest s
    else match run body s with
         | some s' => if s'.length = s.length then run rest s' else none
         | none    => none
  | op :: rest,        s  =>
    match op.step s with
    | some s' => run rest s'
    | none    => none
termination_by p _ => sizeOf p
decreasing_by
  all_goals (simp_wf; try omega)
  all_goals (simp_wf; first | (decreasing_trivial) | (decreasing_tactic))

@[simp] theorem run_nil (s : Stack) : Bytecode.run [] s = some s := by
  simp [run]

/-- Unfold `run` on a `push` instruction. -/
@[simp] theorem run_push (n : Word) (rest : List Op) (s : Stack) :
    Bytecode.run (.push n :: rest) s = Bytecode.run rest (n :: s) := by
  simp [run, Op.step]

@[simp] theorem run_un_cons (op : UnOp) (rest : List Op) (a : Word) (s : Stack) :
    Bytecode.run (.un op :: rest) (a :: s) = Bytecode.run rest (op.apply a :: s) := by
  simp [run, Op.step]

@[simp] theorem run_un_nil (op : UnOp) (rest : List Op) :
    Bytecode.run (.un op :: rest) [] = none := by
  simp [run, Op.step]

@[simp] theorem run_bin_cons2 (op : BinOp) (rest : List Op) (b a : Word) (s : Stack) :
    Bytecode.run (.bin op :: rest) (b :: a :: s) =
      Bytecode.run rest (op.apply a b :: s) := by
  simp [run, Op.step]

@[simp] theorem run_bin_underflow_nil (op : BinOp) (rest : List Op) :
    Bytecode.run (.bin op :: rest) [] = none := by
  simp [run, Op.step]

@[simp] theorem run_bin_underflow_one (op : BinOp) (rest : List Op) (a : Word) :
    Bytecode.run (.bin op :: rest) [a] = none := by
  simp [run, Op.step]

@[simp] theorem run_pop_cons (rest : List Op) (a : Word) (s : Stack) :
    Bytecode.run (.pop :: rest) (a :: s) = Bytecode.run rest s := by
  simp [run, Op.step]

@[simp] theorem run_pop_nil (rest : List Op) :
    Bytecode.run (.pop :: rest) [] = none := by
  simp [run, Op.step]

/-- Running `k` `POP` instructions drops `k` elements from the stack
(when the stack is at least `k` deep). -/
theorem run_replicate_pop (k : Nat) (s : Stack) (h : k ≤ s.length) :
    Bytecode.run (List.replicate k Op.pop) s = some (s.drop k) := by
  induction k generalizing s with
  | zero => simp
  | succ n ih =>
    cases s with
    | nil => simp at h
    | cons a rest =>
      simp only [List.replicate, List.drop, run_pop_cons]
      exact ih rest (by simpa using h)

theorem run_dup (i : Nat) (rest : List Op) (s : Stack) :
    Bytecode.run (.dup i :: rest) s =
      match s[i - 1]? with
      | some v => Bytecode.run rest (v :: s)
      | none   => none := by
  simp only [run, Op.step]
  cases s[i - 1]? <;> simp

theorem run_swap_cons (i : Nat) (rest : List Op) (v : Word) (s : Stack) :
    Bytecode.run (.swap i :: rest) (v :: s) =
      match s[i - 1]?, List.setOpt s (i - 1) v with
      | some w, some s' => Bytecode.run rest (w :: s')
      | _, _            => none := by
  simp only [run, Op.step]
  cases s[i - 1]? with
  | none   => rfl
  | some _ => cases List.setOpt s (i - 1) v <;> rfl

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
    cases op with
    | iff body =>
      cases s with
      | nil =>
        show Bytecode.run (.iff body :: (rest ++ b)) [] =
          match Bytecode.run (.iff body :: rest) [] with
          | some s' => Bytecode.run b s'
          | none    => none
        unfold Bytecode.run; rfl
      | cons c s' =>
        show Bytecode.run (.iff body :: (rest ++ b)) (c :: s') =
          match Bytecode.run (.iff body :: rest) (c :: s') with
          | some s'' => Bytecode.run b s''
          | none     => none
        simp only [Bytecode.run]
        split
        · rw [ih]
        · split
          · split <;> simp [ih]
          · rfl
    | push n =>
      show Bytecode.run (.push n :: (rest ++ b)) s =
        match Bytecode.run (.push n :: rest) s with
        | some s' => Bytecode.run b s'
        | none    => none
      simp [Bytecode.run, ih]
    | pop =>
      show Bytecode.run (.pop :: (rest ++ b)) s =
        match Bytecode.run (.pop :: rest) s with
        | some s' => Bytecode.run b s'
        | none    => none
      cases s with
      | nil       => simp [Bytecode.run]
      | cons _ _  => simp [Bytecode.run, ih]
    | bin bop =>
      show Bytecode.run (.bin bop :: (rest ++ b)) s =
        match Bytecode.run (.bin bop :: rest) s with
        | some s' => Bytecode.run b s'
        | none    => none
      cases s with
      | nil => simp [Bytecode.run]
      | cons _ s1 =>
        cases s1 with
        | nil      => simp [Bytecode.run]
        | cons _ _ => simp [Bytecode.run, ih]
    | un uop =>
      show Bytecode.run (.un uop :: (rest ++ b)) s =
        match Bytecode.run (.un uop :: rest) s with
        | some s' => Bytecode.run b s'
        | none    => none
      cases s with
      | nil      => simp [Bytecode.run]
      | cons _ _ => simp [Bytecode.run, ih]
    | dup i =>
      show Bytecode.run (.dup i :: (rest ++ b)) s =
        match Bytecode.run (.dup i :: rest) s with
        | some s' => Bytecode.run b s'
        | none    => none
      simp only [Bytecode.run, Op.step]
      cases s[i - 1]? with
      | none   => rfl
      | some _ => simp [ih]
    | swap i =>
      show Bytecode.run (.swap i :: (rest ++ b)) s =
        match Bytecode.run (.swap i :: rest) s with
        | some s' => Bytecode.run b s'
        | none    => none
      cases s with
      | nil => simp [Bytecode.run]
      | cons v s1 =>
        simp only [Bytecode.run, Op.step]
        cases s1[i - 1]? with
        | none => rfl
        | some _ =>
          cases List.setOpt s1 (i - 1) v with
          | none   => rfl
          | some _ => simp [ih]

end Bytecode

end YulC.Mini
