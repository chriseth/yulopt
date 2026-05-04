import YulC.Mini.Util
import YulC.Mini.Syntax
import YulC.Mini.Semantics
import YulC.Mini.Evm
import YulC.Mini.Compiler

/-!
# Correctness of the mini compiler

`Matches env layout stack` is the simulation invariant tying the
source environment to the target stack via the compile-time layout:

* the stack and the layout have the same length;
* every variable visible in `env` reads back through the layout to
  the corresponding stack slot.

The proof proceeds in three layers:

1. `Expr.compile_correct`     — a compiled expression pushes its value.
2. `Stmt.compile_correct`     — a compiled statement preserves `Matches`.
3. `Program.compile_correct`  — induction on statements; the headline
   theorem is on programs starting from the empty environment.
-/

namespace YulC.Mini

/-- Simulation invariant relating a source environment to a target
stack via a `Layout`. -/
def Matches (env : Env) (layout : Layout) (stack : Stack) : Prop :=
  stack.length = layout.length ∧
  ∀ x, Env.lookup env x = (Layout.depth layout x).bind (fun d => stack[d]?)

namespace Matches

theorem length {env layout stack} (h : Matches env layout stack) :
    stack.length = layout.length := h.1

theorem empty : Matches [] [] [] := by
  refine ⟨rfl, ?_⟩
  intro x; simp

/-- Pushing an anonymous value preserves `Matches`. -/
theorem cons_none {env layout stack} (h : Matches env layout stack)
    (v : Word) : Matches env (none :: layout) (v :: stack) := by
  refine ⟨by simpa using h.1, fun x => ?_⟩
  have hx := h.2 x
  simp only [Layout.depth]
  cases hd : Layout.depth layout x <;> simp_all

/-- Pushing a named binder preserves `Matches`. -/
theorem cons_some {env layout stack} (h : Matches env layout stack)
    (x : Ident) (v : Word) :
    Matches ((x, v) :: env) (some x :: layout) (v :: stack) := by
  refine ⟨by simpa using h.1, fun y => ?_⟩
  by_cases hxy : x = y
  · subst hxy; simp
  · have hx := h.2 y
    simp only [Layout.depth, Env.lookup, hxy, if_false]
    cases hd : Layout.depth layout y <;> simp_all

end Matches

/-! ## Expression compilation -/

theorem Expr.compile_correct
    (e : Expr) (env : Env) (layout : Layout) (stack : Stack) (v : Word) :
    Matches env layout stack →
    Expr.eval e env = some v →
    ∃ ops, Expr.compile e layout = some ops ∧
           Bytecode.run ops stack = some (v :: stack) := by
  induction e generalizing layout stack v with
  | lit n =>
    intro _ heval
    simp at heval
    exact ⟨[Op.push n], rfl, by simp [heval]⟩
  | var x =>
    intro h heval
    simp at heval
    have hx := h.2 x
    rw [heval] at hx
    cases hd : Layout.depth layout x with
    | none => rw [hd] at hx; simp at hx
    | some d =>
      rw [hd] at hx; simp at hx
      exact ⟨[Op.dup (d + 1)], by simp [hd], by simp [hx.symm]⟩
  | un op a iha =>
    intro h heval
    simp at heval
    obtain ⟨av, hav, hop⟩ := heval
    obtain ⟨ca, hca, hra⟩ := iha layout stack av h hav
    refine ⟨ca ++ [Op.un op], by simp [hca], ?_⟩
    rw [Bytecode.run_append, hra]; simp [← hop]
  | bin op a b iha ihb =>
    intro h heval
    simp only [Expr.eval] at heval
    cases hav : a.eval env with
    | none => rw [hav] at heval; simp at heval
    | some av =>
    cases hbv : b.eval env with
    | none => rw [hav, hbv] at heval; simp at heval
    | some bv =>
      rw [hav, hbv] at heval; simp at heval
      obtain ⟨ca, hca, hra⟩ := iha layout stack av h hav
      obtain ⟨cb, hcb, hrb⟩ :=
        ihb (none :: layout) (av :: stack) bv (h.cons_none av) hbv
      refine ⟨ca ++ cb ++ [Op.bin op], by simp [hca, hcb], ?_⟩
      rw [Bytecode.run_append, Bytecode.run_append, hra]
      simp [hrb, ← heval]

/-! ## Statement compilation -/

mutual

theorem Stmt.compile_correct
    (s : Stmt) (env env' : Env) (layout : Layout) (stack : Stack) :
    Matches env layout stack →
    Stmt.exec s env = some env' →
    ∃ ops layout' stack',
      Stmt.compile s layout = some (ops, layout') ∧
      Bytecode.run ops stack = some stack' ∧
      Matches env' layout' stack' := by
  intro hM hexec
  cases s with
  | letDecl x e =>
    simp only [Stmt.exec] at hexec
    cases hv : e.eval env with
    | none => rw [hv] at hexec; simp at hexec
    | some v =>
    cases hl : Env.lookup env x with
    | some _ => rw [hv, hl] at hexec; simp at hexec
    | none =>
      rw [hv, hl] at hexec; simp at hexec
      subst hexec
      obtain ⟨copsE, hcoE, hruE⟩ :=
        Expr.compile_correct e env layout stack v hM hv
      exact ⟨copsE, some x :: layout, v :: stack, by simp [hcoE], hruE,
             hM.cons_some x v⟩
  | assign x e =>
    simp only [Stmt.exec] at hexec
    cases hv : e.eval env with
    | none => rw [hv] at hexec; simp at hexec
    | some v =>
      rw [hv] at hexec; simp only at hexec
      obtain ⟨copsE, hcoE, hruE⟩ :=
        Expr.compile_correct e env layout stack v hM hv
      -- `update` succeeded ⇒ `x` is bound ⇒ `depth` and stack-slot exist.
      have hxsome : Env.lookup env x ≠ none := fun hnone =>
        nomatch (Env.update_eq_none_of_lookup_eq_none env hnone) ▸ hexec
      have hM2 := hM.2 x
      cases hd : Layout.depth layout x with
      | none => rw [hd] at hM2; simp at hM2; exact absurd hM2 hxsome
      | some d =>
        rw [hd] at hM2; simp at hM2
        have hdlt : d < stack.length :=
          hM.length ▸ Layout.depth_lt_length hd
        cases hs : stack[d]? with
        | none      => rw [hs] at hM2; exact absurd hM2 hxsome
        | some vold =>
          obtain ⟨snew, hsnew⟩ := List.exists_setOpt stack d v hdlt
          refine ⟨copsE ++ [Op.swap (d + 1), Op.pop], layout, snew,
                  by simp [hcoE, hd], ?_, ?_, ?_⟩
          · rw [Bytecode.run_append, hruE]; simp [hs, hsnew]
          · rw [List.length_setOpt hsnew, hM.length]
          · intro y
            by_cases hxy : x = y
            · subst hxy
              rw [Env.update_lookup_self hexec, hd]
              simp [List.getElem?_setOpt_self hsnew]
            · rw [Env.update_lookup_other hexec hxy]
              have hMy := hM.2 y
              cases hdy : Layout.depth layout y with
              | none    => rw [hdy] at hMy; simp at hMy; simp [hMy]
              | some dy =>
                have hdy_ne : dy ≠ d := fun heq =>
                  hxy (Layout.depth_inj (heq ▸ hd) hdy)
                rw [hdy] at hMy; rw [hMy]
                simp [List.getElem?_setOpt_other hsnew hdy_ne]
  | block body =>
    -- Block as syntactic grouping reduces directly to `Program.compile_correct_aux`.
    simp only [Stmt.exec] at hexec
    rw [Stmt.compile]
    exact Program.compile_correct_aux body env env' layout stack hM hexec
termination_by sizeOf s

theorem Program.compile_correct_aux :
    ∀ (p : Program) (env env' : Env) (layout : Layout) (stack : Stack),
      Matches env layout stack →
      Program.exec p env = some env' →
      ∃ ops layout' stack',
        Program.compile p layout = some (ops, layout') ∧
        Bytecode.run ops stack = some stack' ∧
        Matches env' layout' stack' := by
  intro p env env' layout stack hM hexec
  match p with
  | [] =>
    simp at hexec
    exact ⟨[], layout, stack, rfl, rfl, hexec ▸ hM⟩
  | s :: rest =>
    simp only [Program.exec] at hexec
    cases h1 : Stmt.exec s env with
    | none => rw [h1] at hexec; simp at hexec
    | some env1 =>
      rw [h1] at hexec; simp only at hexec
      obtain ⟨ops1, layout1, stack1, hco1, hru1, hM1⟩ :=
        Stmt.compile_correct s env env1 layout stack hM h1
      obtain ⟨ops2, layout2, stack2, hco2, hru2, hM2⟩ :=
        Program.compile_correct_aux rest env1 env' layout1 stack1 hM1 hexec
      refine ⟨ops1 ++ ops2, layout2, stack2, ?_, ?_, hM2⟩
      · show Program.compile (s :: rest) layout = some (ops1 ++ ops2, layout2)
        unfold Program.compile; rw [hco1]; simp [hco2]
      · rw [Bytecode.run_append, hru1]; simp [hru2]
termination_by p _ _ _ _ _ _ => sizeOf p

end

/-- **End-to-end compiler correctness.**

For a closed program (starting from the empty environment), if the
source semantics succeeds with environment `env'`, the compiler emits
bytecode that, run on the empty stack, terminates with a stack
related to `env'` by `Matches`. -/
theorem Program.compile_correct
    (p : Program) (env' : Env) :
    Program.exec p [] = some env' →
    ∃ ops layout' stack',
      Program.compile p [] = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches env' layout' stack' := by
  intro hexec
  exact Program.compile_correct_aux p [] env' [] [] Matches.empty hexec

end YulC.Mini
