import YulC.Mini.Util
import YulC.Mini.Syntax
import YulC.Mini.Semantics
import YulC.Mini.Evm
import YulC.Mini.Compiler
import YulC.Mini.Optim
import YulC.Mini.Optim.Peephole

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
      exact ⟨[Op.dup (d + 1)], by simp [hd],
             by simp [Bytecode.run_dup, hx.symm]⟩
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

/-! ## Statement compilation

We strengthen the invariant from `Matches` to `Sim`: at statement
boundaries the layout is exactly the names of the environment (in
order) and the stack is exactly the values. `Sim` implies `Matches`,
so `Expr.compile_correct` is reused unchanged.

The structural shape of `Sim` lets us cleanly handle scoped constructs
(`block`, `iff`): inside the body the env grows by `inner ++ outer`
where `outer` mirrors the enclosing env (same names, possibly updated
values); on exit we drop `inner` from both env and stack and the layout
returns to the enclosing one. -/

/-- Stronger structural invariant tying env, layout, stack
elementwise. -/
def Sim (env : Env) (layout : Layout) (stack : Stack) : Prop :=
  layout = env.map (fun e => some e.fst) ∧ stack = env.map Prod.snd

namespace Sim

theorem empty : Sim [] [] [] := ⟨rfl, rfl⟩

theorem cons {env l s} (h : Sim env l s) (x : Ident) (v : Word) :
    Sim ((x, v) :: env) (some x :: l) (v :: s) :=
  ⟨by simp [h.1], by simp [h.2]⟩

end Sim

/-- Helper: name-list equality lifts through `(some ∘ fst)` mapping. -/
theorem map_some_fst_eq {l1 l2 : Env}
    (h : l1.map Prod.fst = l2.map Prod.fst) :
    l1.map (fun e : Ident × Word => some e.fst) =
      l2.map (fun e : Ident × Word => some e.fst) := by
  have h1 : l1.map (fun e : Ident × Word => some e.fst) =
            (l1.map Prod.fst).map some := by
    simp [List.map_map, Function.comp_def]
  have h2 : l2.map (fun e : Ident × Word => some e.fst) =
            (l2.map Prod.fst).map some := by
    simp [List.map_map, Function.comp_def]
  rw [h1, h2, h]

/-- `Env.lookup`, expressed as a depth-into-the-name-projection lookup
over the value-projection. -/
theorem Env.lookup_via_map (env : Env) (x : Ident) :
    Env.lookup env x =
      (Layout.depth (env.map fun e => some e.fst) x).bind
        (fun d => (env.map Prod.snd)[d]?) := by
  induction env with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨k, w⟩ := head
    by_cases hkx : k = x
    · subst hkx; simp
    · simp only [Env.lookup, hkx, if_false, List.map_cons, Layout.depth]
      rw [ih]
      cases hd : Layout.depth (rest.map fun e => some e.fst) x with
      | none => simp
      | some d => simp

/-- `Sim` implies `Matches`. -/
theorem Sim.toMatches {env l s} (h : Sim env l s) : Matches env l s := by
  obtain ⟨hl, hs⟩ := h
  refine ⟨by rw [hl, hs]; simp, ?_⟩
  intro x; rw [hl, hs]; exact Env.lookup_via_map env x

/-- The value-update lemma at the level of the `map snd` projection:
`update` corresponds to `setOpt` at the `depth` of the matching name. -/
theorem Env.update_map_snd {env env' : Env} {x : Ident} {v : Word} {d : Nat}
    (h : Env.update env x v = some env')
    (hd : Layout.depth (env.map fun e => some e.fst) x = some d) :
    List.setOpt (env.map Prod.snd) d v = some (env'.map Prod.snd) := by
  induction env generalizing env' d with
  | nil => simp at h
  | cons head tail ih =>
    obtain ⟨k, w⟩ := head
    by_cases hkx : k = x
    · subst hkx
      simp at h; subst h
      simp [Layout.depth] at hd; subst hd; simp
    · simp [hkx] at h; obtain ⟨env_rest, hrest, rfl⟩ := h
      simp only [List.map_cons, Layout.depth] at hd
      rw [if_neg hkx] at hd
      cases hd' : Layout.depth (tail.map fun e : Ident × Word => some e.fst) x with
      | none =>
        rw [hd'] at hd
        simp at hd
      | some d' =>
        rw [hd'] at hd
        simp at hd; subst hd
        simp [List.map_cons, ih hrest hd']

/-! ### Structural invariant: source execution only extends the
environment by prepending fresh inner bindings on top of an updated copy
of the outer environment. -/

mutual

theorem Stmt.exec_ext (s : Stmt) {env env' : Env}
    (h : Stmt.exec s env = some env') :
    ∃ k, env'.length = env.length + k ∧
         (env'.drop k).map Prod.fst = env.map Prod.fst := by
  cases s with
  | letDecl x e =>
    simp only [Stmt.exec] at h
    cases hv : e.eval env with
    | none => rw [hv] at h; simp at h
    | some v =>
      cases hl : Env.lookup env x with
      | some _ => rw [hv, hl] at h; simp at h
      | none => rw [hv, hl] at h; simp at h; subst h
                exact ⟨1, by simp, by simp⟩
  | assign x e =>
    simp only [Stmt.exec] at h
    cases hv : e.eval env with
    | none => rw [hv] at h; simp at h
    | some v =>
      rw [hv] at h; simp only at h
      exact ⟨0, by simp [Env.update_length h], by simp [Env.update_map_fst h]⟩
  | block body =>
    simp only [Stmt.exec] at h
    cases hb : Program.exec body env with
    | none      => rw [hb] at h; simp at h
    | some envI =>
      rw [hb] at h; simp only at h
      obtain rfl : env' = envI.drop (envI.length - env.length) := by
        simpa using h.symm
      obtain ⟨k, hlen, hnames⟩ := Program.exec_ext body hb
      refine ⟨0, ?_, ?_⟩
      · simp [List.length_drop, hlen]
      · simp [List.drop_drop, hlen, hnames]
  | iff cond body =>
    simp only [Stmt.exec] at h
    cases hc : cond.eval env with
    | none   => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h; simp only at h
      cases hb : Program.exec body env with
      | none      => rw [hb] at h; simp at h
      | some envI =>
        rw [hb] at h; simp only at h
        by_cases hcz : c = 0
        · simp [hcz] at h; subst h; exact ⟨0, by simp, by simp⟩
        · rw [if_neg hcz] at h
          obtain rfl : env' = envI.drop (envI.length - env.length) := by
            simpa using h.symm
          obtain ⟨k, hlen, hnames⟩ := Program.exec_ext body hb
          refine ⟨0, ?_, ?_⟩
          · simp [List.length_drop, hlen]
          · simp [List.drop_drop, hlen, hnames]
termination_by sizeOf s

theorem Program.exec_ext (p : Program) {env env' : Env}
    (h : Program.exec p env = some env') :
    ∃ k, env'.length = env.length + k ∧
         (env'.drop k).map Prod.fst = env.map Prod.fst := by
  match p with
  | [] => simp at h; subst h; exact ⟨0, by simp, by simp⟩
  | s :: rest =>
    simp only [Program.exec] at h
    cases h1 : Stmt.exec s env with
    | none      => rw [h1] at h; simp at h
    | some env1 =>
      rw [h1] at h; simp only at h
      obtain ⟨k1, hlen1, hnames1⟩ := Stmt.exec_ext s h1
      obtain ⟨k2, hlen2, hnames2⟩ := Program.exec_ext rest h
      refine ⟨k1 + k2, by omega, ?_⟩
      have : env'.drop (k1 + k2) = (env'.drop k2).drop k1 := by
        rw [List.drop_drop]; congr 1; omega
      rw [this]
      have hmap : (env'.drop k2).map Prod.fst = env1.map Prod.fst := hnames2
      have hgoal : (env'.drop k2 |>.drop k1).map Prod.fst =
             (env1.drop k1).map Prod.fst := by
        rw [List.map_drop, hmap, ← List.map_drop]
      rw [hgoal, hnames1]
termination_by sizeOf p

end

/-! ### Statement compile-correctness with `Sim` -/

mutual

theorem Stmt.compile_correct
    (s : Stmt) (env env' : Env) (layout : Layout) (stack : Stack) :
    Sim env layout stack →
    Stmt.exec s env = some env' →
    ∃ ops layout' stack',
      Stmt.compile s layout = some (ops, layout') ∧
      Bytecode.run ops stack = some stack' ∧
      Sim env' layout' stack' := by
  intro hS hexec
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
        Expr.compile_correct e env layout stack v hS.toMatches hv
      exact ⟨copsE, some x :: layout, v :: stack, by simp [hcoE], hruE,
             hS.cons x v⟩
  | assign x e =>
    simp only [Stmt.exec] at hexec
    cases hv : e.eval env with
    | none => rw [hv] at hexec; simp at hexec
    | some v =>
      rw [hv] at hexec; simp only at hexec
      have hM := hS.toMatches
      obtain ⟨copsE, hcoE, hruE⟩ :=
        Expr.compile_correct e env layout stack v hM hv
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
                  by simp [hcoE, hd], ?_, ?_⟩
          · rw [Bytecode.run_append, hruE]
            simp [Bytecode.run_swap_cons, hs, hsnew]
          · refine ⟨?_, ?_⟩
            · rw [hS.1, map_some_fst_eq (Env.update_map_fst hexec).symm]
            · have hd' : Layout.depth (env.map fun e => some e.fst) x = some d := by
                rw [← hS.1]; exact hd
              have hupd := Env.update_map_snd hexec hd'
              rw [hS.2] at hsnew
              rw [hupd] at hsnew
              exact (Option.some.inj hsnew).symm
  | block body =>
    simp only [Stmt.exec] at hexec
    cases hb : Program.exec body env with
    | none      => rw [hb] at hexec; simp at hexec
    | some envI =>
      rw [hb] at hexec; simp only at hexec
      obtain ⟨opsB, lB, stackB, hcoB, hruB, hSB⟩ :=
        Program.compile_correct_aux body env envI layout stack hS hb
      -- Layout extension and length facts.
      have hLext : lB = envI.map (fun e => some e.fst) := hSB.1
      have hSext : stackB = envI.map Prod.snd := hSB.2
      have henvLen : envI.length ≥ env.length := by
        obtain ⟨k, hk, _⟩ := Program.exec_ext body hb
        omega
      have hkEq : lB.length - layout.length = envI.length - env.length := by
        rw [hLext, hS.1]; simp
      have hStackLen : stackB.length = envI.length := by
        rw [hSext]; simp
      have hkBound : lB.length - layout.length ≤ stackB.length := by
        rw [hStackLen, hkEq]; omega
      -- Compile target.
      refine ⟨opsB ++ List.replicate (lB.length - layout.length) Op.pop,
              layout, stackB.drop (lB.length - layout.length),
              ?_, ?_, ?_⟩
      · simp only [Stmt.compile, hcoB]
      · rw [Bytecode.run_append, hruB]
        simp [Bytecode.run_replicate_pop _ _ hkBound]
      · obtain rfl : env' = envI.drop (envI.length - env.length) := by
          simpa using hexec.symm
        refine ⟨?_, ?_⟩
        · obtain ⟨k', hk', hnames⟩ := Program.exec_ext body hb
          have hk_eq : envI.length - env.length = k' := by omega
          rw [hk_eq, hS.1]
          exact map_some_fst_eq hnames.symm
        · rw [hSext]
          obtain ⟨k', hk', _⟩ := Program.exec_ext body hb
          have hk_eq : envI.length - env.length = k' := by omega
          rw [hkEq, hk_eq, ← List.map_drop]
  | iff cond body =>
    simp only [Stmt.exec] at hexec
    cases hc : cond.eval env with
    | none   => rw [hc] at hexec; simp at hexec
    | some c =>
      rw [hc] at hexec; simp only at hexec
      cases hb : Program.exec body env with
      | none      => rw [hb] at hexec; simp at hexec
      | some envI =>
        rw [hb] at hexec; simp only at hexec
        obtain ⟨copsC, hcoC, hruC⟩ :=
          Expr.compile_correct cond env layout stack c hS.toMatches hc
        obtain ⟨opsB, lB, stackB, hcoB, hruB, hSB⟩ :=
          Program.compile_correct_aux body env envI layout stack hS hb
        have hLext : lB = envI.map (fun e => some e.fst) := hSB.1
        have hSext : stackB = envI.map Prod.snd := hSB.2
        have henvLen : envI.length ≥ env.length := by
          obtain ⟨k, hk, _⟩ := Program.exec_ext body hb
          omega
        have hkEq : lB.length - layout.length = envI.length - env.length := by
          rw [hLext, hS.1]; simp
        have hStackLen : stackB.length = envI.length := by
          rw [hSext]; simp
        have hkBound : lB.length - layout.length ≤ stackB.length := by
          rw [hStackLen, hkEq]; omega
        have hLenStack : stack.length = layout.length := by
          rw [hS.1, hS.2]; simp
        have hLenDrop :
            (stackB.drop (lB.length - layout.length)).length = stack.length := by
          rw [List.length_drop, hStackLen, hkEq, hLenStack, hS.1]
          simp; omega
        by_cases hcz : c = 0
        · -- c = 0 branch: body bytecode is emitted but skipped at runtime.
          simp [hcz] at hexec; subst hexec
          refine ⟨copsC ++ [Op.iff (opsB ++ List.replicate
                                      (lB.length - layout.length) Op.pop)],
                  layout, stack, ?_, ?_, hS⟩
          · simp only [Stmt.compile, hcoC, hcoB]
          · rw [Bytecode.run_append, hruC]
            show Bytecode.run [Op.iff _] (c :: stack) = some stack
            simp [Bytecode.run, hcz]
        · -- c ≠ 0 branch: body bytecode runs.
          rw [if_neg hcz] at hexec
          obtain rfl : env' = envI.drop (envI.length - env.length) := by
            simpa using hexec.symm
          refine ⟨copsC ++
                  [Op.iff (opsB ++ List.replicate (lB.length - layout.length)
                                                  Op.pop)],
                  layout, stackB.drop (lB.length - layout.length), ?_, ?_, ?_⟩
          · simp only [Stmt.compile, hcoC, hcoB]
          · rw [Bytecode.run_append, hruC]
            show Bytecode.run [Op.iff _] (c :: stack) =
                 some (stackB.drop (lB.length - layout.length))
            simp only [Bytecode.run, hcz, if_false]
            rw [Bytecode.run_append, hruB]
            dsimp only
            rw [Bytecode.run_replicate_pop _ _ hkBound]
            simp [hLenDrop]
          · refine ⟨?_, ?_⟩
            · obtain ⟨k', hk', hnames⟩ := Program.exec_ext body hb
              have hk_eq : envI.length - env.length = k' := by omega
              rw [hk_eq, hS.1]
              exact map_some_fst_eq hnames.symm
            · rw [hSext]
              obtain ⟨k', hk', _⟩ := Program.exec_ext body hb
              have hk_eq : envI.length - env.length = k' := by omega
              rw [hkEq, hk_eq, ← List.map_drop]
termination_by sizeOf s

theorem Program.compile_correct_aux
    (p : Program) (env env' : Env) (layout : Layout) (stack : Stack) :
    Sim env layout stack →
    Program.exec p env = some env' →
    ∃ ops layout' stack',
      Program.compile p layout = some (ops, layout') ∧
      Bytecode.run ops stack = some stack' ∧
      Sim env' layout' stack' := by
  intro hS hexec
  match p with
  | [] =>
    simp at hexec
    exact ⟨[], layout, stack, rfl, by simp, hexec ▸ hS⟩
  | s :: rest =>
    simp only [Program.exec] at hexec
    cases h1 : Stmt.exec s env with
    | none => rw [h1] at hexec; simp at hexec
    | some env1 =>
      rw [h1] at hexec; simp only at hexec
      obtain ⟨ops1, layout1, stack1, hco1, hru1, hS1⟩ :=
        Stmt.compile_correct s env env1 layout stack hS h1
      obtain ⟨ops2, layout2, stack2, hco2, hru2, hS2⟩ :=
        Program.compile_correct_aux rest env1 env' layout1 stack1 hS1 hexec
      refine ⟨ops1 ++ ops2, layout2, stack2, ?_, ?_, hS2⟩
      · show Program.compile (s :: rest) layout = some (ops1 ++ ops2, layout2)
        unfold Program.compile; rw [hco1]; simp [hco2]
      · rw [Bytecode.run_append, hru1]; simp [hru2]
termination_by sizeOf p

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
  obtain ⟨ops, lay', st', hco, hru, hS⟩ :=
    Program.compile_correct_aux p [] env' [] [] Sim.empty hexec
  exact ⟨ops, lay', st', hco, hru, hS.toMatches⟩

/-! ## End-to-end *optimised* pipeline (Yul → optimised bytecode)

`compileOptimized` runs the full verified pipeline:

    Yul source
      → optimize           (flatten, fold, algebraic — `YulC.Mini.Optim`)
      → Program.compile    (codegen — above)
      → Bytecode.peephole  (PUSH; POP cancellation — `Optim.Peephole`)

The headline theorem `compileOptimized_correct` is the optimised
counterpart of `Program.compile_correct`: the same `Matches`
postcondition, but for the optimised bytecode. -/

/-- Optimise, compile, then peephole-rewrite the resulting bytecode. -/
def compileOptimized (p : Program) : Option (List Op × Layout) :=
  match Program.compile (optimize p) [] with
  | some (ops, layout') => some (Bytecode.peephole ops, layout')
  | none                => none

/-- **End-to-end optimised compiler correctness.**

If the source program runs to environment `env'`, then the optimised
bytecode (post-peephole) runs on the empty stack to a stack matching
`env'` via `Matches`. Proof: `optimize_exec` preserves semantics, so
apply `Program.compile_correct` to the optimised program and commute
through `Bytecode.peephole_run`. -/
theorem compileOptimized_correct (p : Program) (env' : Env)
    (hexec : Program.exec p [] = some env') :
    ∃ ops layout' stack',
      compileOptimized p = some (ops, layout') ∧
      Bytecode.run ops [] = some stack' ∧
      Matches env' layout' stack' := by
  have hexec' : Program.exec (optimize p) [] = some env' := by
    rw [optimize_exec]; exact hexec
  obtain ⟨ops, layout', stack', hcomp, hrun, hM⟩ :=
    Program.compile_correct (optimize p) env' hexec'
  refine ⟨Bytecode.peephole ops, layout', stack', ?_, ?_, hM⟩
  · simp [compileOptimized, hcomp]
  · rw [Bytecode.peephole_run]; exact hrun

end YulC.Mini
