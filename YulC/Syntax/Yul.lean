
/-!
# Yul AST

Abstract syntax for Yul programs. See `PLAN.md` §3.
-/
namespace YulC.Syntax

/-- 256-bit EVM word literal. Placeholder until we commit to a concrete
representation (`BitVec 256` vs hand-rolled `Word256`). -/
abbrev Word := Nat

abbrev Ident := String

mutual
inductive Expr where
  | lit       (w : Word)
  | var       (x : Ident)
  | call      (f : Ident) (args : List Expr)
  deriving Inhabited

inductive Stmt where
  | block       (stmts : List Stmt)
  | letDecl     (xs : List Ident) (rhs : Option Expr)
  | assign      (xs : List Ident) (rhs : Expr)
  | ifS         (cond : Expr) (body : List Stmt)
  | switchS     (scrutinee : Expr)
                (cases : List (Word × List Stmt))
                (default : Option (List Stmt))
  | forS        (init : List Stmt) (cond : Expr)
                (post : List Stmt) (body : List Stmt)
  | breakS
  | continueS
  | leaveS
  | exprStmt    (e : Expr)
  | funDef      (name : Ident) (params : List Ident)
                (returns : List Ident) (body : List Stmt)
  deriving Inhabited
end

/-- A Yul object/program: a top-level block of statements. Sub-objects and
data sections (`object "C" { code … }`) will be added later. -/
structure Program where
  body : List Stmt
  deriving Inhabited

end YulC.Syntax
