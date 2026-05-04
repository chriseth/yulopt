import YulC.Syntax.Yul

/-!
# Disambiguator

Renames every binder so all identifiers are globally unique.
Prerequisite for every other Yul-level pass. See `PLAN.md` §4.1.

Proof difficulty: easy (α-renaming is semantics-preserving).
-/
namespace YulC.Yul.Disambiguator
open YulC.Syntax

def run (p : Program) : Program := p  -- TODO

end YulC.Yul.Disambiguator
