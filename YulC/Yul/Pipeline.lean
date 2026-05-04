import YulC.Syntax.Yul
import YulC.Yul.Disambiguator
import YulC.Yul.Normalize
import YulC.Yul.SSA
import YulC.Yul.Simplify
import YulC.Yul.DCE
import YulC.Yul.CSE
import YulC.Yul.LoadResolver
import YulC.Yul.LICM
import YulC.Yul.Inline

/-!
# Yul optimizer pipeline driver

Step-letter parser, bracket-loop fixpoint (cap 12), mandatory pre/post
cleanup sequences, default sequence, `--yul-optimizations` override.

See `PLAN.md` §4.6.
-/
namespace YulC.Yul.Pipeline
open YulC.Syntax

inductive Step
  | disambiguator
  | functionHoister | functionGrouper
  | forLoopInitRewriter
  | forLoopCondIntoBody | forLoopCondOutOfBody
  | varDeclInitializer | blockFlattener
  | expressionSplitter | ssaTransform | ssaReverser
  | rematerialiser | literalRematerialiser | expressionJoiner
  | expressionSimplifier
  | conditionalSimplifier | conditionalUnsimplifier
  | structuralSimplifier | controlFlowSimplifier
  | deadCodeEliminator | unusedPruner | unusedAssignEliminator
  | unusedStoreEliminator | equalStoreEliminator
  | unusedFunctionParameterPruner | circularReferencesPruner
  | loadResolver | loopInvariantCodeMotion
  | commonSubexpressionEliminator
  | expressionInliner | fullInliner
  | functionSpecializer | equivalentFunctionCombiner

inductive PipelineItem
  | step (s : Step)
  | loop (body : List PipelineItem)

def parseSequence (_s : String) : Except String (List PipelineItem) :=
  .error "step-letter parser not implemented"

def runStep : Step → Program → Program
  | .disambiguator                  => Disambiguator.run
  | .functionHoister                => Normalize.hoistFunctions
  | .functionGrouper                => Normalize.groupFunctions
  | .forLoopInitRewriter            => Normalize.rewriteForInit
  | .forLoopCondIntoBody            => Normalize.forCondIntoBody
  | .forLoopCondOutOfBody           => Normalize.forCondOutOfBody
  | .varDeclInitializer             => Normalize.varDeclInitializer
  | .blockFlattener                 => Normalize.flattenBlocks
  | .expressionSplitter             => SSA.expressionSplitter
  | .ssaTransform                   => SSA.ssaTransform
  | .ssaReverser                    => SSA.ssaReverser
  | .rematerialiser                 => SSA.rematerialiser
  | .literalRematerialiser          => SSA.literalRematerialiser
  | .expressionJoiner               => SSA.expressionJoiner
  | .expressionSimplifier           => Simplify.expressionSimplifier
  | .conditionalSimplifier          => Simplify.conditionalSimplifier
  | .conditionalUnsimplifier        => Simplify.conditionalUnsimplifier
  | .structuralSimplifier           => Simplify.structuralSimplifier
  | .controlFlowSimplifier          => Simplify.controlFlowSimplifier
  | .deadCodeEliminator             => DCE.deadCodeEliminator
  | .unusedPruner                   => DCE.unusedPruner
  | .unusedAssignEliminator         => DCE.unusedAssignEliminator
  | .unusedStoreEliminator          => DCE.unusedStoreEliminator
  | .equalStoreEliminator           => DCE.equalStoreEliminator
  | .unusedFunctionParameterPruner  => DCE.unusedFunctionParameterPruner
  | .circularReferencesPruner       => DCE.circularReferencesPruner
  | .loadResolver                   => LoadResolver.run
  | .loopInvariantCodeMotion        => LICM.run
  | .commonSubexpressionEliminator  => CSE.run
  | .expressionInliner              => Inline.expressionInliner
  | .fullInliner                    => Inline.fullInliner
  | .functionSpecializer            => Inline.functionSpecializer
  | .equivalentFunctionCombiner     => Inline.equivalentFunctionCombiner

/-- Maximum number of times a bracketed sub-sequence is repeated. Mirrors
solc's hard cap of 12. -/
def maxLoopRounds : Nat := 12

partial def run (items : List PipelineItem) (p : Program) : Program :=
  items.foldl (init := p) fun p it =>
    match it with
    | .step s   => runStep s p
    | .loop body =>
        let rec loop (n : Nat) (p : Program) : Program :=
          match n with
          | 0     => p
          | n + 1 =>
              let p' := run body p
              -- TODO: structural-equality fixpoint check
              loop n p'
        loop maxLoopRounds p

end YulC.Yul.Pipeline
