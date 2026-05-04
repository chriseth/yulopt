import YulC.Syntax.Yul

/-!
# Yul parser

Parser from Yul source text to `YulC.Syntax.Program`. Stub.
-/
namespace YulC.Syntax.Parser

def parse (_src : String) : Except String Program :=
  .error "parser not implemented"

end YulC.Syntax.Parser
