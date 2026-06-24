/-! CLIF AST types. -/

namespace BfoToLean.Clif

inductive SExpr where
  | sym (s : String)
  | str (s : String)
  | lst (xs : Array SExpr)
  deriving Inhabited, Repr, BEq

partial def SExpr.render : SExpr → String
  | .sym s => s
  | .str s =>
    let escaped := s.replace "\\" "\\\\" |>.replace "'" "\\'"
    s!"'{escaped}'"
  | .lst xs =>
    let inner := String.intercalate " " (xs.toList.map render)
    s!"({inner})"

structure Axiom where
  id : String
  gloss : String
  form : SExpr
  deriving Inhabited

structure Module where
  filename : String
  axioms : Array Axiom
  fileHeader : String
  deriving Inhabited

end BfoToLean.Clif
