import BfoToLean.Lint

/-! CLIF → Lean translation. The rule table is applied uniformly. -/

namespace BfoToLean

open Clif

/-- Lean reserved words that collide with BFO variable names. -/
private def leanReserved : List String := ["end"]

/-- lowerCamelCase for bound variables (`s-prime` → `sPrime`); Lean keywords
get a trailing underscore (`end` → `end_`). -/
def normalizeIdent (s : String) : String :=
  let parts := s.splitOn "-"
  let raw := match parts with
    | [] => ""
    | first :: rest => first ++ String.join (rest.map String.capitalize)
  if leanReserved.contains raw then raw ++ "_" else raw

/-- UpperCamelCase for vocabulary — relations, classifiers, named universals
(`instance-of` → `InstanceOf`). -/
def normalizeVocab (s : String) : String :=
  String.join ((s.splitOn "-").map String.capitalize)

/-- Axiom `def` name: id uppercased, hyphen dropped (`vbm-1` → `VBM1`). -/
def axiomDefName (id : String) : String :=
  (id.replace "-" "").toUpper

/-- Module-bundle field name: id in snake_case, typed by the def
(`vbm-1` → `vbm_1 : VBM1`). -/
def axiomFieldName (id : String) : String :=
  id.replace "-" "_"

/-- Map a CLIF filename to a PascalCase module identifier:
`material-entity.cl` → `MaterialEntity`. -/
def moduleId (filename : String) : String :=
  normalizeVocab (filename.replace ".cl" "")

/-- A single translated axiom def. -/
structure LeanAxiom where
  id : String                  -- "xxx-n"
  defName : String             -- "XXXN"  (the `def` name)
  fieldName : String           -- "xxx_n" (the module-bundle field name)
  module : String              -- "MaterialEntity"
  gloss : String
  body : String                -- the Lean Prop expression
  deriving Inhabited

/-- Build a balanced binary chain over a list of operands, using the
given binary operator string (e.g. `"∧"` or `"∨"`). The resulting
expression has parse-tree depth O(log n), so a long `[xtf-1]`-style
conjunction does not exceed Lean's `maxRecDepth`. -/
private partial def balancedChain (op : String) (zero : String)
    : List String → String
  | [] => zero
  | [x] => x
  | xs =>
    let n := xs.length
    let mid := n / 2
    let left := balancedChain op zero (xs.take mid)
    let right := balancedChain op zero (xs.drop mid)
    s!"({left} {op} {right})"

/-- Pretty-print a translated SExpr formula. Every non-atomic subexpression
is parenthesised, so the output is safe under Lean's parser without tracking
precedence. `bound` is the set of in-scope quantifier-bound variable names: a
bare atom in it is a variable (lowerCamelCase), otherwise a named universal
constant (UpperCamelCase vocabulary). -/
private partial def renderForm (bound : Std.HashSet String) (form : SExpr)
    : Except String String := do
  match form with
  | .sym s =>
    return if bound.contains s then normalizeIdent s else normalizeVocab s
  | .str _ => unreachable!
  | .lst xs =>
    match xs.toList with
    | .sym "forall" :: .lst vs :: body
    | .sym "exists" :: .lst vs :: body =>
      let op := match xs[0]! with | .sym s => s | _ => unreachable!
      let names := vs.map fun
        | .sym name => name
        | _ => unreachable!
      let bound := names.foldl (·.insert ·) bound
      let binderStr := String.intercalate " " (names.map normalizeIdent).toList
      let bodyStr ← match body with
        | [single] => renderForm bound single
        | _ =>
          let parts ← body.mapM (renderForm bound)
          pure ("(" ++ String.intercalate " ∧ " parts ++ ")")
      let q := if op == "forall" then "∀" else "∃"
      return s!"({q} ({binderStr} : Type), {bodyStr})"
    | .sym "and" :: args =>
      if args.isEmpty then return "True"
      let parts ← args.mapM (renderForm bound)
      return balancedChain "∧" "True" parts
    | .sym "or" :: args =>
      if args.isEmpty then return "False"
      let parts ← args.mapM (renderForm bound)
      return balancedChain "∨" "False" parts
    | [.sym "not", a] =>
      let inner ← renderForm bound a
      return s!"(¬ {inner})"
    | [.sym "if", a, b] =>
      let a ← renderForm bound a
      let b ← renderForm bound b
      return s!"({a} → {b})"
    | [.sym "iff", a, b] =>
      let a ← renderForm bound a
      let b ← renderForm bound b
      return s!"({a} ↔ {b})"
    | [.sym "=", a, b] =>
      let a ← renderForm bound a
      let b ← renderForm bound b
      return s!"({a} = {b})"
    | .sym op :: args =>
      -- Application head is always vocabulary (relation / classifier).
      let argStrs ← args.mapM (renderForm bound)
      let parts := normalizeVocab op :: argStrs
      return ("(" ++ String.intercalate " " parts ++ ")")
    | _ => unreachable!

def translate (vocab : Vocabulary) : Except String (Array LeanAxiom) := do
  let mut result : Array LeanAxiom := #[]
  for (id, owningFile, ax) in vocab.canonicalAxioms do
    let body ← renderForm {} ax.form
    let mod := moduleId owningFile
    result := result.push {
      id := id
      defName := axiomDefName id
      fieldName := axiomFieldName id
      module := mod
      gloss := ax.gloss
      body := body
    }
  return result

end BfoToLean
