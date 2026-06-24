import BfoToLean.Clif.Reader
import Std.Data.HashMap
import Std.Data.HashSet

/-! Vocabulary + arity inference.

The lint pass walks every parsed axiom and infers:
  - the arity of each relation symbol from its application sites,
  - the named individual constants (BFO's ~35 universals) from any
    argument position that is not a quantifier-bound variable,
  - the cross-file duplicate axiom ids whose forms agree (deduped)
    and disagree (hard error). -/

namespace BfoToLean

open Clif

/-- Hard-coded operator set: the small CLIF logical vocabulary. -/
def operators : List String :=
  ["forall", "exists", "and", "or", "not", "if", "iff", "="]

/-- Hard-coded classifying predicates. They have a fixed shape
(Type → Prop) and are emitted up front, not from the inferred arity
table. -/
def classifiers : List String :=
  ["universal", "particular", "entity"]

structure Vocabulary where
  /-- Relation symbol (CLIF kebab-case form) → inferred arity. -/
  arity : Std.HashMap String Nat := {}
  /-- Named individual constants (BFO universals + any others). -/
  constants : Array String := #[]
  /-- Sorted axioms: id → (canonical owning module name, axiom). -/
  canonicalAxioms : Array (String × String × Axiom) := #[]
  deriving Inhabited

/-- The first sighting (file + axiom id) of each relation arity, so an
arity-mismatch error can name both the previous site and the conflict
site. -/
private structure ArityProvenance where
  filename : String
  axiomId : String
  deriving Inhabited

/-- Mutable state for the vocabulary walker: relation arities, the
first sighting of each arity (for the conflict-error message), and the
set of named-constant symbols seen in argument position. -/
private structure WalkState where
  arity : Std.HashMap String Nat := {}
  arityProv : Std.HashMap String ArityProvenance := {}
  consts : Std.HashSet String := {}

private abbrev WalkM := StateT WalkState (Except String)

/-- Collect the set of CLIF symbols that appear in any quantifier
binder anywhere in the corpus, plus the predicates from
`(cl:outdiscourse …)` and the universe of classifiers/operators.
Anything else in argument position is a named individual constant.

`siteFile` / `siteAxiomId` name the source location each call-site
arity is observed from; an arity-mismatch error message names both
sites (the previous one is looked up in `arityProv`). -/
private partial def walkAxiom (siteFile : String) (siteAxiomId : String)
    (form : SExpr) (bound : List String) : WalkM Unit := do
  match form with
  | .sym _ | .str _ => return ()
  | .lst xs =>
    if xs.isEmpty then return ()
    match xs[0]! with
    | .sym op =>
      if op == "forall" || op == "exists" then
        if xs.size < 3 then
          throw s!"{siteFile}:[{siteAxiomId}]: malformed {op}: expected (forall/exists (vars...) body...)"
        let vs ← match xs[1]! with
          | .lst vs => pure vs
          | other => throw s!"{siteFile}:[{siteAxiomId}]: quantifier binder list not a list: {other.render}"
        let mut newBound := bound
        for v in vs do
          match v with
          | .sym name => newBound := name :: newBound
          | other => throw s!"{siteFile}:[{siteAxiomId}]: quantifier binder not a symbol: {other.render}"
        for body in xs.extract 2 xs.size do
          walkAxiom siteFile siteAxiomId body newBound
      else if operators.contains op || classifiers.contains op then
        -- Operator / classifier: walk into args; classifying predicates'
        -- single argument may be a named constant.
        for arg in xs.extract 1 xs.size do
          walkAxiom siteFile siteAxiomId arg bound
      else
        -- Ordinary relation: record arity from this call site.
        let arityHere := xs.size - 1
        let s ← get
        match s.arity[op]? with
        | none =>
          set { s with
            arity := s.arity.insert op arityHere
            arityProv := s.arityProv.insert op { filename := siteFile, axiomId := siteAxiomId } }
        | some prev =>
          if prev ≠ arityHere then
            let prevSite := s.arityProv[op]?.getD { filename := "<unknown>", axiomId := "<unknown>" }
            throw s!"arity mismatch for `{op}`: arity {prev} at {prevSite.filename}:[{prevSite.axiomId}], arity {arityHere} at {siteFile}:[{siteAxiomId}]"
        for arg in xs.extract 1 xs.size do
          match arg with
          | .sym name =>
            if ¬ bound.contains name then
              modify fun s => { s with consts := s.consts.insert name }
          | _ => pure ()
          walkAxiom siteFile siteAxiomId arg bound
    | head =>
      -- Head is not a symbol — e.g. `(some-list ...) ...`. The CLIF we
      -- target has no such forms, so this is a hard error.
      throw s!"{siteFile}:[{siteAxiomId}]: non-symbol head in application: {head.render}"

/-- Infer the converter's vocabulary from the parsed modules.
Also deduplicates cross-file axiom-id collisions (byte-equal forms)
and flags genuine differing-form collisions. -/
def Vocabulary.infer (modules : Array Module) : Except String Vocabulary := do
  -- ax id → (first owning module, axiom we already kept)
  let mut seen : Std.HashMap String (String × Axiom) := {}
  let walkAll : WalkM Unit := do
    for m in modules do
      for ax in m.axioms do
        walkAxiom m.filename ax.id ax.form []
  let (_, finalState) ← walkAll.run {}
  -- Run the cross-file duplicate-id check in a second pass. (Done
  -- outside the walker because it doesn't share its state.)
  for m in modules do
    for ax in m.axioms do
      match seen[ax.id]? with
      | none => seen := seen.insert ax.id (m.filename, ax)
      | some (otherMod, other) =>
        if other.form == ax.form then
          -- Byte-equal duplicate — keep the lexicographically smallest
          -- owning module name.
          if m.filename < otherMod then
            seen := seen.insert ax.id (m.filename, ax)
        else
          throw s!"axiom id `{ax.id}` appears in both {otherMod} and {m.filename} with DIFFERING forms"
  -- Classifiers and `instance-of` are guaranteed: even though
  -- instance-of would be picked up from any body, we want to surface
  -- a problem if it isn't.
  if ¬ finalState.arity.contains "instance-of" then
    throw "instance-of never used in any axiom body — vocabulary inference failed"
  -- Constants minus anything that's actually a relation head.
  let classifiersAndOps : List String := classifiers ++ operators
  let sortedConsts :=
    (finalState.consts.toArray.filter fun n =>
      ¬ finalState.arity.contains n && ¬ classifiersAndOps.contains n).qsort (· < ·)
  let canonical := seen.toArray.qsort (fun a b => a.1 < b.1)
  return { arity := finalState.arity, constants := sortedConsts, canonicalAxioms := canonical }

end BfoToLean
