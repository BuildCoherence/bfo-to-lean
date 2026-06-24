import BfoToLean

/-- Walk the parsed modules, build the set of distinct CLIF axiom ids
that should appear as `def`s in the generated file. -/
private def expectedAxiomIds (modules : Array BfoToLean.Clif.Module) : Nat :=
  let ids : Std.HashSet String :=
    modules.foldl (init := {}) fun acc m =>
      m.axioms.foldl (init := acc) fun acc ax => acc.insert ax.id
  ids.size

/-- The first character offset at which two strings differ, or `none` if
they're identical. -/
private def firstDifferingOffset (a b : String) : Option Nat := Id.run do
  let mut pa : String.Pos.Raw := ⟨0⟩
  let mut pb : String.Pos.Raw := ⟨0⟩
  let mut i : Nat := 0
  while ¬ pa.atEnd a ∧ ¬ pb.atEnd b do
    if pa.get a ≠ pb.get b then
      return some i
    pa := pa.next a
    pb := pb.next b
    i := i + 1
  if pa.atEnd a ∧ pb.atEnd b then return none
  -- One side is a proper prefix of the other; the divergence sits at
  -- the end of the shorter side.
  return some i

/-- A 2·radius-character window centred on `offset` of `s`, with
whitespace escaped so the line stays visually one line. -/
private def windowAt (s : String) (offset : Nat) (radius : Nat := 40) : String := Id.run do
  let startChar := if offset > radius then offset - radius else 0
  let stopChar := offset + radius
  let mut p : String.Pos.Raw := ⟨0⟩
  let mut i : Nat := 0
  while i < startChar ∧ ¬ p.atEnd s do
    p := p.next s
    i := i + 1
  let mut acc := ""
  while i < stopChar ∧ ¬ p.atEnd s do
    let c := p.get s
    acc := acc ++ (match c with
      | '\n' => "\\n"
      | '\t' => "\\t"
      | '\r' => "\\r"
      | c    => String.singleton c)
    p := p.next s
    i := i + 1
  return acc

/-- Entry point for `lake exe convert`.

Default behaviour: regenerate `BFO.lean` from `vendor/bfo-source/`.

With `--check`: re-run the converter, byte-compare to the committed
`BFO.lean`, and assert distinct CLIF ids equal translated axiom defs.
Exit non-zero on any mismatch. -/
def main (args : List String) : IO UInt32 := do
  let outPath : System.FilePath := "BFO.lean"
  let vendorDir := "vendor/bfo-source"
  let r ← BfoToLean.runConverterFull vendorDir
  let text := r.text
  if args.contains "--check" then
    -- Downgrade only "file isn't there yet" to a friendly message; let
    -- every other IO error surface verbatim.
    let existingOpt ← try
        let bytes ← IO.FS.readFile outPath
        pure (some bytes)
      catch e =>
        match e with
        | .noFileOrDirectory .. => pure none
        | _ => throw e
    let existing ← match existingOpt with
      | some s => pure s
      | none =>
        IO.eprintln s!"DETERMINISM FAIL: no committed {outPath} found"
        IO.eprintln "  Run `lake exe convert` (without --check) to write it first, then commit."
        return 2
    if existing ≠ text then
      IO.eprintln s!"DETERMINISM FAIL: {outPath} differs from converter output"
      IO.eprintln s!"  on-disk size:    {existing.length}"
      IO.eprintln s!"  converter size:  {text.length}"
      match firstDifferingOffset existing text with
      | none =>
        -- Strings are equal up to the shared prefix yet `existing ≠ text` —
        -- one is a proper prefix of the other.
        IO.eprintln "  (one file is a prefix of the other; lengths differ)"
      | some off =>
        IO.eprintln s!"  first diff at char offset: {off}"
        IO.eprintln s!"  on-disk  ±40 chars: {windowAt existing off}"
        IO.eprintln s!"  expected ±40 chars: {windowAt text off}"
      return 1
    let expected := expectedAxiomIds r.modules
    let emitted := r.axioms.size
    if expected ≠ emitted then
      IO.eprintln s!"COMPLETENESS FAIL: expected {expected} distinct CLIF ids, translated {emitted} axiom defs"
      return 1
    IO.println s!"OK: {outPath} matches converter output ({text.length} bytes)"
    IO.println s!"OK: completeness — {emitted} axiom defs for {expected} distinct CLIF ids"
    return 0
  else
    -- Write-then-rename so a killed process can't leave BFO.lean
    -- truncated. tmpPath and outPath share a filesystem (same
    -- directory), so the rename is atomic.
    let tmpPath : System.FilePath := "BFO.lean.tmp"
    IO.FS.writeFile tmpPath text
    IO.FS.rename tmpPath outPath
    IO.println s!"Wrote {outPath} ({text.length} bytes)"
    return 0
