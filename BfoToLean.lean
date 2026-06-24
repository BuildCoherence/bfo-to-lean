import BfoToLean.Clif.Ast
import BfoToLean.Clif.Reader
import BfoToLean.Lint
import BfoToLean.Translate
import BfoToLean.Provenance
import BfoToLean.Emit

namespace BfoToLean

open Clif

/-- Parse every `*.cl` file under `<vendorDir>/21838-2/common-logic`
in alphabetical order. -/
def parseAllModules (vendorDir : String) : IO (Array Clif.Module) := do
  let dir : System.FilePath := vendorDir ++ "/21838-2/common-logic"
  let entries ← dir.readDir
  let clFiles := entries.filterMap fun e =>
    if e.fileName.endsWith ".cl" then some e.fileName else none
  let sorted := clFiles.qsort (· < ·)
  let mut modules : Array Clif.Module := #[]
  for fname in sorted do
    let path : System.FilePath := dir / fname
    let src ← IO.FS.readFile path
    match Clif.parseModule fname src with
    | .ok m => modules := modules.push m
    | .error err => throw (IO.userError s!"parse {fname}: {err}")
  return modules

/-- The full intermediate state produced by `runConverterFull`: the
parsed modules, the inferred vocabulary, the translated axiom array,
and the emitted Lean text. -/
structure ConvertResult where
  modules : Array Clif.Module
  vocab : Vocabulary
  axioms : Array LeanAxiom
  text : String

/-- Run the converter against a vendored source directory, returning
every intermediate state. Callers that only need the text use
`runConverter`. -/
def runConverterFull (vendorDir : String) : IO ConvertResult := do
  let modules ← parseAllModules vendorDir
  if modules.isEmpty then
    throw (IO.userError s!"no .cl files found under {vendorDir}")
  let prov ← Provenance.read vendorDir modules[0]!.fileHeader
  let vocab ← match Vocabulary.infer modules with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"lint: {e}")
  let axioms ← match translate vocab with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"translate: {e}")
  let text := emit prov vocab axioms
  return { modules, vocab, axioms, text }

/-- Run the converter against a vendored source directory, returning
the generated Lean text. Thin wrapper over `runConverterFull` for
callers that don't need the intermediate state. -/
def runConverter (vendorDir : String) : IO String := do
  let r ← runConverterFull vendorDir
  return r.text

end BfoToLean
