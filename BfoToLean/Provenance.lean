/-! Build the provenance header block embedded at the top of the
generated `BFO.lean` file. The header carries only values that vary
with the pinned inputs (BFO commit SHA, the BFO source's own
generated-date string) — never wall-clock, never absolute paths. -/

namespace BfoToLean

/-- Read the converter's semver out of `lakefile.toml` (the single
source of truth). -/
def readConverterVersion (lakefilePath : String := "lakefile.toml") : IO String := do
  let src ← IO.FS.readFile lakefilePath
  let after := (src.splitOn "version = \"")[1]!
  return (after.splitOn "\"")[0]!

structure Provenance where
  bfoRepo : String
  bfoCommitSha : String
  bfoAuthor : String
  bfoGeneratedDate : String
  converterVersion : String
  deriving Inhabited

/-- Extract a JSON string value for a given top-level key from
`.provenance.json`. The shape is fixed (the writer is
`bin/refresh-bfo-source`); a malformed file crashes on the array
index, which is the right signal for a maintainer who just ran
`lake exe convert`. Kept in lock-step with `bin/read-provenance-field`;
both accept the same shape. -/
private def extractJsonString (key : String) (src : String) : String :=
  let needle := "\"" ++ key ++ "\""
  let after := (src.splitOn needle)[1]!
  (after.splitOn "\"")[1]!

/-- Find the `Author: <name>` and `generated YYYY/MM/DD` lines in a
CLIF file's header comment block. Both are stable across runs against
the same pinned BFO source. -/
private def extractFromClifHeader (header : String) : String × String := Id.run do
  let mut author := ""
  let mut date := ""
  for line in header.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.startsWith "Author:" then
      author := (line.drop "Author:".length).toString.trimAscii.toString
    else if line.startsWith "BFO " then
      let parts := line.splitOn "generated "
      if parts.length ≥ 2 then date := parts[1]!.trimAscii.toString
  return (author, date)

/-- Read provenance from disk: the `.provenance.json` for the commit
SHA / repo, and any one `.cl` file for the author/date lines. -/
def Provenance.read (vendorDir : String) (oneClifFileBytes : String) : IO Provenance := do
  let provJson ← IO.FS.readFile (vendorDir ++ "/.provenance.json")
  let (author, date) := extractFromClifHeader oneClifFileBytes
  let version ← readConverterVersion
  return {
    bfoRepo := extractJsonString "repo" provJson
    bfoCommitSha := extractJsonString "commit_sha" provJson
    bfoAuthor := author
    bfoGeneratedDate := date
    converterVersion := version
  }

/-- Render the provenance header as a `--` comment block. -/
def Provenance.render (p : Provenance) : String :=
  let lines : List String := [
    "-- ============================================================",
    "-- BFO 2020 — single-sorted CLIF axiomatization, ported to Lean 4",
    "--",
    "-- This file is a derivative of BFO 2020, produced by mechanical",
    "-- CLIF→Lean translation. License: CC BY 4.0",
    "-- (https://creativecommons.org/licenses/by/4.0/).",
    "--",
    s!"-- Upstream:        {p.bfoRepo}",
    s!"-- Upstream commit: {p.bfoCommitSha}",
    s!"-- Upstream author: {p.bfoAuthor}",
    s!"-- BFO source date: {p.bfoGeneratedDate}",
    s!"-- Converter:       bfo-to-lean v{p.converterVersion}",
    "--",
    "-- The precise modification record is (commit_sha, converter_version):",
    "-- regenerating from the same pair produces a byte-identical file.",
    "-- ============================================================"
  ]
  String.intercalate "\n" lines

end BfoToLean
