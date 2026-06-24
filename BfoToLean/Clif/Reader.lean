import BfoToLean.Clif.Ast

/-! CLIF s-expression reader.

Threads a `Pos` (1-based line, 1-based column) through every step so a
parse error is reported as `<file>:<line>:<col>: <msg>`. -/

namespace BfoToLean.Clif

/-- 1-based line/column position. -/
structure Pos where
  line : Nat := 1
  col : Nat := 1
  deriving Inhabited, BEq

private def advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then { line := p.line + 1, col := 1 }
  else { line := p.line, col := p.col + 1 }

private def Pos.render (p : Pos) : String := s!"{p.line}:{p.col}"

private def isWhite (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def isSymChar (c : Char) : Bool :=
  ¬ (isWhite c || c == '(' || c == ')' || c == '\'' || c == '"')

private def skipWhite : Pos → List Char → Pos × List Char
  | p, [] => (p, [])
  | p, c :: cs =>
    if isWhite c then skipWhite (advance p c) cs
    else (p, c :: cs)

/-- Read a quoted string. Backslash escapes pass the next character
through verbatim (`\'` → `'`, `\\` → `\`). -/
private def readString (quote : Char) (start : Pos) (acc : String) :
    Pos → List Char → Except String (String × Pos × List Char)
  | _, [] => .error s!"{start.render}: unterminated string (opened with {quote})"
  | p, c :: cs =>
    if c == quote then .ok (acc, advance p c, cs)
    else if c == '\\' then
      match cs with
      | [] => .error s!"{p.render}: trailing backslash in string"
      | c' :: cs' =>
        let p1 := advance p c
        let p2 := advance p1 c'
        readString quote start (acc.push c') p2 cs'
    else readString quote start (acc.push c) (advance p c) cs

private def readSymbol (acc : String) :
    Pos → List Char → String × Pos × List Char
  | p, [] => (acc, p, [])
  | p, c :: cs =>
    if isSymChar c then readSymbol (acc.push c) (advance p c) cs
    else (acc, p, c :: cs)

mutual
  private partial def readOne :
      Pos → List Char → Except String (SExpr × Pos × List Char)
    | p, [] => .error s!"{p.render}: unexpected end of input"
    | p, c :: cs =>
      if isWhite c then
        let (p', cs') := skipWhite p (c :: cs)
        readOne p' cs'
      else if c == '(' then do
        let (xs, p', rest) ← readList (advance p c) cs #[]
        return (.lst xs, p', rest)
      else if c == ')' then .error s!"{p.render}: unexpected ')'"
      else if c == '\'' then do
        let (s, p', rest) ← readString '\'' p "" (advance p c) cs
        return (.str s, p', rest)
      else if c == '"' then do
        let (s, p', rest) ← readString '"' p "" (advance p c) cs
        return (.str s, p', rest)
      else
        let (s, p', rest) := readSymbol "" p (c :: cs)
        if s.isEmpty then .error s!"{p.render}: unexpected character '{c}'"
        else .ok (.sym s, p', rest)

  private partial def readList (p : Pos) (input : List Char) (acc : Array SExpr) :
      Except String (Array SExpr × Pos × List Char) := do
    let (p', input') := skipWhite p input
    match input' with
    | [] => .error s!"{p'.render}: unterminated list — missing ')'"
    | ')' :: rest => return (acc, advance p' ')', rest)
    | rest =>
      let (x, p'', rest') ← readOne p' rest
      readList p'' rest' (acc.push x)
end

/-- Parse the input as a sequence of top-level s-expressions. -/
partial def read (src : String) : Except String (Array SExpr) := do
  let rec loop (p : Pos) (cs : List Char) (acc : Array SExpr) :
      Except String (Array SExpr) := do
    let (p', cs') := skipWhite p cs
    match cs' with
    | [] => return acc
    | rest =>
      let (x, p'', rest') ← readOne p' rest
      loop p'' rest' (acc.push x)
  loop {} src.toList #[]

/-- Find the matching `[` for the trailing `]` of `cs` (a reversed
list of trimmed chars). Returns the 0-based character index of the
`[` from the start of the original (non-reversed) char list. -/
private def findMatchingOpen (chars : List Char) : Option Nat :=
  let n := chars.length
  let rec go (depth : Nat) (i : Nat) : List Char → Option Nat
    | [] => none
    | c :: rest =>
      let i' := i - 1
      if c == ']' then go (depth + 1) i' rest
      else if c == '[' then
        if depth = 1 then some i'
        else go (depth - 1) i' rest
      else go depth i' rest
  go 0 n chars.reverse

/-- Find the last `[xxx-n]` id at the end of a CLIF gloss string,
returning `(strippedGloss, id)`. -/
def extractId (raw : String) : Option (String × String) :=
  let trimmed := raw.trimAsciiEnd.toString
  if ¬ trimmed.endsWith "]" then none
  else
    let chars := trimmed.toList
    match findMatchingOpen chars with
    | none => none
    | some openIdx =>
      let n := chars.length
      let idInner := String.ofList ((chars.drop (openIdx + 1)).take (n - openIdx - 2))
      let parts := idInner.splitOn "-"
      if parts.length = 2 then
        let alpha := parts[0]!
        let digits := parts[1]!
        let alphaOk :=
          alpha.length > 0 && alpha.all (fun c => c.isLower && c.isAlpha)
        let digitsOk :=
          digits.length > 0 && digits.all Char.isDigit
        if alphaOk && digitsOk then
          let before := String.ofList (chars.take openIdx)
          some (before.trimAsciiEnd.toString, idInner)
        else none
      else none

/-- Find the body of the first `(cl:ttl "url" body...)` form anywhere
in the forest of forms. CLIF lets a `cl:comment` wrap the entire file,
so the ttl is often nested one level inside the header comment. -/
partial def findTtl : Array SExpr → Option (Array SExpr)
  | forms =>
    let rec go : List SExpr → Option (Array SExpr)
      | [] => none
      | f :: rest =>
        match f with
        | .lst args =>
          if args.size ≥ 1 then
            match args[0]! with
            | .sym "cl:ttl" =>
              if args.size < 3 then none
              else some (args.extract 2 args.size)
            | _ =>
              -- Recurse into inner forms.
              match go args.toList with
              | some r => some r
              | none => go rest
          else go rest
        | _ => go rest
    go forms.toList

/-- The file-header comment string is the first `(cl:comment '...')`
form whose body is a `cl:ttl` — its text is the header, and its body
carries the axiomatization. -/
def findFileHeader (forms : Array SExpr) : String :=
  let rec go : List SExpr → String
    | [] => ""
    | f :: rest =>
      match f with
      | .lst args =>
        if args.size ≥ 2 then
          match args[0]!, args[1]! with
          | .sym "cl:comment", .str s => s
          | _, _ => go rest
        else go rest
      | _ => go rest
  go forms.toList

/-- Walk `(cl:ttl "url" (cl:text body ...))` and extract the
`(cl:comment 'gloss' axiom)` pairs plus the file's header comment. -/
def collectModuleBody (forms : Array SExpr) : Array Axiom × String := Id.run do
  let header := findFileHeader forms
  let .some ttlBody := findTtl forms | unreachable!
  let mut textBody : Array SExpr := #[]
  for form in ttlBody do
    match form with
    | .lst args =>
      if args.size ≥ 1 then
        match args[0]! with
        | .sym "cl:text" => textBody := args.extract 1 args.size
        | _ => pure ()
    | _ => pure ()
  let mut axioms : Array Axiom := #[]
  for form in textBody do
    match form with
    | .lst args =>
      if args.size ≥ 1 then
        match args[0]! with
        | .sym "cl:comment" =>
          let .str glossRaw := args[1]! | unreachable!
          if args.size = 2 then continue
          let axiomForm := args[2]!
          let some (gloss, id) := extractId glossRaw | continue
          axioms := axioms.push { id, gloss, form := axiomForm }
        | _ => pure ()
    | _ => pure ()
  return (axioms, header)

/-- Parse a single CLIF module. -/
def parseModule (filename : String) (src : String) : Except String Module := do
  let forms ← read src
  let (axs, header) := collectModuleBody forms
  return { filename, axioms := axs, fileHeader := header }

end BfoToLean.Clif
