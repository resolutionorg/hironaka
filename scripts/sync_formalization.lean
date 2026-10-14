/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Lean
import Hironaka

/-!
# The generated regions of `formalization.yaml`, and the docstring sections they compile

Run as `lake lean scripts/sync_formalization.lean` from the directory of `lakefile.toml`: Lake
builds the library this file imports and hands it to Lean (from its artifact cache when it is
cached), and the computation below runs on the environment it gives.

## The docstring sections

The docstring of a main theorem (a theorem of `comparator.json`), and of a definition its statement
uses, says how the statement relates to its source in a section headed by the line
`Relation to the source.` on its own, followed by Markdown bullets, each beginning with one of the
bold labels `**Translation.**`, `**Unformalised.**`, `**Out of scope.**`, `**Correction.**`,
`**Interpretation.**`, `**Restatement.**`, `**Strengthening.**`, `**Gap.**` and
`**Formalisation note.**`:
```
Relation to the source.
* **Translation.** `S.weakTransformSeq J i` is Hironaka's $J_i$, and `S.boundarySeq E₀ i` his $E_i$.
* **Interpretation.** Hironaka's "coherent sheaf of non-zero ideals" is read as …
* **Gap.** Hironaka's "algebraic scheme" is of finite type over a local ring of his class ℬ; …
```
An item may contain inline code and inline LaTeX `$…$`. The kinds are those of verso-blueprint's
editorial annotations, chosen by three questions in order. Does the source's item have a formalised
counterpart? If not, it is *Unformalised* (a statement or proof is missing) or *Out of scope* (none
is owed, by decision). Is the source's claim true as printed? If it is false, a *Correction* adds
the hypothesis it needs and states the corrected version; if it is underspecified, an
*Interpretation* fixes one reading. For a true claim, how do the statements compare? A
*Restatement* is a logically equivalent form, a *Strengthening* implies the source's statement, and
a *Gap* is weaker or incomparable. A *Translation* is a dictionary entry (this Lean expression is
the source's such-and-such), whatever the answers. A *Formalisation note* is the fallback for a
remark that is none of these, such as one on the form of a statement that no source prints.

A section is read by the rules of the blueprint, which renders each item as a box
(`Informal.SourceRelation.parse` in verso-blueprint; the script repeats them, so that both read the
same items, hence the same hashes, from every docstring):
* the heading is the first line whose text, without leading and trailing whitespace, is exactly
  `Relation to the source.`; its indentation is the section's base indentation;
* after the heading (blank lines allowed) comes a list of bullets: a bullet is a line indented at
  most three columns more than the heading whose text starts with `*`, `-` or `+` followed by a
  space or a tab (a tab counts as one column);
* an item continues on the following lines that are indented more than its bullet and are not
  bullets themselves; blank lines inside an item separate paragraphs;
* the section ends before the first non-blank line that is neither a bullet nor a continuation, or
  at the end of the docstring;
* each item begins with exactly one of the bold labels, the period inside the bold; its text is
  everything after the label, continuation lines included.

The script checks the format, and fails (a nonzero exit status) if
* a section has a bullet that does not begin with one of the labels, has no bullets, has an
  item with no text, or appears twice in one docstring;
* a main theorem has no section;
* a declaration of `Hironaka` with a section is neither a main theorem, nor another theorem citing
  a source, nor a declaration that the statement of a main theorem uses, so that its items would
  be compiled nowhere;
* a `Source statement:` paragraph (see *The citations of a theorem* below) has no bracketed
  citation, or cites a key that is not in the bibliography;
* a docstring still has the heading `Deviations from the source.` of the earlier format.

## The generated regions

`formalization.yaml` has two regions that this script writes, each between two comment lines that
it owns,
```
  # BEGIN GENERATED status.main_results: do not edit
  …
  # END GENERATED status.main_results
```
and the same pair for `alignment.statements`. The rest of the file is hand-written,
`fidelity.divergences` included: the script changes only the lines between the markers. A file
`formalization.NAME.yaml` beside it that declares a namespace in the template's field
`alignment.namespace` has the same two regions, and the theorems of that namespace go there
instead: material kept apart from what `formalization.yaml` describes.

* `status.main_results` has one entry per theorem of `comparator.json`, in its order: `declaration`;
  `file`, the source file of its module; `sorry_count`, the number of constants in the dependency
  closure of the theorem whose own type or value uses `sorryAx`; `axioms`, the axioms it depends
  on, as `#print axioms` computes them; `comparator_config`; `statement_vocabulary`, the files
  holding the definitions its statement uses; and `literature_dependencies`, the results it assumes
  from the literature, which is empty (every main theorem is proved, and `scripts/check_axioms.lean`
  checks that it depends on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`).
  The definitions a statement uses are every definition of `Hironaka` reachable from the type of
  the theorem, following the type and value of each definition, only the type of each theorem, and
  the coercion instances declared beside them (the walk of `scripts/check_defs.lean`, one theorem at
  a time); `scripts/check_defs.lean` checks that their files are `Defs.lean` files. Reading those
  files, with Mathlib and Lean core, is enough to know what the statement means.
* `alignment.statements` has one entry per theorem: the theorems of `comparator.json`, in its
  order, then the other theorems of the library that cite a source, by file and name. An entry
  has the fields of the formalization.yaml template: `source`, the citations of the theorem's
  `Source statement:` paragraphs (`KEY, locator, page`, several joined by "; ") with each key
  written as the authors' last names and the year of its entry in `references.bib`
  (`Hironaka 1964, Main Theorem I, p. 132`); `lean`; `module`, the source file of its module;
  `status`, `proved` (for a main theorem that cites no source, `source` is `none (not in the
  sources)` and `status` is `proved (not in the sources)`); and `note`, the items of its
  section, each after its label, when it has any. The sections of the definitions the statements
  use are not compiled here: they are read in the docstrings and the blueprint, and listed for the
  review ledger.

`coeClasses`, `uses` and the closure in `generate` repeat the first pass of
`scripts/check_defs.lean` (scripts run by `lake lean` cannot import one another), as
`scripts/check_blueprint.lean` does, so a change to that walk is made in all three files.

## Modes

With the environment variable `FORMALIZATION_CHECK` set, the file is only compared with the result,
and elaboration fails if a generated region is out of date. With `LIST_REVIEW_ITEMS` set, nothing is
written: the script prints on standard output every compiled item as an entry of the review ledger
`blueprint/reviews.json` (the main theorems in the order of `comparator.json`, then the definitions
their statements use, by file and name),
```
{"decl": "…", "kind": "Translation", "hash": "…", "reviewer": "", "date": ""}
```
ready to paste once `reviewer` and `date` (`YYYY-MM-DD`) are filled in.

## The hash of an item

`hash` is 16 lowercase hexadecimal digits: the 64-bit FNV-1a hash (offset basis
`0xcbf29ce484222325`, prime `0x100000001b3`; for each byte, exclusive-or it into the state, then
multiply by the prime modulo `2^64`) of the UTF-8 bytes of the item's text after its label, with
every run of whitespace (space, tab, line feed, carriage return) replaced by one space and the
leading and trailing whitespace removed. So re-wrapping an item keeps its hash, and any other change
to its text changes it. The blueprint computes the same hash to decide whether an item has been
reviewed: an item is reviewed when the ledger has an entry with its declaration, kind and hash.
-/

open Lean

namespace SyncFormalization

/-- The file, relative to the directory of `lakefile.toml`. -/
def yamlFile : System.FilePath := "formalization.yaml"

/-- The files `formalization.NAME.yaml` beside `yamlFile` that declare a namespace (a line
`  namespace: "N"` under `alignment:`), with that namespace: the theorems of the namespace are
written there instead of in `yamlFile`. -/
def namespaceFiles (root : System.FilePath) : IO (Array (System.FilePath × Name)) := do
  let mut out := #[]
  for entry in ← root.readDir do
    let n := entry.fileName
    unless n.startsWith "formalization." && n.endsWith ".yaml" && n != yamlFile.toString do continue
    for line in (← IO.FS.readFile entry.path).splitOn "\n" do
      if line.startsWith "  namespace: \"" then
        let ns := ((line.drop "  namespace: \"".length).takeWhile (· != '"')).toString
        out := out.push ((⟨n⟩ : System.FilePath), ns.toName)
  return out

/-- The heading of a section. -/
def heading : String := "Relation to the source."

/-- The heading of the earlier format, no longer accepted. -/
def oldHeading : String := "Deviations from the source."

/-- The labels of the kinds of item, in the order of the compiled text (the order of
`Informal.SourceRelation.Label.all` in verso-blueprint): the dictionary, the kinds in the order of
the three questions, the fallback. -/
def labels : List String :=
  ["Translation", "Unformalised", "Out of scope", "Correction", "Interpretation", "Restatement",
    "Strengthening", "Gap", "Formalisation note"]

/-- The axioms the main theorems are expected to depend on, in the order they are listed. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The width at which the compiled text is wrapped, the indentation included. -/
def width : Nat := 100

/-! ### Items -/

/-- An item of a section: its kind (a label) and its text after the label, normalized. -/
structure Item where
  /-- The label. -/
  kind : String
  /-- The text after the label, with every run of whitespace collapsed to one space. -/
  text : String
  deriving Inhabited

/-- `s` with every run of whitespace (space, tab, line feed, carriage return) replaced by one space
and the leading and trailing whitespace removed. -/
def normalize (s : String) : String :=
  " ".intercalate (((s.split Char.isWhitespace).toList.map (·.toString)).filter (!·.isEmpty))

/-- The 64-bit FNV-1a hash of the UTF-8 bytes of `s`. -/
def fnv1a64 (s : String) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for b in s.toUTF8 do
    h := (h ^^^ b.toUInt64) * 0x100000001b3
  return h

/-- `h` as 16 lowercase hexadecimal digits. -/
def hex16 (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The hash of an item, as the review ledger records it. -/
def Item.hash (i : Item) : String :=
  hex16 (fnv1a64 i.text)

/-! ### Reading a section

The rules of the blueprint's parser, `Informal.SourceRelation.parse` in verso-blueprint's
`src/VersoBlueprint/SourceRelation.lean`, repeated (a script run by `lake lean` cannot import it),
so that the script and the blueprint read the same items, hence the same hashes, from every
docstring. A change to these rules is made in both places. -/

/-- A space or a tab, the characters of indentation. -/
def isIndentChar (c : Char) : Bool := c == ' ' || c == '\t'

/-- The number of spaces and tabs that begin `line` (a tab counts as one column). -/
def indentOf (line : String) : Nat := (line.toList.takeWhile isIndentChar).length

/-- `line` without its indentation. -/
def dropIndent (line : String) : List Char := line.toList.dropWhile isIndentChar

/-- Whether `line` is empty or whitespace. -/
def isBlank (line : String) : Bool := line.toList.all Char.isWhitespace

/-- `line` without its indentation and its trailing whitespace. -/
def trimLine (line : String) : String :=
  String.ofList ((dropIndent line).reverse.dropWhile Char.isWhitespace).reverse

/-- The text after the marker of `line` when it is a bullet of a section whose heading is indented
`base` columns: at most `base + 3` columns of indentation, then `*`, `-` or `+`, then a space or a
tab (the text starts after the spaces and tabs that follow the marker). -/
def bulletContent? (base : Nat) (line : String) : Option (List Char) :=
  if indentOf line > base + 3 then none
  else
    match dropIndent line with
    | m :: c :: rest =>
      if (m == '*' || m == '-' || m == '+') && isIndentChar c then
        some (rest.dropWhile isIndentChar)
      else none
    | _ => none

/-- `**bold**rest` split into the bold text and the rest; `none` when it does not begin with a bold
span. -/
def splitBold? (content : List Char) : Option (String × List Char) :=
  match content with
  | '*' :: '*' :: rest =>
    let rec go (acc : List Char) : List Char → Option (String × List Char)
      | '*' :: '*' :: after => some (String.ofList acc.reverse, after)
      | c :: more => go (c :: acc) more
      | [] => none
    go [] rest
  | _ => none

/-- A bullet of a section: its indentation, its text after the marker, and the lines that continue
it, blank lines included. -/
structure Bullet where
  /-- The indentation of the bullet's line. -/
  indent : Nat
  /-- The text after the marker. -/
  content : List Char
  /-- The following lines that continue the item: blank lines, and lines indented more than the
  bullet that are not bullets. -/
  continuation : Array String := #[]

/-- The bullets of the section whose heading is the line `h` of `lines`. After the heading, blank
lines are skipped; a bullet begins an item, which continues on the following lines that are blank
or indented more than its bullet, unless they are bullets themselves (a line such as `  * …`, at
most three columns deeper than the heading, begins a new bullet). The section ends before the first
non-blank line that is neither a bullet nor a continuation, or at the end of the docstring. -/
def bullets (lines : Array String) (h : Nat) : Array Bullet := Id.run do
  let base := indentOf lines[h]!
  let mut out : Array Bullet := #[]
  let mut cur? : Option Bullet := none
  for line in lines.extract (h + 1) lines.size do
    if isBlank line then
      if let some cur := cur? then
        cur? := some { cur with continuation := cur.continuation.push "" }
    else if let some content := bulletContent? base line then
      if let some cur := cur? then out := out.push cur
      cur? := some { indent := indentOf line, content }
    else
      match cur? with
      | some cur =>
        if indentOf line > cur.indent then
          cur? := some { cur with continuation := cur.continuation.push line }
        else break
      | none => break
  if let some cur := cur? then out := out.push cur
  return out

/-- The labels as an item writes them, for error messages. -/
def labelList : String := ", ".intercalate (labels.map (s!"**{·}.**"))

/-- The items of the section of a docstring, each as its label and its text after the label in
Markdown (the item's lines without their indentation and trailing whitespace, joined by line feeds,
the trailing empty lines dropped; the blueprint's `Item.markdown`): `none` when the docstring has no
section, an error message when the section is malformed. Beyond what the blueprint reports (a bullet
without one of the labels, a heading not followed by bullets), the heading must occur once. -/
def readSection (doc : String) : Except String (Option (Array (String × String))) := do
  let lines := (doc.splitOn "\n").toArray
  match (List.range lines.size).filter fun i => trimLine lines[i]! == heading with
  | [] => return none
  | [h] =>
    let bs := bullets lines h
    if bs.isEmpty then throw "the heading is not followed by a list of bullets"
    let items ← bs.mapM fun b => do
      let shown := trimLine (String.ofList b.content)
      let some (bold, after) := splitBold? b.content
        | throw s!"the bullet `{shown}` does not begin with one of the labels {labelList}"
      let some k := labels.find? (bold == s!"{·}.")
        | throw s!"the bullet `{shown}` begins with **{bold}**, not with one of the labels \
            {labelList}"
      let itemLines := trimLine (String.ofList after) :: b.continuation.toList.map trimLine
      pure (k, "\n".intercalate (itemLines.reverse.dropWhile String.isEmpty).reverse)
    return some items
  | _ => throw s!"the heading `{heading}` occurs more than once"

/-- The items of the section of a docstring, their text normalized: `none` when it has no section,
an error message when the section is malformed (`readSection`) or an item has no text. -/
def parseSection (doc : String) : Except String (Option (Array Item)) := do
  let some items ← readSection doc | return none
  return some (← items.mapM fun (k, markdown) => do
    let text := normalize markdown
    if text.isEmpty then throw s!"an item labelled {k} has no text"
    pure ({ kind := k, text } : Item))

/-! ### The citations of a theorem

A theorem that formalizes an item of the literature names it in a paragraph of its docstring that
begins with `Source statement:` and continues with a bracketed citation of the item,
`[KEY, locator]` or `[KEY, locator, page]`, then optionally a comment in parentheses, one paragraph
per item:
```
Source statement: [Hir64, Main Theorem I, p. 132]

Source statement: [Wlo09, Theorem 2.0.3] (compatible-family form)
```
`KEY` is the key of an entry of the bibliography, and doc-gen4 links the citation to that entry. -/

/-- The words that begin a paragraph naming the item of the literature a theorem formalizes. -/
def sourceMarker : String := "Source statement:"

/-- The paragraphs of a docstring: its runs of non-blank lines, each joined and normalized. -/
def paragraphs (doc : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur : Array String := #[]
  for line in doc.splitOn "\n" do
    if isBlank line then
      unless cur.isEmpty do out := out.push (normalize (" ".intercalate cur.toList))
      cur := #[]
    else
      cur := cur.push line
  unless cur.isEmpty do out := out.push (normalize (" ".intercalate cur.toList))
  return out

/-- The citations of the `Source statement:` paragraphs of a docstring, in order: the text between
the brackets, whitespace normalized (`Hir64, Main Theorem I, p. 132`); an error message when such a
paragraph does not continue with a bracketed citation. -/
def sourceCitations (doc : String) : Except String (Array String) := do
  let noCitation (p : String) :=
    s!"the paragraph `{p}` has no citation `[KEY, locator, page]` after `{sourceMarker}`"
  let mut out : Array String := #[]
  for p in paragraphs doc do
    unless p.startsWith sourceMarker do continue
    match (p.toList.drop sourceMarker.length).dropWhile (· == ' ') with
    | '[' :: inner =>
      let cite := inner.takeWhile (· != ']')
      if cite.isEmpty || cite.length == inner.length then throw (noCitation p)
      out := out.push (String.ofList cite)
    | _ => throw (noCitation p)
  return out

/-- The key of a citation: its text up to the first comma. -/
def citationKey (cite : String) : String :=
  String.ofList (cite.toList.takeWhile (· != ','))

/-! ### The statement vocabulary -/

/-- The classes whose instances elaboration unfolds. -/
def coeClasses : List Name :=
  [``CoeFun, ``CoeSort, ``Coe, ``CoeTail, ``CoeHead, ``CoeOut, ``CoeDep, ``CoeTC, ``CoeOTC,
    ``CoeHTC, ``CoeHTCT, ``CoeT]

/-- The declarations Lean generates for an inductive type, under its name. -/
def inductiveAuxiliaries : List String :=
  ["ctorIdx", "toCtorIdx", "noConfusionType", "noConfusion", "casesOn", "recOn", "below", "brecOn",
    "binductionOn", "ibelow", "ctorElim", "ctorElimType"]

/-- Declarations Lean generates alongside another one; their files are not listed. -/
partial def isGenerated (env : Environment) (n : Name) : Bool :=
  n.isInternal || isAuxRecursor env n || isNoConfusion env n || Meta.isMatcherCore env n ||
    (env.getProjectionFnInfo? n).isSome || env.isConstructor n ||
    (env.find? n matches some (.recInfo _)) ||
    (match n with
      | .str p s => env.isConstructor p || s == "congr_simp" ||
          (isAuxRecursor env p || isNoConfusion env p) ||
          (env.find? p matches some (.inductInfo _) && inductiveAuxiliaries.contains s) ||
          s == "eq_def" || s == "eq_unfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
      | _ => false)

/-- The constants a constant mentions: its type, its value unless it is a theorem, and the
constructors and recursors tied to an inductive type. -/
def uses (env : Environment) (ci : ConstantInfo) : Array Name := Id.run do
  let mut s := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => s := s ++ v.value.getUsedConstants
  | .opaqueInfo v => s := s ++ v.value.getUsedConstants
  | .inductInfo d =>
    for c in d.ctors do
      s := s.push c
      if let some cc := env.find? c then s := s ++ cc.type.getUsedConstants
  | .ctorInfo d => s := s.push d.induct
  | .recInfo d => s := s ++ d.all.toArray
  | _ => pure ()
  return s

/-! ### Axioms -/

/-- The expressions of a constant that its axioms are read from, and whether it is an axiom. -/
def axiomExprs (env : Environment) (c : Name) : Bool × Array Expr :=
  match env.find? c with
  | some (.axiomInfo v) => (true, #[v.type])
  | some (.defnInfo v) => (false, #[v.type, v.value])
  | some (.thmInfo v) => (false, #[v.type, v.value])
  | some (.opaqueInfo v) => (false, #[v.type, v.value])
  | some (.quotInfo _) => (false, #[])
  | some (.ctorInfo v) => (false, #[v.type])
  | some (.recInfo v) => (false, #[v.type])
  | some (.inductInfo v) => (false, #[v.type] ++ (v.ctors.map mkConst).toArray)
  | none => (false, #[])

/-- The axioms a constant depends on, computed as `#print axioms` does (and as
`scripts/check_axioms.lean` does), with one cache shared across constants. The sentinel entry
inserted before the recursion prevents cycling through an inductive type and its constructors. -/
partial def axiomsOf (env : Environment) (c : Name) :
    StateM (Std.HashMap Name (Array Name)) (Array Name) := do
  if let some r := (← get)[c]? then return r
  modify (·.insert c #[])
  let (isAxiom, exprs) := axiomExprs env c
  let mut acc : NameSet := {}
  if isAxiom then acc := acc.insert c
  for e in exprs do
    for d in e.getUsedConstants do
      for a in ← axiomsOf env d do
        acc := acc.insert a
  let r := acc.toArray.qsort Name.lt
  modify (·.insert c r)
  return r

/-- The number of constants in the dependency closure of `c` whose own type or value uses `sorryAx`,
given the axioms of every constant (the closure is entered only where `sorryAx` is among them). -/
def sorryCount (env : Environment) (axioms : Std.HashMap Name (Array Name)) (c : Name) : Nat :=
  Id.run do
    let mut stack := #[c]
    let mut seen : NameSet := {}
    let mut count := 0
    while h : stack.size > 0 do
      let n := stack.back
      stack := stack.pop
      if seen.contains n then continue
      seen := seen.insert n
      unless (axioms.getD n #[]).contains ``sorryAx do continue
      let deps := (axiomExprs env n).2.foldl (fun s e => s ++ e.getUsedConstants) #[]
      if deps.contains ``sorryAx then count := count + 1
      stack := stack ++ deps
    return count

/-- The axioms in the order `formalization.yaml` lists them: the standard ones first. -/
def sortAxioms (axs : Array Name) : Array Name :=
  let rank (a : Name) : Nat := (standardAxioms.idxOf? a).getD standardAxioms.length
  axs.qsort fun a b => rank a < rank b || (rank a == rank b && Name.lt a b)

/-! ### Generation -/

/-- Walk up from a directory to the directory containing `lakefile.toml`. -/
partial def findRoot (dir : System.FilePath) : IO System.FilePath := do
  if ← (dir / "lakefile.toml").pathExists then return dir
  match dir.parent with
  | some p => findRoot p
  | none =>
    throw <| IO.userError "sync_formalization: lakefile.toml not found above the working directory"

/-- The file of a module, relative to the repository root. -/
def fileOf (m : Name) : String :=
  "/".intercalate (m.components.map toString) ++ ".lean"

/-- A string as a YAML scalar (JSON's double-quoted form, which YAML reads). -/
def q (s : String) : String :=
  (Json.str s).compress

/-! ### Reading `references.bib`

The strict part of BibTeX that `scripts/check_references.py` accepts (its `read_bib`), read
with the same rules: the keys of the entries, and the fields the labels below need. -/

/-- A character of a reference key: an ASCII letter or digit, or a Latin letter with a diacritic of
Unicode's Latin-1 Supplement and Latin Extended-A and Extended-B blocks, such as the `ł` of
`Wło05` (the signs `×` and `÷` of the Latin-1 Supplement excepted). -/
def isRefKeyChar (c : Char) : Bool :=
  c.isAlphanum || (0xC0 ≤ c.val && c.val ≤ 0x24F && c.val != 0xD7 && c.val != 0xF7)

/-- An entry of a BibTeX file. -/
structure BibEntry where
  /-- The entry type, in lower case: `article`, `book`. -/
  type : String
  /-- The key: `Hir64`. -/
  key : String
  /-- The fields in order, each a name in lower case and a value: the text between the braces as
  written, or the number. -/
  fields : Array (String × String)
  /-- The line of the file at which the entry starts. -/
  line : Nat
  deriving Inhabited, Repr

/-- The value of the field `name` of an entry, if it has one. -/
def BibEntry.field? (e : BibEntry) (name : String) : Option String :=
  (e.fields.find? (·.1 == name)).map (·.2)

namespace BibParser

/-- The parser state: the rest of the input and the current line. -/
abbrev M := StateT (List Char × Nat) (Except String)

/-- Fails with `msg`, prefixed by the current line. -/
def fail {α : Type} (msg : String) : M α := do
  throw s!"line {(← get).2}: {msg}"

/-- The next character, if any, without consuming it. -/
def peek? : M (Option Char) :=
  return (← get).1.head?

/-- Consumes the next character. -/
def next : M Char := do
  match ← get with
  | (c :: cs, n) =>
    set (cs, if c == '\n' then n + 1 else n)
    return c
  | ([], _) => fail "unexpected end of file"

/-- Consumes the characters satisfying `p` and returns them. -/
partial def takeWhile (p : Char → Bool) (acc : String := "") : M String := do
  match ← peek? with
  | some c => if p c then do discard next; takeWhile p (acc.push c) else return acc
  | none => return acc

/-- Consumes white space. -/
def skipWs : M Unit :=
  discard <| takeWhile Char.isWhitespace

/-- Consumes the character `c`, described as `what` in the error message if it is not next. -/
def expect (c : Char) (what : String) : M Unit := do
  if (← peek?) == some c then discard next else fail s!"expected {what}"

/-- The text up to the brace closing an opened one, braces inside balanced; consumes the closing
brace. -/
partial def braced (depth : Nat := 0) (acc : String := "") : M String := do
  match ← next with
  | '}' => if depth == 0 then return acc else braced (depth - 1) (acc.push '}')
  | '{' => braced (depth + 1) (acc.push '{')
  | c => braced depth (acc.push c)

/-- A field value: text in braces, or a number. -/
def value : M String := do
  match ← peek? with
  | some '{' => discard next; braced
  | some c =>
    if c.isDigit then takeWhile Char.isDigit
    else fail "expected a value in braces or a number"
  | none => fail "unexpected end of file"

/-- The fields of an entry up to its closing brace, which is consumed. -/
partial def fields (acc : Array (String × String)) : M (Array (String × String)) := do
  skipWs
  if (← peek?) == some '}' then discard next; return acc
  let name := (← takeWhile fun c => c.isAlphanum || c == '_' || c == '-').toLower
  if name.isEmpty then fail "expected a field name or `}`"
  skipWs; expect '=' "`=` after the field name"; skipWs
  let v ← value
  if acc.any (·.1 == name) then fail s!"the field `{name}` occurs twice"
  skipWs
  match ← peek? with
  | some ',' => discard next; fields (acc.push (name, v))
  | some '}' => discard next; return acc.push (name, v)
  | _ => fail "expected `,` or `}` after a field"

/-- An entry, `@type{key, field = {value}, …}`. -/
def entry : M BibEntry := do
  let line := (← get).2
  expect '@' "`@`"
  let type ← takeWhile Char.isAlpha
  if type.isEmpty then fail "expected an entry type after `@`"
  skipWs; expect '{' "`{` after the entry type"; skipWs
  let key ← takeWhile isRefKeyChar
  match key.toList with
  | c :: _ => if c.isDigit then fail s!"the key `{key}` starts with a digit"
  | [] => fail "expected a key: a letter followed by letters and digits"
  skipWs; expect ',' s!"`,` after the key `{key}`"
  return { type := type.toLower, key, fields := ← fields #[], line }

/-- The entries of the rest of the file. Text outside the entries (comments) is skipped: it is
everything up to the next `@`. -/
partial def entries (acc : Array BibEntry) : M (Array BibEntry) := do
  discard <| takeWhile (· != '@')
  if (← peek?).isNone then return acc
  entries (acc.push (← entry))

end BibParser

/-- The entries of a BibTeX file, or an error naming the line where it is malformed. The file is
read in a strict part of BibTeX: an entry is `@type{key, name = {value}, …}`, where the key is a
reference key (`isRefKeyChar`), a field name is made of ASCII letters, digits, `_` and `-`, and a
value is text in braces (braces inside balanced) or a number; text between entries is a comment,
so it must not contain `@`. Strings (`@string`), quoted values and concatenation (`#`) are errors. -/
def parseBib (s : String) : Except String (Array BibEntry) :=
  (BibParser.entries #[]).run' (s.toList, 1)

/-! ### The author-year label of a bibliography entry

How `formalization.yaml` writes the key of an entry in a generated `source`: the last names of its
authors and its year, `Hironaka 1964` for `Hir64`, `Bierstone–Milman 1997` for `BM97`. -/

/-- `value` split at the occurrences of `sep` outside braces. -/
def splitTop (value sep : String) : Array String := Id.run do
  let sepChars := sep.toList
  let mut parts : Array String := #[]
  let mut cur : Array Char := #[]
  let mut depth : Int := 0
  let mut rest := value.toList
  for _ in [0:value.length + 1] do
    match rest with
    | [] => break
    | c :: tl =>
      if c == '{' || c == '}' then
        depth := if c == '{' then depth + 1 else depth - 1
        cur := cur.push c
        rest := tl
      else if depth == 0 && sepChars.isPrefixOf rest then
        parts := parts.push (String.ofList cur.toList)
        cur := #[]
        rest := rest.drop sepChars.length
      else
        cur := cur.push c
        rest := tl
  return parts.push (String.ofList cur.toList)

/-- A field value as text: braces dropped, `---` an em dash, `--` an en dash, whitespace
collapsed. -/
def plainText (value : String) : String :=
  normalize ((((value.replace "{" "").replace "}" "").replace "---" "—").replace "--" "–")

/-- The label of an entry: the last names of its authors joined by an en dash, then its year. -/
def bibLabel (e : BibEntry) : String :=
  let last := (splitTop ((e.field? "author").getD "") " and ").toList.map fun name =>
    let name := normalize name
    let parts := splitTop name ","
    if parts.size > 1 then plainText parts[0]! else plainText (splitTop name " ").back!
  "–".intercalate last ++ ((e.field? "year").map (" " ++ ·)).getD ""

/-- What the script computes for one main theorem. -/
structure MainTheorem where
  /-- The theorem. -/
  name : Name
  /-- The source file of its module. -/
  file : String
  /-- Its axioms, in the listed order. -/
  axioms : Array Name
  /-- The number of constants of its closure that use `sorryAx`. -/
  sorryCount : Nat
  /-- The files holding the definitions its statement uses, sorted. -/
  vocabulary : Array String
  /-- The declarations its statement uses. -/
  closure : NameSet
  /-- The citations of its `Source statement:` paragraphs, `KEY, locator, page; …`, if any. -/
  cite? : Option String
  deriving Inhabited

/-- The words of `text`: its pieces between spaces, except that a space inside inline code (between
backticks) or inline math (between dollar signs) does not separate words, so that `wrap` breaks
neither across lines. -/
def words (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut code := false
  let mut math := false
  for c in text.toList do
    if c == ' ' && !code && !math then
      unless cur.isEmpty do out := out.push cur
      cur := ""
    else
      if c == '`' && !math then code := !code
      else if c == '$' && !code then math := !math
      cur := cur.push c
  unless cur.isEmpty do out := out.push cur
  return out

/-- The words of `text` laid out in lines of at most `width` characters (a longer word gets a line
of its own), the first line after `first`, the others after `rest`. -/
def wrap (first rest text : String) : Array String := Id.run do
  let mut lines : Array String := #[]
  let mut cur := first
  let mut empty := true
  for w in words text do
    if empty then
      cur := cur ++ w
      empty := false
    else if cur.length + 1 + w.length ≤ width then
      cur := cur ++ " " ++ w
    else
      lines := lines.push cur
      cur := rest ++ w
  return lines.push cur

/-- The lines of the region `status.main_results`, the key included. -/
def mainResultsLines (thms : Array MainTheorem) : Array String := Id.run do
  let mut out := #["  main_results:"]
  for t in thms do
    let axs := ", ".intercalate (t.axioms.toList.map (q ·.toString))
    out := out ++ #[
      s!"    - declaration: {q t.name.toString}",
      s!"      file: {q t.file}",
      s!"      sorry_count: {t.sorryCount}",
      s!"      axioms: [{axs}]",
      "      comparator_config: \"comparator.json\""]
    if t.vocabulary.isEmpty then
      out := out.push "      statement_vocabulary: []"
    else
      out := out.push "      statement_vocabulary:"
      for f in t.vocabulary do
        out := out.push s!"        - {q f}"
    out := out.push "      literature_dependencies: []"
  return out

/-- The lines of the items of one declaration in the compiled text. -/
def itemLines (items : Array Item) : Array String :=
  let ordered := labels.toArray.flatMap fun k => items.filter (·.kind == k)
  ordered.flatMap fun i => wrap "    - " "      " s!"{i.kind}. {i.text}"

/-- The declarations whose items the review ledger lists, in its order, with their items: the main
theorems, then the other declarations of the statements, by file and name. -/
def compiled (env : Environment) (thms : Array MainTheorem)
    (sections : Std.HashMap Name (Array Item)) : Array (Name × Array Item) := Id.run do
  let mut out : Array (Name × Array Item) := #[]
  for t in thms do
    out := out.push (t.name, sections.getD t.name #[])
  let mut defs : NameSet := {}
  for t in thms do
    for n in t.closure.toList do
      if sections.contains n then defs := defs.insert n
  let key (n : Name) : String × String :=
    (((env.getModuleIdxFor? n).map fun i => fileOf env.header.moduleNames[i.toNat]!).getD "",
      n.toString)
  let sorted := defs.toArray.qsort fun a b =>
    (key a).1 < (key b).1 || ((key a).1 == (key b).1 && (key a).2 < (key b).2)
  for n in sorted do
    out := out.push (n, sections.getD n #[])
  return out

/-- One statement of `alignment.statements`: the theorem, its citations with the keys written as
labels (`none` for a main theorem that cites no source), its file and its items. -/
structure Statement where
  /-- The theorem. -/
  name : Name
  /-- `Label, locator, page; …`, if the theorem cites a source. -/
  source? : Option String
  /-- The source file of its module. -/
  file : String
  /-- The items of its section. -/
  items : Array Item

/-- The lines of the region `alignment.statements`, the key included. -/
def alignmentLines (stmts : Array Statement) : Array String := Id.run do
  let mut out := #["  statements:"]
  for st in stmts do
    out := out ++ #[
      s!"    - source: {q (st.source?.getD "none (not in the sources)")}",
      s!"      lean: {q st.name.toString}",
      s!"      module: {q st.file}",
      s!"      status: {q (if st.source?.isSome then "proved" else "proved (not in the sources)")}"]
    unless st.items.isEmpty do
      out := out.push "      note: |-"
      let ordered := labels.toArray.flatMap fun k => st.items.filter (·.kind == k)
      out := out ++ ordered.flatMap fun i => wrap "        - " "          " s!"{i.kind}. {i.text}"
  return out

/-- `text` with the lines strictly between the markers of `region` replaced by `body`. -/
def replaceRegion (text region : String) (body : Array String) : Except String String := do
  let lines := (text.splitOn "\n").toArray
  let begin? := lines.findIdx? fun l =>
    l.trimAscii.toString.startsWith s!"# BEGIN GENERATED {region}:"
  let end? := lines.findIdx? fun l => l.trimAscii.toString == s!"# END GENERATED {region}"
  match begin?, end? with
  | some b, some e =>
    unless b < e do throw s!"the markers of {region} are out of order"
    return "\n".intercalate (lines.extract 0 (b + 1) ++ body ++ lines.extract e lines.size).toList
  | _, _ => throw s!"the markers of {region} (`# BEGIN GENERATED {region}: …` and \
      `# END GENERATED {region}`) are missing"

/-- Check the sections, compute the regions, and return the new text of each file that has them
(`formalization.yaml`, and the files declaring a namespace) with the review items (declaration and
item, in the order of the compiled text). -/
def generate (env : Environment) (root : System.FilePath) :
    IO (Array (System.FilePath × String) × Array (Name × Item) × Nat) := do
  let moduleNames := env.header.moduleNames
  let libModule? (n : Name) : Option Name := do
    let m := moduleNames[(← env.getModuleIdxFor? n).toNat]!
    if m.getRoot == `Hironaka then some m else none
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "comparator.json"))
  let names ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let nameSet : NameSet := names.foldl (fun s n => s.insert n.toName) {}
  -- the sections of every declaration of the library
  let mut errors : Array String := #[]
  let mut sections : Std.HashMap Name (Array Item) := {}
  let mut malformed : NameSet := {}
  let mut citations : Std.HashMap Name (Array String) := {}
  for idx in [0:env.header.modules.size] do
    unless env.header.modules[idx]!.module.getRoot == `Hironaka do continue
    for c in env.header.moduleData[idx]!.constNames do
      let some doc ← findDocString? env c | continue
      if (doc.splitOn "\n").any (trimLine · == oldHeading) then
        errors := errors.push s!"`{c}`: the heading `{oldHeading}` of the earlier format"
      match parseSection doc with
      | .error e =>
        errors := errors.push s!"`{c}`: {e}"
        malformed := malformed.insert c
      | .ok none => pure ()
      | .ok (some items) => sections := sections.insert c items
      match sourceCitations doc with
      | .error e => errors := errors.push s!"`{c}`: {e}"
      | .ok cs => unless cs.isEmpty do citations := citations.insert c cs
  -- the coercion instances of the library
  let coeInstances := env.constants.map₁.toList.filterMap fun (n, ci) =>
    if (libModule? n).isSome && Meta.isInstanceCore env n &&
        ci.type.getForallBody.getAppFn.constName?.any coeClasses.contains then some n else none
  let cites : Std.HashMap Name String :=
    citations.fold (fun acc k v => acc.insert k ("; ".intercalate v.toList)) {}
  -- the same citations with each key written as its author-year label
  let bib ← IO.ofExcept <| parseBib (← IO.FS.readFile (root / "references.bib"))
  let bibLabels : Std.HashMap String String :=
    bib.foldl (fun m e => m.insert e.key (bibLabel e)) {}
  for (c, cs) in citations.toList do
    for cite in cs do
      unless bibLabels.contains (citationKey cite) do
        errors := errors.push s!"`{c}`: the citation `[{cite}]` of a `{sourceMarker}` paragraph \
          is not of a key of the bibliography"
  let labelledCites : Std.HashMap Name String := citations.fold (init := {}) fun acc k v =>
    acc.insert k <| "; ".intercalate <| v.toList.map fun cite =>
      let key := citationKey cite
      bibLabels.getD key key ++ String.ofList (cite.toList.drop key.length)
  let mut axiomCache : Std.HashMap Name (Array Name) := {}
  let mut thms : Array MainTheorem := #[]
  for t in names do
    let some ci := env.find? t.toName
      | throw <| IO.userError s!"sync_formalization: {t} is not a declaration of the library"
    let some m := libModule? t.toName
      | throw <| IO.userError s!"sync_formalization: {t} is not a declaration of the library"
    unless sections.contains t.toName || malformed.contains t.toName do
      errors := errors.push s!"`{t}`: a main theorem without a section `{heading}`"
    -- the declarations its statement uses
    let mut stack := ci.type.getUsedConstants
    let mut seen : NameSet := {}
    let mut done := false
    while !done do
      while h : stack.size > 0 do
        let n := stack.back
        stack := stack.pop
        if seen.contains n then continue
        let some _ := libModule? n | continue
        if nameSet.contains n then continue
        seen := seen.insert n
        if let some c := env.find? n then stack := stack ++ uses env c
      let modules : NameSet := seen.foldl (fun s n => s.insert (libModule? n).get!) {}
      stack := (coeInstances.filter fun n =>
        !seen.contains n && modules.contains (libModule? n).get!).toArray
      done := stack.isEmpty
    let mut files : Std.HashSet String := {}
    for n in seen.toList do
      if env.find? n matches some (.thmInfo _) then continue
      if isGenerated env n then continue
      files := files.insert (fileOf (libModule? n).get!)
    let (axs, cache') := (axiomsOf env t.toName).run axiomCache
    axiomCache := cache'
    thms := thms.push {
      name := t.toName, file := fileOf m, axioms := sortAxioms axs
      sorryCount := sorryCount env axiomCache t.toName
      vocabulary := files.toArray.qsort (· < ·), closure := seen, cite? := cites[t.toName]? }
  -- the statements of `alignment.statements`: the main theorems, then the other theorems of the
  -- library that cite a source, by file and name
  let tagged : Array (Name × String) := Id.run do
    let mut out := #[]
    for (n, _) in citations.toList do
      if nameSet.contains n then continue
      unless env.find? n matches some (.thmInfo _) do continue
      let some m := libModule? n | continue
      out := out.push (n, fileOf m)
    return out.qsort fun a b => a.2 < b.2 || (a.2 == b.2 && a.1.toString < b.1.toString)
  let stmts : Array Statement :=
    thms.map (fun t => { name := t.name, source? := labelledCites[t.name]?, file := t.file
                         items := sections.getD t.name #[] }) ++
    tagged.map (fun (n, f) => { name := n, source? := labelledCites[n]?, file := f
                                items := sections.getD n #[] })
  -- every section is compiled somewhere: in the statements, or in the review ledger of the
  -- definitions the statements use
  let used : NameSet := stmts.foldl (fun s st => s.insert st.name) <|
    thms.foldl (fun s t => (t.closure.toList.foldl NameSet.insert s).insert t.name) {}
  for (n, _) in sections.toList do
    unless used.contains n do
      errors := errors.push s!"`{n}`: a section on a declaration that is neither a main theorem, \
        nor another theorem citing a source, nor used by the statement of a main theorem, \
        so compiled nowhere"
  unless errors.isEmpty do
    for e in errors.qsort (· < ·) do IO.eprintln s!"sync_formalization: {e}"
    throw <| IO.userError s!"sync_formalization: {errors.size} docstring error(s)"
  -- each file gets the regions of its theorems: a file declaring a namespace those of the
  -- namespace, `yamlFile` the others
  let regions (file : System.FilePath) (keep : Name → Bool) : IO String := do
    let text ← IO.FS.readFile (root / file)
    let text ← IO.ofExcept <| replaceRegion text "status.main_results"
      (mainResultsLines (thms.filter (keep ·.name)))
    IO.ofExcept <| replaceRegion text "alignment.statements"
      (alignmentLines (stmts.filter (keep ·.name)))
  let spaces ← namespaceFiles root
  let elsewhere (n : Name) : Bool := spaces.any fun (_, ns) => n.getRoot == ns
  let mut files := #[(yamlFile, ← regions yamlFile (!elsewhere ·))]
  for (file, ns) in spaces do
    files := files.push (file, ← regions file (·.getRoot == ns))
  let review := (compiled env thms sections).flatMap fun (n, items) =>
    (labels.toArray.flatMap fun k => items.filter (·.kind == k)).map (n, ·)
  return (files, review, names.size)

/-- The review ledger entry of an item, with `reviewer` and `date` left empty. -/
def ledgerEntry (n : Name) (i : Item) : String :=
  s!"\{\"decl\": {q n.toString}, \"kind\": {q i.kind}, \"hash\": {q i.hash}, \
    \"reviewer\": \"\", \"date\": \"\"}"

end SyncFormalization

open Lean Elab Command SyncFormalization in
run_cmd do
  let env ← getEnv
  let root ← findRoot (← IO.currentDir)
  let (files, review, n) ← generate env root
  if (← IO.getEnv "LIST_REVIEW_ITEMS").isSome then
    -- written to standard output directly: a `logInfo` message would carry a position prefix
    let out ← IO.getStdout
    out.putStrLn "["
    for h : i in [0:review.size] do
      let (d, item) := review[i]
      out.putStrLn s!"  {ledgerEntry d item}{if i + 1 < review.size then "," else ""}"
    out.putStrLn "]"
    out.flush
  else if (← IO.getEnv "FORMALIZATION_CHECK").isSome then
    for (file, text) in files do
      unless (← IO.FS.readFile (root / file)) == text do
        throwError "sync_formalization: the generated regions of {file} are out of date; rerun \
          `lake lean scripts/sync_formalization.lean`"
    logInfo m!"sync_formalization: {", ".intercalate (files.toList.map (·.1.toString))} up to date \
      ({n} theorems, {review.size} items)"
  else
    for (file, text) in files do
      IO.FS.writeFile (root / file) text
    logInfo m!"sync_formalization: wrote the generated regions of \
      {", ".intercalate (files.toList.map (·.1.toString))} ({n} theorems, {review.size} items)"
