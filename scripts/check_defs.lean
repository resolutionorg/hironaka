/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Lean
import Hironaka

/-!
# Definitions check

Run as `lake lean scripts/check_defs.lean` from the directory of `lakefile.toml`: Lake builds the
library this file imports and hands it to Lean (from its artifact cache when it is cached). The
statement vocabulary is every constant of `Hironaka` reachable from the types of the main theorems
(the theorems that `comparator.json` checks; a name there that is not a theorem of the library is a
violation), following the type and value of each definition and only the type of each theorem (a
proof never changes what a definition means), together with the coercion instances declared beside
it, which elaboration unfolds. The script checks that

* every definition of the statement vocabulary is declared in a module named `Defs` (the theorems
  it cites need not be: their statements are fixed by the definitions that cite them, and their
  proofs are irrelevant to what the definitions mean);
* every declaration in such a module is used by the vocabulary: it is vocabulary, or it occurs,
  directly or through other proofs, in the value of a vocabulary definition. Declarations Lean
  generates with another one (constructor lemmas, projections, equation lemmas, `@[mk_iff]`
  lemmas, matchers and auxiliary recursors) are exempt;
* every module of `Hironaka` named `Defs` declares some of the statement vocabulary, so that the
  name means the same thing throughout the library;
* the Challenge files (`Challenge.lean` and every file under `Challenge/`) import only modules
  named `Defs` from `Hironaka` (besides them they import only Mathlib).

It prints each violation and exits with a nonzero status if there is one. The walk that computes the
statement vocabulary is repeated in `scripts/check_blueprint.lean` and
`scripts/sync_formalization.lean`, so a change to it is made in all three files.
-/

open Lean

namespace CheckDefs

/-- The main theorems: the names of `comparator.json`. A name that is not a theorem of the library
is reported as a violation. -/
def mainTheorems (env : Environment) (root : System.FilePath) : IO (NameSet × Array String) := do
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "comparator.json"))
  let names ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let mut s : NameSet := {}
  let mut errors : Array String := #[]
  for n in names do
    if env.find? n.toName matches some (.thmInfo _) then s := s.insert n.toName
    else errors := errors.push s!"comparator.json names {n}, which is not a theorem of the library"
  return (s, errors)

/-- The Challenge files, relative to the repository root: `Challenge.lean` and every Lean file under
`Challenge/`. -/
def challengeFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut fs : Array System.FilePath := #["Challenge.lean"]
  if ← (root / "Challenge").isDir then
    for f in ← (root / "Challenge").walkDir do
      if f.extension == some "lean" then
        fs := fs.push ⟨(f.toString.drop (root.toString.length + 1)).toString⟩
  return fs.qsort (·.toString < ·.toString)

/-- The module imported by a line of a module header, if the line is an import (`import`, with
any of the modifiers `public`, `meta`, `all`). -/
def importOf? (line : String) : Option Name := Id.run do
  let mut s := line.trimAscii.toString
  for p in ["public ", "meta "] do
    if let some r := s.dropPrefix? p then s := r.toString.trimAscii.toString
  let some r := s.dropPrefix? "import " | return none
  let mut t := r.toString.trimAscii.toString
  if let some r' := t.dropPrefix? "all " then t := r'.toString.trimAscii.toString
  return some ((t.splitOn " ").headD "").toName

/-- The classes whose instances elaboration unfolds. -/
def coeClasses : List Name :=
  [``CoeFun, ``CoeSort, ``Coe, ``CoeTail, ``CoeHead, ``CoeOut, ``CoeDep, ``CoeTC, ``CoeOTC,
    ``CoeHTC, ``CoeHTCT, ``CoeT]

/-- Whether a module is a definitions module. -/
def isDefsModule (m : Name) : Bool := m.getString! == "Defs"

/-- The constants a constant mentions: its type, its value unless it is a theorem and `proofs` is
false, and the constructors and recursors tied to an inductive type. -/
def uses (env : Environment) (ci : ConstantInfo) (proofs : Bool) : Array Name := Id.run do
  let mut s := ci.type.getUsedConstants
  match ci with
  | .thmInfo v => if proofs then s := s ++ v.value.getUsedConstants
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

/-- The declarations Lean generates for an inductive type, under its name. -/
def inductiveAuxiliaries : List String :=
  ["ctorIdx", "toCtorIdx", "noConfusionType", "noConfusion", "casesOn", "recOn", "below", "brecOn",
    "binductionOn", "ibelow", "ctorElim", "ctorElimType"]

/-- Declarations Lean generates alongside another declaration, which cannot be moved away from it:
auxiliary declarations and the lemmas generated for them, constructor lemmas, projections,
equation lemmas, the congruence lemmas `simp` generates and the lemmas `foo_iff` that `@[mk_iff]`
generates for an inductive `Foo`. -/
partial def isGenerated (env : Environment) (n : Name) : Bool :=
  n.isInternal || isAuxRecursor env n || isNoConfusion env n || Meta.isMatcherCore env n ||
    (env.getProjectionFnInfo? n).isSome ||
    (env.find? n matches some (.recInfo _)) ||
    (match n with
      | .str p s => env.isConstructor p || s == "congr_simp" ||
          (isAuxRecursor env p || isNoConfusion env p) ||
          (env.find? p matches some (.inductInfo _) && inductiveAuxiliaries.contains s) ||
          s == "eq_def" || s == "eq_unfold" ||
          (s.startsWith "eq_" && (s.drop 3).all Char.isDigit) ||
          (s.endsWith "_iff" &&
            env.find? (p.str (s.take (s.length - 4)).toString.capitalize)
              matches some (.inductInfo _))
      | _ => false)

/-- Walk up from a directory to the directory containing `lakefile.toml`. -/
partial def findRoot (dir : System.FilePath) : IO System.FilePath := do
  if ← (dir / "lakefile.toml").pathExists then return dir
  match dir.parent with
  | some p => findRoot p
  | none => throw <| IO.userError "check_defs: lakefile.toml not found above the working directory"

/-- The check, on the environment `env` of this file. -/
def check (env : Environment) (root : System.FilePath) : IO UInt32 := do
  let (mains, nameErrors) ← mainTheorems env root
  let moduleNames := env.header.moduleNames
  let libModule? (n : Name) : Option Name := do
    let m := moduleNames[(← env.getModuleIdxFor? n).toNat]!
    if m.getRoot == `Hironaka then some m else none
  let coeInstances := env.constants.map₁.toList.filterMap fun (n, ci) =>
    if (libModule? n).isSome && Meta.isInstanceCore env n &&
        ci.type.getForallBody.getAppFn.constName?.any coeClasses.contains then some n else none
  -- the statement vocabulary
  let mut stack : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if mains.contains n then
      stack := stack ++ ci.type.getUsedConstants
  let mut vocab : NameSet := {}
  let mut done := false
  while !done do
    while h : stack.size > 0 do
      let n := stack.back
      stack := stack.pop
      if vocab.contains n then continue
      let some m := libModule? n | continue
      if mains.contains n then continue
      vocab := vocab.insert n
      if let some ci := env.find? n then stack := stack ++ uses env ci false
    let modules : NameSet := vocab.foldl (fun s n => s.insert (libModule? n).get!) {}
    stack := (coeInstances.filter fun n =>
      !vocab.contains n && modules.contains (libModule? n).get!).toArray
    done := stack.isEmpty
  -- everything the vocabulary's values use, proofs included
  let mut used : NameSet := {}
  stack := vocab.toArray
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if used.contains n then continue
    let some _ := libModule? n | continue
    used := used.insert n
    if let some ci := env.find? n then stack := stack ++ uses env ci true
  let mut errors : Array String := nameErrors
  let mut vocabDefsModules : NameSet := {}
  for n in vocab.toList do
    let m := (libModule? n).get!
    if env.find? n matches some (.thmInfo _) then continue
    if isDefsModule m then vocabDefsModules := vocabDefsModules.insert m
    else errors := errors.push s!"statement definition outside a Defs module: {n} ({m})"
  for (n, ci) in env.constants.map₁.toList do
    if isGenerated env n then continue
    let some m := libModule? n | continue
    if vocabDefsModules.contains m && !used.contains n then
      let kind := if ci matches .thmInfo _ then "theorem" else "declaration"
      errors := errors.push s!"{kind} in a Defs module that no statement needs: {n} ({m})"
  for f in ← (root / "Hironaka").walkDir do
    if f.fileName == some "Defs.lean" then
      let rel := (f.toString.drop (root.toString.length + 1)).toString
      let m := (System.FilePath.mk rel).withExtension "" |>.components.foldl Name.mkStr .anonymous
      if !vocabDefsModules.contains m then
        errors := errors.push s!"Defs module that declares no statement definition: {m}"
  for f in ← challengeFiles root do
    for line in (← IO.FS.readFile (root / f)).splitOn "\n" do
      let some imp := importOf? line | continue
      if imp.getRoot == `Hironaka && !isDefsModule imp then
        errors := errors.push s!"{f} imports a module that is not a Defs module: {imp}"
  for e in errors.qsort (· < ·) do IO.println e
  IO.println s!"check_defs: {vocab.size} vocabulary constants in {vocabDefsModules.size} Defs \
    modules, {errors.size} violations"
  return if errors.isEmpty then 0 else 1

end CheckDefs

open Lean Elab Command CheckDefs in
run_cmd do
  let root ← findRoot (← IO.currentDir)
  if (← check (← getEnv) root) != 0 then throwError "check_defs: violations found"
