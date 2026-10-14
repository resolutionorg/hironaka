/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Lean
import Hironaka
import HironakaExamples

/-!
# Axiom audit

Run as `lake lean scripts/check_axioms.lean` from the directory of `lakefile.toml`: Lake builds the
libraries `Hironaka` and `HironakaExamples`, which this file imports through their root modules,
and hands them to Lean (from its artifact cache when they are cached). Every module of the two
libraries found on disk under the repository root (the directory containing `lakefile.toml` above
the current directory, or above `HIRONAKA_ROOT` when it is set) must be imported by a root module,
and the script checks that every constant declared in them depends on no axiom other than
`propext`, `Classical.choice` and `Quot.sound`. In particular no constant may depend on `sorryAx`,
so the libraries contain no `sorry`. This covers every constant of the libraries; the comparator
checks the main theorems and what their proofs use.

The script prints the axioms of every main theorem (the theorems that `comparator.json` checks; a
name there that is not a theorem of the libraries is a violation), one line each in the format of
`#print axioms`, then one summary line, and it exits with a nonzero status on any violation.
-/

open Lean

namespace CheckAxioms

/-- The libraries. -/
def libraries : List String := ["Hironaka", "HironakaExamples"]

/-- The axioms a constant may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Module name of a source file path relative to the repository root. -/
def moduleOfPath (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl (fun n c => Name.mkStr n c) .anonymous

/-- Walk up from a directory to the directory containing `lakefile.toml`. -/
partial def findRoot (dir : System.FilePath) : IO System.FilePath := do
  if ← (dir / "lakefile.toml").pathExists then return dir
  match dir.parent with
  | some p => findRoot p
  | none =>
    throw <| IO.userError "check_axioms: lakefile.toml not found above the working directory"

/-- Every module of the libraries present on disk (the root modules included), sorted. -/
def discoverModules (root : System.FilePath) : IO (Array Name) := do
  let mut mods : Array Name := #[]
  for lib in libraries do
    if ← (root / (lib ++ ".lean")).pathExists then
      mods := mods.push (Name.mkSimple lib)
    let dir := root / lib
    if ← dir.isDir then
      for f in ← dir.walkDir do
        if f.extension == some "lean" then
          let rel : String := (f.toString.drop (root.toString.length + 1)).toString
          mods := mods.push (moduleOfPath rel)
  return mods.qsort (·.toString < ·.toString)

/-- The axioms a constant depends on, computed as `#print axioms` does, with one cache shared
across all constants. The sentinel entry inserted before the recursion prevents cycling through an
inductive type and its constructors. -/
partial def axiomsOf (env : Environment) (c : Name) :
    StateM (Std.HashMap Name (Array Name)) (Array Name) := do
  if let some r := (← get)[c]? then return r
  modify (·.insert c #[])
  let (isAxiom, exprs) : Bool × Array Expr :=
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
  let mut acc : NameSet := {}
  if isAxiom then acc := acc.insert c
  for e in exprs do
    for d in e.getUsedConstants do
      for a in ← axiomsOf env d do
        acc := acc.insert a
  let r := acc.toArray.qsort Name.lt
  modify (·.insert c r)
  return r

/-- The audit, on the environment `env` of this file. -/
def run (root : System.FilePath) (env : Environment) : IO Unit := do
  let mods ← discoverModules root
  let missing := mods.filter fun m => !env.header.moduleNames.contains m
  unless missing.isEmpty do
    for m in missing do IO.println s!"check_axioms: module `{m}` is not imported by a root module"
    throw <| IO.userError s!"check_axioms: {missing.size} module(s) missing from the root modules"
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "comparator.json"))
  let comparatorNames ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let comparatorSet : NameSet := comparatorNames.foldl (fun s n => s.insert n.toName) {}
  let isOurs (m : Name) : Bool := libraries.any fun l => (Name.mkSimple l).isPrefixOf m
  let mut cache : Std.HashMap Name (Array Name) := {}
  let mut audited := 0
  let mut failures : Array String := #[]
  for n in comparatorNames do
    unless (env.find? n.toName).any (· matches .thmInfo _) do
      failures := failures.push s!"comparator.json: `{n}` is not a theorem of the libraries"
  let mut mainLines : Array String := #[]
  for idx in [0:env.header.modules.size] do
    let m := env.header.modules[idx]!.module
    unless isOurs m do continue
    for c in env.header.moduleData[idx]!.constNames do
      let (axs, cache') := (axiomsOf env c).run cache
      cache := cache'
      audited := audited + 1
      let bad := axs.filter fun a => !allowedAxioms.contains a
      unless bad.isEmpty do
        failures := failures.push s!"{m}: `{c}` depends on {bad.toList}"
      if comparatorSet.contains c && (env.find? c).any (fun info => info matches .thmInfo _) then
        mainLines := mainLines.push s!"'{c}' depends on axioms: {axs.toList}"
  for l in mainLines.qsort (· < ·) do IO.println l
  for f in failures do IO.println s!"check_axioms: FAIL {f}"
  if failures.isEmpty then
    IO.println s!"check_axioms: OK — {mods.size} modules, {audited} constants, every axiom among \
      {allowedAxioms}, no sorry"
  else
    throw <| IO.userError s!"check_axioms: {failures.size} constant(s) depend on a forbidden axiom"

/-- The repository root: `$HIRONAKA_ROOT` when set, else the current directory, each walked up to
the directory containing `lakefile.toml`. -/
def root : IO System.FilePath := do
  let start : System.FilePath ← match ← IO.getEnv "HIRONAKA_ROOT" with
    | some r => pure ⟨r⟩
    | none => IO.currentDir
  findRoot start

end CheckAxioms

open Lean Elab Command CheckAxioms in
run_cmd do run (← root) (← getEnv)
