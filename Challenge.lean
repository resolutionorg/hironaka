/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Challenge.Algebraic
public import Challenge.Analytic
public import Challenge.Standard

/-!
# The main theorems, stated against the definitions only

The main theorems of the library with every proof replaced by `sorry`, in files that import only the
modules defining the vocabulary of the statements. These files and the import closure of those
modules are the audit surface of what the library claims.

[leanprover/comparator](https://github.com/leanprover/comparator) (`comparator.json`) checks that
each statement here is structurally identical to the library's theorem of the same name and replays
the library's proof in the kernel with no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`. Since it compares elaborated types, each file imports only its own vocabulary and not
all of `Mathlib`: an instance the library's module does not see would elaborate a statement
differently.
-/

public section
