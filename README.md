# Hironaka's resolution of singularities in characteristic zero

[![Build](https://github.com/resolutionorg/hironaka/actions/workflows/build.yml/badge.svg)](https://github.com/resolutionorg/hironaka/actions/workflows/build.yml)
[![Comparator](https://github.com/resolutionorg/hironaka/actions/workflows/comparator.yml/badge.svg)](https://github.com/resolutionorg/hironaka/actions/workflows/comparator.yml)

**[API documentation](https://resolutionorg.github.io/hironaka/docs/)** · **[Blueprint](https://resolutionorg.github.io/hironaka/blueprint/)** ·
[Statements](Challenge) · [`formalization.yaml`](formalization.yaml) · [Sources](references.bib)

A Lean 4 formalization, over Mathlib, of resolution of singularities in characteristic zero:
Hironaka's main theorems and their refinements by Kollár, Włodarczyk and Bierstone–Milman, for
algebraic schemes and for real- and complex-analytic manifolds and spaces. The main theorems are
listed below. The worked examples of the sources form a second library, `HironakaExamples`. Every
theorem is proved: neither library contains a `sorry`.

## Main theorems

The main theorems are those named in [`comparator.json`](comparator.json). Each is stated at the end
of the module that proves it, and again with `sorry` in a challenge file. A theorem from a source
names it in its docstring, in a paragraph `Source statement: [Hir64, Main Theorem I, p. 132]`.

| Source | Lean name |
|---|---|
| **In Mathlib's language** | |
| Hironaka 1964, Main Theorem I (resolution by a single blow-up) | [`AlgebraicGeometry.exists_isBlowUpAlong_smooth`](Hironaka/Resolution/Standard/Algebraic.lean)<br>[Challenge](Challenge/Standard.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/standard-theorems/#sec-standard-algebraic) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Standard/Algebraic.html#AlgebraicGeometry.exists_isBlowUpAlong_smooth) |
| Atiyah 1970, Resolution Theorem (local monomialization of a real-analytic function), with the Jacobian clause of Bierstone–Milman 1997, Theorem 1.10 | [`exists_proper_analytic_monomialization`](Hironaka/Resolution/Standard/Analytic.lean)<br>[Challenge](Challenge/Standard.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/standard-theorems/#sec-standard-analytic) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Standard/Analytic.html#exists_proper_analytic_monomialization) |
| **Algebraic schemes** | |
| Hironaka 1964, Main Theorem II (order reduction) | [`AlgebraicGeometry.exists_blowUpSequence_ord_weakTransformSeq_lt`](Hironaka/Resolution/Algebraic/Hir64/ComponentwiseMainTheorems.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-mt2) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Hir64/ComponentwiseMainTheorems.html#AlgebraicGeometry.exists_blowUpSequence_ord_weakTransformSeq_lt) |
| Hironaka 1964, Main Theorem II(N) (principalization) | [`AlgebraicGeometry.exists_blowUpSequence_weakTransformSeq_eq_top`](Hironaka/Resolution/Algebraic/Hir64/ComponentwiseMainTheorems.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-mt2n) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Hir64/ComponentwiseMainTheorems.html#AlgebraicGeometry.exists_blowUpSequence_weakTransformSeq_eq_top) |
| Hironaka 1964, Corollary 1 (trivialization of a system of ideal sheaves) | [`AlgebraicGeometry.exists_blowUpSequence_forall_exists_stalkIdeal_weakTransformSeq_eq_top`](Hironaka/Resolution/Algebraic/Hir64/ComponentwiseCorollaries.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-cor1) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Hir64/ComponentwiseCorollaries.html#AlgebraicGeometry.exists_blowUpSequence_forall_exists_stalkIdeal_weakTransformSeq_eq_top) |
| Kollár 2007, Theorem 35 (functorial principalization) | [`AlgebraicGeometry.exists_functorial_principalization`](Hironaka/Resolution/Algebraic/Kol07/Thm35/Principalization/FunctorClauses.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-principalization) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Kol07/Thm35/Principalization/FunctorClauses.html#AlgebraicGeometry.exists_functorial_principalization) |
| Hironaka 1964, Corollary 3 (simplification of an algebraic boundary) | [`AlgebraicGeometry.exists_blowUpSequence_isInvertible_isSncBoundary_radical_comap`](Hironaka/Resolution/Algebraic/Hir64/ComponentwiseCorollaries.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-cor3) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Hir64/ComponentwiseCorollaries.html#AlgebraicGeometry.exists_blowUpSequence_isInvertible_isSncBoundary_radical_comap) |
| Kollár 2007, Theorem 36 (functorial resolution) | [`AlgebraicGeometry.exists_functorial_resolution`](Hironaka/Resolution/Algebraic/Kol07/Thm36/Theorem36.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-resolution) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Kol07/Thm36/Theorem36.html#AlgebraicGeometry.exists_functorial_resolution) |
| Kollár 2007, Theorem 27 (strong resolution of a variety) | [`AlgebraicGeometry.exists_strong_resolution`](Hironaka/Resolution/Algebraic/Kol07/Thm36/Theorem36.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-strong-resolution) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Kol07/Thm36/Theorem36.html#AlgebraicGeometry.exists_strong_resolution) |
| Hironaka 1964, Main Theorem I | [`AlgebraicGeometry.exists_support_eq_singularLocus_isRegular_blowUp`](Hironaka/Resolution/Algebraic/Hir64/MainTheoremI.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-mt1) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Hir64/MainTheoremI.html#AlgebraicGeometry.exists_support_eq_singularLocus_isRegular_blowUp) |
| Hironaka 1964, the weak form after Main Theorem I | [`AlgebraicGeometry.exists_dense_isIso_restrict_isRegular_blowUp`](Hironaka/Resolution/Algebraic/Hir64/MainTheoremI.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-mt1-weak) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Hir64/MainTheoremI.html#AlgebraicGeometry.exists_dense_isIso_restrict_isRegular_blowUp) |
| Włodarczyk 2005, Theorem 1.0.2 (embedded desingularization) | [`AlgebraicGeometry.exists_functorial_embeddedDesingularization`](Hironaka/Resolution/Algebraic/Wlo05/EmbeddedFunctorClauses.lean)<br>[Challenge](Challenge/Algebraic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/algebraic-theorems/#sec-embedded) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Algebraic/Wlo05/EmbeddedFunctorClauses.html#AlgebraicGeometry.exists_functorial_embeddedDesingularization) |
| **Analytic manifolds and spaces** | |
| Hironaka 1964, Main Theorem II″(N), in the form of Włodarczyk 2009, Theorem 2.0.3 | [`AnalyticManifold.exists_extensionCompatibleFamily_weakTransformSeq_eq_top`](Hironaka/Resolution/Analytic/Wlo09/HironakaAssembly.lean)<br>[Challenge](Challenge/Analytic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/analytic-theorems/#sec-mt2pp) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Analytic/Wlo09/HironakaAssembly.html#AnalyticManifold.exists_extensionCompatibleFamily_weakTransformSeq_eq_top) |
| Bierstone–Milman 1997, Theorem 1.10 (with the Jacobian clause), in the same form | [`AnalyticManifold.exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback`](Hironaka/Resolution/Analytic/BM97/JacobianAssembly.lean)<br>[Challenge](Challenge/Analytic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/analytic-theorems/#sec-bm) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Analytic/BM97/JacobianAssembly.html#AnalyticManifold.exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback) |
| Włodarczyk 2009, Theorem 2.0.3 (functorial locally finite principalization) | [`AnalyticManifold.exists_functorial_principalization`](Hironaka/Resolution/Analytic/Wlo09/FunctorialPrincipalization.lean)<br>[Challenge](Challenge/Analytic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/analytic-theorems/#sec-wlo09-principalization) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Analytic/Wlo09/FunctorialPrincipalization.html#AnalyticManifold.exists_functorial_principalization) |
| Włodarczyk 2009, Theorem 2.0.2 (locally finite embedded desingularization) | [`AnalyticManifold.exists_embeddedDesingularization`](Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingularization.lean)<br>[Challenge](Challenge/Analytic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/analytic-theorems/#sec-wlo09-embedded) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingularization.html#AnalyticManifold.exists_embeddedDesingularization) |
| Kollár 2007, Theorem 45; Włodarczyk 2009, Theorem 2.0.1 (resolution of analytic spaces) | [`AnalyticSpace.exists_functorial_resolution`](Hironaka/Resolution/Analytic/Kol07Thm45/ResolutionAssembly.lean)<br>[Challenge](Challenge/Analytic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/analytic-theorems/#sec-spaces) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Analytic/Kol07Thm45/ResolutionAssembly.html#AnalyticSpace.exists_functorial_resolution) |
| Kollár 2007, Theorem 45 (1)–(4), for a reduced complex-analytic space | [`AnalyticSpace.exists_surjective_resolution_of_isReduced`](Hironaka/Resolution/Analytic/Kol07Thm45/ResolutionAssembly.lean)<br>[Challenge](Challenge/Analytic.lean) · [Blueprint](https://resolutionorg.github.io/hironaka/blueprint/analytic-theorems/#sec-spaces-complex) · [Doc](https://resolutionorg.github.io/hironaka/docs/Hironaka/Resolution/Analytic/Kol07Thm45/ResolutionAssembly.html#AnalyticSpace.exists_surjective_resolution_of_isReduced) |

## Verifying

The challenge files in [`Challenge/`](Challenge) state the main theorems with `sorry` proofs,
importing from this library only the `Defs.lean` files that define the vocabulary of the
statements. Read with those files, they say exactly what is claimed. Each also unfolds the
predicates its statements use, as `example`s. [`Challenge/Standard.lean`](Challenge/Standard.lean)
imports Mathlib only: it states the two definitions of the library that its first theorem uses,
with the library's names and bodies.

[leanprover/comparator](https://github.com/leanprover/comparator) checks, for each name in
[`comparator.json`](comparator.json), that the challenge statement and the library theorem are the
same and that the proof uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`. With
`landrun` and a `lean4export` built for this toolchain on the `PATH`:

```
lake build Hironaka Challenge
lake env path/to/comparator comparator.json   # expect: Your solution is okay!
```

[`scripts/check_axioms.lean`](scripts/check_axioms.lean) checks the same bound for every constant of
both libraries, so that none depends on `sorryAx`, and prints the axioms of each main theorem.

## Building

The Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain) and Mathlib in
[`lake-manifest.json`](lake-manifest.json). With `elan` installed, in the root of the repository:

```
lake exe cache get                      # fetch the prebuilt Mathlib
lake build                              # the library Hironaka
lake build HironakaExamples Challenge   # examples, challenge files
```

[`scripts/`](scripts) holds the checks run in CI: no axioms beyond the standard three, the
statement vocabulary in the `Defs.lean` files, the challenge files matching
[`comparator.json`](comparator.json), the blueprint covering the statements, and others. Each is
described at the head of its file.

## Layout

| path | contents |
|---|---|
| [`Hironaka/`](Hironaka) | the library, by role: the objects in `Algebra/`, `Analytic/`, `Scheme/`, `Manifold/` and `AnalyticSpace/`, whose `Defs.lean` files hold what the statements use; the proof machinery in `Resolution/`, with the main theorems in folders named after the sources |
| [`HironakaExamples/`](HironakaExamples) | the worked examples and counterexamples of the sources; no module of `Hironaka` imports it |
| [`Challenge.lean`](Challenge.lean), [`Challenge/`](Challenge) | the main theorems stated against the definitions only |
| [`comparator.json`](comparator.json) | the names of the main theorems, read by the comparator and the checks |
| [`blueprint/`](blueprint) | the blueprint, a Verso document in a nested Lake package |
| [`formalization.yaml`](formalization.yaml) | a machine-readable description of the project and of how each statement aligns with its source |
| [`references.bib`](references.bib) | the sources, under the keys by which everything cites them |
| [`scripts/`](scripts) | the checks, and the generators of the computed parts of `formalization.yaml` and of the blueprint's Sources list |

## Documentation

The API documentation of `Hironaka` and `HironakaExamples` and the blueprint are linked at the top
of this file. The blueprint, in [`blueprint/`](blueprint), presents the statements to a
mathematical reader, with background chapters, a section for each main theorem and chapters on
the definitions the statements use.

## `formalization.yaml`

[`formalization.yaml`](formalization.yaml) describes the project in the format of
[mathlib-initiative/formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml)
(version `v0.4`): the sources, the main results with their axioms, how the library was produced
and reviewed. Where the format leaves the shape open or has no field, this file adds:

- `alignment.statements`: the format's suggested table, one entry per theorem matched with the
  item of the source it formalizes and its module, read from the `Source statement:` paragraphs
  of the docstrings; its `note` lists the labelled notes of the theorem's docstring (Gap, Correction,
  Interpretation, …), the same notes the blueprint shows.
- `status.main_results[].statement_vocabulary`: for each main result, the definition modules a
  reader needs to understand its statement.
- `automation.methods[].cost.tokens`: the model tokens of each phase of the work, beside the
  format's wall time and hardware.

The main results and the alignment table are generated from the library, so they stay current
with it.

## Sources

The sources, and the keys by which the docstrings and the blueprint cite them, are listed in the BibTeX file [`references.bib`](references.bib).

## Provenance

This library was produced by an automated formalization process run by Claude Fable 5.1 (Anthropic),
directed and audited by Chris Elliott at Resolution, following the human-written sources listed in
the bibliography ([`references.bib`](references.bib)), and then refactored and prepared for release
by Billy Snikkers and Adam Newgas at Resolution, also through Claude Code sessions. Every theorem is
checked by Lean's kernel; the axioms used are `propext`, `Classical.choice` and `Quot.sound` only.

## License

Apache License 2.0; see [`LICENSE`](LICENSE). Copyright (c) 2026 Resolution.
