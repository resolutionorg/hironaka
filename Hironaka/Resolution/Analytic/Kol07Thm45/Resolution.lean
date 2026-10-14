/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlue
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The resolution of an analytic space: gluing over an exhaustion, and the value off the class

Włodarczyk defines the canonical desingularization of an analytic space `Y` by gluing: for an
open cover `{U_i}` of `Y` with compact closures `Z_i := Ū_i`, let `des_i : Ỹ_{Z_i} → Y_{Z_i}` be the
canonical desingularization of the germ `Y_{Z_i}` and `Ũ_i := des_i⁻¹(U_i) → U_i` its restriction;
`Ỹ` is the manifold obtained by gluing the `Ũ_i` along the `Ũ_ij`, and `des : Ỹ → Y` is a proper
bimeromorphic morphism [Wlo09, §4.3]; the desingularization of a germ commutes with local
analytic isomorphisms [Wlo09, §4, (3)⇒(4)]. Kollár observes that a resolution functor on
neighbourhoods of compact sets that commutes with open embeddings yields a resolution of every
analytic space that is an increasing union of compact subsets [Kol07, 44], which is his
Theorem 45 [Kol07, Theorem 45]. The cover is taken here as an EXHAUSTION `U_0 ⋐ U_1 ⋐ ⋯`,
`⋃ U_n = X` (an analytic space is countable at infinity and locally compact Hausdorff,
[Hir64, Ch. 0, §1, p. 120]), interchangeable with Włodarczyk's locally finite cover. For an
embedded desingularization functor `bed : BEDanFamStar 𝕜`:

* `BEDanFamStar.ExhaustionGluing bed X`: the gluing datum — an exhaustion `U_n` of `X` by
  relatively compact opens, local embedding data `D_n` over each `U_n` with a gluing datum each
  (`PieceGlue.lean`), and a `GlueOver` of the pieces `resolutionOn (D n) bed` (the
  `Ũ_n := des_n⁻¹(U_n)`, indexed by `ULift ℕ` for the universe of the gluing construction) over
  `X` along the overlaps `U_n ∩ U_m` — the transitions are the open embeddings `R(U_n) ↪ R(U_m)`
  between the resolutions over nested members (`resolutionOn_indep` in `GluingProperties.lean`:
  an open embedding of germs extends to an open embedding of desingularizations,
  [Wlo09, §4, (3)⇒(4)]), the cocycle identity by their uniqueness, and the glued space is Hausdorff
  by the closed-graph criterion; its existence for reduced `X` under `hbed : bed.IsEmbeddedDesing`
  is `resolutionGlues_of_isEmbeddedDesing` (`GluingProperties.lean`), the proposition being
  `BEDanFamStar.ResolutionGlues bed X := Nonempty (ExhaustionGluing bed X)`;
* `BEDanFamStar.resolutionPair bed X`: for reduced `X` with a gluing datum the glued space with
  its descended map, otherwise the pair `⟨X, 𝟙 X⟩` — the value OFF THE CLASS of reduced spaces (the
  assignment `ResolutionAssignment.space` of the resolution theorem `exists_functorial_resolution`
  is defined on every analytic space while its clauses are stated for reduced ones; compare
  `Hironaka.Resolution.BR_eq_nil_of_not_class` for the algebraic functor) as the outer `if`, and
  the fallback for a missing gluing datum (never taken under `hbed`) as the inner one;
* `BEDanFamStar.resolution bed X : AnalyticSpace 𝕜` (`R(X)`) and
  `BEDanFamStar.resolutionMap bed X : resolution bed X ⟶ X` (`Π_X`); `bed` first, so that
  `bed.resolution : AnalyticSpace 𝕜 → AnalyticSpace 𝕜` is the field `space` of a
  `ResolutionAssignment` and `bed.resolutionMap` its `map`. Unfolding lemmas for every branch:
  `resolutionPair_eq_of_glues`, `resolutionPair_eq_of_not_glues`,
  `resolutionPair_eq_of_not_isReduced`, `resolution_eq_of_not_isReduced`,
  `resolutionMap_heq_of_not_isReduced`.

`resolution bed X` is a `K`-space glued with open-embedding transitions; it is a different
construction from the charted manifold `limitManifold` of a compatible family of successions, which
is used for the resolution of manifolds. `hbed` binds no definition.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set
open AnalyticSpace KLocallyRingedSpace

universe u

namespace Hironaka.Manifold.BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜] (bed : BEDanFamStar.{u} 𝕜)
  (X : AnalyticSpace.{u} 𝕜)

/-- **A gluing datum along an exhaustion** ([Wlo09, §4.3]; [Kol07, 44]) — relatively compact opens
`U_0 ⋐ U_1 ⋐ ⋯` exhausting `X`, local embedding data `D_n` over each `U_n` with a gluing datum
each, and the gluing over `X` of the pieces `Ũ_n := resolutionOn (D n) bed` along the overlaps
`U_n ∩ U_m`. -/
structure ExhaustionGluing where
  /-- The exhaustion by relatively compact opens. -/
  U : ℕ → Opens X
  isCompact_closure_U : ∀ n, IsCompact (closure (U n : Set X))
  closure_U_subset_succ : ∀ n, closure (U n : Set X) ⊆ U (n + 1)
  iUnion_U : ⋃ n, (U n : Set X) = univ
  /-- Local embedding data over each member of the exhaustion. -/
  D : ∀ n, LocalEmbeddingData 𝕜 X (U n)
  /-- Each member is resolved by a genuine gluing of the local resolutions of its pieces. -/
  glues : ∀ n, (D n).ResolutionGluesOn bed
  /-- The gluing over `X` of the restricted resolutions `Ũ_n → U_n` along `U_n ∩ U_m`. -/
  glue : GlueOver X (fun n : ULift.{u} ℕ => (D n.down).resolutionOn bed)
    (fun n => (D n.down).resolutionOnToSpace bed) (fun n => U n.down)

/-- **A gluing datum along an exhaustion exists**; its proof for reduced `X` under
`hbed : bed.IsEmbeddedDesing` is `resolutionGlues_of_isEmbeddedDesing` (`GluingProperties.lean`). -/
abbrev ResolutionGlues : Prop := Nonempty (bed.ExhaustionGluing X)

open Classical in
/-- **The resolving space with its map**, as a pair (Włodarczyk's `Ỹ_Z := ⋃ Ṽ_{i,Z_i}`
[Wlo09, §4, (3)⇒(4)]; Kollár's resolution functor on all analytic spaces [Kol07, Theorem 45]) — for
reduced `X` with a gluing datum the glued space and the descended map; off the class of reduced
spaces (`R(X) := X`, `Π_X := 𝟙`) or without a gluing datum (a fallback never taken under `hbed`)
the pair `⟨X, 𝟙 X⟩`. -/
def resolutionPair :
    Σ R : AnalyticSpace.{u} 𝕜, (R ⟶ X) :=
  if _hX : X.IsReduced then
    (if h : bed.ResolutionGlues X then ⟨h.some.glue.gluedOver, h.some.glue.descMap⟩
      else ⟨X, 𝟙 X⟩)
  else ⟨X, 𝟙 X⟩

/-- **The resolving space `R(X) = resolution bed X`** — the glued space of the restricted
resolutions along an exhaustion (Włodarczyk's `Ỹ` [Wlo09, §4.3]); `X` itself off the class of
reduced spaces. -/
def resolution : AnalyticSpace.{u} 𝕜 := (bed.resolutionPair X).1

/-- **The resolution map `Π_X = resolutionMap bed X : R(X) → X`** — the descended map `des : Ỹ → Y`
[Wlo09, §4.3]; the identity off the class of reduced spaces. -/
def resolutionMap : bed.resolution X ⟶ X :=
    (bed.resolutionPair X).2

/-! ### Unfolding lemmas -/

open Classical in
/-- On a reduced `X` with a gluing datum, the pair is the chosen datum's glued space and
descended map. -/
theorem resolutionPair_eq_of_glues (hX : X.IsReduced) (h : bed.ResolutionGlues X) :
    bed.resolutionPair X = ⟨h.some.glue.gluedOver, h.some.glue.descMap⟩ := by
  unfold resolutionPair
  rw [dite_eq_left hX, dite_eq_left h]

open Classical in
/-- On a reduced `X` without a gluing datum, the pair is `⟨X, 𝟙 X⟩` (a branch never taken under
`hbed`). -/
theorem resolutionPair_eq_of_not_glues (hX : X.IsReduced) (h : ¬ bed.ResolutionGlues X) :
    bed.resolutionPair X = ⟨X, 𝟙 X⟩ := by
  unfold resolutionPair
  rw [dite_eq_left hX, dite_eq_right h]

open Classical in
/-- Off the class of reduced spaces the pair is `⟨X, 𝟙 X⟩` (the analytic counterpart of
`Hironaka.Resolution.BR_eq_nil_of_not_class`). -/
theorem resolutionPair_eq_of_not_isReduced (hX : ¬ X.IsReduced) :
    bed.resolutionPair X = ⟨X, 𝟙 X⟩ := by
  unfold resolutionPair
  rw [dite_eq_right hX]

/-- On a reduced `X` with a gluing datum, `R(X)` is the chosen glued space. -/
theorem resolution_eq_of_glues (hX : X.IsReduced) (h : bed.ResolutionGlues X) :
    bed.resolution X = h.some.glue.gluedOver :=
  congrArg Sigma.fst (bed.resolutionPair_eq_of_glues X hX h)

/-- **The value off the class**: `R(X) = X` for a non-reduced `X`. -/
theorem resolution_eq_of_not_isReduced (hX : ¬ X.IsReduced) : bed.resolution X = X :=
  congrArg Sigma.fst (bed.resolutionPair_eq_of_not_isReduced X hX)

/-- `Π_X` is (heterogeneously) the identity for a non-reduced `X`. -/
theorem resolutionMap_heq_of_not_isReduced (hX : ¬ X.IsReduced) :
    HEq (bed.resolutionMap X) (𝟙 X) :=
  (Sigma.ext_iff.mp (bed.resolutionPair_eq_of_not_isReduced X hX)).2

end Hironaka.Manifold.BEDanFamStar

end
