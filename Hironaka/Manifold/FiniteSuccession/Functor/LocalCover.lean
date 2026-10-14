/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
public import Hironaka.Manifold.Submanifold
import Hironaka.Manifold.Chart.Transport
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# The local cover `X' = ∐ Uᵢ → X` of a triple

For any `X`, choose an open affine cover `X = ⋃ Uᵢ` and let `X' := ∐ Uᵢ`; then `X'` is affine and
there is a smooth surjection `g : X' → X` (the proof of [Kol07, Proposition 37]). On manifolds: a
countable cover by chart domains (second countability), `X'` their disjoint union
(`sigmaManifold`), `g` the coproduct of the inclusions, a surjective coproduct of analytic open
embeddings, and the triple on `X'` the pullback data of `T` along `g`, a local triple (each chart
domain is a chart union with one piece, its own chart restricted; the disjoint union of chart
unions is one). The inclusion of an open subset is an analytic open embedding (its local inverse
the codomain restriction of the identity, analytic by Mathlib's `ContMDiffAt.subtypeVal_comp_iff`).
The file also records that a closed submanifold of an open subset `U`, read in the bundled `U`,
is a closed submanifold of the manifold `U` (`IsClosedSubmanifoldOn.restrict`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The inclusion of an open subset is an analytic open embedding -/

section Inclusion

variable (M) (U : Opens M)

open scoped Classical in
/-- The local inverse of the inclusion `U → M` at a point of `U`: the codomain restriction of the
identity on `U`, an arbitrary point off `U`. -/
def inclusionInv (x : U) : M → M.restrict U := fun y => if h : y ∈ U then ⟨y, h⟩ else x

open scoped Classical in
theorem inclusionInv_of_mem (x : U) {y : M} (hy : y ∈ U) : inclusionInv M U x y = ⟨y, hy⟩ := by
  unfold inclusionInv
  exact dite_eq_left hy

open scoped Classical in
theorem val_inclusionInv_of_mem (x : U) {y : M} (hy : y ∈ U) :
    M.inclusion U (inclusionInv M U x y) = y := by
  change (inclusionInv M U x y).1 = y
  rw [inclusionInv_of_mem M U x hy]

/-- The inclusion of an open subset as an analytic isomorphism onto it. -/
def inclusionPartialDiffeomorph (x : U) :
    PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (M.restrict U) M ω where
  toFun := M.inclusion U
  invFun := inclusionInv M U x
  source := univ
  target := U
  map_source' y _ := y.2
  map_target' _ _ := mem_univ _
  left_inv' y _ := by
    change inclusionInv M U x y.1 = y
    rw [inclusionInv_of_mem M U x y.2]
    exact Subtype.ext rfl
  right_inv' y hy := val_inclusionInv_of_mem M U x hy
  open_source := isOpen_univ
  open_target := U.2
  contMDiffOn_toFun := (M.inclusion U).contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    intro y hy
    refine ContMDiffAt.contMDiffWithinAt ?_
    have hval : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω ((Subtype.val : U → M) ∘ inclusionInv M U x) y := by
      refine contMDiffAt_id.congr_of_eventuallyEq ?_
      filter_upwards [U.2.mem_nhds hy] with z hz
      exact val_inclusionInv_of_mem M U x hz
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E) ω) (inclusionInv M U x) univ y).mp hval

/-- The inclusion of an open subset is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_inclusion :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (M.inclusion U) := fun x =>
  IsLocalDiffeomorphAt.of_eqOn (inclusionPartialDiffeomorph M U x) (mem_univ x) fun _ _ => rfl

/-- The inclusion of an open subset is an analytic open embedding. -/
theorem isAnalyticOpenEmbedding_inclusion : IsAnalyticOpenEmbedding (M.inclusion U) :=
  ⟨isLocalDiffeomorph_inclusion M U, Subtype.val_injective⟩

theorem range_inclusion : range (M.inclusion U) = U := Subtype.range_val

end Inclusion

/-! ### A chart domain is a chart union with one piece -/

/-- The chart domain of a point, as an open subset. -/
def chartDomain (x : M) : Opens M := ⟨(chartAt E x).source, (chartAt E x).open_source⟩

theorem mem_chartDomain (x : M) : x ∈ chartDomain x := mem_chart_source E x

/-- A chart domain, as a manifold, is a countable chart union with one piece — its own chart
restricted (Mathlib's chart of the open subset at the point). -/
theorem isCountableChartUnion_restrict_chartDomain (x : M) :
    (M.restrict (chartDomain x)).IsCountableChartUnion := by
  refine ⟨PUnit, inferInstance, fun _ => univ, fun _ => isClopen_univ, ?_, iUnion_const univ,
    fun _ => ?_⟩
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · refine ⟨chartAt E (⟨x, mem_chartDomain x⟩ : chartDomain x),
      IsManifold.chart_mem_maximalAtlas _, ?_⟩
    change ((chartAt E (⟨x, mem_chartDomain x⟩ : chartDomain x)).source : Set (chartDomain x)) =
      univ
    rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    ext y
    exact ⟨fun _ => mem_univ y, fun _ => y.2⟩

/-! ### The local cover -/

/-- A countable set of points whose chart domains cover `M` (second countability). -/
theorem exists_countable_chartDomain_cover :
    ∃ t : Set M, t.Countable ∧ ⋃ x ∈ t, (chartDomain x : Set M) = univ := by
  obtain ⟨t, ht, hcov⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x : M => (chartDomain x : Set M))
      fun x => (chartDomain x).2
  refine ⟨t, ht, hcov.trans (eq_univ_of_forall fun y => mem_iUnion.mpr ⟨y, mem_chartDomain y⟩)⟩

/-! ### Closed submanifolds of an open subset, read in the bundled open subset -/

section Restrict

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (U : Opens M)

/-- The inverse of the inclusion of `U` maps a subset of `U` onto its preimage in the bundled
`U`. -/
theorem image_inclusionInv_eq (p : M.restrict U) (Y : Set M) :
    ⇑(inclusionPartialDiffeomorph M U p).symm ''
        (Y ∩ (inclusionPartialDiffeomorph M U p).symm.source) =
      ⇑(M.inclusion U) ⁻¹' Y ∩ (inclusionPartialDiffeomorph M U p).symm.target := by
  ext q
  constructor
  · rintro ⟨y, ⟨hyY, hyU⟩, rfl⟩
    refine ⟨?_, Set.mem_univ _⟩
    change M.inclusion U (inclusionInv M U p y) ∈ Y
    rw [val_inclusionInv_of_mem M U p hyU]
    exact hyY
  · rintro ⟨hq, -⟩
    refine ⟨q.1, ⟨hq, q.2⟩, ?_⟩
    change inclusionInv M U p q.1 = q
    rw [inclusionInv_of_mem M U p q.2]
    rfl

/-- A closed submanifold of the
open subset `U` (`IsClosedSubmanifoldOn`) is a closed submanifold of the manifold `U` —
its adapted charts transported along the inverse of the inclusion (`transportChart`). -/
theorem IsClosedSubmanifoldOn.restrict {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifoldOn ψ₀ (U : Set M) Y c) :
    IsClosedSubmanifold ψ₀ (⇑(M.inclusion U) ⁻¹' Y : Set (M.restrict U)) c where
  isClosed := hY.1
  exists_adaptedChart := by
    intro p hp
    obtain ⟨φ, σ, hpφ, -, hφ⟩ := hY.2 p.1 ⟨hp, p.2⟩
    refine ⟨transportChart (inclusionPartialDiffeomorph M U p).symm φ, σ, ?_,
      isAdaptedChart_transportChart _ (image_inclusionInv_eq U p Y) hφ⟩
    rw [transportChart_source]
    exact ⟨Set.mem_univ _, hpφ⟩

end Restrict

end Manifold

end
