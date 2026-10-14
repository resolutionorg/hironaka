/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Chart.Cotangent
public import Hironaka.Manifold.Snc.Trace
public import Hironaka.Resolution.Analytic.Functor.ModifiedMarkedFam
import Hironaka.Manifold.AdaptedChart
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.Chart.Adapted
import Hironaka.Manifold.Chart.Order
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.IdealSheaf.LogDerivRestrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Sheaf.LocalRing
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Snc.Restrict
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Ideal
import Hironaka.Resolution.Analytic.MaximalContact.CommonCharts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.GDelta.MetrizableSpace


/-!
# The stop predicate on a hypersurface of maximal contact: descent and lift

The modified marked resolution recurses on the dimension inside its first step
([Wlo09, Theorem 7.4.1]): the functor one dimension down runs on the restriction of the ideal to
the hypersurface of maximal contact `H⁺` and its centres are pushed forward. The two clauses of the
structure `BMOmodFam` about the stop predicate `IsSmoothTransversalIdealAt` therefore have to move
between the ambient manifold and `H`, as in Włodarczyk's argument for the strict transforms
([Wlo05, Theorem 4.7.1, proof]: the predicate for `(F, J)` at a point `y ∈ H` descends to the trace
family and the restricted ideal on `H`, and the predicate on `H` lifts back because `u ∈ J` for the
equation `u` of `H`, "since `u ∈ σ^c(I)` it follows that `σ^c(I) = I_{Ỹ₁}`"). This module proves
the two directions and the chart facts they share; the persistence half is `StopPersistence.lean`.

* Chart facts. `exists_chart_of_linearIndependent_linearPart`: `n` sections near `y`, vanishing at
  `y`, whose linear parts in one chart of the maximal atlas are linearly independent, are the
  coordinates (up to a permutation of the indices) of a chart of the maximal atlas at `y`
  (`exists_chart_extending` read through the linear parts of `Chart/Cotangent.lean`).
  `exists_eq_sum_of_germ_mem_span`: a germ in the ideal spanned by finitely many germs is, on a
  neighbourhood, a combination of their representatives with section coefficients.
  `IsClosedSubmanifold.restrictStalk_coord_eq_coord_chartOn`: the restriction to a closed
  submanifold of a coordinate germ off the block of an adapted chart is the corresponding coordinate
  germ of the induced chart. `IsSncChartAt.frequently_notMem_of_notMem_range`: in a chart adapted to
  `H` which is a chart with simple normal crossings for `F`, a member whose coordinate is off the
  block of `H` does not contain `H` near the point.
* Descent. `IsSmoothTransversalIdealAt.restrict_maximalContact`: for `H` of maximal contact at the
  mark `1` (`𝓘_H ≤ J`), `y ∈ H` in the cosupport of `J`, and the predicate for `(F, J)` at `y`, the
  predicate holds on the bundled `H` for the trace family and `J|_H`. The equation `u` of `H` lies
  in `J_y = (z_σ)` and not in `𝔪_y²`, so a coefficient `a_{i₀}` is a unit near `y`
  (`linearPart_mul_of_mem_maximalIdeal`) and `u` replaces the coordinate `z_{σ i₀}`
  (`exists_chart_of_linearIndependent_linearPart` with `linearIndependent_update_tilt`); in the new
  chart the members through `y` stay coordinate hyperplanes, `H = {u = 0}`, and
  `J = (u, z_{σ i}, i ≠ i₀)` (`exists_eq_sum_of_germ_mem_span`); the induced chart of `H` is a
  chart with simple normal crossings for the trace family (`IsSncChartAt.restrict_isSncChartAt`,
  `frequently_notMem_of_notMem_range`) on which `J|_H` is spanned by the `c − 1` restricted
  coordinates (`stalkIdeal_pullback`, `germMap_inclusionMap`,
  `restrictStalk_coord_eq_coord_chartOn`, `restrictStalk_coord_sub`).
* Lift. `IsSmoothTransversalIdealAt.of_restrict_maximalContact`: for `H` of maximal contact with
  `F ∪ H` of simple normal crossings and the members not containing `H` (`HasSncWithProper`),
  `y ∈ H` in the cosupport of `J`, and the predicate on `H` for the trace family and `J|_H`, the
  predicate holds for `(F, J)` at `y`. An adapted chart `φₐ` of `H` which is a chart with simple
  normal crossings for `F` gives the retraction `r` onto `H` along the `u`-direction (the inverse
  of the induced chart after the projection off the block); the new ambient coordinates are `u` and
  the cylinder extensions `w_m ∘ r` of the coordinates of the chart of the hypersurface, independent
  because the linear parts of the `w_m` in the induced chart form a basis
  (`linearIndependent_cotangentClass_iff_linearPart`) and `u` is transverse. In the chart `φₐ` the
  members are cylinders over their traces, so they are coordinate hyperplanes of the new chart;
  `H = {u = 0}`; at `a ∈ H` the ideal is `J_a = (u) + (J|_H)_a` lifted (`ker_restrictStalk_eq_span`,
  `Ideal.comap_map_of_surjective`, `restrictStalk_surjective`), and off `H` it is the unit ideal.

The identification of the transforms and centres of the pushed-forward run with those of the run one
dimension down is `markedTransformSeq_pullback_pushforwardIncl`, `support_center_pushforward` and
`noEmptyCenters_pushforwardRestrict`, which `ClausePushforward.lean` and
`ClauseClosedEmbedding.lean` use on the way to the two clauses;
`BlowUpSequence.toSuccession_pushforward` and `pushforwardRestrictOf_eq` are the forms used by the
closed-embedding functor (`ClosedEmbeddingFam.lean`) and the restriction bridge (`BDBridge.lean`).
-/

@[expose] public section


noncomputable section

open Set Topology TopologicalSpace Filter Opposite CategoryTheory
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The chart facts -/

/-- `n` sections near `y`, vanishing at `y`, whose linear parts in one chart of the maximal atlas
are linearly independent, are the coordinates (up to a permutation `σ` of the indices) of a chart of
the maximal atlas at `y` whose source lies in their domain (`exists_chart_extending` for `n`
sections, read through their linear parts). -/
theorem _root_.Hironaka.Manifold.exists_chart_of_linearIndependent_linearPart {U : Opens M} {y : M}
    (hyU : y ∈ U)
    (f : Fin n → (structureSheaf 𝕜 E M).presheaf.obj (op U)) (hf0 : ∀ i, f i ⟨y, hyU⟩ = 0)
    {φ : OpenPartialHomeomorph M E} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M)
    (hyφ : y ∈ φ.source)
    (hind : LinearIndependent 𝕜 fun i =>
      linearPart E ψ φ hφ hyφ ((structureSheaf 𝕜 E M).presheaf.germ U y hyU (f i))) :
    ∃ (e : OpenPartialHomeomorph M E) (σ : Fin n ↪ Fin n),
      e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M ∧ y ∈ e.source ∧ e.source ⊆ U ∧
        ∀ x ∈ e.source, ∀ i, extendSection 𝕜 E (f i) x = ψ (e x) (σ i) := by
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  have hind' : HasIndependentDifferentialsAt E (fun i => extendSection 𝕜 E (f i)) y := by
    rw [hasIndependentDifferentialsAt_iff_linearIndependent_cotangentClass' E hyU f,
      linearIndependent_cotangentClass_iff_linearPart E ψ φ hφ hyφ]
    exact hind
  have hz : ∀ i, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (extendSection 𝕜 E (f i)) y := fun i =>
    (contMDiffOn_extendSection (f i)).contMDiffAt (U.2.mem_nhds hyU)
  have hz0 : ∀ i, extendSection 𝕜 E (f i) y = 0 := fun i => by
    rw [extendSection_of_mem 𝕜 E _ hyU]
    exact hf0 i
  obtain ⟨e, σ, he, hye, -, hz'⟩ := exists_chart_extending ψ _ y hz hz0 hind'
  refine ⟨e.restrOpen U U.2, σ, ?_, ⟨hye, hyU⟩, fun x hx => hx.2, fun x hx i => hz' x hx.1 i⟩
  rw [OpenPartialHomeomorph.restrOpen_eq_restr]
  exact restr_mem_maximalAtlas _ he U.2

/-- From germs to sections: a germ in the ideal spanned by finitely many germs is, on a
neighbourhood, a combination of their representatives with section coefficients. -/
theorem _root_.Hironaka.Manifold.exists_eq_sum_of_germ_mem_span {U V : Opens M} {y : M}
    (hyU : y ∈ U) (hyV : y ∈ V)
    (s : (structureSheaf 𝕜 E M).presheaf.obj (op U)) {c : ℕ}
    (t : Fin c → (structureSheaf 𝕜 E M).presheaf.obj (op V))
    (h : (structureSheaf 𝕜 E M).presheaf.germ U y hyU s ∈
      Ideal.span (Set.range fun i => (structureSheaf 𝕜 E M).presheaf.germ V y hyV (t i))) :
    ∃ (W : Opens M) (_ : y ∈ W) (a : Fin c → (structureSheaf 𝕜 E M).presheaf.obj (op W)),
      ∀ x ∈ W, extendSection 𝕜 E s x =
        ∑ i, extendSection 𝕜 E (a i) x * extendSection 𝕜 E (t i) x := by
  classical
  obtain ⟨g, hg⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ((structureSheaf 𝕜 E M).presheaf.stalk y)).mp h
  choose W₀ hW₀ a₀ ha₀ using fun i => (structureSheaf 𝕜 E M).presheaf.exists_germ_eq (g i)
  -- the identity of germs of functions
  have hcs : ∀ (g : Fin c → M → 𝕜), (↑(∑ i, g i) : (𝓝 y).Germ 𝕜) = ∑ i, (↑(g i) : (𝓝 y).Germ 𝕜) :=
    fun g => map_sum (Filter.Germ.coeRingHom (𝓝 y)) g Finset.univ
  have hgerm : (↑(extendSection 𝕜 E s) : (𝓝 y).Germ 𝕜) =
      ↑(∑ i, extendSection 𝕜 E (a₀ i) * extendSection 𝕜 E (t i)) := by
    have h1 := congrArg (stalkToGerm 𝓘(𝕜, E) ω M y) hg
    rw [map_sum, stalkToGerm_structureSheaf_germ] at h1
    rw [← h1, hcs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, map_mul, ← ha₀ i, stalkToGerm_structureSheaf_germ,
      stalkToGerm_structureSheaf_germ, Filter.Germ.coe_mul]
  obtain ⟨W', hW', hW'o, hW'y⟩ := eventually_nhds_iff.mp (Filter.Germ.coe_eq.mp hgerm)
  let W : Opens M := ⟨W', hW'o⟩ ⊓ ⨅ i, W₀ i
  have hmemW : ∀ x, x ∈ W ↔ x ∈ W' ∧ ∀ i, x ∈ W₀ i := fun x => by
    change x ∈ ((⟨W', hW'o⟩ ⊓ ⨅ i, W₀ i : Opens M) : Set M) ↔ _
    rw [Opens.coe_inf, Opens.coe_iInf, Set.mem_inter_iff, Set.mem_iInter]
    rfl
  have hyW : y ∈ W := (hmemW y).mpr ⟨hW'y, hW₀⟩
  refine ⟨W, hyW, fun i => (structureSheaf 𝕜 E M).presheaf.map
    (homOfLE ((inf_le_right.trans (iInf_le _ i)) : W ≤ W₀ i)).op (a₀ i), fun x hx => ?_⟩
  obtain ⟨hxW', hxW₀⟩ := (hmemW x).mp hx
  rw [hW' x hxW', Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.mul_apply, extendSection_of_mem 𝕜 E _ (hxW₀ i), extendSection_of_mem 𝕜 E _ hx]
  rfl

/-- The coordinates off the block: the restriction to `Y` of a coordinate germ of an adapted chart
whose index is off the block `σ` is the corresponding coordinate germ of the induced chart
`chartOn` of `Y`. -/
theorem IsClosedSubmanifold.restrictStalk_coord_eq_coord_chartOn {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (a : Y) {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
    (h : IsAdaptedChart ψ Y φ σ) (ha : (a : M) ∈ φ.source) (k : {k : Fin n // k ∉ Set.range σ}) :
    letI := hY.chartedSpace
    hY.restrictStalk a (coord E ψ φ h.1 ha k.1) =
      coord (Fin (n - c) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n - c) → 𝕜)) (h.chartOn a.2)
        (h.chartOn_mem_maximalAtlas' hY a.2) ha (complEquiv σ k) := by
  let _i := hY.chartedSpace
  have hφ1 : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M := h.1
  have hχ : h.chartOn a.2 ∈ IsManifold.maximalAtlas 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y :=
    h.chartOn_mem_maximalAtlas' hY a.2
  refine stalkToGerm_injective _ _ _ _ ?_
  rw [hY.stalkToGerm_restrictStalk, stalkToGerm_coord hφ1 ha, stalkToGerm_coord hχ ha,
    germRestrict_coe]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [(h.chartOn a.2).open_source.mem_nhds
    (show a ∈ (h.chartOn a.2).source from ha)] with x hx
  have hx' : (x : M) ∈ φ.source := hx
  change extendSection 𝕜 E (chartSection E ψ φ hφ1 k.1) x =
    extendSection 𝕜 (Fin (n - c) → 𝕜) (chartSection (Fin (n - c) → 𝕜)
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - c) → 𝕜)) (h.chartOn a.2) hχ (complEquiv σ k)) x
  rw [extendSection_of_mem 𝕜 E _ hx', extendSection_of_mem 𝕜 _ _ hx]
  change ψ (φ x) k.1 = projCompl σ (ψ (φ x)) (complEquiv σ k)
  simp [projCompl]

/-- Two distinct coordinate hyperplanes: in a chart adapted to `H` which is a chart with simple
normal crossings for `F` at `a ∈ H`, a member through `a` whose coordinate is off the block of `H`
does not contain `H` near `a` (the hypothesis of `IsSncChartAt.restrict_isSncChartAt`). -/
theorem HypersurfaceFamily.IsSncChartAt.frequently_notMem_of_notMem_range {H : Set M} {c : ℕ}
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ H φ σ)
    {F : HypersurfaceFamily M} {a : M} {cidx : {j // a ∈ F.hyp j} → Fin n}
    (hc : F.IsSncChartAt ψ φ a cidx) (ha : a ∈ H) (j : {j // a ∈ F.hyp j})
    (hj : cidx j ∉ Set.range σ) : ∃ᶠ x in 𝓝[H] a, x ∉ F.hyp j.1 := by
  classical
  have haφ : a ∈ φ.source := hc.2.1
  have h0 : ψ (φ a) (cidx j) = 0 := (hc.2.2.1 j a haφ).mp j.2
  set v : 𝕜 → E := fun ε => ψ.symm (Function.update (ψ (φ a)) (cidx j) ε) with hv
  have hv0 : v 0 = φ a := by
    change ψ.symm (Function.update (ψ (φ a)) (cidx j) 0) = φ a
    conv_lhs => rw [← h0]
    rw [Function.update_eq_self, ψ.symm_apply_apply]
  have hvc : Continuous v :=
    ψ.symm.continuous.comp (continuous_const.update (cidx j) continuous_id)
  have hev : ∀ᶠ ε in 𝓝 (0 : 𝕜), v ε ∈ φ.target := by
    have := hvc.continuousAt (x := (0 : 𝕜))
    rw [ContinuousAt, hv0] at this
    exact this.eventually_mem (φ.open_target.mem_nhds (φ.map_source haφ))
  have hγ : Tendsto (fun ε => φ.symm (v ε)) (𝓝 (0 : 𝕜)) (𝓝 a) := by
    have h2 : Tendsto v (𝓝 (0 : 𝕜)) (𝓝 (φ a)) := by
      have := hvc.continuousAt (x := (0 : 𝕜))
      rw [ContinuousAt, hv0] at this
      exact this
    have := (φ.continuousAt_symm (φ.map_source haφ)).tendsto.comp h2
    rw [φ.left_inv haφ] at this
    exact this
  rw [frequently_nhdsWithin_iff]
  have hγ' : Tendsto (fun ε => φ.symm (v ε)) (𝓝[≠] (0 : 𝕜)) (𝓝 a) :=
    hγ.mono_left nhdsWithin_le_nhds
  refine hγ'.frequently (Filter.Eventually.frequently ?_)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev, self_mem_nhdsWithin] with ε hε hε0
  have hs : φ.symm (v ε) ∈ φ.source := φ.map_target hε
  have hcoord : ψ (φ (φ.symm (v ε))) = Function.update (ψ (φ a)) (cidx j) ε := by
    rw [φ.right_inv hε]
    exact ψ.apply_symm_apply _
  refine ⟨fun hmem => hε0 ?_, (hφ.2 _ hs).mpr fun i => ?_⟩
  · have := (hc.2.2.1 j _ hs).mp hmem
    rw [hcoord, Function.update_self] at this
    exact this
  · rw [hcoord, Function.update_of_ne (fun h => hj ⟨i, h⟩)]
    exact (hφ.2 a haφ).mp ha i

/-! ### The predicate descends to a hypersurface of maximal contact and lifts back -/

/-- **The descent of the predicate** ([Wlo05, Theorem 4.7.1, proof]; [Wlo09, Theorem 7.4.1]): for
`H` a smooth hypersurface of maximal contact at the mark `1` (`𝓘_H ≤ J` at `y`), a point `y ∈ H` of
the cosupport of `J`, and the predicate for `(F, J)` at `y`, the predicate holds on the bundled `H`
for the trace family and the restriction of `J` at `y`. The equation `u` of `H` lies in
`J_y = (z_σ)` and is not in `𝔪_y²`, so some coefficient is a unit and `u` replaces the coordinate
`z_{σ i₀}` (`exists_chart_of_linearIndependent_linearPart` with the linear parts of
`CommonCharts.lean`); in the new chart `J` is spanned by `u` and the other `z_{σ i}` near `y`
(`exists_eq_sum_of_germ_mem_span`), the members through `y` stay coordinate hyperplanes, and
`H = {u = 0}`; the induced chart of `H` is a chart with simple normal crossings for the trace family
(`IsSncChartAt.restrict_isSncChartAt`, `frequently_notMem_of_notMem_range`) on which `J|_H` is
spanned by the restricted coordinates (`restrictStalk_coord_eq_coord_chartOn`,
`stalkIdeal_pullback`, `germMap_inclusionMap`, `restrictStalk_coord_sub`). -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.restrict_maximalContact_of_stalkIdeal_le
    {H : Set M} (hH : IsClosedSubmanifold ψ H 1) {F : HypersurfaceFamily M}
    {J : AnalyticManifold.IdealSheaf M} {y : M}
        (hle : hH.idealSheaf.stalkIdeal y ≤ J.stalkIdeal y)
    (hy : y ∈ H) (hJy : J.stalkIdeal y ≠ ⊤) (h : F.IsSmoothTransversalIdealAt ψ J y) :
    (hH.traceFamily F).IsSmoothTransversalIdealAt (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff)
      ((⟨y, hy⟩ : H) : hH.toAnalyticManifold) := by
  classical
  let _i := hH.chartedSpace
  obtain ⟨c, φ, σ, cidx, hφ, hJ, hne⟩ := h
  have hφ1 : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M := hφ.1
  have hyφ : y ∈ φ.source := hφ.2.1
  -- the coordinates `z_σ` vanish at `y` (the stalk is proper)
  have hz0 : ∀ i, ψ (φ y) (σ i) = 0 := by
    intro i
    by_contra hne0
    exact hJy (Ideal.eq_top_of_isUnit_mem _ ((hJ y hyφ).symm ▸ Ideal.subset_span ⟨i, rfl⟩)
      (isUnit_coord_of_ne_zero φ hφ1 hyφ hne0))
  -- the equation `u` of `H`: an adapted chart `φH` of `H` at `y`
  obtain ⟨φH, τ, hyH, hφH⟩ := hH.exists_adaptedChart y hy
  have hφH1 : φH ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M := hφH.1
  have hu0 : ψ (φH y) (τ 0) = 0 := (hφH.2 y hyH).mp hy 0
  have hu_mem : coord E ψ φH hφH1 hyH (τ 0) ∈
      IsLocalRing.maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk y) :=
    coord_mem_maximalIdeal_of_eq_zero φH hφH1 hyH hu0
  -- `u ∈ J_y = (z_σ)_y`
  have huJ : coord E ψ φH hφH1 hyH (τ 0) ∈
      Ideal.span (Set.range fun i => coord E ψ φ hφ1 hyφ (σ i)) := by
    rw [← hJ y hyφ]
    refine hle ?_
    rw [hH.stalkIdeal_idealSheaf_eq_span hy hφH hyH]
    exact Ideal.subset_span ⟨0, rfl⟩
  -- `c ≥ 1`: with `c = 0` the stalk `J_y` would be zero and `u = 0`, against `u ∉ 𝔪_y²`
  rcases c with _ | c
  · exfalso
    rw [Set.range_eq_empty, Ideal.span_empty, Ideal.mem_bot] at huJ
    exact coord_notMem_maximalIdeal_sq φH hφH1 hyH (huJ ▸ Ideal.zero_mem _)
  -- `u = Σ aᵢ z_{σ i}` on an open `W ∋ y` (`exists_eq_sum_of_germ_mem_span`)
  obtain ⟨W, hyW, a, hWeq⟩ := exists_eq_sum_of_germ_mem_span (U := ⟨φH.source, φH.open_source⟩)
    (V := ⟨φ.source, φ.open_source⟩) hyH hyφ (chartSection E ψ φH hφH1 (τ 0))
    (fun i => chartSection E ψ φ hφ1 (σ i)) huJ
  -- the germ form of that identity at every point of `W`
  have hcs : ∀ (x : M) (g : Fin (c + 1) → M → 𝕜),
      (↑(∑ i, g i) : (𝓝 x).Germ 𝕜) = ∑ i, (↑(g i) : (𝓝 x).Germ 𝕜) :=
    fun x g => map_sum (Filter.Germ.coeRingHom (𝓝 x)) g Finset.univ
  have hgermW : ∀ x (hxW : x ∈ W) (hxH : x ∈ φH.source) (hxφ : x ∈ φ.source),
      coord E ψ φH hφH1 hxH (τ 0) = ∑ i, (structureSheaf 𝕜 E M).presheaf.germ W x hxW (a i) *
        coord E ψ φ hφ1 hxφ (σ i) := by
    intro x hxW hxH hxφ
    apply stalkToGerm_injective 𝓘(𝕜, E) ω M x
    have hR : stalkToGerm 𝓘(𝕜, E) ω M x (∑ i, (structureSheaf 𝕜 E M).presheaf.germ W x hxW (a i) *
        coord E ψ φ hφ1 hxφ (σ i)) =
        ↑(∑ i, extendSection 𝕜 E (a i) * extendSection 𝕜 E (chartSection E ψ φ hφ1 (σ i))) := by
      rw [map_sum, hcs]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, stalkToGerm_structureSheaf_germ, stalkToGerm_coord hφ1 hxφ, Filter.Germ.coe_mul]
    rw [hR, stalkToGerm_coord hφH1 hxH]
    refine Filter.Germ.coe_eq.mpr ?_
    filter_upwards [W.2.mem_nhds hxW] with z hz
    rw [Finset.sum_apply]
    exact hWeq z hz
  -- the linear part of `u` in the chart `φ`, and a nonzero coefficient `a i₀ (y)`
  have hlin : linearPart E ψ φ hφ1 hyφ (coord E ψ φH hφH1 hyH (τ 0)) =
      ∑ i, extendSection 𝕜 E (a i) y • (Pi.single (σ i) 1 : Fin n → 𝕜) := by
    rw [hgermW y hyW hyH hyφ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [linearPart_mul_of_mem_maximalIdeal E ψ φ hφ1 hyφ _
      (coord_mem_maximalIdeal_of_eq_zero φ hφ1 hyφ (hz0 i)), linearPart_coord_eq_single,
      eval_germ' W hyW]
  have hlin_ne : linearPart E ψ φ hφ1 hyφ (coord E ψ φH hφH1 hyH (τ 0)) ≠ 0 := fun h0 =>
    coord_notMem_maximalIdeal_sq φH hφH1 hyH (mem_sq_of_linearPart_eq_zero E ψ φ hφ1 hyφ hu_mem h0)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, extendSection 𝕜 E (a i₀) y ≠ 0 := by
    by_contra hcon
    refine hlin_ne ?_
    rw [hlin]
    exact Finset.sum_eq_zero fun i _ => by rw [not_not.mp (not_exists.mp hcon i), zero_smul]
  have hv : linearPart E ψ φ hφ1 hyφ (coord E ψ φH hφH1 hyH (τ 0)) (σ i₀) =
      extendSection 𝕜 E (a i₀) y := by
    rw [hlin, Finset.sum_apply, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      simp [(σ.injective.ne hi).symm]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  -- the open `U₀ = φ.source ∩ φH.source ∩ {x ∈ W | a i₀ x ≠ 0}` and the `n` sections on it
  have hWa : IsOpen {x : M | x ∈ W ∧ extendSection 𝕜 E (a i₀) x ≠ 0} :=
    (contMDiffOn_extendSection (a i₀)).continuousOn.isOpen_inter_preimage W.2 isOpen_ne
  let U₀ : Opens M := ⟨φ.source, φ.open_source⟩ ⊓ ⟨φH.source, φH.open_source⟩ ⊓ ⟨_, hWa⟩
  have hyU₀ : y ∈ U₀ := ⟨⟨hyφ, hyH⟩, hyW, hi₀⟩
  have hU₀φ : ∀ x ∈ U₀, x ∈ φ.source := fun _ hx => hx.1.1
  have hU₀H : ∀ x ∈ U₀, x ∈ φH.source := fun _ hx => hx.1.2
  have hU₀W : ∀ x ∈ U₀, x ∈ W := fun _ hx => hx.2.1
  have hU₀a : ∀ x ∈ U₀, extendSection 𝕜 E (a i₀) x ≠ 0 := fun _ hx => hx.2.2
  let rφ := (structureSheaf 𝕜 E M).presheaf.map
    (homOfLE (show U₀ ≤ ⟨φ.source, φ.open_source⟩ from fun x hx => hU₀φ x hx)).op
  let rH := (structureSheaf 𝕜 E M).presheaf.map
    (homOfLE (show U₀ ≤ ⟨φH.source, φH.open_source⟩ from fun x hx => hU₀H x hx)).op
  let cst : 𝕜 → (structureSheaf 𝕜 E M).presheaf.obj (op U₀) := fun r =>
    (structureSheaf 𝕜 E M).presheaf.map (homOfLE (le_top : U₀ ≤ ⊤)).op (constSection 𝕜 E M r)
  let f : Fin n → (structureSheaf 𝕜 E M).presheaf.obj (op U₀) := fun k =>
    if k = σ i₀ then rH (chartSection E ψ φH hφH1 (τ 0))
    else rφ (chartSection E ψ φ hφ1 k) + cst (-ψ (φ y) k)
  -- the values of the sections
  have hfval : ∀ x (hx : x ∈ U₀) k, extendSection 𝕜 E (f k) x =
      if k = σ i₀ then ψ (φH x) (τ 0) else ψ (φ x) k - ψ (φ y) k := by
    intro x hx k
    rw [extendSection_of_mem 𝕜 E _ hx]
    by_cases hk : k = σ i₀
    · rw [ite_eq_left hk]
      change (f k) ⟨x, hx⟩ = _
      simp only [f, ite_eq_left hk]
      rfl
    · rw [ite_eq_right hk]
      change (f k) ⟨x, hx⟩ = _
      simp only [f, ite_eq_right hk]
      change ψ (φ x) k + -ψ (φ y) k = _
      ring
  have hf0 : ∀ k, f k ⟨y, hyU₀⟩ = 0 := by
    intro k
    have := hfval y hyU₀ k
    rw [extendSection_of_mem 𝕜 E _ hyU₀] at this
    rw [this]
    split_ifs with hk
    · exact hu0
    · exact sub_self _
  -- the germs of the sections at `y` and their linear parts
  have hgerm : ∀ k, (structureSheaf 𝕜 E M).presheaf.germ U₀ y hyU₀ (f k) =
      if k = σ i₀ then coord E ψ φH hφH1 hyH (τ 0)
      else coord E ψ φ hφ1 hyφ k + const 𝕜 E M y (-ψ (φ y) k) := by
    intro k
    by_cases hk : k = σ i₀
    · rw [ite_eq_left hk]
      simp only [f, ite_eq_left hk]
      exact (structureSheaf 𝕜 E M).presheaf.germ_res_apply _ y hyU₀ _
    · rw [ite_eq_right hk]
      simp only [f, ite_eq_right hk]
      rw [map_add, (structureSheaf 𝕜 E M).presheaf.germ_res_apply _ y hyU₀,
        (structureSheaf 𝕜 E M).presheaf.germ_res_apply _ y hyU₀]
      rfl
  have hind : LinearIndependent 𝕜 fun k =>
      linearPart E ψ φ hφ1 hyφ ((structureSheaf 𝕜 E M).presheaf.germ U₀ y hyU₀ (f k)) := by
    have h1 : (fun k => linearPart E ψ φ hφ1 hyφ
        ((structureSheaf 𝕜 E M).presheaf.germ U₀ y hyU₀ (f k))) =
        Function.update (fun m => (Pi.single m 1 : Fin n → 𝕜) +
          (if m = σ i₀ ∧ σ i₀ ≠ σ i₀ then (Pi.single (σ i₀) 1 : Fin n → 𝕜) else 0)) (σ i₀)
          (linearPart E ψ φ hφ1 hyφ (coord E ψ φH hφH1 hyH (τ 0))) := by
      funext k
      rw [hgerm k]
      by_cases hk : k = σ i₀
      · subst hk
        rw [ite_eq_left rfl, Function.update_self]
      · rw [ite_eq_right hk, Function.update_of_ne hk, map_add, linearPart_const, add_zero,
          linearPart_coord_eq_single, ite_eq_right (fun h => hk h.1), add_zero]
    rw [h1]
    exact linearIndependent_update_tilt (σ i₀) (σ i₀) _ (hv ▸ hi₀) (fun h => absurd rfl h)
  -- the chart `e` with the coordinates `f` (`exists_chart_of_linearIndependent_linearPart`)
  obtain ⟨e, σe, he, hye, hesub, hecoord⟩ :=
    exists_chart_of_linearIndependent_linearPart ψ hyU₀ f hf0 hφ1 hyφ hind
  have heφ : ∀ x ∈ e.source, x ∈ φ.source := fun x hx => hU₀φ x (hesub hx)
  have heH : ∀ x ∈ e.source, x ∈ φH.source := fun x hx => hU₀H x (hesub hx)
  -- (E1) the members through `y` are coordinate hyperplanes of `e`
  have hE1 : ∀ (j : {j // y ∈ F.hyp j}), ∀ x ∈ e.source,
      x ∈ F.hyp j.1 ↔ ψ (e x) (σe (cidx j)) = 0 := by
    intro j x hx
    rw [← hecoord x hx, hfval x (hesub hx), ite_eq_right (hne j i₀),
      (hφ.2.2.1 j y hyφ).mp j.2, sub_zero]
    exact hφ.2.2.1 j x (heφ x hx)
  -- (E2) `H` is the coordinate hyperplane `σe (σ i₀)` of `e`
  have hE2 : ∀ x ∈ e.source, x ∈ H ↔ ψ (e x) (σe (σ i₀)) = 0 := by
    intro x hx
    rw [← hecoord x hx, hfval x (hesub hx), ite_eq_left rfl, hφH.2 x (heH x hx)]
    exact ⟨fun h => h 0, fun h i => by rw [Subsingleton.elim i 0]; exact h⟩
  -- (E3) the coordinate germs of `e`: `σe (σ i)`, `i ≠ i₀`, is `z_{σ i}`; `σe (σ i₀)` is `u`
  have hE3 : ∀ x (hx : x ∈ e.source) i, i ≠ i₀ →
      coord E ψ e he hx (σe (σ i)) = coord E ψ φ hφ1 (heφ x hx) (σ i) := by
    intro x hx i hi
    refine coord_eq_coord_of_eventuallyEq E he hx hφ1 (heφ x hx) ?_
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    rw [← hecoord z hz, hfval z (hesub hz), ite_eq_right (σ.injective.ne hi), hz0 i, sub_zero]
  have hE4 : ∀ x (hx : x ∈ e.source),
      coord E ψ e he hx (σe (σ i₀)) = coord E ψ φH hφH1 (heH x hx) (τ 0) := by
    intro x hx
    refine coord_eq_coord_of_eventuallyEq E he hx hφH1 (heH x hx) ?_
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    rw [← hecoord z hz, hfval z (hesub hz), ite_eq_left rfl]
  -- (E5) `J` on the source of `e` is spanned by the coordinates `σe (σ i)`
  have hE5 : ∀ x (hx : x ∈ e.source),
      J.stalkIdeal x = Ideal.span (Set.range fun i => coord E ψ e he hx (σe (σ i))) := by
    intro x hx
    have hxφ := heφ x hx
    have hxH := heH x hx
    have hxW := hU₀W x (hesub hx)
    have hunit : IsUnit ((structureSheaf 𝕜 E M).presheaf.germ W x hxW (a i₀)) := by
      rw [contMDiffSheafCommRing.isUnit_stalk_iff 𝓘(𝕜, E) ω M _]
      change eval 𝕜 E M x _ ≠ 0
      rw [eval_germ' W hxW]
      exact hU₀a x (hesub hx)
    have hsum := hgermW x hxW hxH hxφ
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)] at hsum
    rw [hJ x hxφ]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      change coord E ψ φ hφ1 hxφ (σ i) ∈
        Ideal.span (Set.range fun i => coord E ψ e he hx (σe (σ i)))
      by_cases hi : i = i₀
      · subst hi
        rw [← Ideal.unit_mul_mem_iff_mem _ hunit]
        have : (structureSheaf 𝕜 E M).presheaf.germ W x hxW (a i) * coord E ψ φ hφ1 hxφ (σ i) =
            coord E ψ φH hφH1 hxH (τ 0) - ∑ k ∈ Finset.univ.erase i,
              (structureSheaf 𝕜 E M).presheaf.germ W x hxW (a k) * coord E ψ φ hφ1 hxφ (σ k) := by
          rw [hsum]
          abel
        rw [this, ← hE4 x hx]
        refine Ideal.sub_mem _ (Ideal.subset_span ⟨i, rfl⟩) (Ideal.sum_mem _ fun k hk => ?_)
        rw [← hE3 x hx k (Finset.ne_of_mem_erase hk)]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
      · rw [← hE3 x hx i hi]
        exact Ideal.subset_span ⟨i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      change coord E ψ e he hx (σe (σ i)) ∈
        Ideal.span (Set.range fun i => coord E ψ φ hφ1 hxφ (σ i))
      by_cases hi : i = i₀
      · subst hi
        rw [hE4 x hx, hgermW x hxW hxH hxφ]
        exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
      · rw [hE3 x hx i hi]
        exact Ideal.subset_span ⟨i, rfl⟩
  -- the chart `e` is adapted to `H` and an snc chart of `F` at `y`
  have he_ad : IsAdaptedChart ψ H e (singleEmb (σe (σ i₀))) := isAdaptedChart_singleIdx he hE2
  have hc_e : F.IsSncChartAt ψ e y fun j => σe (cidx j) :=
    ⟨he, hye, fun j x hx => hE1 j x hx, σe.injective.comp hφ.2.2.2⟩
  have hnot : ∀ (j : {j // y ∈ F.hyp j}), σe (cidx j) ∉ Set.range (singleEmb (σe (σ i₀))) := by
    rintro j ⟨_, h⟩
    exact hne j i₀ (σe.injective h).symm
  have hne' : ∀ j, y ∈ F.hyp j → ∃ᶠ x in 𝓝[H] y, x ∉ F.hyp j := fun j hj =>
    hc_e.frequently_notMem_of_notMem_range ψ he_ad hy ⟨j, hj⟩ (hnot ⟨j, hj⟩)
  have hsnc := hc_e.restrict_isSncChartAt hH he_ad hy hne'
  -- the indices of the restricted coordinates: `σ (i₀.succAbove i)`, off the block of `H`
  have hnotσ : ∀ i : Fin c, σe (σ (i₀.succAbove i)) ∉ Set.range (singleEmb (σe (σ i₀))) := by
    rintro i ⟨_, h⟩
    exact Fin.succAbove_ne i₀ i (σ.injective (σe.injective h)).symm
  let σ' : Fin c ↪ Fin (n - 1) :=
    ⟨fun i => complEquiv (singleEmb (σe (σ i₀))) ⟨σe (σ (i₀.succAbove i)), hnotσ i⟩, by
      intro i j hij
      have := congrArg Subtype.val ((complEquiv (singleEmb (σe (σ i₀)))).injective hij)
      exact Fin.succAbove_right_injective (σ.injective (σe.injective this))⟩
  refine ⟨c, he_ad.chartOn hy, σ', _, hsnc, fun p hp => ?_, fun j i => ?_⟩
  · -- the restricted ideal at `p = ⟨x, hxH⟩ ∈ H`
    obtain ⟨x, hxH⟩ := p
    have hx' : x ∈ e.source := hp
    set p : hH.toAnalyticManifold := ((⟨x, hxH⟩ : H) : hH.toAnalyticManifold) with hpdef
    refine (IdealSheaf.stalkIdeal_pullback (φ := ⇑hH.inclusionMap)
      (hφ := hH.inclusionMap.contMDiff) J p).trans ?_
    rw [hH.germMap_inclusionMap p]
    change Ideal.map (hH.restrictStalk p) (J.stalkIdeal x) = _
    rw [hE5 x hx']
    refine (Ideal.map_span (hH.restrictStalk p) _).trans ?_
    refine (congrArg Ideal.span (Set.range_comp _ _).symm).trans ?_
    have hzero : hH.restrictStalk p (coord E ψ e he hx' (σe (σ i₀))) = 0 := by
      have h0 := hH.restrictStalk_coord_sub ⟨x, hxH⟩ he_ad hx' 0
      dsimp only at h0
      rw [singleEmb_apply, eval_coord, (hE2 x hx').mp hxH, map_zero, sub_zero] at h0
      exact h0
    have hrest : ∀ i : Fin c,
        hH.restrictStalk p (coord E ψ e he hx' (σe (σ (i₀.succAbove i)))) =
        coord (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
          (he_ad.chartOn hy) (he_ad.chartOn_mem_maximalAtlas' hH hy) hp (σ' i) := by
      intro i
      have h1 := hH.restrictStalk_coord_eq_coord_chartOn ψ ⟨x, hxH⟩ he_ad hx'
        ⟨σe (σ (i₀.succAbove i)), hnotσ i⟩
      dsimp only at h1
      refine h1.trans ?_
      exact coord_eq_coord_of_eventuallyEq (Fin (n - 1) → 𝕜)
        (he_ad.chartOn_mem_maximalAtlas' hH hxH) hx' (he_ad.chartOn_mem_maximalAtlas' hH hy) hp
        (Filter.Eventually.of_forall fun _ => rfl)
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      by_cases hi : i = i₀
      · subst hi
        change hH.restrictStalk p (coord E ψ e he hx' (σe (σ i))) ∈ _
        rw [hzero]
        exact Ideal.zero_mem _
      · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
        change hH.restrictStalk p (coord E ψ e he hx' (σe (σ (i₀.succAbove i')))) ∈ _
        rw [hrest i']
        exact Ideal.subset_span ⟨i', rfl⟩
    · rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨i₀.succAbove i, hrest i⟩
  · -- transversality on `H`
    intro hij
    have := congrArg Subtype.val ((complEquiv (singleEmb (σe (σ i₀)))).injective hij)
    exact hne ⟨j.1, j.2⟩ (i₀.succAbove i) (σe.injective this)

/-- **The descent of the predicate** ([Wlo05, Theorem 4.7.1, proof]; [Wlo09, Theorem 7.4.1]): for
`H` a smooth hypersurface of maximal contact at the mark `1` (`𝓘_H ≤ J`), a point `y ∈ H` of the
cosupport of `J`, and the predicate for `(F, J)` at `y`, the predicate holds on the bundled `H` for
the trace family and the restriction of `J` at `y`: the instance of
`restrict_maximalContact_of_stalkIdeal_le` at the inequality of stalks at `y` (the proof uses the
hypothesis `𝓘_H ≤ J` only at the point). -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.restrict_maximalContact {H : Set M}
    (hH : IsClosedSubmanifold ψ H 1) {F : HypersurfaceFamily M}
        {J : AnalyticManifold.IdealSheaf M}
    (hle : hH.idealSheaf ≤ J) {y : M} (hy : y ∈ H) (hJy : J.stalkIdeal y ≠ ⊤)
    (h : F.IsSmoothTransversalIdealAt ψ J y) :
    (hH.traceFamily F).IsSmoothTransversalIdealAt (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff)
      ((⟨y, hy⟩ : H) : hH.toAnalyticManifold) :=
  restrict_maximalContact_of_stalkIdeal_le ψ hH (IdealSheaf.le_def.mp hle y) hy hJy h

/-- **The lift of the predicate** ([Wlo05, Theorem 4.7.1, proof]: "since `u ∈ σ^c(I)` it follows
that `σ^c(I) = I_{Ỹ₁}`"; [Wlo09, Theorem 7.4.1]): for `H` of maximal contact at the mark `1`
(`𝓘_H ≤ J` near `y`) with `F ∪ H` of simple normal crossings and the members not containing `H`
(`HasSncWithProper`), a point `y ∈ H` of the cosupport of `J`, and the predicate on the bundled `H`
for the trace family and `J|_H` at `y`, the predicate holds for `(F, J)` at `y`. The cylinder
argument: in the adapted chart `φₐ` of `H` with simple normal crossings for `F`, the retraction `r`
onto `H` (the inverse of the induced chart after the projection off the block of `H`) makes every
member a cylinder over its trace; the new ambient coordinates are the equation `u` of `H` and the
cylinder extensions `w_m = φ_H(r x)_m − φ_H(y)_m` of all the coordinates of the chart `φ_H` of the
hypersurface, independent because the linear parts of the `w_m` are those of the chart of the
hypersurface (the chain rule through the projection;
`linearIndependent_cotangentClass_iff_linearPart`) and `u` is transverse
(`exists_chart_of_linearIndependent_linearPart`); in the new chart the members through `y` are the
coordinate hyperplanes of their trace coordinates, `H = {u = 0}`, `J = (u) + (J|_H lifted)` at the
points of `H` (`ker_restrictStalk_eq_span`, `Ideal.comap_map_of_surjective`; `hJy` keeps the
restricted stalk proper) and `J = ⊤` off `H`. -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.of_restrict_maximalContact_of_eventually_le
    {H : Set M} (hH : IsClosedSubmanifold ψ H 1) {F : HypersurfaceFamily M}
    (hFH : F.HasSncWithProper ψ H 1) {J : AnalyticManifold.IdealSheaf M} {y : M}
    (hle : ∀ᶠ x in 𝓝 y, hH.idealSheaf.stalkIdeal x ≤ J.stalkIdeal x) (hy : y ∈ H)
    (hJy : J.stalkIdeal y ≠ ⊤)
    (h : (hH.traceFamily F).IsSmoothTransversalIdealAt
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff)
      ((⟨y, hy⟩ : H) : hH.toAnalyticManifold)) :
    F.IsSmoothTransversalIdealAt ψ J y := by
  classical
  let _i := hH.chartedSpace
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  -- the open neighbourhood of `y` on which `𝓘_H ≤ J` holds stalkwise
  obtain ⟨N, hNle, hNopen, hyN⟩ : ∃ N : Set M,
      (∀ x ∈ N, hH.idealSheaf.stalkIdeal x ≤ J.stalkIdeal x) ∧ IsOpen N ∧ y ∈ N := by
    obtain ⟨v, hv, hvle⟩ := Filter.eventually_iff_exists_mem.mp hle
    obtain ⟨N, hNv, hNopen, hyN⟩ := mem_nhds_iff.mp hv
    exact ⟨N, fun x hx => hvle x (hNv hx), hNopen, hyN⟩
  set p₀ : H := ⟨y, hy⟩ with hp₀
  obtain ⟨c', φH, σ', cidx', hφH, hJH, hne'⟩ := h
  have hrefl : ∀ w : Fin (n - 1) → 𝕜, (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) w = w :=
    fun _ => rfl
  have hφH1 : φH ∈ IsManifold.maximalAtlas 𝓘(𝕜, Fin (n - 1) → 𝕜) ω H := hφH.1
  have hyφH : p₀ ∈ φH.source := hφH.2.1
  -- the ambient chart adapted to `H` and snc for `F` at `y`
  obtain ⟨φa, τ, cidxa, hφa, hca, hcaτ⟩ := hFH y hy
  have hφa1 : φa ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M := hφa.1
  have hyφa : y ∈ φa.source := hca.2.1
  have hu0 : ψ (φa y) (τ 0) = 0 := (hφa.2 y hyφa).mp hy 0
  have hτ : ∀ k, k ∉ Set.range τ ↔ k ≠ τ 0 := fun k =>
    ⟨fun h hk => h ⟨0, hk.symm⟩,
      fun h ⟨i, hi⟩ => h (hi.symm.trans (congrArg τ (Subsingleton.elim i 0)))⟩
  -- the induced chart `χ` of `H`, the retraction `r` and its domain `D`
  set χ := hφa.chartOn hy with hχdef
  have hχ1 : χ ∈ IsManifold.maximalAtlas 𝓘(𝕜, Fin (n - 1) → 𝕜) ω H :=
    hφa.chartOn_mem_maximalAtlas' hH hy
  have hyχ : p₀ ∈ χ.source := hyφa
  let r : M → H := fun x => hφa.symmAux hy (projCompl τ (ψ (φa x)))
  let D : Set M := φa.source ∩
    (fun x => ψ.symm (embedCompl τ (projCompl τ (ψ (φa x))))) ⁻¹' φa.target
  have hDo : IsOpen D :=
    ((ψ.symm.continuous.comp ((continuous_embedCompl τ).comp
      ((continuous_projCompl τ).comp ψ.continuous))).comp_continuousOn
        φa.continuousOn).isOpen_inter_preimage φa.open_source φa.open_target
  have hyD : y ∈ D := by
    refine ⟨hyφa, ?_⟩
    change ψ.symm (embedCompl τ (projCompl τ (ψ (φa y)))) ∈ φa.target
    rw [embedCompl_projCompl τ (fun i => by rw [Subsingleton.elim i 0]; exact hu0),
      ψ.symm_apply_apply]
    exact φa.map_source hyφa
  have hrD : ∀ x ∈ D, (r x : M) = φa.symm (ψ.symm (embedCompl τ (projCompl τ (ψ (φa x))))) :=
    fun x hx => hφa.coe_symmAux hy hx.2
  have hrφ : ∀ x ∈ D, (r x : M) ∈ φa.source := fun x hx => by
    rw [hrD x hx]
    exact φa.map_target hx.2
  have hrcoord : ∀ x ∈ D, ψ (φa (r x)) = embedCompl τ (projCompl τ (ψ (φa x))) := fun x hx => by
    rw [hrD x hx, φa.right_inv hx.2, ψ.apply_symm_apply]
  have hrH : ∀ x ∈ D, x ∈ H → (r x : M) = x := fun x hx hxH => by
    rw [hrD x hx, embedCompl_projCompl τ (fun i => (hφa.2 x hx.1).mp hxH i), ψ.symm_apply_apply,
      φa.left_inv hx.1]
  have hry : r y = p₀ := Subtype.ext (hrH y hyD hy)
  have hχsymm : ∀ x, r x = χ.symm (projCompl τ (ψ (φa x))) := fun _ => rfl
  have hrcont : ContinuousOn r D := by
    have h1 : ContinuousOn (fun x => projCompl τ (ψ (φa x))) D :=
      ((continuous_projCompl τ).comp ψ.continuous).comp_continuousOn
        (φa.continuousOn.mono Set.inter_subset_left)
    have h2 : Set.MapsTo (fun x => projCompl τ (ψ (φa x))) D χ.target := fun x hx => hx.2
    exact (χ.continuousOn_symm.comp h1 h2).congr fun x _ => hχsymm x
  -- the domain `U₀ = D ∩ r⁻¹(φH.source)` of the new coordinates
  have hU₀o : IsOpen (D ∩ r ⁻¹' φH.source) := hrcont.isOpen_inter_preimage hDo φH.open_source
  let U₀ : Opens M := ⟨D ∩ r ⁻¹' φH.source, hU₀o⟩
  have hyU₀ : y ∈ U₀ := ⟨hyD, by change r y ∈ φH.source; rw [hry]; exact hyφH⟩
  have hU₀D : ∀ x ∈ U₀, x ∈ D := fun _ hx => hx.1
  have hU₀r : ∀ x ∈ U₀, r x ∈ φH.source := fun _ hx => hx.2
  have hU₀φ : ∀ x ∈ U₀, x ∈ φa.source := fun x hx => (hU₀D x hx).1
  -- the cylinder coordinates `w m := φH (r x) m − φH p₀ m` and their smoothness on `U₀`
  let P : E →L[𝕜] (Fin (n - 1) → 𝕜) :=
    (ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜)
      (((complEquiv τ).symm k).1)).comp (ψ : E →L[𝕜] (Fin n → 𝕜))
  have hP : ∀ v, P v = projCompl τ (ψ v) := fun _ => rfl
  let w : Fin (n - 1) → M → 𝕜 := fun m x => φH (r x) m - φH p₀ m
  have hw_smooth : ∀ m, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (w m) U₀ := by
    intro m
    have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω (fun x => P (φa x)) U₀ :=
      P.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas (n := ω) hφa1).mono fun x hx => hU₀φ x hx)
    have h2 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω (fun x => χ.symm (P (φa x))) U₀ :=
      (contMDiffOn_symm_of_mem_maximalAtlas (n := ω) hχ1).comp h1 fun x hx => (hU₀D x hx).2
    have h3 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
        (fun x => φH (χ.symm (P (φa x)))) U₀ :=
      (contMDiffOn_of_mem_maximalAtlas (n := ω) hφH1).comp h2 fun x hx => hU₀r x hx
    exact ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin (n - 1) => 𝕜)
      m).contMDiff.comp_contMDiffOn h3).sub contMDiffOn_const
  let wsec : Fin (n - 1) → (structureSheaf 𝕜 E M).presheaf.obj (op U₀) := fun m =>
    sectionOfContMDiffOn (w m) U₀ (hw_smooth m)
  let usec : (structureSheaf 𝕜 E M).presheaf.obj (op U₀) := (structureSheaf 𝕜 E M).presheaf.map
    (homOfLE (show U₀ ≤ ⟨φa.source, φa.open_source⟩ from fun x hx => hU₀φ x hx)).op
    (chartSection E ψ φa hφa1 (τ 0))
  -- the indices: `kk m` is the ambient index of the `H`-coordinate `m`
  let kk : Fin (n - 1) → Fin n := fun m => ((complEquiv τ).symm m).1
  have hkkτ : ∀ m, kk m ∉ Set.range τ := fun m => ((complEquiv τ).symm m).2
  have hkk0 : ∀ m, kk m ≠ τ 0 := fun m => (hτ _).mp (hkkτ m)
  have hkk_inj : Function.Injective kk := fun m m' h =>
    (complEquiv τ).symm.injective (Subtype.ext h)
  have hmkk : ∀ m, complEquiv τ ⟨kk m, hkkτ m⟩ = m := fun m => by
    change complEquiv τ ⟨((complEquiv τ).symm m).1, _⟩ = m
    rw [Subtype.coe_eta]
    exact (complEquiv τ).apply_symm_apply m
  let f : Fin n → (structureSheaf 𝕜 E M).presheaf.obj (op U₀) := fun k =>
    if hk : k ∈ Set.range τ then usec else wsec (complEquiv τ ⟨k, hk⟩)
  have hfτ : f (τ 0) = usec := dite_eq_left (Set.mem_range_self 0)
  have hfkk : ∀ m, f (kk m) = wsec m := fun m => by
    rw [show f (kk m) = wsec (complEquiv τ ⟨kk m, hkkτ m⟩) from dite_eq_right (hkkτ m), hmkk m]
  -- the values of the sections
  have husec : ∀ x (hx : x ∈ U₀), extendSection 𝕜 E usec x = ψ (φa x) (τ 0) := fun x hx => by
    rw [extendSection_of_mem 𝕜 E _ hx]
    rfl
  have hwsec : ∀ m x (hx : x ∈ U₀), extendSection 𝕜 E (wsec m) x = φH (r x) m - φH p₀ m :=
    fun m x hx => by
      rw [extendSection_of_mem 𝕜 E _ hx]
      rfl
  have hf0 : ∀ k, f k ⟨y, hyU₀⟩ = 0 := by
    intro k
    by_cases hk : k ∈ Set.range τ
    · obtain ⟨i, rfl⟩ := hk
      rw [Subsingleton.elim i 0, hfτ]
      have := husec y hyU₀
      rw [extendSection_of_mem 𝕜 E _ hyU₀] at this
      rw [this]
      exact hu0
    · simp only [f, dite_eq_right hk]
      have := hwsec (complEquiv τ ⟨k, hk⟩) y hyU₀
      rw [extendSection_of_mem 𝕜 E _ hyU₀] at this
      rw [this, hry, sub_self]
  -- the germs at `y`
  have hgu : (structureSheaf 𝕜 E M).presheaf.germ U₀ y hyU₀ usec = coord E ψ φa hφa1 hyφa (τ 0) :=
    (structureSheaf 𝕜 E M).presheaf.germ_res_apply _ y hyU₀ _
  -- the linear parts: `u ↦ e_{τ 0}`, `w m ↦ embedCompl τ (Lχ m)`
  set Lχ : Fin (n - 1) → (Fin (n - 1) → 𝕜) := fun m =>
    linearPart (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) χ hχ1 hyχ
      (coord (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 hyφH m)
    with hLχ
  have hLχ_ind : LinearIndependent 𝕜 Lχ := by
    have h1 : LinearIndependent 𝕜 fun m => cotangentClass (Fin (n - 1) → 𝕜) p₀
        (coord (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 hyφH m) :=
      (linearIndependent_cotangentClass_iff_linearPart (Fin (n - 1) → 𝕜)
        (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 hyφH _).mpr
        (linearIndependent_linearPart_coord (Fin (n - 1) → 𝕜)
          (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 hyφH id Function.injective_id)
    exact (linearIndependent_cotangentClass_iff_linearPart (Fin (n - 1) → 𝕜)
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) χ hχ1 hyχ _).mp h1
  have hLχ_span : Submodule.span 𝕜 (Set.range Lχ) = ⊤ :=
    hLχ_ind.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, Module.finrank_fin_fun])
  have hPy : P (φa y) = χ p₀ := by
    rw [hP, ← hry, hχsymm y]
    exact (χ.right_inv hyD.2).symm
  -- the linear part of `w m` in the chart `φa`
  have hLP : ∀ m, linearPart E ψ φa hφa1 hyφa ((structureSheaf 𝕜 E M).presheaf.germ U₀ y hyU₀
      (wsec m)) = embedCompl τ (Lχ m) := by
    intro m
    -- the function `w m` read in the chart `φa` is `gH ∘ P` up to the constant, near `φa y`
    set gH : (Fin (n - 1) → 𝕜) → 𝕜 := fun v =>
      extendSection 𝕜 (Fin (n - 1) → 𝕜) (chartSection (Fin (n - 1) → 𝕜)
        (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 m) (χ.symm v) with hgH
    have hgH_diff : DifferentiableAt 𝕜 gH (χ p₀) := by
      have h1 : ContMDiffAt 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜) ω (extendSection 𝕜 (Fin (n - 1) → 𝕜)
          (chartSection (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH
            hφH1 m)) p₀ :=
        (contMDiffOn_extendSection _).contMDiffAt (φH.open_source.mem_nhds hyφH)
      have h2 : ContMDiffAt 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜) ω gH (χ p₀) :=
        ContMDiffAt.comp_of_eq h1 (contMDiffAt_chart_symm (Fin (n - 1) → 𝕜) χ hyχ hχ1)
          (χ.left_inv hyχ)
      exact (contMDiffAt_iff_contDiffAt.mp h2).differentiableAt (by simp)
    have hev : (extendSection 𝕜 E (wsec m) ∘ φa.symm) =ᶠ[𝓝 (φa y)]
        fun v => gH (P v) - φH p₀ m := by
      have hmem : ∀ᶠ v in 𝓝 (φa y), φa.symm v ∈ (U₀ : Set M) :=
        (φa.continuousAt_symm (φa.map_source hyφa)).eventually_mem
          (by rw [φa.left_inv hyφa]; exact U₀.2.mem_nhds hyU₀)
      filter_upwards [hmem, φa.open_target.mem_nhds (φa.map_source hyφa)] with v hv hvT
      have hrv : r (φa.symm v) = χ.symm (P v) := by
        rw [hχsymm, hP, φa.right_inv hvT]
      have hmemr : χ.symm (P v) ∈ φH.source := hrv ▸ hU₀r _ hv
      change extendSection 𝕜 E (wsec m) (φa.symm v) = gH (P v) - φH p₀ m
      rw [hwsec m _ hv, hgH]
      dsimp only
      congr 1
      rw [hrv]
      exact (extendSection_of_mem 𝕜 (Fin (n - 1) → 𝕜) (chartSection (Fin (n - 1) → 𝕜)
        (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 m) hmemr).symm
    have hfd : fderiv 𝕜 (extendSection 𝕜 E (wsec m) ∘ φa.symm) (φa y) =
        (fderiv 𝕜 gH (χ p₀)).comp P := by
      rw [hev.fderiv_eq, fderiv_sub_const, ← hPy]
      exact fderiv_comp (φa y) (hPy ▸ hgH_diff) P.differentiableAt |>.trans (by rw [P.fderiv])
    funext i
    rw [linearPart_apply, ← eval_coordDerivStalk, eval_coordDerivStalk_germ, hfd,
      ContinuousLinearMap.comp_apply, hP, ψ.apply_symm_apply]
    -- `projCompl τ (Pi.single i 1)` is `0` at `τ 0` and the basis vector `complEquiv τ i` else
    by_cases hi : i ∈ Set.range τ
    · have h0 : projCompl τ (Pi.single i (1 : 𝕜)) = 0 := by
        funext k
        simp only [projCompl, Pi.zero_apply, Pi.single_apply]
        rw [ite_eq_right]
        rintro rfl
        exact ((complEquiv τ).symm k).2 hi
      rw [h0, map_zero]
      obtain ⟨j, rfl⟩ := hi
      exact (embedCompl_apply_range τ _ j).symm
    · have h1 : projCompl τ (Pi.single i (1 : 𝕜)) = Pi.single (complEquiv τ ⟨i, hi⟩) 1 := by
        funext k
        simp only [projCompl, Pi.single_apply]
        congr 1
        apply propext
        constructor
        · intro h
          rw [← (complEquiv τ).apply_symm_apply k]
          congr 1
          exact Subtype.ext h
        · rintro rfl
          rw [Equiv.symm_apply_apply]
      rw [h1]
      change _ = embedCompl τ (Lχ m) i
      simp only [embedCompl, dite_eq_right hi, hLχ]
      -- `χ` carries `hH.chartedSpace`, the coordinate germ of `φH` the bundled manifold's instance:
      -- defeq at default transparency only, hence `erw`
      erw [linearPart_apply, ← eval_coordDerivStalk, eval_coordDerivStalk_germ]
      rfl
  -- the linear parts of the `n` sections and their independence
  set LP : Fin n → (Fin n → 𝕜) := fun k =>
    linearPart E ψ φa hφa1 hyφa ((structureSheaf 𝕜 E M).presheaf.germ U₀ y hyU₀ (f k)) with hLPdef
  have hLPτ : LP (τ 0) = Pi.single (τ 0) 1 := by
    rw [hLPdef]
    dsimp only
    rw [hfτ, hgu, linearPart_coord_eq_single]
  have hLPkk : ∀ m, LP (kk m) = embedCompl τ (Lχ m) := fun m => by
    rw [hLPdef]
    dsimp only
    rw [hfkk m]
    exact hLP m
  have hind : LinearIndependent 𝕜 LP := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_
      (by rw [Fintype.card_fin, Module.finrank_fin_fun])
    rw [← (Pi.basisFun 𝕜 (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [Pi.basisFun_apply]
    by_cases hk : k ∈ Set.range τ
    · obtain ⟨i, rfl⟩ := hk
      rw [Subsingleton.elim i 0, ← hLPτ]
      exact Submodule.subset_span ⟨τ 0, rfl⟩
    · have hk' : (Pi.single k (1 : 𝕜) : Fin n → 𝕜) =
          embedComplₗ τ (Pi.single (complEquiv τ ⟨k, hk⟩) 1) := by
        change _ = embedCompl τ (Pi.single (complEquiv τ ⟨k, hk⟩) 1)
        rw [embedCompl_single, Equiv.symm_apply_apply]
      rw [hk']
      have hmem : (Pi.single (complEquiv τ ⟨k, hk⟩) (1 : 𝕜) : Fin (n - 1) → 𝕜) ∈
          Submodule.span 𝕜 (Set.range Lχ) := by
        rw [hLχ_span]
        exact Submodule.mem_top
      have := Submodule.mem_map_of_mem (f := embedComplₗ τ) hmem
      rw [Submodule.map_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨kk m, hLPkk m⟩
  -- the ambient chart `e` with the coordinates `f` (`exists_chart_of_linearIndependent_linearPart`)
  obtain ⟨e, σe, he, hye, hesub, hecoord⟩ :=
    exists_chart_of_linearIndependent_linearPart ψ hyU₀ f hf0 hφa1 hyφa hind
  -- the chart restricted to the neighbourhood `N` on which `𝓘_H ≤ J` holds stalkwise
  obtain ⟨e, he, hye, hesub, hecoord, hesN⟩ : ∃ e' : OpenPartialHomeomorph M E,
      e' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M ∧ y ∈ e'.source ∧ e'.source ⊆ (U₀ : Set M) ∧
        (∀ x ∈ e'.source, ∀ i, extendSection 𝕜 E (f i) x = ψ (e' x) (σe i)) ∧ e'.source ⊆ N := by
    refine ⟨e.restrOpen N hNopen, ?_, ?_, ?_, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.restrOpen_eq_restr]
      exact restr_mem_maximalAtlas _ he hNopen
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact ⟨hye, hyN⟩
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact fun x hx => hesub hx.1
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact fun x hx i => hecoord x hx.1 i
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact fun x hx => hx.2
  have heU₀ : ∀ x ∈ e.source, x ∈ U₀ := fun x hx => hesub hx
  -- (G1) the coordinate `σe (τ 0)` of `e` is `u`; (G2) `σe (kk m)` is the cylinder coordinate
  have hG1 : ∀ x ∈ e.source, ψ (e x) (σe (τ 0)) = ψ (φa x) (τ 0) := fun x hx => by
    rw [← hecoord x hx, hfτ, husec x (heU₀ x hx)]
  have hG2 : ∀ x ∈ e.source, ∀ m, ψ (e x) (σe (kk m)) = φH (r x) m - φH p₀ m := fun x hx m => by
    rw [← hecoord x hx, hfkk m, hwsec m x (heU₀ x hx)]
  -- (G3) `H` is the coordinate hyperplane `σe (τ 0)` of `e`
  have hG3 : ∀ x ∈ e.source, x ∈ H ↔ ψ (e x) (σe (τ 0)) = 0 := fun x hx => by
    rw [hG1 x hx, hφa.2 x (hU₀φ x (heU₀ x hx))]
    exact ⟨fun h => h 0, fun h i => by rw [Subsingleton.elim i 0]; exact h⟩
  have he_ad : IsAdaptedChart ψ H e (singleEmb (σe (τ 0))) := isAdaptedChart_singleIdx he hG3
  -- (G4) the members through `y` are the coordinate hyperplanes `σe (kk (cidx' j))`
  have hG4 : ∀ (j : {j // y ∈ F.hyp j}), ∀ x ∈ e.source,
      x ∈ F.hyp j.1 ↔ ψ (e x) (σe (kk (cidx' ⟨j.1, j.2⟩))) = 0 := by
    intro j x hx
    have hxU := heU₀ x hx
    have hxD := hU₀D x hxU
    have hp₀j := (hφH.2.2.1 ⟨j.1, j.2⟩ p₀ hyφH).mp j.2
    rw [hrefl] at hp₀j
    have hrxj := hφH.2.2.1 ⟨j.1, j.2⟩ (r x) (hU₀r x hxU)
    rw [hrefl] at hrxj
    rw [hG2 x hx, hp₀j, sub_zero, ← hrxj]
    change x ∈ F.hyp j.1 ↔ (r x : M) ∈ F.hyp j.1
    rw [hca.2.2.1 j x (hU₀φ x hxU), hca.2.2.1 j (r x) (hrφ x hxD), hrcoord x hxD]
    simp only [embedCompl, dite_eq_right (hcaτ j), projCompl, Equiv.symm_apply_apply]
  have hcidx_inj : Function.Injective fun j : {j // y ∈ F.hyp j} =>
      σe (kk (cidx' ⟨j.1, j.2⟩)) := by
    intro j j' h
    dsimp only at h
    exact Subtype.ext (congrArg Subtype.val (hφH.2.2.2 (hkk_inj (σe.injective h))))
  have hc_e : F.IsSncChartAt ψ e y fun j => σe (kk (cidx' ⟨j.1, j.2⟩)) :=
    ⟨he, hye, fun j x hx => hG4 j x hx, hcidx_inj⟩
  -- (G5) the `H`-coordinates `σ'` vanish at `y` (the restricted stalk at `y` is proper)
  have hσ'0 : ∀ i, φH p₀ (σ' i) = 0 := by
    intro i
    by_contra hne0
    have hunit : IsUnit (coord (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
        φH hφH1 hyφH (σ' i)) := by
      refine isUnit_coord_of_ne_zero φH hφH1 hyφH ?_
      rw [hrefl]
      exact hne0
    have htop : (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff).stalkIdeal p₀ = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ ((hJH p₀ hyφH).symm ▸ Ideal.subset_span ⟨i, rfl⟩) hunit
    have htop' := (IdealSheaf.stalkIdeal_pullback (φ := ⇑hH.inclusionMap)
      (hφ := hH.inclusionMap.contMDiff) J p₀).symm.trans htop
    rw [Ideal.eq_top_iff_one, Ideal.mem_map_iff_of_surjective _
      (hH.germMap_inclusionMap_surjective p₀)] at htop'
    obtain ⟨s, hs, hs1⟩ := htop'
    refine hJy (Ideal.eq_top_of_isUnit_mem _ hs ?_)
    have : IsLocalHom (germMap ⇑hH.inclusionMap hH.inclusionMap.contMDiff p₀) :=
      isLocalHom_germMap (φ := ⇑hH.inclusionMap) (hφ := hH.inclusionMap.contMDiff) p₀
    exact isUnit_of_map_unit (germMap ⇑hH.inclusionMap hH.inclusionMap.contMDiff p₀) s
      (hs1 ▸ isUnit_one)
  -- (G6) the restriction to `H` of the cylinder coordinate germs
  have hG6 : ∀ x (hxH : x ∈ H) (hx : x ∈ e.source) (hxr : (⟨x, hxH⟩ : H) ∈ φH.source) m,
      φH p₀ m = 0 →
      hH.restrictStalk ⟨x, hxH⟩ (coord E ψ e he hx (σe (kk m))) =
        coord (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 hxr m := by
    intro x hxH hx hxr m hm
    refine stalkToGerm_injective _ _ _ _ ?_
    -- the two `ChartedSpace` paths on `H` meet here: `Eq.trans` (default transparency), not `rw`
    refine Eq.trans ?_ (stalkToGerm_coord hφH1 hxr m).symm
    rw [hH.stalkToGerm_restrictStalk, stalkToGerm_coord he hx, germRestrict_coe]
    refine Filter.Germ.coe_eq.mpr ?_
    filter_upwards [(φH.open_source.inter (e.open_source.preimage continuous_subtype_val)).mem_nhds
      ⟨hxr, hx⟩] with q hq
    have hqe : (q : M) ∈ e.source := hq.2
    have hqH : q ∈ φH.source := hq.1
    change extendSection 𝕜 E (chartSection E ψ e he (σe (kk m))) (q : M) =
      extendSection 𝕜 (Fin (n - 1) → 𝕜) (chartSection (Fin (n - 1) → 𝕜)
        (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 m) q
    rw [extendSection_of_mem 𝕜 E _ hqe]
    refine Eq.trans ?_ (extendSection_of_mem 𝕜 (Fin (n - 1) → 𝕜) (chartSection (Fin (n - 1) → 𝕜)
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 m) hqH).symm
    change ψ (e q) (σe (kk m)) = φH q m
    rw [hG2 q hqe m, hm, sub_zero]
    exact congrArg (fun z : H => φH z m) (Subtype.ext (hrH q (hU₀D q (heU₀ q hqe)) q.2))
  -- the `c' + 1` coordinates of `J`: `u` and the cylinder coordinates `σ'`
  set σnew : Fin (c' + 1) ↪ Fin n :=
    ⟨Fin.cons (σe (τ 0)) fun i => σe (kk (σ' i)), Fin.cons_injective_of_injective
      (by rintro ⟨i, hi⟩; exact hkk0 (σ' i) (σe.injective hi))
      (σe.injective.comp (hkk_inj.comp σ'.injective))⟩ with hσnew
  have hrange : ∀ x (hx : x ∈ e.source),
      Set.range (fun i => coord E ψ e he hx (σnew i)) =
        insert (coord E ψ e he hx (σe (τ 0)))
          (Set.range fun i => coord E ψ e he hx (σe (kk (σ' i)))) := by
    intro x hx
    change Set.range ((fun k => coord E ψ e he hx k) ∘
      Fin.cons (σe (τ 0)) fun i => σe (kk (σ' i))) = _
    rw [Set.range_comp, Fin.range_cons, Set.image_insert_eq, ← Set.range_comp]
    rfl
  have hideal : ∀ x (hx : x ∈ e.source),
      J.stalkIdeal x = Ideal.span (Set.range fun i => coord E ψ e he hx (σnew i)) := by
    intro x hx
    have hxU := heU₀ x hx
    have hxD := hU₀D x hxU
    rw [hrange x hx, Ideal.span_insert]
    by_cases hxH : x ∈ H
    · have hqr : r x = ⟨x, hxH⟩ := Subtype.ext (hrH x hxD hxH)
      have hqφH : (⟨x, hxH⟩ : H) ∈ φH.source := by
        rw [← hqr]
        exact hU₀r x hxU
      set q : hH.toAnalyticManifold := ((⟨x, hxH⟩ : H) : hH.toAnalyticManifold) with hqdef
      have hker : RingHom.ker (hH.restrictStalk q) =
          Ideal.span {coord E ψ e he hx (σe (τ 0))} := by
        have := hH.ker_restrictStalk_eq_span hxH he_ad hx
        rw [Set.range_unique] at this
        exact this
      have hkerJ : RingHom.ker (hH.restrictStalk q) ≤ J.stalkIdeal x := by
        have := hH.stalkIdeal_idealSheaf_of_mem hxH
        change hH.idealSheaf.stalkIdeal x = RingHom.ker (hH.restrictStalk q) at this
        rw [← this]
        exact hNle x (hesN hx)
      have hmapJ : Ideal.map (hH.restrictStalk q) (J.stalkIdeal x) =
          Ideal.span (Set.range fun i => coord (Fin (n - 1) → 𝕜)
            (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 hqφH (σ' i)) := by
        have := hJH q hqφH
        rw [IdealSheaf.stalkIdeal_pullback, hH.germMap_inclusionMap q] at this
        exact this
      have hmapI : Ideal.map (hH.restrictStalk q)
          (Ideal.span (Set.range fun i => coord E ψ e he hx (σe (kk (σ' i))))) =
          Ideal.span (Set.range fun i => coord (Fin (n - 1) → 𝕜)
            (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) φH hφH1 hqφH (σ' i)) := by
        refine (Ideal.map_span _ _).trans ?_
        refine (congrArg Ideal.span (Set.range_comp _ _).symm).trans ?_
        refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
        change hH.restrictStalk q (coord E ψ e he hx (σe (kk (σ' i)))) = _
        exact hG6 x hxH hx hqφH (σ' i) (hσ'0 i)
      have hsurj := hH.restrictStalk_surjective q
      have h1 := Ideal.comap_map_of_surjective _ hsurj (J.stalkIdeal x)
      have h2 := Ideal.comap_map_of_surjective _ hsurj
        (Ideal.span (Set.range fun i => coord E ψ e he hx (σe (kk (σ' i)))))
      rw [hmapJ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerJ] at h1
      rw [hmapI, ← RingHom.ker_eq_comap_bot, hker] at h2
      rw [← h1, h2, sup_comm]
    · have hJtop : J.stalkIdeal x = ⊤ := by
        refine top_le_iff.mp ?_
        rw [← hH.stalkIdeal_idealSheaf_of_notMem hxH]
        exact hNle x (hesN hx)
      rw [hJtop]
      symm
      refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) ?_
      refine isUnit_coord_of_ne_zero e he hx ?_
      rw [hG1 x hx]
      intro h0
      exact hxH ((hφa.2 x (hU₀φ x hxU)).mpr fun i => by rw [Subsingleton.elim i 0]; exact h0)
  -- assembly
  refine ⟨c' + 1, e, σnew, _, hc_e, fun x hx => hideal x hx, fun j i => ?_⟩
  refine Fin.cases ?_ (fun i' => ?_) i
  · rw [hσnew]
    change σe (kk (cidx' ⟨j.1, j.2⟩)) ≠
      (Fin.cons (σe (τ 0)) (fun i => σe (kk (σ' i))) : Fin (c' + 1) → Fin n) 0
    rw [Fin.cons_zero]
    exact fun h => hkk0 _ (σe.injective h)
  · rw [hσnew]
    change σe (kk (cidx' ⟨j.1, j.2⟩)) ≠
      (Fin.cons (σe (τ 0)) (fun i => σe (kk (σ' i))) : Fin (c' + 1) → Fin n) i'.succ
    rw [Fin.cons_succ]
    exact fun h => hne' ⟨j.1, j.2⟩ i' (hkk_inj (σe.injective h))

/-- **The lift of the predicate** ([Wlo05, Theorem 4.7.1, proof]; [Wlo09, Theorem 7.4.1]): for `H`
of maximal contact at the mark `1` (`𝓘_H ≤ J`) with `F ∪ H` of simple normal crossings and the
members not containing `H` (`HasSncWithProper`), a point `y ∈ H` of the cosupport of `J`, and the
predicate on the bundled `H` for the trace family and `J|_H` at `y`, the predicate holds for
`(F, J)` at `y`: the instance of `of_restrict_maximalContact_of_eventually_le` at the global
inequality (the proof uses `𝓘_H ≤ J` only on the source of its chart). -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.of_restrict_maximalContact {H : Set M}
    (hH : IsClosedSubmanifold ψ H 1) {F : HypersurfaceFamily M} (hFH : F.HasSncWithProper ψ H 1)
    {J : AnalyticManifold.IdealSheaf M} (hle : hH.idealSheaf ≤ J) {y : M} (hy : y ∈ H)
    (hJy : J.stalkIdeal y ≠ ⊤)
    (h : (hH.traceFamily F).IsSmoothTransversalIdealAt
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff)
      ((⟨y, hy⟩ : H) : hH.toAnalyticManifold)) :
    F.IsSmoothTransversalIdealAt ψ J y :=
  of_restrict_maximalContact_of_eventually_le ψ hH hFH
    (Filter.Eventually.of_forall fun x => IdealSheaf.le_def.mp hle x) hy hJy h

end Manifold

end
