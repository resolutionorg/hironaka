/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.RealPlaneCircle
public import Hironaka.Manifold.FiniteSuccession.Cons
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.SaturationFiniteType
import Hironaka.Manifold.BlowUp.Transform.StrictSubspace
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bierstone–Milman's Example 3.16: the strict transform exceeds the closure

[BM97, Example 3.16]: for `X = V(x⁴(x−1)² + y²)` in the real plane, blown up at the origin, the
ideal-theoretic strict transform `X'` has a point over the origin that does not lie in the
closure of `π⁻¹(|X| ∖ {0})` — the inclusion of the closure in the strict transform, which holds
in general, is strict over `ℝ`. [BM97, Example 3.16]
concludes that the geometric strict transform `X''` of [BM97, Remark 3.15], the smallest
closed subspace of `π⁻¹(X)` containing `π⁻¹(X) ∖ π⁻¹(0)`, has `|X''| = {(1, 0)}` and differs
from `X'`; this file verifies the closure statement, not the identification of `|X''|` with the
closure. In the blow-up chart
`x = u, y = uv` the pulled-back equation is `u²·(u²(u−1)² + v²)`: the exceptional divisor
`{u = 0}` is divided out once with multiplicity two, and the strict transform
`V(u²(u−1)² + v²)` meets the exceptional divisor at the point `p = (0, 0)` of the `x`-axis
direction, while `|X| ∖ {0} ⊆ {(1, 0)}` lifts into the single point `(1, 0)` of the chart. The
argument:

* `dvd_of_mul_pow_eq_mul_of_prime`: in a domain, `a u^k = b g` with `u` prime and `u ∤ g` forces
  `g ∣ a` — the saturation of `(u² g')` by `(u)` lies in `(g')`;
* `not_dvd_coord_of_ne`: two distinct coordinate germs vanishing at a point do not divide one
  another (in the Taylor series `X_j` is not a multiple of `X_i`) — hence `u ∤ g'`;
* `isAdaptedChart_origin`, `blowUpChartMap_zero`, `germ_bm316Section`,
  `bm316Ideal_cosupport_diff_subset` (`|X| ∖ {0} ⊆ {(1, 0)}`, a real sum of squares);
* `exists_mem_strictTransform_notMem_closure_bm316_of_blowUp`: the witness `p = Φ⁻¹(0)` for the
  blow-up chart `Φ` of index `0` over the identity chart; `π p = 0`; the stalk of `X'` at `p` is
  the saturation (of finite type by `saturationStalk_hasLocalGenerators`), the exceptional stalk
  is `(u)`, the total transform's stalk is `(u²·g')` (the chart formulas `germMap_coord_self`,
  `germMap_coord_of_ne`), `u` is prime (`prime_coord_of_eq_zero`), so the saturation lies in
  `(g')` with `g'(p) = 0`: `p ∈ |X'|`; and `closure (π⁻¹(|X| ∖ {0})) ⊆ π⁻¹{(1, 0)}` misses `p`.

The saturation of a principal ideal by a prime is [BM97, Proposition 3.13] in this case; the
same example is computed in the ring of convergent power series in
`HironakaExamples/Saturation.lean`.
-/

public section

open Set TopologicalSpace Opposite CategoryTheory Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

noncomputable section

namespace Hironaka.Manifold

open _root_.Manifold

/-- In a domain, if `u` is prime and `u ∤ g`, then `a u^k = b g` forces `g ∣ a` — the core of
the saturation computation ([BM97, Proposition 3.13] for a principal ideal). -/
theorem dvd_of_mul_pow_eq_mul_of_prime {R : Type*} [CommRing R] [IsDomain R] {u g : R}
    (hu : Prime u) (hg : ¬ u ∣ g) : ∀ (k : ℕ) (a b : R), a * u ^ k = b * g → g ∣ a
  | 0, a, b, h => by
    rw [pow_zero, mul_one] at h
    exact ⟨b, by rw [h, mul_comm]⟩
  | k + 1, a, b, h => by
    have hub : u ∣ b := by
      have h1 : u ∣ b * g := ⟨a * u ^ k, by rw [← h, pow_succ]; ring⟩
      exact (hu.dvd_or_dvd h1).resolve_right hg
    obtain ⟨b', rfl⟩ := hub
    have h' : a * u ^ k = b' * g := by
      apply mul_left_cancel₀ hu.ne_zero
      calc u * (a * u ^ k) = a * u ^ (k + 1) := by ring
        _ = u * b' * g := h
        _ = u * (b' * g) := by ring
    exact dvd_of_mul_pow_eq_mul_of_prime hu hg k a b' h'

section NotDvd

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) {b : M} (hb : b ∈ φ.source) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

/-- Two distinct coordinate germs vanishing at `b` do not divide one
another — in the Taylor series `X_j` is not a multiple of `X_i` (its coefficient at `X_j` is `1`,
while every coefficient of `X_i · w` at a monomial without `X_i` vanishes). -/
theorem not_dvd_coord_of_ne {i j : Fin n} (h0 : ψ (φ b) i = 0) (h0' : ψ (φ b) j = 0)
    (hij : i ≠ j) : ¬ coord E ψ φ hφ hb i ∣ coord E ψ φ hφ hb j := by
  rintro ⟨w, hw⟩
  have h := congrArg (taylorHom E ψ φ hb hφ) hw
  rw [map_mul, taylorHom_coord, taylorHom_coord, h0, h0', map_zero, add_zero, add_zero] at h
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) h
  rw [MvPowerSeries.coeff_X, ite_eq_left rfl, MvPowerSeries.coeff_mul] at hc
  refine one_ne_zero (hc.trans (Finset.sum_eq_zero fun q hq => ?_))
  rw [MvPowerSeries.coeff_X, ite_eq_right, zero_mul]
  intro hq1
  have hi := DFunLike.congr_fun (Finset.HasAntidiagonal.mem_antidiagonal.mp hq) i
  simp only [Finsupp.add_apply, hq1, Finsupp.single_apply, hij.symm, ite_true, ite_false] at hi
  omega

end NotDvd

section BM316

/-- The identity chart of the plane is adapted to the origin, with both coordinates vanishing:
the computation of the `exists_adaptedChart` field of `isClosedSubmanifold_origin` (`RealPlane`),
repeated as a standalone statement. -/
theorem isAdaptedChart_origin :
    IsAdaptedChart (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) ({0} : Set realPlane)
      (chartAt (Fin 2 → ℝ) (0 : realPlane)) (Function.Embedding.refl (Fin 2)) :=
  ⟨IsManifold.chart_mem_maximalAtlas (0 : realPlane), fun x _ => by
    change x ∈ ({0} : Set (Fin 2 → ℝ)) ↔ ∀ i : Fin 2, x i = 0
    simp only [Set.mem_singleton_iff, funext_iff, Pi.zero_apply]⟩

/-- The blow-up chart map of the plane sends `0` to `0`. -/
theorem blowUpChartMap_zero (σ : Fin 2 ↪ Fin 2) (i : Fin 2) :
    blowUpChartMap (𝕜 := ℝ) σ i 0 = 0 := by
  funext j
  simp only [blowUpChartMap, Pi.zero_apply, mul_zero, ite_self]

/-- The germ of `x⁴(x−1)² + y²` at `x` in the coordinate germs of the identity chart. -/
theorem germ_bm316Section (x : realPlane) :
    (structureSheaf ℝ (Fin 2 → ℝ) realPlane).presheaf.germ planeChart x (mem_planeChart x)
        bm316Section =
      coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
        (chartAt (Fin 2 → ℝ) (0 : realPlane)) (IsManifold.chart_mem_maximalAtlas (0 : realPlane))
        (mem_chartAt_source_plane x) 0 ^ 4 *
      (coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
        (chartAt (Fin 2 → ℝ) (0 : realPlane)) (IsManifold.chart_mem_maximalAtlas (0 : realPlane))
        (mem_chartAt_source_plane x) 0 - 1) ^ 2 +
      coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
        (chartAt (Fin 2 → ℝ) (0 : realPlane)) (IsManifold.chart_mem_maximalAtlas (0 : realPlane))
        (mem_chartAt_source_plane x) 1 ^ 2 := by
  rw [bm316Section, map_add, map_mul, map_pow, map_pow, map_sub, map_one, map_pow,
    germ_planeCoordSection, germ_planeCoordSection]

/-- [BM97, Example 3.16]: the support of `V(x⁴(x−1)² + y²)` off the origin lies in `{(1, 0)}`
— a real sum of two squares vanishes iff both do. -/
theorem bm316Ideal_cosupport_diff_subset :
    bm316Ideal.support \ {0} ⊆ {fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0} := by
  rintro x ⟨hx, hx0⟩
  rw [IdealSheaf.mem_support, stalkIdeal_bm316Ideal, Ne, Ideal.span_singleton_eq_top,
    germ_bm316Section, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
    mem_maximalIdeal_iff_eval, map_add, map_mul, map_pow, map_pow, map_sub, map_one, map_pow,
    eval_coord_plane, eval_coord_plane] at hx
  have h0 := (add_eq_zero_iff_of_nonneg (by positivity) (sq_nonneg (x 1))).mp hx
  have hx1 : x 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h0.2
  have hx00 : x 0 ^ 4 = 0 ∨ (x 0 - 1) ^ 2 = 0 := mul_eq_zero.mp h0.1
  rw [Set.mem_singleton_iff]
  rcases hx00 with h4 | h1
  · exfalso
    apply hx0
    rw [Set.mem_singleton_iff]
    funext i
    fin_cases i
    · exact pow_eq_zero_iff (by norm_num) |>.mp h4
    · exact hx1
  · have hx0' : x 0 = 1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    funext i
    fin_cases i
    · simpa using hx0'
    · simpa using hx1

/-- [BM97, Example 3.16]: the strict transform of `V(x⁴(x−1)² + y²) ⊆ ℝ²` under the blow-up of
the plane at the origin has a point over the origin outside the closure of `π⁻¹(|X| ∖ {0})`.
The point is the `x`-axis direction `p = Φ⁻¹(0)`
in the blow-up chart `Φ` of index `0`: there the total transform is `(u²·g')` with
`g' = u²(u−1)² + v²`, the exceptional ideal is `(u)`, and the saturation lies in `(g')`, a proper
ideal; the closure of `π⁻¹(|X| ∖ {0}) ⊆ π⁻¹{(1, 0)}` misses `p` since `π p = 0`. -/
theorem exists_mem_strictTransform_notMem_closure_bm316_of_blowUp :
    ∃ p, p ∈ (strictTransformSubspace isClosedSubmanifold_origin
        (isBlowUp_blowUpπ (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) isClosedSubmanifold_origin)
        bm316Ideal).support ∧
      p ∉ closure (Manifold.blowUpπ (ContinuousLinearEquiv.refl ℝ
          (Fin 2 → ℝ)) isClosedSubmanifold_origin ⁻¹'
        (bm316Ideal.support \ {0})) := by
  have h := isBlowUp_blowUpπ (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) isClosedSubmanifold_origin
  obtain ⟨Φ, hΦ⟩ := h.exists_chart _ _ isAdaptedChart_origin 0
  have h0 : (0 : Fin 2 → ℝ) ∈ Φ.target := by
    rw [hΦ.mem_target_iff]
    refine ⟨_, ?_, rfl⟩
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_target]
    exact Set.mem_univ _
  have hp : Φ.symm 0 ∈ Φ.source := Φ.map_target h0
  have hΦp : Φ (Φ.symm 0) = 0 := Φ.right_inv h0
  have hπp : Manifold.blowUpπ (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) isClosedSubmanifold_origin
      (Φ.symm 0) = 0 := by
    have hc := hΦ.comm _ hp
    rw [hΦp, chartAt_self_eq] at hc
    change Manifold.blowUpπ (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) isClosedSubmanifold_origin
      (Φ.symm 0) = blowUpChartMap (Function.Embedding.refl (Fin 2)) 0 (0 : Fin 2 → ℝ) at hc
    rw [blowUpChartMap_zero] at hc
    exact hc
  have hΦp0 : ∀ i, ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ) (Φ (Φ.symm 0)) i = 0 := fun i => by
    rw [hΦp]; rfl
  refine ⟨Φ.symm 0, ?_, ?_⟩
  · -- the stalk of `X'` at `p` is the saturation, contained in `(g')`, and `g' ∈ 𝔪_p`
    rw [IdealSheaf.mem_support, stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _
      (saturationStalk_hasLocalGenerators _ _ _)]
    have hprime : Prime (coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) Φ
        hΦ.mem_maximalAtlas hp 0) :=
      prime_coord_of_eq_zero (E := Fin 2 → ℝ) (ψ := ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) Φ
        hΦ.mem_maximalAtlas hp (hΦp0 0)
    have hdom := isDomain_stalk (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) hΦ.mem_maximalAtlas hp
    have hnd := not_dvd_coord_of_ne (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) Φ hp
      hΦ.mem_maximalAtlas (hΦp0 0) (hΦp0 1) (by decide)
    set u := coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) Φ hΦ.mem_maximalAtlas hp 0
      with hu
    set v := coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) Φ hΦ.mem_maximalAtlas hp 1
      with hv
    have hug' : ¬ u ∣ u ^ 2 * (u - 1) ^ 2 + v ^ 2 := by
      rintro ⟨c, hc⟩
      exact hnd (hprime.dvd_of_dvd_pow (n := 2) ⟨c - u * (u - 1) ^ 2, by linear_combination hc⟩)
    have hE : (isClosedSubmanifold_origin.idealSheaf.pullback _ h.contMDiff).stalkIdeal (Φ.symm 0) =
        Ideal.span {u} := by
      have := stalkIdeal_exceptionalIdealSheaf_eq_span_coord isClosedSubmanifold_origin h
        isAdaptedChart_origin hΦ hp
      simpa only [Function.Embedding.refl_apply] using this
    have e0 := hΦ.germMap_coord_self h.contMDiff
      (IsManifold.chart_mem_maximalAtlas (0 : realPlane)) hp
    have e1 := hΦ.germMap_coord_of_ne h.contMDiff
      (IsManifold.chart_mem_maximalAtlas (0 : realPlane)) hp (k := 1) (by decide)
    simp only [Function.Embedding.refl_apply] at e0 e1
    have hgen : germMap _ h.contMDiff (Φ.symm 0)
        ((structureSheaf ℝ (Fin 2 → ℝ) realPlane).presheaf.germ planeChart
          (Manifold.blowUpπ (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) isClosedSubmanifold_origin
              (Φ.symm 0))
          (mem_planeChart _) bm316Section) =
        u ^ 2 * (u ^ 2 * (u - 1) ^ 2 + v ^ 2) := by
      rw [germ_bm316Section, map_add, map_mul, map_pow, map_pow, map_sub, map_one, map_pow, e0, e1]
      ring
    have hT : (bm316Ideal.pullback _ h.contMDiff).stalkIdeal (Φ.symm 0) =
        Ideal.span {u ^ 2 * (u ^ 2 * (u - 1) ^ 2 + v ^ 2)} := by
      rw [IdealSheaf.stalkIdeal_pullback, stalkIdeal_bm316Ideal, Ideal.map_span,
        Set.image_singleton, hgen]
    have hsat : saturationStalk isClosedSubmanifold_origin h bm316Ideal (Φ.symm 0) ≤
        Ideal.span {u ^ 2 * (u - 1) ^ 2 + v ^ 2} := by
      refine iSup_le fun k => ?_
      intro a ha
      rw [Submodule.mem_colon] at ha
      have h1 := ha (u ^ k)
        (by rw [hE]; exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self u) k)
      rw [hT, smul_eq_mul, Ideal.mem_span_singleton] at h1
      obtain ⟨c, hc⟩ := h1
      rw [Ideal.mem_span_singleton]
      exact dvd_of_mul_pow_eq_mul_of_prime hprime hug' k a (u ^ 2 * c) (by rw [hc]; ring)
    intro htop
    have h1 : (1 : (structureSheaf ℝ (Fin 2 → ℝ)
        (Manifold.blowUp (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
          isClosedSubmanifold_origin)).presheaf.stalk (Φ.symm 0)) ∈
        Ideal.span {u ^ 2 * (u - 1) ^ 2 + v ^ 2} := by
      apply hsat
      rw [htop]
      exact Submodule.mem_top
    rw [Ideal.mem_span_singleton] at h1
    have hg'm : u ^ 2 * (u - 1) ^ 2 + v ^ 2 ∈ IsLocalRing.maximalIdeal
        ((structureSheaf ℝ (Fin 2 → ℝ)
          (Manifold.blowUp (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
            isClosedSubmanifold_origin)).presheaf.stalk (Φ.symm 0)) := by
      rw [mem_maximalIdeal_iff_eval]
      simp only [map_add, map_mul, map_pow, map_sub, map_one, hu, hv, eval_coord, hΦp0]
      norm_num
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hg'm) (isUnit_of_dvd_one h1)
  · -- the closure of the transform off the centre lies over `(1, 0)`, and `π p = 0`
    intro hcl
    have hcl' : closure (Manifold.blowUpπ (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
        isClosedSubmanifold_origin ⁻¹' (bm316Ideal.support \ {0})) ⊆
        Manifold.blowUpπ (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) isClosedSubmanifold_origin ⁻¹'
          {fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0} :=
      closure_minimal (Set.preimage_mono bm316Ideal_cosupport_diff_subset)
        (isClosed_singleton.preimage h.contMDiff.continuous)
    have h1 := hcl' hcl
    rw [Set.mem_preimage, Set.mem_singleton_iff, hπp] at h1
    have h2 : (0 : ℝ) = 1 := congrFun h1 0
    exact zero_ne_one h2

end BM316

end Hironaka.Manifold

end
