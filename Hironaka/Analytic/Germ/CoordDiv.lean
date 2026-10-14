/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Weierstrass.Basic
public import Hironaka.Analytic.ConvSeries.Eval
import Hironaka.Analytic.ConvSeries.Bridge
import Hironaka.Analytic.ConvSeries.Mul
import Hironaka.Analytic.ConvSeries.Rescale
import Hironaka.Analytic.Germ.Coordinate
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Division by a coordinate, at the function level

An analytic `F` on a polydisc vanishing on the hyperplane `{x_k = 0}` is `x_k · G` with `G`
analytic on the same polydisc. Off the hyperplane `G = F / x_k`; on it `G = ∂_k F`. Analyticity
of `G` at a point `p` of the hyperplane: expand `F` at `p`
(`Hironaka/Analytic/ConvSeries/Bridge.lean`), `F(p + y) = ∑ c_ν y^ν`; the monomials free of
`y_k` must vanish (the `y_k`-free part of `c` sums to zero on `{y_k = 0}`, hence everywhere by
independence of `y_k`, hence is zero by uniqueness of coefficients), so `c = y_k · divX k c` and
`G(p + y) = ∑ (divX k c)_ν y^ν`: for `y_k ≠ 0` by division and for `y_k = 0` by differentiating
`s ↦ s · (∑ (divX k c)_ν (y + s e_k)^ν)` at `s = 0`. A coordinate subspace `{x_k = 0, k ∈ I}`
inside `{F = 0}` on a polydisc gives `F = ∑_{k ∈ I} x_k G_k` by induction on `I` (division by
`x_k` for `F - F ∘ P_k`, `P_k` setting `x_k` to `0`;
`exists_sum_coord_mul_of_vanish_on_subspace`). Not in the sources as such: it is the
function-level form of the division by a coordinate that Bierstone and Milman use implicitly
[BM88, proof of Theorem 4.4, pp. 24–25]. Used by the Taylor expansion of germs on a manifold
(`Hironaka/Manifold/Germ`) and by the lifting of functions to a blow-up
(`Hironaka/Manifold/BlowUp`).

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open MvPowerSeries Filter
open scoped Topology ENNReal NNReal

namespace Analytic

variable {K : Type*} [RCLike K]

variable {n : ℕ}

@[simp]
theorem evalSeries_zero (x : Fin n → K) : evalSeries (0 : MvPowerSeries (Fin n) K) x = 0 := by
  unfold evalSeries
  simp

theorem isOpen_polydisc (ρ : Radius n) : IsOpen (polydisc K ρ) := by
  have : polydisc K ρ = ⋂ k, {x : Fin n → K | ‖x k‖ < (ρ k : ℝ)} := by
    ext x; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const

/-! ### The `x_k`-free part of a series -/

/-- The monomials of `c` free of `x_k`. -/
noncomputable def freePart (k : Fin n) (c : MvPowerSeries (Fin n) K) : MvPowerSeries (Fin n) K :=
  fun ν => if ν k = 0 then coeff ν c else 0

theorem coeff_freePart (k : Fin n) (c : MvPowerSeries (Fin n) K) (ν : Fin n →₀ ℕ) :
    coeff ν (freePart k c) = if ν k = 0 then coeff ν c else 0 := rfl

theorem convNorm_freePart_le (ρ : Fin n → ℝ≥0) (k : Fin n) (c : MvPowerSeries (Fin n) K) :
    ConvNorm ρ (freePart k c) ≤ ConvNorm ρ c := by
  unfold ConvNorm
  refine ENNReal.tsum_le_tsum fun ν => mul_le_mul' ?_ le_rfl
  rw [coeff_freePart]
  split_ifs
  · exact le_rfl
  · simp

theorem freePart_mem_conv (k : Fin n) {c : MvPowerSeries (Fin n) K} (hc : c ∈ Conv K n) :
    freePart k c ∈ Conv K n := by
  obtain ⟨ρ, hρ⟩ := hc
  exact ⟨ρ, ne_top_of_le_ne_top hρ (convNorm_freePart_le ρ k c)⟩

theorem monomialEval_update_zero_of_apply_eq_zero (x : Fin n → K) (k : Fin n) {ν : Fin n →₀ ℕ}
    (hν : ν k = 0) : monomialEval (Function.update x k 0) ν = monomialEval x ν := by
  unfold monomialEval
  rw [Finsupp.prod_pow, Finsupp.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = k
  · subst hj
    rw [hν, pow_zero, pow_zero]
  · rw [Function.update_of_ne hj]

/-- On `{x_k = 0}` only the `x_k`-free monomials contribute. -/
theorem evalSeries_eq_freePart_of_apply_eq_zero (c : MvPowerSeries (Fin n) K) (k : Fin n)
    {x : Fin n → K} (hx : x k = 0) : evalSeries c x = evalSeries (freePart k c) x := by
  unfold evalSeries
  refine tsum_congr fun ν => ?_
  rw [coeff_freePart]
  split_ifs with h
  · rfl
  · rw [zero_mul, monomialEval, Finsupp.prod_pow,
      Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hx, zero_pow h]), mul_zero]

/-- The `x_k`-free part does not depend on `x_k`. -/
theorem evalSeries_freePart_update (c : MvPowerSeries (Fin n) K) (k : Fin n) (x : Fin n → K) :
    evalSeries (freePart k c) (Function.update x k 0) = evalSeries (freePart k c) x := by
  unfold evalSeries
  refine tsum_congr fun ν => ?_
  rw [coeff_freePart]
  split_ifs with h
  · rw [monomialEval_update_zero_of_apply_eq_zero x k h]
  · rw [zero_mul, zero_mul]

theorem tendsto_update_zero (k : Fin n) :
    Tendsto (fun x : Fin n → K => Function.update x k 0) (𝓝 0) (𝓝 0) := by
  have h := ((continuous_id (X := Fin n → K)).update k (continuous_const (y := (0 : K)))).tendsto
    (0 : Fin n → K)
  have h0 : Function.update (0 : Fin n → K) k (0 : K) = 0 := Function.update_eq_self_iff.mpr rfl
  simpa [h0] using h

/-- A convergent series whose sum vanishes on `{x_k = 0}` near `0` has no monomials free of
`x_k`. -/
theorem coeff_eq_zero_of_eventually_vanish {c : MvPowerSeries (Fin n) K} (hc : c ∈ Conv K n)
    (k : Fin n) (hvan : ∀ᶠ x in 𝓝 (0 : Fin n → K), x k = 0 → evalSeries c x = 0) :
    ∀ ν : Fin n →₀ ℕ, ν k = 0 → coeff ν c = 0 := by
  have hfree : freePart k c = 0 := by
    refine eq_of_evalSeries_eventuallyEq (freePart_mem_conv k hc) (zero_mem _) ?_
    filter_upwards [(tendsto_update_zero k).eventually hvan] with x hx
    rw [evalSeries_zero, ← evalSeries_freePart_update,
      ← evalSeries_eq_freePart_of_apply_eq_zero c k (Function.update_self k 0 x)]
    exact hx (Function.update_self k 0 x)
  intro ν hν
  have h := congrArg (coeff ν) hfree
  rwa [coeff_freePart, ite_eq_left hν, map_zero] at h

/-! ### Division by a coordinate -/

/-- Division by a coordinate at function level: an analytic `F` on a polydisc vanishing on
`{x_k = 0}` is `x_k · G` with `G` analytic on the same polydisc. -/
theorem exists_eq_mul_coord_of_vanish (k : Fin n) {ρ : Radius n} {F : (Fin n → K) → K}
    (hF : AnalyticOnNhd K F (polydisc K ρ)) (h0 : ∀ x ∈ polydisc K ρ, x k = 0 → F x = 0) :
    ∃ G : (Fin n → K) → K, AnalyticOnNhd K G (polydisc K ρ) ∧
      ∀ x ∈ polydisc K ρ, F x = x k * G x := by
  classical
  set G : (Fin n → K) → K :=
    fun x => if x k = 0 then fderiv K F x (Pi.single k 1) else F x / x k with hG
  have hopen : IsOpen (polydisc K ρ) := isOpen_polydisc ρ
  refine ⟨G, fun p hp => ?_, fun x hx => ?_⟩
  · by_cases hpk : p k = 0
    · -- expand `F` at `p`
      obtain ⟨ρ', c, hc, hFc⟩ := AnalyticAt.exists_conv_coeff (hF p hp)
      have htend : Tendsto (fun y : Fin n → K => p + y) (𝓝 0) (𝓝 p) := by
        have h := (tendsto_const_nhds (x := p)).add (tendsto_id (x := 𝓝 (0 : Fin n → K)))
        rwa [add_zero] at h
      have hev : ∀ᶠ y in 𝓝 (0 : Fin n → K), p + y ∈ polydisc K ρ :=
        htend.eventually (hopen.mem_nhds hp)
      have hcvan : ∀ᶠ y in 𝓝 (0 : Fin n → K), y k = 0 → evalSeries c y = 0 := by
        filter_upwards [eventually_abs_lt ρ', hev] with y hy hpy hyk
        rw [← hFc y hy]
        exact h0 _ hpy (by rw [Pi.add_apply, hpk, hyk, add_zero])
      have hcoeff := coeff_eq_zero_of_eventually_vanish ⟨ρ', hc⟩ k hcvan
      set c' := divX k c with hc'
      have hc'B : ConvNorm ρ' c' ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hc) (convNorm_divX_le ρ' k c)
      have hsplit : ∀ y : Fin n → K, (∀ i, ‖y i‖ ≤ ρ' i) →
          evalSeries c y = y k * evalSeries c' y := fun y hy => by
          rw [← X_mul_divX k hcoeff, ← pow_one (X k),
            evalSeries_mul (convNorm_X_pow_ne_top ρ' k 1) hc'B hy, evalSeries_X_pow, pow_one]
      -- `G (p + y) = evalSeries c' y` for `y` small
      have hGy : ∀ y : Fin n → K, (∀ i, ‖y i‖ < ρ' i) → p + y ∈ polydisc K ρ →
          G (p + y) = evalSeries c' y := by
        intro y hy hpy
        have hy' : ∀ i, ‖y i‖ ≤ ρ' i := fun i => (hy i).le
        by_cases hyk : y k = 0
        · -- the derivative in the `k`-direction
          have hpyk : (p + y) k = 0 := by rw [Pi.add_apply, hpk, hyk, add_zero]
          simp only [hG, ite_eq_left hpyk]
          -- the line `s ↦ p + y + s • e_k`
          have hline : HasDerivAt (fun s : K => p + y + s • (Pi.single k 1 : Fin n → K))
              (Pi.single k 1) 0 := by
            have h := ((hasDerivAt_id (0 : K)).smul_const (Pi.single k 1 : Fin n → K)).const_add
              (p + y)
            simpa using h
          have hF' : HasFDerivAt F (fderiv K F (p + y))
              (p + y + (0 : K) • (Pi.single k 1 : Fin n → K)) := by
            simpa using (hF _ hpy).differentiableAt.hasFDerivAt
          have h1 : HasDerivAt (fun s : K => F (p + y + s • (Pi.single k 1 : Fin n → K)))
              (fderiv K F (p + y) (Pi.single k 1)) 0 :=
            hF'.comp_hasDerivAt (0 : K) hline
          -- the same function is `s * evalSeries c' (y + s • e_k)` near `0`
          have hc'an : AnalyticAt K (evalSeries c') y :=
            analyticOnNhd_evalSeries hc'B y (mem_polydisc_iff.mpr hy)
          have hline' : HasDerivAt (fun s : K => y + s • (Pi.single k 1 : Fin n → K))
              (Pi.single k 1) 0 := by
            have h := ((hasDerivAt_id (0 : K)).smul_const (Pi.single k 1 : Fin n → K)).const_add y
            simpa using h
          have h2 : HasDerivAt
              (fun s : K => s * evalSeries c' (y + s • (Pi.single k 1 : Fin n → K)))
              (evalSeries c' y) 0 := by
            have hc'' : HasFDerivAt (evalSeries c') (fderiv K (evalSeries c') y)
                (y + (0 : K) • (Pi.single k 1 : Fin n → K)) := by
              simpa using hc'an.differentiableAt.hasFDerivAt
            have hinner := hc''.comp_hasDerivAt (0 : K) hline'
            have h := (hasDerivAt_id (0 : K)).mul hinner
            refine h.congr_deriv ?_
            simp
          have heq : (fun s : K => F (p + y + s • (Pi.single k 1 : Fin n → K))) =ᶠ[𝓝 0]
              fun s : K => s * evalSeries c' (y + s • (Pi.single k 1 : Fin n → K)) := by
            have hsmall : ∀ᶠ s : K in 𝓝 0,
                ∀ i, ‖(y + s • (Pi.single k 1 : Fin n → K)) i‖ < ρ' i := by
              have hcont : Tendsto (fun s : K => y + s • (Pi.single k 1 : Fin n → K))
                  (𝓝 0) (𝓝 y) := by
                have h := (tendsto_const_nhds (x := y)).add
                  ((tendsto_id (x := 𝓝 (0 : K))).smul_const (Pi.single k 1 : Fin n → K))
                rwa [zero_smul, add_zero] at h
              have hmem : ∀ᶠ z in 𝓝 y, z ∈ polydisc K ρ' :=
                (isOpen_polydisc ρ').mem_nhds (mem_polydisc_iff.mpr hy)
              exact hcont.eventually (hmem.mono fun z hz => mem_polydisc_iff.mp hz)
            filter_upwards [hsmall] with s hs
            rw [add_assoc, hFc _ hs, hsplit _ fun i => (hs i).le, Pi.add_apply, hyk, Pi.smul_apply,
              Pi.single_eq_same, smul_eq_mul, mul_one, zero_add]
          exact (h1.congr_of_eventuallyEq heq.symm).unique h2
        · have hpyk : (p + y) k ≠ 0 := by rwa [Pi.add_apply, hpk, zero_add]
          simp only [hG, ite_eq_right hpyk]
          rw [hFc y hy, hsplit y hy', Pi.add_apply, hpk, zero_add, mul_div_cancel_left₀ _ hyk]
      -- hence `G` is analytic at `p`
      have han : AnalyticAt K (fun x => evalSeries c' (x - p)) p := by
        have h1 : AnalyticAt K (evalSeries c') (p - p) := by
          rw [sub_self]
          exact analyticOnNhd_evalSeries hc'B 0 (mem_polydisc_iff.mpr fun i => by
            rw [Pi.zero_apply, norm_zero]; exact_mod_cast ρ'.pos i)
        exact AnalyticAt.comp (g := evalSeries c') (f := fun x => x - p) h1
          (analyticAt_id.sub analyticAt_const)
      refine han.congr ?_
      have htend' : Tendsto (fun x : Fin n → K => x - p) (𝓝 p) (𝓝 0) := by
        have h := (tendsto_id (x := 𝓝 p)).sub (tendsto_const_nhds (x := p))
        rwa [sub_self] at h
      filter_upwards [htend'.eventually (eventually_abs_lt ρ'), hopen.mem_nhds hp] with x hx hxp
      have := hGy (x - p) hx (by rwa [add_sub_cancel])
      rw [add_sub_cancel] at this
      exact this.symm
    · -- off the hyperplane `G = F / x_k`
      have hne : ∀ᶠ x in 𝓝 p, x k ≠ 0 := (continuous_apply k).continuousAt.eventually_ne hpk
      have han : AnalyticAt K (fun x : Fin n → K => F x / x k) p :=
        (hF p hp).div ((ContinuousLinearMap.proj (R := K) (φ := fun _ : Fin n => K) k).analyticAt p)
          hpk
      refine han.congr ?_
      filter_upwards [hne] with x hx
      simp only [hG, ite_eq_right hx]
  · by_cases hxk : x k = 0
    · rw [hxk, zero_mul]
      exact h0 x hx hxk
    · simp only [hG, ite_eq_right hxk]
      exact (mul_div_cancel₀ (F x) hxk).symm

/-! ### Coordinate subspaces inside the zero set -/

/-- A statement true near `0` holds on some polydisc around `0`. -/
theorem exists_polydisc_of_eventually {P : (Fin n → K) → Prop}
    (h : ∀ᶠ y in 𝓝 (0 : Fin n → K), P y) : ∃ ρ : Radius n, ∀ y ∈ polydisc K ρ, P y := by
  obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨⟨fun _ => Real.toNNReal ε, fun _ => Real.toNNReal_pos.mpr hε0⟩, fun y hy => ?_⟩
  refine hε ?_
  rw [mem_polydisc_iff] at hy
  rw [dist_zero_right, pi_norm_lt_iff hε0]
  intro k
  calc ‖y k‖ < Real.toNNReal ε := hy k
    _ = ε := Real.coe_toNNReal ε hε0.le

variable (K) in
/-- Setting the coordinate `k` to `0`, as a continuous linear map. -/
noncomputable def updateZeroCLM (k : Fin n) : (Fin n → K) →L[K] (Fin n → K) :=
  ContinuousLinearMap.id K _ -
    (ContinuousLinearMap.single K (fun _ : Fin n => K) k).comp (ContinuousLinearMap.proj k)

/-- `updateZeroCLM K k x` is `x` with the coordinate `k` set to `0`. -/
theorem updateZeroCLM_apply (k : Fin n) (x : Fin n → K) :
    updateZeroCLM K k x = Function.update x k 0 := by
  ext j
  change x j - (Pi.single k (x k) : Fin n → K) j = Function.update x k 0 j
  by_cases hj : j = k
  · subst hj
    rw [Pi.single_eq_same, Function.update_self, sub_self]
  · rw [Pi.single_eq_of_ne hj, Function.update_of_ne hj, sub_zero]

/-- Setting a coordinate to `0` stays in the polydisc. -/
theorem update_zero_mem_polydisc {ρ : Radius n} {x : Fin n → K} (hx : x ∈ polydisc K ρ)
    (k : Fin n) :
    Function.update x k 0 ∈ polydisc K ρ := by
  rw [mem_polydisc_iff] at hx ⊢
  intro j
  by_cases hj : j = k
  · subst hj
    rw [Function.update_self, norm_zero]
    exact_mod_cast ρ.pos j
  · rw [Function.update_of_ne hj]
    exact hx j

/-- A coordinate subspace inside the zero set on a polydisc gives `F ∈ (x_k : k ∈ I)` with
analytic coefficients on the polydisc. -/
theorem exists_sum_coord_mul_of_vanish_on_subspace (I : Finset (Fin n)) {ρ : Radius n}
    {F : (Fin n → K) → K} (hF : AnalyticOnNhd K F (polydisc K ρ))
    (hvan : ∀ x ∈ polydisc K ρ, (∀ k ∈ I, x k = 0) → F x = 0) :
    ∃ G : Fin n → (Fin n → K) → K, (∀ k ∈ I, AnalyticOnNhd K (G k) (polydisc K ρ)) ∧
      ∀ x ∈ polydisc K ρ, F x = ∑ k ∈ I, x k * G k x := by
  classical
  induction I using Finset.induction_on generalizing F with
  | empty =>
    refine ⟨fun _ _ => 0, fun k hk => absurd hk (Finset.notMem_empty k), fun x hx => ?_⟩
    rw [Finset.sum_empty]
    exact hvan x hx fun k hk => absurd hk (Finset.notMem_empty k)
  | insert k I hk ih =>
    -- `F₂ := F ∘ P_k` and `F₁ := F - F₂`
    have hP : AnalyticOnNhd K (fun x => F (Function.update x k 0)) (polydisc K ρ) := fun x hx => by
      have h1 : AnalyticAt K F (updateZeroCLM K k x) := by
        rw [updateZeroCLM_apply]; exact hF _ (update_zero_mem_polydisc hx k)
      have h2 := h1.comp ((updateZeroCLM K k).analyticAt x)
      refine h2.congr (Eventually.of_forall fun z => ?_)
      change F (updateZeroCLM K k z) = F (Function.update z k 0)
      rw [updateZeroCLM_apply]
    obtain ⟨G₁, hG₁, hF₁⟩ := exists_eq_mul_coord_of_vanish k (hF.sub hP) fun x hx hxk => by
      change F x - F (Function.update x k 0) = 0
      rw [Function.update_eq_self_iff.mpr hxk.symm, sub_self]
    obtain ⟨G₂, hG₂, hF₂⟩ := ih hP fun x hx hxI => hvan _ (update_zero_mem_polydisc hx k)
      fun j hj => by
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Function.update_self j 0 x
        · rw [Function.update_of_ne (fun h => hk (by rw [← h]; exact hj))]
          exact hxI j hj
    refine ⟨Function.update G₂ k G₁, fun j hj => ?_, fun x hx => ?_⟩
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [Function.update_self]; exact hG₁
      · rw [Function.update_of_ne (fun h => hk (by rw [← h]; exact hj))]; exact hG₂ j hj
    · rw [Finset.sum_insert hk, Function.update_self]
      have h1 := hF₁ x hx
      change F x - F (Function.update x k 0) = x k * G₁ x at h1
      rw [Finset.sum_congr rfl fun j hj => by
        rw [Function.update_of_ne (fun h => hk (by rw [← h]; exact hj))], ← hF₂ x hx]
      linear_combination h1

end Analytic
