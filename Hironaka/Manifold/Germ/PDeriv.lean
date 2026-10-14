/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Hironaka.Manifold.Germ.Taylor
import Hironaka.Analytic.ConvSeries.Bridge
import Hironaka.Analytic.ConvSeries.Rescale
import Hironaka.Manifold.Germ.TaylorHom
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The Taylor homomorphism commutes with differentiation

Bierstone–Milman's Taylor series homomorphism `T_a` "commutes with differentiation" [BM97, (0.3)].
A convergent power series may be differentiated term by term: on the polydisc of half the radius,
`∂_i (evalSeries c) = evalSeries (∂_{X_i} c)` (`fderiv_evalSeries_single`, from Mathlib's
`hasDerivAt_tsum_of_isPreconnected` along the `i`-th coordinate line, the terms being the
monomials `a_ν y^{ν_i} ∏_{k ≠ i} x_k^{ν_k}` with the summable majorant `2/ρ_i · ‖a_ν‖ ρ^ν`), and
the derived series is convergent (`pderiv_mem_conv`, `‖∂_{X_i} c‖_{ρ/2} · ρ_i ≤ 2 ‖c‖_ρ`); the
formal derivative `∂_{X_i}` is Mathlib's `MvPowerSeries.pderiv`.
Hence the power series of the coordinate derivative `∂_i g` of an analytic germ is `∂_{X_i}` of the
power series of `g` (`IsSeriesOf.pderiv`, `taylorGerm_pderivGerm`), and the Taylor homomorphism
satisfies `T_a (∂_i f) = ∂_{X_i} (T_a f)` (`IsTaylorHom.pderiv'`; the form on the stalk operators
is `IsTaylorHom.pderiv` in `Hironaka/Manifold/Germ/CoordDerivChart.lean`).
-/

public noncomputable section

open TopologicalSpace Filter Topology Analytic MvPowerSeries _root_.Finset
open scoped Manifold ContDiff NNReal ENNReal
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Series

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- `x^ν` with the `i`-th factor split off. -/
theorem monomialEval_eq_mul_prod_erase (x : Fin n → 𝕜) (i : Fin n) (ν : Fin n →₀ ℕ) :
    monomialEval x ν = x i ^ ν i * ∏ k ∈ univ.erase i, x k ^ ν k := by
  rw [monomialEval, Finsupp.prod_fintype _ _ (fun k => pow_zero _),
    ← Finset.mul_prod_erase univ _ (mem_univ i)]

theorem monomialEval_update (x : Fin n → 𝕜) (i : Fin n) (y : 𝕜) (ν : Fin n →₀ ℕ) :
    monomialEval (Function.update x i y) ν = y ^ ν i * ∏ k ∈ univ.erase i, x k ^ ν k := by
  rw [monomialEval_eq_mul_prod_erase, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- `m (r/2)^(m−1) ≤ (2/r) r^m` for `r > 0`. -/
theorem nat_mul_half_pow_le {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (m : ℝ) * (r / 2) ^ (m - 1) ≤ 2 / r * r ^ m := by
  cases m with
  | zero => simp only [Nat.cast_zero, zero_mul]; positivity
  | succ k =>
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ 2 * 2 ^ k := by
      have h2 : k + 1 ≤ 2 * 2 ^ k :=
        (Nat.lt_two_pow_self).trans_le (Nat.le_mul_of_pos_left _ two_pos)
      exact_mod_cast h2
    have h3 : (0 : ℝ) < 2 ^ k := by positivity
    calc ((k + 1 : ℕ) : ℝ) * (r / 2) ^ (k + 1 - 1)
        = ((k + 1 : ℕ) : ℝ) / 2 ^ k * r ^ k := by
          rw [Nat.add_sub_cancel, div_pow]; ring
      _ ≤ 2 * r ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr.le k)
          rw [div_le_iff₀ h3]
          exact h1
      _ = 2 / r * r ^ (k + 1) := by
          rw [pow_succ]; field_simp

/-- `(m+1) (ρ/2)^μ ≤ 2 ρ^μ` when `m ≤ |μ|` — for `m = μ_i`. -/
theorem monomialEval_half_le (ρ : Fin n → ℝ≥0) (μ : Fin n →₀ ℕ) (i : Fin n) :
    ((μ i + 1 : ℕ) : ℝ≥0) * monomialEval (fun k => ρ k / 2) μ ≤ 2 * monomialEval ρ μ := by
  have h1 : monomialEval ρ μ = monomialEval (fun k => ρ k / 2) μ * 2 ^ Finsupp.degree μ := by
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum, monomialEval, monomialEval,
      Finsupp.prod_fintype _ _ (fun k => pow_zero _),
      Finsupp.prod_fintype _ _ (fun k => pow_zero _), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_pow, div_mul_cancel₀ _ two_ne_zero]
  have h2 : ((μ i + 1 : ℕ) : ℝ≥0) ≤ 2 * 2 ^ Finsupp.degree μ := by
    have h3 : μ i ≤ Finsupp.degree μ := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    have h4 : μ i + 1 ≤ 2 * 2 ^ Finsupp.degree μ :=
      (Nat.lt_two_pow_self).trans_le
        ((Nat.pow_le_pow_right two_pos h3).trans (Nat.le_mul_of_pos_left _ two_pos))
    exact_mod_cast h4
  calc ((μ i + 1 : ℕ) : ℝ≥0) * monomialEval (fun k => ρ k / 2) μ
      ≤ 2 * 2 ^ Finsupp.degree μ * monomialEval (fun k => ρ k / 2) μ :=
        mul_le_mul_of_nonneg_right h2 zero_le
    _ = 2 * monomialEval ρ μ := by rw [h1]; ring

/-- The formal derivative of a convergent series is convergent:
`‖∂_{X_i} c‖_{ρ/2} · ρ_i ≤ 2 ‖c‖_ρ`. -/
theorem pderiv_mem_conv {c : MvPowerSeries (Fin n) 𝕜} (hc : c ∈ Conv 𝕜 n) (i : Fin n) :
    MvPowerSeries.pderiv (R := 𝕜) i c ∈ Conv 𝕜 n := by
  obtain ⟨ρ, hρ⟩ := hc
  refine ⟨⟨fun k => ρ k / 2, fun k => by have := ρ.2 k; positivity⟩, fun h => ?_⟩
  have hle : ConvNorm (fun k => ρ k / 2) (MvPowerSeries.pderiv (R := 𝕜) i c) * (ρ i : ℝ≥0∞) ≤
      2 * ConvNorm ρ c := by
    unfold ConvNorm
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    calc ∑' μ : Fin n →₀ ℕ, ‖coeff μ (MvPowerSeries.pderiv (R := 𝕜) i c)‖ₑ *
            (monomialEval (fun k => ρ k / 2) μ : ℝ≥0∞) * (ρ i : ℝ≥0∞)
        ≤ ∑' μ : Fin n →₀ ℕ, 2 * (‖coeff (μ + Finsupp.single i 1) c‖ₑ *
            (monomialEval ρ (μ + Finsupp.single i 1) : ℝ≥0∞)) := by
          refine ENNReal.tsum_le_tsum fun μ => ?_
          rw [coeff_pderiv, mul_comm (coeff (μ + Finsupp.single i 1) c), ← Nat.cast_add_one]
          have hm : ‖((μ i + 1 : ℕ) : 𝕜)‖ₑ = (((μ i + 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
            rw [enorm_eq_nnnorm]
            congr 1
            exact NNReal.eq (by rw [coe_nnnorm, RCLike.norm_natCast, NNReal.coe_natCast])
          have h2 := ENNReal.coe_le_coe.mpr (monomialEval_half_le ρ μ i)
          rw [enorm_mul, monomialEval_add, monomialEval_single_pow, pow_one, ENNReal.coe_mul, hm]
          calc (((μ i + 1 : ℕ) : ℝ≥0) : ℝ≥0∞) * ‖coeff (μ + Finsupp.single i 1) c‖ₑ *
                  (monomialEval (fun k => ρ k / 2) μ : ℝ≥0∞) * (ρ i : ℝ≥0∞)
              = ((((μ i + 1 : ℕ) : ℝ≥0) * monomialEval (fun k => ρ k / 2) μ : ℝ≥0) : ℝ≥0∞) *
                  (‖coeff (μ + Finsupp.single i 1) c‖ₑ * (ρ i : ℝ≥0∞)) := by
                rw [ENNReal.coe_mul]; ring
            _ ≤ ((2 * monomialEval ρ μ : ℝ≥0) : ℝ≥0∞) *
                  (‖coeff (μ + Finsupp.single i 1) c‖ₑ * (ρ i : ℝ≥0∞)) := mul_le_mul' h2 le_rfl
            _ = 2 * (‖coeff (μ + Finsupp.single i 1) c‖ₑ *
                  ((monomialEval ρ μ : ℝ≥0∞) * (ρ i : ℝ≥0∞))) := by
                rw [ENNReal.coe_mul, ENNReal.coe_ofNat]; ring
      _ ≤ ∑' ν : Fin n →₀ ℕ, 2 * (‖coeff ν c‖ₑ * (monomialEval ρ ν : ℝ≥0∞)) :=
          ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective (Finsupp.single i 1))
            (fun ν => 2 * (‖coeff ν c‖ₑ * (monomialEval ρ ν : ℝ≥0∞)))
  rw [h, ENNReal.top_mul (ENNReal.coe_ne_zero.mpr (ρ.2 i).ne')] at hle
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hρ (top_le_iff.mp hle)

/-- Termwise differentiation of a convergent power series along the `i`-th coordinate (Mathlib's
`hasDerivAt_tsum_of_isPreconnected`): on the polydisc of half the radius,
`∂_i (evalSeries c) = evalSeries (∂_{X_i} c)`. -/
theorem fderiv_evalSeries_single {ρ : Radius n} {c : MvPowerSeries (Fin n) 𝕜}
    (hρ : ConvNorm ρ c ≠ ⊤) {x : Fin n → 𝕜} (hx : ∀ k, ‖x k‖ < (ρ k : ℝ) / 2) (i : Fin n) :
    fderiv 𝕜 (evalSeries c) x (Pi.single i 1) =
      evalSeries (MvPowerSeries.pderiv (R := 𝕜) i c) x := by
  classical
  set P : (Fin n →₀ ℕ) → 𝕜 := fun ν => ∏ k ∈ univ.erase i, x k ^ ν k with hP
  set g : (Fin n →₀ ℕ) → 𝕜 → 𝕜 := fun ν y => coeff ν c * (y ^ ν i * P ν) with hg
  set g' : (Fin n →₀ ℕ) → 𝕜 → 𝕜 :=
    fun ν y => coeff ν c * (((ν i : ℕ) : 𝕜) * y ^ (ν i - 1) * P ν) with hg'
  have hxle : ∀ k, ‖x k‖ ≤ ρ k := fun k => (hx k).le.trans (half_le_self (ρ k).2)
  have hρi : (0 : ℝ) < ρ i := NNReal.coe_pos.mpr (ρ.2 i)
  have hderiv : ∀ ν y, HasDerivAt (g ν) (g' ν y) y := fun ν y =>
    ((hasDerivAt_pow (ν i) y).mul_const (P ν)).const_mul (coeff ν c)
  set u : (Fin n →₀ ℕ) → ℝ := fun ν => 2 / (ρ i : ℝ) * (‖coeff ν c‖ * (monomialEval ρ ν : ℝ))
    with hu
  have hu_sum : Summable u := (summable_weighted hρ).mul_left _
  have hP_le : ∀ ν, ‖P ν‖ ≤ ∏ k ∈ univ.erase i, (ρ k : ℝ) ^ ν k := fun ν => by
    rw [hP, norm_prod]
    exact Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hxle k) _
  have hradius : ∀ ν, (monomialEval ρ ν : ℝ) =
      (ρ i : ℝ) ^ ν i * ∏ k ∈ univ.erase i, (ρ k : ℝ) ^ ν k := fun ν => by
    rw [coe_monomialEval, Finsupp.prod_fintype _ _ (fun k => pow_zero _),
      ← Finset.mul_prod_erase univ _ (mem_univ i)]
  have hbound : ∀ ν y, y ∈ Metric.ball (0 : 𝕜) ((ρ i : ℝ) / 2) → ‖g' ν y‖ ≤ u ν := by
    intro ν y hy
    rw [mem_ball_zero_iff] at hy
    have h1 : (ν i : ℝ) * ‖y‖ ^ (ν i - 1) * ‖P ν‖ ≤ 2 / (ρ i : ℝ) * (monomialEval ρ ν : ℝ) := by
      rw [hradius]
      calc (ν i : ℝ) * ‖y‖ ^ (ν i - 1) * ‖P ν‖
          ≤ (ν i : ℝ) * ((ρ i : ℝ) / 2) ^ (ν i - 1) * ∏ k ∈ univ.erase i, (ρ k : ℝ) ^ ν k :=
            mul_le_mul (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) hy.le _) (Nat.cast_nonneg _)) (hP_le ν)
              (norm_nonneg _) (by positivity)
        _ ≤ 2 / (ρ i : ℝ) * (ρ i : ℝ) ^ ν i * ∏ k ∈ univ.erase i, (ρ k : ℝ) ^ ν k :=
            mul_le_mul_of_nonneg_right (nat_mul_half_pow_le hρi (ν i))
              (Finset.prod_nonneg fun k _ => by positivity)
        _ = 2 / (ρ i : ℝ) * ((ρ i : ℝ) ^ ν i * ∏ k ∈ univ.erase i, (ρ k : ℝ) ^ ν k) := by ring
    calc ‖g' ν y‖ = ‖coeff ν c‖ * ((ν i : ℝ) * ‖y‖ ^ (ν i - 1) * ‖P ν‖) := by
          rw [hg']
          simp only [norm_mul, RCLike.norm_natCast, norm_pow]
      _ ≤ ‖coeff ν c‖ * (2 / (ρ i : ℝ) * (monomialEval ρ ν : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = u ν := by rw [hu]; ring
  have hopen : IsOpen (Metric.ball (0 : 𝕜) ((ρ i : ℝ) / 2)) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : 𝕜) ((ρ i : ℝ) / 2)) :=
    (convex_ball (0 : 𝕜) _).isPreconnected
  have hxi : x i ∈ Metric.ball (0 : 𝕜) ((ρ i : ℝ) / 2) := mem_ball_zero_iff.mpr (hx i)
  have hg0 : Summable fun ν => g ν (x i) := by
    refine (hasSum_evalSeries hρ hxle).summable.congr fun ν => ?_
    rw [hg, monomialEval_eq_mul_prod_erase]
  have hsum := hasDerivAt_tsum_of_isPreconnected hu_sum hopen hconn (fun ν y _ => hderiv ν y)
    hbound hxi hg0 hxi
  have heq : (fun z => ∑' ν, g ν z) = fun z => evalSeries c (Function.update x i z) := by
    funext z
    unfold evalSeries
    refine tsum_congr fun ν => ?_
    rw [hg, monomialEval_update]
  rw [heq] at hsum
  have hl : HasDerivAt (fun z : 𝕜 => Function.update x i z) (Pi.single i 1) (x i) := by
    refine hasDerivAt_pi.mpr fun k => ?_
    by_cases hk : k = i
    · simp only [hk, Function.update_self, Pi.single_eq_same]
      exact hasDerivAt_id _
    · simp only [Function.update_of_ne hk, Pi.single_eq_of_ne hk]
      exact hasDerivAt_const _ _
  have hF : HasFDerivAt (evalSeries c) (fderiv 𝕜 (evalSeries c) x) (Function.update x i (x i)) := by
    rw [Function.update_eq_self]
    exact ((analyticOnNhd_evalSeries hρ) x fun k =>
      (hx k).trans_le (half_le_self (ρ k).2)).differentiableAt.hasFDerivAt
  have hval := (hF.comp_hasDerivAt (x i) hl).unique hsum
  rw [hval]
  have hzero : ∀ ν, ν ∉ Set.range (fun μ : Fin n →₀ ℕ => μ + Finsupp.single i 1) →
      g' ν (x i) = 0 := by
    intro ν hν
    have hνi : ν i = 0 := by
      by_contra h
      exact hν ⟨ν - Finsupp.single i 1, tsub_add_cancel_of_le
        (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))⟩
    rw [hg']
    simp only [hνi, Nat.cast_zero, zero_mul, mul_zero]
  have hsumm : Summable fun ν => g' ν (x i) := hu_sum.of_norm_bounded fun ν => hbound ν (x i) hxi
  have hreindex : ∑' ν, g' ν (x i) = ∑' μ, g' (μ + Finsupp.single i 1) (x i) :=
    ((Function.Injective.hasSum_iff (add_left_injective (Finsupp.single i 1)) hzero).mpr
      hsumm.hasSum).tsum_eq.symm
  rw [hreindex]
  unfold evalSeries
  refine tsum_congr fun μ => ?_
  have h1 : (μ + Finsupp.single i 1 : Fin n →₀ ℕ) i = μ i + 1 := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
  have h2 : P (μ + Finsupp.single i 1) = P μ := by
    rw [hP]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, ite_eq_right (Finset.ne_of_mem_erase hk).symm,
      add_zero]
  rw [hg']
  dsimp only
  rw [h1, h2, Nat.add_sub_cancel, monomialEval_eq_mul_prod_erase x i, coeff_pderiv]
  push_cast
  ring

end Series

section Germ

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜))

theorem pderivGerm_coe (i : Fin n) (b : E) (f : E → 𝕜)
    (hf : (↑f : (𝓝 b).Germ 𝕜) ∈ analyticGermsAt 𝕜 E b) :
    (pderivGerm E ψ i b ⟨↑f, hf⟩).1 = ↑(fun y => fderiv 𝕜 f y (ψ.symm (Pi.single i 1))) := rfl

/-- The power series of the coordinate derivative `∂_i g` of an analytic germ is `∂_{X_i}` of the
power series of `g`. -/
theorem IsSeriesOf.pderiv {b : E} {f : E → 𝕜} {c : MvPowerSeries (Fin n) 𝕜}
    (hc : IsSeriesOf ψ b (↑f) c) (i : Fin n) :
    IsSeriesOf ψ b ↑(fun z => fderiv 𝕜 f z (ψ.symm (Pi.single i 1)))
      (MvPowerSeries.pderiv (R := 𝕜) i c) := by
  obtain ⟨ρ, hρ⟩ := hc.1
  refine ⟨pderiv_mem_conv hc.1 i, ?_⟩
  have h2 := hc.2
  rw [germCompCoord_coe, Germ.coe_eq] at h2
  rw [germCompCoord_coe]
  refine Germ.coe_eq.mpr ?_
  filter_upwards [h2.eventually_nhds,
    Analytic.eventually_norm_sub_lt (ψ b) ⟨fun k => ρ k / 2, fun k => by have := ρ.2 k; positivity⟩]
    with y hy hy2
  have hy3 : ∀ k, ‖(y - ψ b) k‖ < (ρ k : ℝ) / 2 := fun k => by
    have h := hy2 k
    change ‖(y - ψ b) k‖ < ((ρ k / 2 : ℝ≥0) : ℝ) at h
    rwa [NNReal.coe_div, NNReal.coe_ofNat] at h
  have hG : HasFDerivAt (fun y => evalSeries c (y - ψ b))
      (fderiv 𝕜 (evalSeries c) (y - ψ b)) y := by
    have h3 : HasFDerivAt (evalSeries c) (fderiv 𝕜 (evalSeries c) (y - ψ b)) (y - ψ b) :=
      ((analyticOnNhd_evalSeries hρ) (y - ψ b) fun k =>
        (hy3 k).trans_le (half_le_self (ρ k).2)).differentiableAt.hasFDerivAt
    have h4 := h3.comp y (hasFDerivAt_sub_const (ψ b))
    rwa [ContinuousLinearMap.comp_id] at h4
  have hF : HasFDerivAt (f ∘ ψ.symm) (fderiv 𝕜 (evalSeries c) (y - ψ b)) (ψ (ψ.symm y)) := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hG.congr_of_eventuallyEq hy
  have hf' : HasFDerivAt f
      ((fderiv 𝕜 (evalSeries c) (y - ψ b)).comp (ψ : E →L[𝕜] (Fin n → 𝕜))) (ψ.symm y) := by
    have h5 := hF.comp (ψ.symm y) ψ.hasFDerivAt
    rwa [show (f ∘ ψ.symm) ∘ ψ = f from funext fun z => by simp] at h5
  simp only [Function.comp_apply]
  rw [hf'.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, fderiv_evalSeries_single hρ hy3 i]

/-- `taylorGerm (∂_i g) = ∂_{X_i} (taylorGerm g)`. -/
theorem taylorGerm_pderivGerm (b : E) (i : Fin n) (g : analyticGermsAt 𝕜 E b) :
    (taylorGerm ψ b (pderivGerm E ψ i b g) : MvPowerSeries (Fin n) 𝕜) =
      MvPowerSeries.pderiv (R := 𝕜) i (taylorGerm ψ b g) := by
  obtain ⟨g0, f, rfl, hfa⟩ := g
  rw [coe_taylorGerm]
  exact taylorGermFun_eq_of_isSeriesOf ψ _
    (IsSeriesOf.pderiv ψ (isSeriesOf_taylorGerm ψ b ⟨↑f, f, rfl, hfa⟩) i)

end Germ

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

include ha hφ in
/-- "`T_a` commutes with differentiation" [BM97, (0.3)]: `T_a(∂_i f) = ∂_{X_i} T_a(f)` for the
coordinate partial derivatives of germs in the chart, read through the chart transport. -/
theorem IsTaylorHom.pderiv'
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T)
    {e : (structureSheaf 𝕜 E M).presheaf.stalk a ≃+* analyticGermsAt 𝕜 E (φ a)}
    (he : IsChartTransport 𝕜 E φ a e) (i : Fin n) (g : analyticGermsAt 𝕜 E (φ a)) :
    T (e.symm (pderivGerm E ψ i (φ a) g)) = MvPowerSeries.pderiv (R := 𝕜) i (T (e.symm g)) := by
  obtain rfl := IsTaylorHom.eq E ψ φ hT (isTaylorHom_taylorHom E ψ φ ha hφ)
  obtain rfl := IsChartTransport.eq E φ he (isChartTransport_chartTransport E φ ha hφ)
  rw [taylorHom_apply, taylorHom_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact taylorGerm_pderivGerm ψ (φ a) i g

end Manifold
