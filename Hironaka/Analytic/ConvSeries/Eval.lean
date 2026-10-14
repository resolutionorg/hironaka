/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Hironaka.Analytic.ConvSeries.Banach
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Evaluation of a convergent series over `K = ℝ` or `ℂ`, and its power series at `0`

For a series `f` of finite `ρ`-norm and a point `x ∈ K^m` of the closed polydisc `‖x_k‖ ≤ ρ_k`,
the terms `a_ν x^ν` are dominated by `‖a_ν‖ ρ^ν`, so the sum `evalSeries f x = ∑_ν a_ν x^ν`
converges absolutely (`summable_norm_evalTerm`, `hasSum_evalSeries`). Regrouped by degree, the
sum is the value at `x` of the formal multilinear series `toFMS f`, whose degree-`n` term is
`∑_{|ν| = n} a_ν · monoMapExp n ν` with `monoMapExp n ν (v₁, …, vₙ) = ∏_i (v_i)_{k_i}` for an
enumeration `k` of `ν`; its norm is at most `∑_{|ν| = n} ‖a_ν‖`, so the radius of `toFMS f` is
at least `min_k ρ_k` and `evalSeries f` has this power series on the sup-norm ball
(`hasFPowerSeriesOnBall_evalSeries`), hence is analytic there, with iterated derivatives at `0`
given by the coefficients (`factorial_smul_sum_eq_iteratedFDeriv`); a monomial sums to itself
(`evalSeries_monomial`, `evalSeries_X_pow`). Standard material [GR71, Kapitel I], phrased through
Mathlib's `HasFPowerSeriesOnBall`; analyticity on the whole open polydisc is in `Rescale.lean`, and
the converse (an analytic function is the sum of a convergent series) in `Bridge.lean`.


-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- On the closed polydisc `‖x_k‖ ≤ ρ_k` the monomials are dominated by `ρ^ν`. -/
theorem norm_monomialEval_le {x : Fin m → K} {ρ : Fin m → ℝ≥0} (hx : ∀ k, ‖x k‖ ≤ ρ k)
    (ν : Fin m →₀ ℕ) : ‖monomialEval x ν‖ ≤ monomialEval ρ ν := by
  rw [coe_monomialEval, monomialEval, Finsupp.prod, Finsupp.prod, norm_prod]
  refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hx k) _

/-! ## Evaluation and absolute convergence -/

/-- The function `x ↦ ∑_ν a_ν x^ν` defined by a formal power series (the sum is the `tsum`; it is
meaningful on the polydisc of a radius vector with finite norm). -/
noncomputable def evalSeries (f : MvPowerSeries (Fin m) K) (x : Fin m → K) : K :=
  ∑' ν : Fin m →₀ ℕ, coeff ν f * monomialEval x ν

/-- The weighted coefficients `‖a_ν‖ ρ^ν` of a series of finite `ρ`-norm are summable. -/
theorem summable_weighted {ρ : Radius m} {f : MvPowerSeries (Fin m) K} (hf : ConvNorm ρ f ≠ ⊤) :
    Summable fun ν : Fin m →₀ ℕ => ‖coeff ν f‖ * (monomialEval ρ ν : ℝ) := by
  rw [convNorm_eq_tsum_coe] at hf
  have h := NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hf)
  convert h using 1
  funext ν
  rw [NNReal.coe_mul, coe_nnnorm]

/-- On the closed polydisc `‖x_k‖ ≤ ρ_k` the series converges absolutely (its terms are dominated
by `‖a_ν‖ ρ^ν`, uniformly in `x`). -/
theorem summable_norm_evalTerm {ρ : Radius m} {f : MvPowerSeries (Fin m) K}
    (hf : ConvNorm ρ f ≠ ⊤) {x : Fin m → K} (hx : ∀ k, ‖x k‖ ≤ ρ k) :
    Summable fun ν : Fin m →₀ ℕ => ‖coeff ν f * monomialEval x ν‖ :=
  (summable_weighted hf).of_nonneg_of_le (fun _ => norm_nonneg _) fun ν => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_monomialEval_le hx ν) (norm_nonneg _)

theorem hasSum_evalSeries {ρ : Radius m} {f : MvPowerSeries (Fin m) K} (hf : ConvNorm ρ f ≠ ⊤)
    {x : Fin m → K} (hx : ∀ k, ‖x k‖ ≤ ρ k) :
    HasSum (fun ν : Fin m →₀ ℕ => coeff ν f * monomialEval x ν) (evalSeries f x) :=
  (summable_norm_evalTerm hf hx).of_norm.hasSum

/-! ## The multilinear terms -/

variable (K) in
/-- The continuous multilinear map `(v₁, …, vₙ) ↦ ∏ i, v_i (k i)` attached to a tuple `k` of
coordinate indices. -/
noncomputable def monoMap (n : ℕ) (k : Fin n → Fin m) :
    ContinuousMultilinearMap K (fun _ : Fin n => (Fin m → K)) K :=
  (ContinuousMultilinearMap.mkPiAlgebraFin K n K).compContinuousLinearMap
    fun i => ContinuousLinearMap.proj (k i)

theorem monoMap_apply (n : ℕ) (k : Fin n → Fin m) (v : Fin n → (Fin m → K)) :
    monoMap K n k v = ∏ i, v i (k i) := by
  simp [monoMap, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]

theorem norm_monoMap_le (n : ℕ) (k : Fin n → Fin m) : ‖monoMap K n k‖ ≤ 1 := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ‖ContinuousMultilinearMap.mkPiAlgebraFin K n K‖ ≤ 1 := by simp
  have h2 : ∀ i : Fin n, ‖(ContinuousLinearMap.proj (k i) : (Fin m → K) →L[K] K)‖ ≤ 1 :=
    fun i => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]
      exact norm_le_pi_norm x (k i)
  calc ‖ContinuousMultilinearMap.mkPiAlgebraFin K n K‖
        * ∏ i, ‖(ContinuousLinearMap.proj (k i) : (Fin m → K) →L[K] K)‖
      ≤ 1 * ∏ i : Fin n, (1 : ℝ) :=
        mul_le_mul h1 (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => h2 i)
          (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
    _ = 1 := by simp

variable (K) in
/-- The multilinear map of a single exponent `ν` in degree `n`: `monoMap` of the enumeration of
`ν` when `|ν| = n`, and `0` otherwise. -/
noncomputable def monoMapExp (n : ℕ) (ν : Fin m →₀ ℕ) :
    ContinuousMultilinearMap K (fun _ : Fin n => (Fin m → K)) K :=
  if h : (expList ν).length = n then monoMap K n fun i => (expList ν).get (Fin.cast h.symm i)
  else 0

theorem monoMapExp_apply_diag {n : ℕ} {ν : Fin m →₀ ℕ} (h : ν.degree = n) (x : Fin m → K) :
    monoMapExp K n ν (fun _ => x) = monomialEval x ν := by
  have hl : (expList ν).length = n := (length_expList ν).trans h
  rw [monoMapExp, dite_eq_left hl, monoMap_apply, ← prod_map_expList, ← List.prod_ofFn]
  congr 1
  subst hl
  change List.ofFn (x ∘ (expList ν).get) = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem norm_monoMapExp_le (n : ℕ) (ν : Fin m →₀ ℕ) : ‖monoMapExp K n ν‖ ≤ 1 := by
  unfold monoMapExp
  split_ifs
  · exact norm_monoMap_le _ _
  · simp

/-! ## The formal multilinear series and its convergence -/

/-- The formal multilinear series of a power series, `∑_{|ν| = n} a_ν · monoMapExp n ν` in
degree `n`. -/
noncomputable def toFMS (f : MvPowerSeries (Fin m) K) : FormalMultilinearSeries K (Fin m → K) K :=
  fun n => ∑ ν ∈ degreeSet m n, coeff ν f • monoMapExp K n ν

theorem toFMS_apply_diag (f : MvPowerSeries (Fin m) K) (n : ℕ) (x : Fin m → K) :
    toFMS f n (fun _ => x) = ∑ ν ∈ degreeSet m n, coeff ν f * monomialEval x ν := by
  rw [toFMS, sum_apply]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [smul_apply, monoMapExp_apply_diag (mem_degreeSet.mp hν),
    smul_eq_mul]

theorem norm_toFMS_le (f : MvPowerSeries (Fin m) K) (n : ℕ) :
    ‖toFMS f n‖ ≤ ∑ ν ∈ degreeSet m n, ‖coeff ν f‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_monoMapExp_le n ν)

/-- The radius of `toFMS f` is at least any `r ≤ min_k ρ_k` when `‖f‖_ρ < ∞`. -/
theorem le_radius_toFMS {ρ : Radius m} {f : MvPowerSeries (Fin m) K} (hf : ConvNorm ρ f ≠ ⊤)
    {r : ℝ≥0} (hr : ∀ k, r ≤ ρ k) : (r : ℝ≥0∞) ≤ (toFMS f).radius := by
  refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
  refine (summable_sum_degreeSet (w := fun ν => ‖coeff ν f‖ * (monomialEval ρ ν : ℝ))
    (fun ν => mul_nonneg (norm_nonneg _) (monomialEval ρ ν).2)
    (summable_weighted hf)).of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _)) fun n => ?_
  calc ‖toFMS f n‖ * (r : ℝ) ^ n
      ≤ (∑ ν ∈ degreeSet m n, ‖coeff ν f‖) * (r : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (norm_toFMS_le f n) (pow_nonneg r.2 _)
    _ = ∑ ν ∈ degreeSet m n, ‖coeff ν f‖ * (r : ℝ) ^ n := Finset.sum_mul _ _ _
    _ ≤ ∑ ν ∈ degreeSet m n, ‖coeff ν f‖ * (monomialEval ρ ν : ℝ) := by
        refine Finset.sum_le_sum fun ν hν => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact_mod_cast pow_le_monomialEval hr (mem_degreeSet.mp hν)

/-- A series of finite `ρ`-norm has the power series `toFMS f` at `0` on the sup-norm ball of any
radius `r ≤ min_k ρ_k` (Mathlib's `HasFPowerSeriesOnBall`). -/
theorem hasFPowerSeriesOnBall_evalSeries {ρ : Radius m} {f : MvPowerSeries (Fin m) K}
    (hf : ConvNorm ρ f ≠ ⊤) {r : ℝ≥0} (hr0 : 0 < r) (hr : ∀ k, r ≤ ρ k) :
    HasFPowerSeriesOnBall (evalSeries f) (toFMS f) 0 r where
  r_le := le_radius_toFMS hf hr
  r_pos := by exact_mod_cast hr0
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < r := by
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] at hy
      exact_mod_cast hy
    have hyρ : ∀ k, ‖y k‖ ≤ ρ k := fun k =>
      (norm_le_pi_norm y k).trans (hy'.le.trans (hr k))
    rw [zero_add]
    simp_rw [toFMS_apply_diag]
    exact hasSum_sum_degreeSet (hasSum_evalSeries hf hyρ)

/-- The function of a series of finite `ρ`-norm is analytic on the open sup-norm ball of radius
`min_k ρ_k` (any `r ≤ ρ_k`). -/
theorem analyticOnNhd_evalSeries_ball {ρ : Radius m} {f : MvPowerSeries (Fin m) K}
    (hf : ConvNorm ρ f ≠ ⊤) {r : ℝ≥0} (hr0 : 0 < r) (hr : ∀ k, r ≤ ρ k) :
    AnalyticOnNhd K (evalSeries f) (Metric.ball 0 r) := fun y hy =>
  (hasFPowerSeriesOnBall_evalSeries hf hr0 hr).analyticAt_of_mem (by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast (mem_ball_zero_iff.mp hy))

/-- The iterated derivatives at `0` are the coefficients up to factorials:
`n! · ∑_{|ν| = n} a_ν x^ν = D^n (evalSeries f) (0) (x, …, x)`. -/
theorem factorial_smul_sum_eq_iteratedFDeriv {ρ : Radius m} {f : MvPowerSeries (Fin m) K}
    (hf : ConvNorm ρ f ≠ ⊤) (n : ℕ) (x : Fin m → K) :
    n.factorial • ∑ ν ∈ degreeSet m n, coeff ν f * monomialEval x ν
      = iteratedFDeriv K n (evalSeries f) 0 (fun _ => x) := by
  obtain ⟨r, hr0, hr⟩ := ρ.exists_le
  rw [← toFMS_apply_diag]
  exact (hasFPowerSeriesOnBall_evalSeries hf hr0 hr).factorial_smul x n

/-! ## Monomials -/

/-- The sum of a monomial `a x^ν` is `a x^ν`. -/
theorem evalSeries_monomial (ν : Fin m →₀ ℕ) (a : K) (x : Fin m → K) :
    evalSeries (monomial ν a) x = a * monomialEval x ν := by
  classical
  unfold evalSeries
  rw [tsum_eq_single ν]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro μ hμ
    rw [coeff_monomial, ite_eq_right hμ, zero_mul]

/-- The sum of `x_k^n` is `x_k^n`. -/
theorem evalSeries_X_pow (k : Fin m) (n : ℕ) (x : Fin m → K) :
    evalSeries (X k ^ n : MvPowerSeries (Fin m) K) x = x k ^ n := by
  rw [X_pow_eq, evalSeries_monomial, one_mul, monomialEval_single_pow]

/-- `x_k^n` has finite majorant norm for every radius vector. -/
theorem convNorm_X_pow_ne_top (ρ : Fin m → ℝ≥0) (k : Fin m) (n : ℕ) :
    ConvNorm ρ (X k ^ n : MvPowerSeries (Fin m) K) ≠ ⊤ := by
  rw [X_pow_eq, convNorm_monomial]
  exact ENNReal.mul_ne_top enorm_ne_top ENNReal.coe_ne_top

end Analytic

/-! ### The real case -/

open scoped ENNReal NNReal Topology
open MvPowerSeries

namespace Analytic

variable {m : ℕ}

/-- On the closed polydisc `|x_k| ≤ ρ_k` the monomials are dominated by `ρ^ν`. -/
theorem abs_monomialEval_le {x : Fin m → ℝ} {ρ : Fin m → ℝ≥0} (hx : ∀ k, |x k| ≤ ρ k)
    (ν : Fin m →₀ ℕ) : |monomialEval x ν| ≤ monomialEval ρ ν :=
  norm_monomialEval_le (K := ℝ) (x := x) (ρ := ρ) hx ν

end Analytic
