/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Basic
import Hironaka.Analytic.Rueckert.Quotient
import Hironaka.Analytic.Rueckert.Slices
import Hironaka.Analytic.Weierstrass.Poly
import Hironaka.Analytic.Weierstrass.Regular
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Dividing by a monic polynomial in the first variable

A monic polynomial `p ∈ 𝒪_m[T]` evaluated at the first variable, `W = p(x_0) = convPolyEval p`,
is `x_0`-regular of some order `d' ≤ deg p`: the order of `p(x_0, 0, …, 0) = x_0^{deg p} +
∑ p_k(0) x_0^k`, a nonzero polynomial in one variable (`IsRegularIn`, in the coefficient form
`isRegularIn_iff`). Weierstrass division by `W` (`exists_division_conv`,
`eq_sum_convTail_sliceConv` of `Slices.lean`) then writes every `G ∈ 𝒪_{m+1}` as
`q W + ∑_{k < d'} b_k(x_1, …, x_m) x_0^k` with convergent `b_k`: the remainder is a polynomial in
`x_0` of degree `< d' ≤ deg p` with coefficients in the tail ring `𝒪_m`. This is the one-variable
step of the iterated division of `FibreDivision.lean` (the division argument of
[Fre17, Ch. I, 8.3]); the monic relations of the fibre coordinates need not be Weierstrass
polynomials (their lower coefficients may have nonzero constant terms), which is why the order
`d'` is not `deg p` in general.
-/

public section

open MvPowerSeries Polynomial

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- The exponent `k` in the first variable, as a `Finsupp.cons`. -/
theorem single_zero_eq_cons (k : ℕ) :
    (Finsupp.single (0 : Fin (m + 1)) k) = Finsupp.cons k (0 : Fin m →₀ ℕ) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

/-- The coefficient of `x_0^j` (with no other variable) in `p(x_0) = convPolyEval p` is the
constant term of the `j`-th coefficient of `p`. -/
theorem coeff_single_zero_convPolyEval (p : Polynomial (Conv K m)) (j : ℕ) :
    coeff (Finsupp.single (0 : Fin (m + 1)) j) (convPolyEval K p : MvPowerSeries (Fin (m + 1)) K) =
      constantCoeff (p.coeff j : MvPowerSeries (Fin m) K) := by
  rw [coe_convPolyEval_eq_sum, map_sum, single_zero_eq_cons]
  simp_rw [coeff_cons_liftTail_mul_X_pow]
  by_cases hj : j ∈ Finset.range (p.natDegree + 1)
  · rw [Finset.sum_eq_single j]
    · rw [ite_eq_left rfl, coeff_zero_eq_constantCoeff_apply]
    · intro k _ hk
      rw [ite_eq_right (Ne.symm hk)]
    · intro h
      exact absurd hj h
  · rw [Finset.sum_eq_zero fun k hk => ?_]
    · have : p.coeff j = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hj)
      rw [this, Subalgebra.coe_zero, map_zero]
    · rw [ite_eq_right]
      rintro rfl
      exact hj hk

/-- A monic polynomial in `x_0` with coefficients in the tail ring is `x_0`-regular of some order
`d' ≤ deg p`: `p(x_0, 0, …, 0)` is a nonzero polynomial in one variable (its leading coefficient
is `1`), and `d'` is its order of vanishing at `0`. -/
theorem exists_isRegularIn_convPolyEval_of_monic (p : Polynomial (Conv K m)) (hp : p.Monic) :
    ∃ d' ≤ p.natDegree,
      IsRegularIn (convPolyEval K p : MvPowerSeries (Fin (m + 1)) K) d' := by
  classical
  have hex : ∃ k, coeff (Finsupp.single (0 : Fin (m + 1)) k)
      (convPolyEval K p : MvPowerSeries (Fin (m + 1)) K) ≠ 0 := by
    refine ⟨p.natDegree, ?_⟩
    rw [coeff_single_zero_convPolyEval, Polynomial.Monic.coeff_natDegree hp, Subalgebra.coe_one,
      map_one]
    exact one_ne_zero
  refine ⟨Nat.find hex, Nat.find_min' hex ?_, ?_⟩
  · rw [coeff_single_zero_convPolyEval, Polynomial.Monic.coeff_natDegree hp, Subalgebra.coe_one,
      map_one]
    exact one_ne_zero
  · rw [isRegularIn_iff]
    refine ⟨fun k hk => ?_, Nat.find_spec hex⟩
    have := Nat.find_min hex hk
    simpa using this

/-- Weierstrass division by an `x_0`-regular series `W` of order `d'` with the remainder written
as a polynomial in `x_0` of degree `< d'` whose coefficients are convergent series in the tail
variables (`eq_sum_convTail_sliceConv`). -/
theorem exists_eq_mul_add_sum_convTail_mul_convX_pow {W : Conv K (m + 1)} {d' : ℕ}
    (hreg : IsRegularIn (W : MvPowerSeries (Fin (m + 1)) K) d') (G : Conv K (m + 1)) :
    ∃ (q : Conv K (m + 1)) (b : Fin d' → Conv K m) (k : Fin d' → ℕ),
      (∀ j, k j < d') ∧ G = q * W + ∑ j, convTail K (b j) * convX K 0 ^ k j := by
  obtain ⟨q, r, hrd, hG⟩ := exists_division_conv (f := G) hreg
  refine ⟨q, fun j => sliceConv r (d' - 1 - j), fun j => d' - 1 - (j : ℕ), fun j => ?_, ?_⟩
  · have := j.2
    change d' - 1 - (j : ℕ) < d'
    omega
  · rw [hG]
    congr 1
    exact eq_sum_convTail_sliceConv hrd

end Analytic
