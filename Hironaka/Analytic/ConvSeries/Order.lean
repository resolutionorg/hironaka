/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Eval
public import Mathlib.RingTheory.MvPowerSeries.Order
import Hironaka.Analytic.ConvSeries.Bridge
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# The order of a convergent series over `K = ℝ` or `ℂ`, formally and at function level

The order `μ(f)` of a power series is Mathlib's `MvPowerSeries.order` (the least degree of a
nonzero coefficient, `⊤` for `0`); for `K = ℝ` it is the order `μ_a(f) = max {k : f_a ∈ 𝔪_a^k}`
of a germ in [BM88, Definition 4.6, p. 23]. Orders add (`MvPowerSeries.order_mul`, the ring
`MvPowerSeries (Fin m) K` having no zero divisors). At function level, `μ(f) ≥ k` iff every
iterated derivative of order `< k` of the function `evalSeries f` vanishes at `0`: the iterated
derivative of order `j` is the symmetrization of the degree-`j` multilinear term
(`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace`), which is zero when the
degree-`j` coefficients vanish; conversely a vanishing derivative kills the homogeneous part of
degree `j` as a function, hence as a polynomial (`MvPolynomial.funext`), hence coefficientwise.
The function-level clause is what lets the order of a germ on a manifold be read off any
convergent expansion (`Hironaka/Manifold/IdealSheaf`).


-/

public section

open scoped ENNReal NNReal Topology
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- Orders add (Mathlib's `MvPowerSeries.order_mul`, `order 0 = ⊤`). -/
theorem order_mul (f g : MvPowerSeries (Fin m) K) : (f * g).order = f.order + g.order :=
  MvPowerSeries.order_mul f g

/-- The degree-`n` term of `toFMS f` vanishes when the degree-`n` coefficients do. -/
theorem toFMS_eq_zero_of_coeff (f : MvPowerSeries (Fin m) K) {n : ℕ}
    (h : ∀ ν, ν.degree = n → coeff ν f = 0) : toFMS f n = 0 := by
  rw [toFMS]
  refine Finset.sum_eq_zero fun ν hν => ?_
  rw [h ν (mem_degreeSet.mp hν)]
  exact zero_smul K (monoMapExp K n ν)

/-- At function level, `μ(f) ≥ k` iff all iterated derivatives of order `< k` of the function
vanish at `0`: the order of a germ in the sense of [BM88, Definition 4.6, p. 23]. -/
theorem le_order_iff_iteratedFDeriv_eq_zero {f : MvPowerSeries (Fin m) K} (hf : f ∈ Conv K m)
    (k : ℕ) :
    (k : ℕ∞) ≤ f.order ↔ ∀ j < k, iteratedFDeriv K j (evalSeries f) 0 = 0 := by
  obtain ⟨ρ, hρ⟩ := hf
  have hρ' : ConvNorm ρ f ≠ ⊤ := hρ
  obtain ⟨r, hr0, hr⟩ := ρ.exists_le
  have hp := hasFPowerSeriesOnBall_evalSeries hρ' hr0 hr
  constructor
  · intro hk j hj
    have hcoeff : ∀ ν, ν.degree = j → coeff ν f = 0 := by
      intro ν hν
      refine MvPowerSeries.coeff_of_lt_order ?_
      rw [hν]
      exact lt_of_lt_of_le (by exact_mod_cast hj) hk
    ext v
    rw [hp.iteratedFDeriv_eq_sum_of_completeSpace v]
    simp [toFMS_eq_zero_of_coeff f hcoeff]
  · intro h
    refine MvPowerSeries.nat_le_order fun ν hν => ?_
    have hj := h ν.degree hν
    -- the homogeneous part of degree `|ν|` vanishes as a function, hence as a polynomial
    have hpoly : homogeneousPoly f ν.degree = 0 := by
      refine MvPolynomial.funext fun x => ?_
      rw [eval_homogeneousPoly, map_zero]
      have hn : (ν.degree.factorial : K) ≠ 0 := by
        exact_mod_cast ν.degree.factorial_ne_zero
      apply mul_left_cancel₀ hn
      have e := factorial_smul_sum_eq_iteratedFDeriv hρ' ν.degree x
      rw [nsmul_eq_mul] at e
      rw [e, hj, mul_zero]
      rfl
    have := congrArg (AddMonoidAlgebra.coeff · ν) hpoly
    rwa [coeff_homogeneousPoly f rfl, AddMonoidAlgebra.coeff_zero] at this

end Analytic
