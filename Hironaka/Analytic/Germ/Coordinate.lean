/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
import Hironaka.Analytic.Germ.Base
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Coordinates and monomials as convergent series; division by a coordinate

The coordinate `x_k` and the monomials `x^θ` as elements of `Conv K n`, and the coefficient shift
`divX k c` with `coeff ν (divX k c) = coeff (ν + e_k) c`, which divides a series with no
monomials free of `x_k` by `x_k` (`X_mul_divX`) and satisfies the majorant bound
`‖divX k c‖_ρ ≤ ρ_k⁻¹ ‖c‖_ρ`, so that it stays convergent; for `k = 0` it is the quotient
operator `wQ 1` of the Weierstrass theory. These are the elementary facts about the local ring of
germs that Bierstone and Milman use without comment when they factor a germ into smooth factors
and monomials [BM88, proof of Theorem 4.4, pp. 24–25]; not in the sources as such.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`). The field-free
lemmas of the germ theory are in `Hironaka/Analytic/Germ/Base.lean`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {n : ℕ}

variable (K) in
/-- The coordinate `x_k` as an element of `Conv K n`. -/
noncomputable def convX (k : Fin n) : Conv K n := ⟨X k, X_mem_conv k⟩

variable (K) in
/-- The monomial `x^θ` as an element of `Conv K n`. -/
noncomputable def convMonomial (θ : Fin n →₀ ℕ) : Conv K n := ⟨monomial θ 1, monomial_mem_conv θ 1⟩

@[simp]
theorem coe_convX (k : Fin n) : (convX K k : MvPowerSeries (Fin n) K) = X k := rfl

theorem coe_convMonomial (θ : Fin n →₀ ℕ) :
    (convMonomial K θ : MvPowerSeries (Fin n) K) = monomial θ 1 := rfl

theorem convMonomial_zero : convMonomial K (0 : Fin n →₀ ℕ) = 1 :=
  Subtype.ext (by rw [coe_convMonomial, MvPowerSeries.monomial_zero_one]; rfl)

theorem convMonomial_add (θ θ' : Fin n →₀ ℕ) :
    convMonomial K (θ + θ') = convMonomial K θ * convMonomial K θ' :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_convMonomial, coe_convMonomial, coe_convMonomial,
      monomial_mul_monomial, one_mul])

theorem convMonomial_single (k : Fin n) : convMonomial K (Finsupp.single k 1) = convX K k :=
  Subtype.ext (by rw [coe_convMonomial, coe_convX, X_def])

theorem convX_ne_zero (k : Fin n) : convX K k ≠ 0 := by
  intro h
  have h1 := congrArg Subtype.val h
  rw [coe_convX] at h1
  have h2 := congrArg (coeff (Finsupp.single k 1)) h1
  rw [coeff_X, ite_eq_left rfl] at h2
  exact one_ne_zero (h2.trans (map_zero _))

/-! ### Division by a coordinate -/

/-- The coefficient shift `x_k⁻¹ · (terms divisible by x_k)`:
`coeff ν (divX k c) = coeff (ν + e_k) c`. -/
noncomputable def divX (k : Fin n) (c : MvPowerSeries (Fin n) K) : MvPowerSeries (Fin n) K :=
  fun ν => coeff (ν + Finsupp.single k 1) c

theorem coeff_divX (k : Fin n) (c : MvPowerSeries (Fin n) K) (ν : Fin n →₀ ℕ) :
    coeff ν (divX k c) = coeff (ν + Finsupp.single k 1) c := rfl

/-- A series without monomials free of `x_k` is `x_k` times its shift. -/
theorem X_mul_divX (k : Fin n) {c : MvPowerSeries (Fin n) K}
    (h0 : ∀ ν : Fin n →₀ ℕ, ν k = 0 → coeff ν c = 0) : X k * divX k c = c := by
  ext ν
  rw [X_def, coeff_monomial_mul]
  by_cases hν : ν k = 0
  · rw [ite_eq_right, h0 ν hν]
    rw [Finsupp.single_le_iff, hν]
    exact Nat.not_succ_le_zero 0
  · rw [ite_eq_left (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hν)), one_mul,
      coeff_divX, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hν))]

/-- Every series is `x_k · divX k c` plus its `x_k`-free part. -/
theorem coeff_X_mul_divX (k : Fin n) (c : MvPowerSeries (Fin n) K) (ν : Fin n →₀ ℕ) :
    coeff ν (X k * divX k c) = if ν k = 0 then 0 else coeff ν c := by
  rw [X_def, coeff_monomial_mul]
  by_cases hν : ν k = 0
  · rw [ite_eq_right, ite_eq_left hν]
    rw [Finsupp.single_le_iff, hν]
    exact Nat.not_succ_le_zero 0
  · rw [ite_eq_left (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hν)), one_mul,
      coeff_divX, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hν)),
      ite_eq_right hν]

/-- The majorant bound `‖divX k c‖_ρ ≤ ρ_k⁻¹ ‖c‖_ρ`. -/
theorem convNorm_divX_le (ρ : Radius n) (k : Fin n) (c : MvPowerSeries (Fin n) K) :
    ConvNorm ρ (divX k c) ≤ ((ρ k)⁻¹ : ℝ≥0) * ConvNorm ρ c := by
  have key : ∀ ν : Fin n →₀ ℕ,
      monomialEval ρ ν = (ρ k)⁻¹ * monomialEval ρ (ν + Finsupp.single k 1) := fun ν => by
    rw [monomialEval_add_single, mul_comm, mul_assoc, mul_inv_cancel₀ (ρ.pos k).ne', mul_one]
  unfold ConvNorm
  calc ∑' ν, ‖coeff ν (divX k c)‖ₑ * (monomialEval ρ ν : ℝ≥0∞)
      = ((ρ k)⁻¹ : ℝ≥0) * ∑' ν : Fin n →₀ ℕ,
          (fun μ => ‖coeff μ c‖ₑ * (monomialEval ρ μ : ℝ≥0∞)) (ν + Finsupp.single k 1) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun ν => ?_
        rw [coeff_divX, key ν, ENNReal.coe_mul]
        ring
    _ ≤ _ :=
        mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective _)
          (fun μ => ‖coeff μ c‖ₑ * (monomialEval ρ μ : ℝ≥0∞)))

theorem divX_mem_conv (k : Fin n) {c : MvPowerSeries (Fin n) K} (hc : c ∈ Conv K n) :
    divX k c ∈ Conv K n := by
  obtain ⟨ρ, hρ⟩ := hc
  exact ⟨ρ, ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hρ)
    (convNorm_divX_le ρ k c)⟩

/-- `x_k ∣ c` in `MvPowerSeries` iff the monomials free of `x_k` are absent; in that case the
quotient `divX k c` is convergent when `c` is. -/
theorem convX_dvd_of_coeff {c : Conv K n} (k : Fin n)
    (h0 : ∀ ν : Fin n →₀ ℕ, ν k = 0 → coeff ν (c : MvPowerSeries (Fin n) K) = 0) :
    convX K k ∣ c :=
  ⟨⟨divX k c, divX_mem_conv k c.2⟩, Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_convX]
    exact (X_mul_divX k h0).symm)⟩

end Analytic
