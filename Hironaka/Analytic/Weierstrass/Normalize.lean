/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Weierstrass.Axis
import Hironaka.Analytic.ConvSeries.Units
import Hironaka.Analytic.Weierstrass.Regular
import Hironaka.Analytic.Weierstrass.Splitting
import Mathlib.Tactic.Positivity.Finset

/-!
# Normalization of a regular series

A convergent `g`, `x_0`-regular of order `d`, is `e(x_0) · (x_0^d - h)` with `e` a convergent unit
in `x_0` alone and `h` without pure `x_0`-terms. The restriction of `g` to the axis is `x_0^d · e`
where `e := axis (wQ d g)` (the pure `x_0`-coefficients of `g` below degree `d` vanish, so
`axis (wR d g) = 0`), and `e(0)` is the `x_0^d`-coefficient of `g`, nonzero by regularity. With
`E := liftFirst e`, a unit of `Conv K (m + 1)` because its constant term is nonzero, put
`h := x_0^d - E⁻¹ g`: its restriction to the axis is `x_0^d - axis E⁻¹ · x_0^d e = 0`, and
`g = E (x_0^d - h)`. This is the reduction to a divisor of the form `x_0^d - h` in the
Banach-algebra proof of Weierstrass division [GR71, Kapitel I]; the smallness of `h` is arranged
in `Division.lean` by shrinking the tail radii.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

theorem wQ_mem_conv {g : MvPowerSeries (Fin (m + 1)) K} (hg : g ∈ Conv K (m + 1)) (d : ℕ) :
    wQ d g ∈ Conv K (m + 1) := by
  obtain ⟨ρ, hρ⟩ := hg
  exact ⟨ρ, ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hρ) (convNorm_wQ_le ρ d g)⟩

theorem tailVanishes_iff_axis_eq_zero (h : MvPowerSeries (Fin (m + 1)) K) :
    TailVanishes h ↔ axis h = 0 := by
  constructor
  · intro hT
    ext ν
    rw [coeff_axis, (coeff ν).map_zero]
    exact hT _
  · intro ha k
    rw [← coeff_single_axis, ha, (coeff _).map_zero]

/-- For `g` with vanishing pure `x_0`-coefficients below `d`, the remainder part `wR d g` has no
pure `x_0`-terms. -/
theorem axis_wR_eq_zero {g : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hg : ∀ k < d, coeff (Finsupp.single 0 k) g = 0) : axis (wR d g) = 0 := by
  ext ν
  rw [coeff_axis, coeff_wR, (coeff ν).map_zero]
  by_cases h : ν 0 < d
  · rw [ite_eq_left (by rwa [Finsupp.single_eq_same]), hg _ h]
  · rw [ite_eq_right (by rwa [Finsupp.single_eq_same])]

/-- `g(x_0, 0) = x_0^d · e(x_0)` with `e = axis (wQ d g)`. -/
theorem axis_eq_X_pow_mul {g : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hg : ∀ k < d, coeff (Finsupp.single 0 k) g = 0) :
    axis g = X 0 ^ d * axis (wQ d g) := by
  conv_lhs => rw [← X_pow_mul_wQ_add_wR d g]
  rw [← axisHom_apply, map_add, map_mul, map_pow]
  simp only [axisHom_apply]
  rw [axis_X_zero, axis_wR_eq_zero hg, add_zero]

/-- Normalization: a convergent `g`, `x_0`-regular of order `d`, is `e(x_0) · (x_0^d - h)` with
`e` a convergent unit in `x_0` alone and `h` without pure `x_0`-terms. -/
theorem IsRegularIn.exists_normalized {g : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hg : g ∈ Conv K (m + 1)) (hreg : IsRegularIn g d) :
    ∃ (e : MvPowerSeries (Fin 1) K) (h : MvPowerSeries (Fin (m + 1)) K),
      e ∈ Conv K 1 ∧ constantCoeff e ≠ 0 ∧ h ∈ Conv K (m + 1) ∧ TailVanishes h ∧
      g = liftFirst e * (X 0 ^ d - h) := by
  obtain ⟨hlow, hd⟩ := (isRegularIn_iff g d).mp hreg
  set e : MvPowerSeries (Fin 1) K := axis (wQ d g) with he
  have heConv : e ∈ Conv K 1 := axis_mem_conv (wQ_mem_conv hg d)
  have he0 : constantCoeff e ≠ 0 := by
    rw [he, constantCoeff_axis, ← coeff_zero_eq_constantCoeff_apply, coeff_wQ, zero_add]
    exact hd
  have hE : (liftFirst e : MvPowerSeries (Fin (m + 1)) K) ∈ Conv K (m + 1) :=
    liftFirst_mem_conv heConv
  have hE0 : constantCoeff (liftFirst e : MvPowerSeries (Fin (m + 1)) K) ≠ 0 := by
    rw [constantCoeff_liftFirst]; exact he0
  obtain ⟨u, hu⟩ := (isUnit_iff_constantCoeff_ne_zero hE).mpr hE0
  obtain ⟨E', hE'Conv, hEE'⟩ : ∃ E' ∈ Conv K (m + 1), liftFirst e * E' = 1 := by
    refine ⟨((u⁻¹ : (Conv K (m + 1))ˣ) : Conv K (m + 1)), Subtype.mem _, ?_⟩
    have h1 := u.mul_inv
    rw [hu] at h1
    exact congrArg Subtype.val h1
  refine ⟨e, X 0 ^ d - E' * g, heConv, he0, ?_, ?_, ?_⟩
  · exact sub_mem (pow_mem (X_mem_conv 0) d) (mul_mem hE'Conv hg)
  · rw [tailVanishes_iff_axis_eq_zero, ← axisHom_apply, map_sub, map_pow, map_mul]
    simp only [axisHom_apply]
    rw [axis_X_zero, axis_eq_X_pow_mul hlow, ← he]
    have h1 : axis E' * e = 1 := by
      have h2 := congrArg axis hEE'
      rw [axis_mul, axis_liftFirst, axis_one, mul_comm] at h2
      exact h2
    calc X 0 ^ d - axis E' * (X 0 ^ d * e) = X 0 ^ d - (axis E' * e) * X 0 ^ d := by ring
      _ = 0 := by rw [h1, one_mul, sub_self]
  · rw [sub_sub_cancel, ← mul_assoc, hEE', one_mul]

end Analytic
