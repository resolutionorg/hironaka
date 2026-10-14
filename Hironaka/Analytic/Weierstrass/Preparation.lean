/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Weierstrass.Exponents
public import Hironaka.Analytic.Weierstrass.Axis
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Hironaka.Analytic.ConvSeries.Units
import Hironaka.Analytic.Weierstrass.AdicComplete
import Hironaka.Analytic.Weierstrass.Division
import Hironaka.Analytic.Weierstrass.Normalize
import Hironaka.Analytic.Weierstrass.Poly
import Hironaka.Analytic.Weierstrass.Regular
import Hironaka.Analytic.Weierstrass.Tail
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Convergent Weierstrass preparation

The Weierstrass preparation theorem for convergent power series [GR65, Chapter II, §B], in the
form Bierstone and Milman quote it [BM88, proof of Theorem 4.4, p. 24]: a convergent `g`,
`x_0`-regular of order `d`, is `u · (x_0^d + ∑_{j<d} c_j x_0^{d-1-j})` with `u` a convergent unit
and convergent `c_j` in the tail variables vanishing at `0`, uniquely. Divide `x_0^d` by `g`
(`Division.lean`): `x_0^d = q g + r` with `r` of `x_0`-degree `< d`. Mathlib's formal argument
(`IsWeierstrassDivision.isUnit_of_map_ne_zero`) shows `q` is a unit; its inverse `u` is
convergent (`Hironaka/Analytic/ConvSeries/Units.lean`), and `g = u (x_0^d - r)` where
`x_0^d - r` is the Weierstrass polynomial with coefficients
`c_j = -(x_0^{d-1-j}-coefficient of r)`, convergent (`Tail.lean`) and vanishing at `0` (restrict
`x_0^d = q g + r` to the axis: `axis r = x_0^d (1 - axis q · e)` has no terms below degree `d`).
Uniqueness: a datum `g = u' P'` with `P'` a Weierstrass polynomial whose coefficients vanish at
`0` is a Weierstrass factorization in Mathlib's sense (`u'` is a unit since its constant term is
the `x_0^d`-coefficient of `g`), and `IsWeierstrassFactorization.elim` applies.

This is the local form behind the coherence of the structure sheaf of an analytic space
(`Hironaka/AnalyticSpace/Oka`); `FunctionLevel.lean` turns it into a statement about analytic
functions on a product polydisc.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

/-- Restricting `x_0^d = q g + r` to the axis: `r` has no pure `x_0`-terms below degree `d`. -/
theorem coeff_single_eq_zero_of_X_pow_eq {g q r : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hlow : ∀ k < d, coeff (Finsupp.single 0 k) g = 0) (hXq : X 0 ^ d = q * g + r) {k : ℕ}
    (hk : k < d) : coeff (Finsupp.single 0 k) r = 0 := by
  have h1 : axis r = X 0 ^ d * (1 - axis q * axis (wQ d g)) := by
    have h2 := congrArg axis hXq
    rw [axis_X_zero_pow, axis_add, axis_mul, axis_eq_X_pow_mul hlow] at h2
    linear_combination (-1 : MvPowerSeries (Fin 1) K) * h2
  rw [← coeff_single_axis, h1, X_pow_eq, coeff_monomial_mul, ite_eq_right]
  rw [Finsupp.single_le_iff, Finsupp.single_eq_same]
  omega

/-- The restriction to the axis of a Weierstrass polynomial with coefficients vanishing at `0` is
`x_0^d`. -/
theorem axis_weierstrassPoly {d : ℕ} {c : Fin d → MvPowerSeries (Fin m) K}
    (hc : ∀ j, constantCoeff (c j) = 0) : axis (weierstrassPoly d c) = X 0 ^ d := by
  unfold weierstrassPoly
  rw [← axisHom_apply, map_add, map_pow, map_sum]
  simp only [map_mul, map_pow, axisHom_apply, axis_liftTail, axis_X_zero, hc, map_zero, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- If `g = u' P'` with `P'` a Weierstrass polynomial whose coefficients vanish at `0`, the
`x_0^d`-coefficient of `g` is the constant term of `u'`. -/
theorem coeff_single_of_mul_weierstrassPoly {g u' : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    {c' : Fin d → MvPowerSeries (Fin m) K} (hc' : ∀ j, constantCoeff (c' j) = 0)
    (hg : g = u' * weierstrassPoly d c') : coeff (Finsupp.single 0 d) g = constantCoeff u' := by
  rw [← coeff_single_axis, hg, axis_mul, axis_weierstrassPoly hc', X_pow_eq, coeff_mul_monomial,
    ite_eq_left le_rfl, tsub_self, mul_one, coeff_zero_eq_constantCoeff_apply, constantCoeff_axis]

/-- A factorization `g = u P` with `P` a Weierstrass polynomial with coefficients vanishing at `0`
and `u(0) ≠ 0` is a Weierstrass factorization over the tail ring. -/
theorem isWeierstrassFactorization_of_eq {g u : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    {c : Fin d → MvPowerSeries (Fin m) K} (hc : ∀ j, constantCoeff (c j) = 0)
    (hu : constantCoeff u ≠ 0) (hg : g = u * weierstrassPoly d c) :
    (splitFirst K m g).IsWeierstrassFactorization (weierstrassPolynomial d c) (splitFirst K m u) :=
  ⟨isDistinguishedAt_weierstrassPolynomial d c hc,
    (MvPowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hu)).map (splitFirst K m),
    by rw [hg, map_mul, splitFirst_weierstrassPoly, mul_comm]⟩

/-- Convergent Weierstrass preparation: `g = u · (x_0^d + ∑_{j<d} c_j x_0^{d-1-j})` with `u` a
convergent unit and convergent `c_j` vanishing at `0`, uniquely [GR65, Chapter II, §B]; the form
quoted in [BM88, proof of Theorem 4.4, p. 24]. -/
theorem exists_unique_weierstrassPreparation {g : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hg : g ∈ Conv K (m + 1)) (hreg : IsRegularIn g d) :
    ∃ (u : MvPowerSeries (Fin (m + 1)) K) (c : Fin d → MvPowerSeries (Fin m) K),
      u ∈ Conv K (m + 1) ∧ constantCoeff u ≠ 0 ∧ (∀ j, c j ∈ Conv K m ∧ constantCoeff (c j) = 0) ∧
      g = u * weierstrassPoly d c ∧
      ∀ (u' : MvPowerSeries (Fin (m + 1)) K) (c' : Fin d → MvPowerSeries (Fin m) K),
        (∀ j, constantCoeff (c' j) = 0) → g = u' * weierstrassPoly d c' → u' = u ∧ c' = c := by
  have hg' := map_residue_ne_zero_of_isRegularIn hreg
  obtain ⟨hlow, hd⟩ := (isRegularIn_iff g d).mp hreg
  obtain ⟨q, r, hqConv, hrConv, hrdeg, hXq, -⟩ :=
    exists_unique_weierstrassDivision (pow_mem (X_mem_conv 0) d) hg hreg
  have H := isWeierstrassDivision_of_eq hreg hrdeg hXq
  rw [map_pow, splitFirst_X_zero] at H
  have hq_unit : IsUnit (splitFirst K m q) := by
    have H' : (PowerSeries.X ^ ((splitFirst K m g).map
        (IsLocalRing.residue (MvPowerSeries (Fin m) K))).order.toNat).IsWeierstrassDivision
        (splitFirst K m g) (splitFirst K m q) (PowerSeries.trunc d (splitFirst K m r)) := by
      rw [toNat_order_map_residue hreg]
      exact H
    exact PowerSeries.IsWeierstrassDivision.isUnit_of_map_ne_zero hg' H'
  have hq0 : constantCoeff q ≠ 0 := by
    have hqu : IsUnit q := by
      have h1 := hq_unit.map (splitFirst K m).symm
      rwa [AlgEquiv.symm_apply_apply] at h1
    exact isUnit_iff_ne_zero.mp (MvPowerSeries.isUnit_iff_constantCoeff.mp hqu)
  obtain ⟨v, hv⟩ := (isUnit_iff_constantCoeff_ne_zero hqConv).mpr hq0
  obtain ⟨u, huConv, huq⟩ : ∃ u ∈ Conv K (m + 1), u * q = 1 := by
    refine ⟨((v⁻¹ : (Conv K (m + 1))ˣ) : Conv K (m + 1)), Subtype.mem _, ?_⟩
    have h1 := v.inv_mul
    rw [hv] at h1
    exact congrArg Subtype.val h1
  have hu0 : constantCoeff u ≠ 0 := by
    intro h0
    have h1 := congrArg constantCoeff huq
    rw [map_mul, h0, zero_mul, map_one] at h1
    exact zero_ne_one h1
  set c : Fin d → MvPowerSeries (Fin m) K :=
    fun j => -(PowerSeries.coeff (d - 1 - j) (splitFirst K m r)) with hc
  have hP : X 0 ^ d - r = weierstrassPoly d c := X_pow_sub_eq_weierstrassPoly hrdeg
  have hc0 : ∀ j, constantCoeff (c j) = 0 := fun j => by
    rw [hc]
    beta_reduce
    rw [map_neg, constantCoeff_coeff_splitFirst,
      coeff_single_eq_zero_of_X_pow_eq hlow hXq (by omega), neg_zero]
  have hgu : g = u * weierstrassPoly d c := by
    rw [← hP]
    calc g = (u * q) * g := by rw [huq, one_mul]
      _ = u * (X 0 ^ d - r) := by rw [mul_assoc, hXq, add_sub_cancel_right]
  refine ⟨u, c, huConv, hu0, fun j => ⟨neg_mem (coeff_splitFirst_mem_conv hrConv _), hc0 j⟩, hgu,
    fun u' c' hc' hgu' => ?_⟩
  have hu'0 : constantCoeff u' ≠ 0 := by
    rw [← coeff_single_of_mul_weierstrassPoly hc' hgu']; exact hd
  obtain ⟨hPP, huu⟩ := (isWeierstrassFactorization_of_eq hc' hu'0 hgu').elim
    (isWeierstrassFactorization_of_eq hc0 hu0 hgu)
  refine ⟨(splitFirst K m).injective huu, funext fun j => ?_⟩
  rw [← coeff_weierstrassPolynomial_rev d c' j, hPP, coeff_weierstrassPolynomial_rev]

end Analytic
