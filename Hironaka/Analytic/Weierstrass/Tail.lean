/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
public import Hironaka.Analytic.Weierstrass.Basic
import Hironaka.Analytic.Weierstrass.Poly
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Coefficient slices in the tail variables

The `k`-th `x_0`-coefficient of a series in `x_0, …, x_m` (under `splitFirst`) is a series in the
tail variables whose majorant norm at the tail radii is at most `ρ_0^{-k}` times the norm of the
whole series: the monomial `x'^x` of the slice comes from `x_0^k x'^x`, of weight `ρ_0^k` times
larger. Hence the coefficients of a convergent series are convergent (needed for the `c_j` of the
preparation theorem). Conversely, a tail series lifted by `liftTail` has the same norm at any
radius vector extending the tail radii. Not in the sources as such: these are estimates of the
majorant-norm calculus of [GR71, Kapitel I].

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

/-- The `k`-th `x_0`-coefficient of `r` has tail norm at most `ρ_0^{-k} ‖r‖_ρ`. -/
theorem convNorm_coeff_splitFirst_le (ρ : Radius (m + 1)) (r : MvPowerSeries (Fin (m + 1)) K)
    (k : ℕ) :
    ConvNorm (fun j => ρ j.succ) (PowerSeries.coeff k (splitFirst K m r)) ≤
      ((ρ 0)⁻¹ ^ k : ℝ≥0) * ConvNorm ρ r := by
  have key : ∀ x : Fin m →₀ ℕ,
      monomialEval (fun j => ρ j.succ) x = (ρ 0)⁻¹ ^ k * monomialEval ρ (Finsupp.cons k x) :=
      fun x => by
    rw [monomialEval_cons, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (ρ.pos 0).ne', one_pow, one_mul]
    rfl
  unfold ConvNorm
  calc ∑' x, ‖coeff x (PowerSeries.coeff k (splitFirst K m r))‖ₑ *
        (monomialEval (fun j => ρ j.succ) x : ℝ≥0∞)
      = ((ρ 0)⁻¹ ^ k : ℝ≥0) * ∑' x : Fin m →₀ ℕ,
          (fun μ => ‖coeff μ r‖ₑ * (monomialEval ρ μ : ℝ≥0∞)) (Finsupp.cons k x) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun x => ?_
        beta_reduce
        rw [MvPowerSeries.coeff_coeff_finSuccEquiv, key x, ENNReal.coe_mul]
        ring
    _ ≤ _ := mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective (cons_injective k)
          (fun μ => ‖coeff μ r‖ₑ * (monomialEval ρ μ : ℝ≥0∞)))

/-- The `x_0`-coefficients of a convergent series are convergent. -/
theorem coeff_splitFirst_mem_conv {r : MvPowerSeries (Fin (m + 1)) K} (hr : r ∈ Conv K (m + 1))
    (k : ℕ) : PowerSeries.coeff k (splitFirst K m r) ∈ Conv K m := by
  obtain ⟨ρ, hρ⟩ := hr
  exact ⟨⟨fun j => ρ j.succ, fun j => ρ.pos j.succ⟩,
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hρ)
      (convNorm_coeff_splitFirst_le ρ r k)⟩

/-- A lifted tail series has the norm of the tail series: `‖liftTail a‖_ρ = ‖a‖_{ρ'}`. -/
theorem convNorm_liftTail (ρ : Fin (m + 1) → ℝ≥0) (a : MvPowerSeries (Fin m) K) :
    ConvNorm ρ (liftTail a) = ConvNorm (fun j => ρ j.succ) a := by
  unfold ConvNorm
  refine (Function.Injective.tsum_eq (f := fun μ : Fin (m + 1) →₀ ℕ =>
    ‖coeff μ (liftTail a)‖ₑ * (monomialEval ρ μ : ℝ≥0∞)) (cons_injective 0) ?_).symm.trans
    (tsum_congr fun x => ?_)
  · intro μ hμ
    by_contra hμ'
    apply hμ
    have h0 : μ 0 ≠ 0 := fun h => hμ' ⟨μ.tail, by
      beta_reduce
      rw [← h, Finsupp.cons_tail]⟩
    have : coeff μ (liftTail a : MvPowerSeries (Fin (m + 1)) K) = 0 := by
      rw [← Finsupp.cons_tail μ, coeff_cons_liftTail, ite_eq_right h0]
    simp [this]
  · rw [coeff_cons_liftTail, ite_eq_left rfl, monomialEval_cons, pow_zero, one_mul]
    rfl

theorem liftTail_mem_conv {a : MvPowerSeries (Fin m) K} (ha : a ∈ Conv K m) :
    (liftTail a : MvPowerSeries (Fin (m + 1)) K) ∈ Conv K (m + 1) := by
  obtain ⟨ρ, hρ⟩ := ha
  refine ⟨⟨Fin.cons 1 ρ, fun k => ?_⟩, ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) k
    · exact one_pos
    · exact ρ.pos j
  · change ConvNorm (Fin.cons 1 ρ) (liftTail a) ≠ ⊤
    rw [convNorm_liftTail]
    have : (fun j : Fin m => (Fin.cons (1 : ℝ≥0) ⇑ρ : Fin (m + 1) → ℝ≥0) j.succ) = ⇑ρ :=
      funext fun j => Fin.cons_succ _ _ _
    rw [this]
    exact hρ

end Analytic
