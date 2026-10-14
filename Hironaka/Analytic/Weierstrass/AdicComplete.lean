/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The formal power series ring is complete for its maximal ideal

Mathlib's formal Weierstrass division and preparation (`PowerSeries.exists_isWeierstrassDivision`,
`PowerSeries.exists_isWeierstrassFactorization`) are stated over a coefficient ring `A` with
`IsAdicComplete (maximalIdeal A) A`. This module supplies that instance for the tail ring
`A = MvPowerSeries (Fin m) K`.

The maximal ideal `𝔪` consists of the series with zero constant term, and `f ∈ 𝔪^n` iff every
coefficient of `f` of total degree `< n` vanishes: one direction by induction on the product
structure of `𝔪^n` (`Submodule.pow_induction_on_left'`), the other by writing a series without
constant term as `∑_i x_i · D_i f`, where `D_i f` collects the monomials whose least variable is
`x_i`, and inducting on `n`. Hausdorffness (`⋂ 𝔪^n = 0`) and precompleteness (a coherent sequence
`f_n` mod `𝔪^n` has the limit whose `ν`-coefficient is that of `f_{|ν|+1}`) are then read off
coefficientwise. Not in the sources, which quote the formal Weierstrass theorems as classical.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

local notation "𝔪" => IsLocalRing.maximalIdeal (MvPowerSeries (Fin m) K)

/-- The maximal ideal of the formal power series ring: zero constant term. -/
theorem mem_maximalIdeal_iff (f : MvPowerSeries (Fin m) K) :
    f ∈ 𝔪 ↔ constantCoeff f = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not]

theorem X_mem_maximalIdeal (i : Fin m) : (X i : MvPowerSeries (Fin m) K) ∈ 𝔪 :=
  (mem_maximalIdeal_iff _).mpr (constantCoeff_X i)

/-- Elements of `𝔪^n` have no coefficients of total degree `< n`. -/
theorem coeff_eq_zero_of_mem_maximalIdeal_pow {n : ℕ} {f : MvPowerSeries (Fin m) K}
    (hf : f ∈ 𝔪 ^ n) (d : Fin m →₀ ℕ) (hd : Finsupp.degree d < n) : coeff d f = 0 := by
  classical
  revert d
  refine Submodule.pow_induction_on_left' 𝔪
    (C := fun n x _ => ∀ d : Fin m →₀ ℕ, Finsupp.degree d < n → coeff d x = 0) ?_ ?_ ?_ hf
  · intro r d hd
    exact absurd hd (Nat.not_lt_zero _)
  · intro x y i _ _ hx hy d hd
    rw [map_add, hx d hd, hy d hd, add_zero]
  · intro a ha i x _ hx d hd
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1 = 0
    · rw [h1, coeff_zero_eq_constantCoeff_apply, (mem_maximalIdeal_iff a).mp ha, zero_mul]
    · have hdeg : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree d := by
        rw [← map_add, hp]
      have h1' : Finsupp.degree p.1 ≠ 0 := fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h)
      rw [hx p.2 (by omega), mul_zero]

/-- The monomials of `f` whose least variable is `x_i`, divided by `x_i`. -/
noncomputable def leastVarShift (i : Fin m) (f : MvPowerSeries (Fin m) K) :
    MvPowerSeries (Fin m) K :=
  fun ν => if ∀ j < i, ν j = 0 then coeff (ν + Finsupp.single i 1) f else 0

theorem coeff_leastVarShift (i : Fin m) (f : MvPowerSeries (Fin m) K) (ν : Fin m →₀ ℕ) :
    coeff ν (leastVarShift i f) =
      if ∀ j < i, ν j = 0 then coeff (ν + Finsupp.single i 1) f else 0 := rfl

/-- A series without constant term is `∑_i x_i · D_i f`, grouping each monomial under its least
variable. -/
theorem sum_X_mul_leastVarShift {f : MvPowerSeries (Fin m) K} (hf : constantCoeff f = 0) :
    ∑ i, X i * leastVarShift i f = f := by
  classical
  ext μ
  rw [map_sum]
  have hterm : ∀ i, coeff μ (X i * leastVarShift i f) =
      if Finsupp.single i 1 ≤ μ then coeff (μ - Finsupp.single i 1) (leastVarShift i f)
      else 0 := fun i => by
    rw [X_def, coeff_monomial_mul]
    split_ifs <;> simp
  simp_rw [hterm]
  by_cases hμ : μ = 0
  · subst hμ
    rw [← coeff_zero_eq_constantCoeff_apply] at hf
    rw [hf]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    rw [Finsupp.single_le_iff]
    simp
  · have hne : μ.support.Nonempty := Finsupp.support_nonempty_iff.mpr hμ
    set i₀ := μ.support.min' hne with hi₀
    have hi₀mem : i₀ ∈ μ.support := Finset.min'_mem _ hne
    have hlt : ∀ j < i₀, μ j = 0 := fun j hj => by
      by_contra h
      exact absurd (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr h)) (not_le.mpr hj)
    have hμi₀ : Finsupp.single i₀ 1 ≤ μ :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi₀mem))
    rw [Finset.sum_eq_single i₀]
    · rw [ite_eq_left hμi₀, coeff_leastVarShift, ite_eq_left, tsub_add_cancel_of_le hμi₀]
      intro j hj
      rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hj.ne, hlt j hj, tsub_zero]
    · intro i _ hi
      rcases lt_or_gt_of_ne hi with h | h
      · rw [ite_eq_right]
        rw [Finsupp.single_le_iff, hlt i h]
        exact Nat.not_succ_le_zero 0
      · split_ifs with hle
        · rw [coeff_leastVarShift, ite_eq_right]
          intro hall
          have := hall i₀ h
          rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne h.ne, tsub_zero] at this
          exact Finsupp.mem_support_iff.mp hi₀mem this
        · rfl
    · intro h
      exact absurd (Finset.mem_univ i₀) h

/-- A series with no coefficients of total degree `< n` lies in `𝔪^n`. -/
theorem mem_maximalIdeal_pow_of_coeff (n : ℕ) {f : MvPowerSeries (Fin m) K}
    (hf : ∀ d : Fin m →₀ ℕ, Finsupp.degree d < n → coeff d f = 0) : f ∈ 𝔪 ^ n := by
  induction n generalizing f with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    have h0 : constantCoeff f = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hf 0 (by simp)
    rw [← sum_X_mul_leastVarShift h0, pow_succ']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (X_mem_maximalIdeal i) (ih ?_)
    intro d hd
    rw [coeff_leastVarShift]
    split_ifs
    · apply hf
      rw [map_add, Finsupp.degree_single]
      omega
    · rfl

/-- The coefficientwise description of `𝔪^n`: no coefficients of total degree `< n`. -/
theorem mem_maximalIdeal_pow_iff (n : ℕ) (f : MvPowerSeries (Fin m) K) :
    f ∈ 𝔪 ^ n ↔ ∀ d : Fin m →₀ ℕ, Finsupp.degree d < n → coeff d f = 0 :=
  ⟨fun hf => coeff_eq_zero_of_mem_maximalIdeal_pow hf, mem_maximalIdeal_pow_of_coeff n⟩

theorem maximalIdeal_pow_smul_top (n : ℕ) :
    (𝔪 ^ n • (⊤ : Submodule (MvPowerSeries (Fin m) K) (MvPowerSeries (Fin m) K))) = 𝔪 ^ n := by
  simp

/-- `⋂_n 𝔪^n = 0`: the topology of the maximal ideal is Hausdorff. -/
instance isHausdorff_maximalIdeal : IsHausdorff 𝔪 (MvPowerSeries (Fin m) K) := by
  refine ⟨fun x hx => ?_⟩
  ext d
  have h := SModEq.zero.mp (hx (Finsupp.degree d + 1))
  rw [maximalIdeal_pow_smul_top] at h
  exact coeff_eq_zero_of_mem_maximalIdeal_pow h d (Nat.lt_succ_self _)

/-- The limit of a sequence coherent modulo the powers of `𝔪`: the `ν`-coefficient of the
`(|ν| + 1)`-st term. -/
noncomputable def adicLimit (f : ℕ → MvPowerSeries (Fin m) K) : MvPowerSeries (Fin m) K :=
  fun d => coeff d (f (Finsupp.degree d + 1))

theorem coeff_adicLimit (f : ℕ → MvPowerSeries (Fin m) K) (d : Fin m →₀ ℕ) :
    coeff d (adicLimit f) = coeff d (f (Finsupp.degree d + 1)) := rfl

/-- A sequence coherent modulo `𝔪^n` has a limit; its `ν`-coefficient is the `ν`-coefficient of
the `(|ν| + 1)`-st term. -/
instance isPrecomplete_maximalIdeal : IsPrecomplete 𝔪 (MvPowerSeries (Fin m) K) := by
  refine ⟨fun f hf => ⟨adicLimit f, fun n => ?_⟩⟩
  rw [SModEq.sub_mem, maximalIdeal_pow_smul_top]
  refine mem_maximalIdeal_pow_of_coeff n fun d hd => ?_
  rw [map_sub, sub_eq_zero, coeff_adicLimit]
  rcases le_total n (Finsupp.degree d + 1) with h | h
  · have h' := hf h
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_top] at h'
    have := coeff_eq_zero_of_mem_maximalIdeal_pow h' d hd
    rwa [map_sub, sub_eq_zero] at this
  · have h' := hf h
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_top] at h'
    have := coeff_eq_zero_of_mem_maximalIdeal_pow h' d (Nat.lt_succ_self _)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

variable (K) in
/-- `MvPowerSeries (Fin m) K` is complete for its maximal ideal, the hypothesis of Mathlib's
formal Weierstrass theorems. -/
instance isAdicComplete_maximalIdeal (m : ℕ) :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin m) K))
      (MvPowerSeries (Fin m) K) := ⟨⟩

end Analytic
