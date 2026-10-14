/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Weierstrass.Basic
public import Hironaka.Analytic.ConvSeries.Banach
public import Mathlib.Analysis.Normed.Operator.Basic
import Hironaka.Analytic.Weierstrass.Exponents
import Mathlib.Tactic.Positivity.Finset

/-!
# The splitting operators `Q`, `R` on the Banach algebras `B_ρ`

For a formal series `F` in `m + 1` variables with distinguished variable `x_0`,
`F = x_0^d · wQ d F + wR d F` where `wR d F` collects the monomials of `x_0`-degree `< d`
(`X_pow_mul_wQ_add_wR`). This module bounds both pieces in the majorant norm:
`‖wR d F‖_ρ ≤ ‖F‖_ρ` (a subseries of a positive series) and `‖wQ d F‖_ρ ≤ ρ_0^{-d} ‖F‖_ρ` (the
monomial `x^ν` of `wQ d F` comes from `x^{ν + d e_0}` of `F`, whose weight is `ρ_0^d` times
larger). Hence `Q = wQ d` and `R = wR d` are continuous linear operators on `B_ρ` with
`‖Q‖ ≤ ρ_0^{-d}`, `‖R‖ ≤ 1`, the estimate behind the contraction step of the Banach-algebra proof
of the Weierstrass division theorem [GR71, Kapitel I].

The module also records the smallness device: if all pure `x_0`-coefficients of `h` vanish,
shrinking the tail radii `ρ_1, …, ρ_m` by a factor `t ≤ 1` (and keeping `ρ_0`) multiplies the
weight of every monomial of `h` by at most `t`, so `‖h‖_{ρ'} ≤ t ‖h‖_ρ` can be made as small as
required.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

/-- The quotient piece: `‖wQ d F‖_ρ ≤ ρ_0^{-d} ‖F‖_ρ`. -/
theorem convNorm_wQ_le (ρ : Radius (m + 1)) (d : ℕ) (F : MvPowerSeries (Fin (m + 1)) K) :
    ConvNorm ρ (wQ d F) ≤ ((ρ 0)⁻¹ ^ d : ℝ≥0) * ConvNorm ρ F := by
  have key : ∀ ν : Fin (m + 1) →₀ ℕ,
      monomialEval ρ ν = (ρ 0)⁻¹ ^ d * monomialEval ρ (ν + Finsupp.single 0 d) := fun ν => by
    rw [monomialEval_add_single_zero, mul_comm, mul_assoc, ← mul_pow, mul_inv_cancel₀ (ρ.pos 0).ne',
      one_pow, mul_one]
  unfold ConvNorm
  calc ∑' ν, ‖coeff ν (wQ d F)‖ₑ * (monomialEval ρ ν : ℝ≥0∞)
      = ((ρ 0)⁻¹ ^ d : ℝ≥0) * ∑' ν,
          (fun μ => ‖coeff μ F‖ₑ * (monomialEval ρ μ : ℝ≥0∞)) (ν + Finsupp.single 0 d) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun ν => ?_
        rw [coeff_wQ, key ν, ENNReal.coe_mul]
        ring
    _ ≤ _ :=
        mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective _)
          (fun μ => ‖coeff μ F‖ₑ * (monomialEval ρ μ : ℝ≥0∞)))

/-- The remainder piece: `‖wR d F‖_ρ ≤ ‖F‖_ρ`. -/
theorem convNorm_wR_le (ρ : Radius (m + 1)) (d : ℕ) (F : MvPowerSeries (Fin (m + 1)) K) :
    ConvNorm ρ (wR d F) ≤ ConvNorm ρ F := by
  unfold ConvNorm
  refine ENNReal.tsum_le_tsum fun ν => mul_le_mul' ?_ le_rfl
  rw [coeff_wR]
  split_ifs
  · exact le_rfl
  · simp

theorem wQ_add (d : ℕ) (F G : MvPowerSeries (Fin (m + 1)) K) :
    wQ d (F + G) = wQ d F + wQ d G := by
  ext ν; simp [coeff_wQ]

theorem wQ_smul (d : ℕ) (c : K) (F : MvPowerSeries (Fin (m + 1)) K) :
    wQ d (c • F) = c • wQ d F := by
  ext ν; simp [coeff_wQ]

theorem wR_add (d : ℕ) (F G : MvPowerSeries (Fin (m + 1)) K) :
    wR d (F + G) = wR d F + wR d G := by
  ext ν; simp only [coeff_wR, map_add]; split_ifs <;> simp

theorem wR_smul (d : ℕ) (c : K) (F : MvPowerSeries (Fin (m + 1)) K) :
    wR d (c • F) = c • wR d F := by
  ext ν; simp only [coeff_wR, coeff_smul]; split_ifs <;> simp

theorem wQ_mem_banachSeries (ρ : Radius (m + 1)) (d : ℕ) (F : BanachSeries K ρ) :
    wQ d (F : MvPowerSeries (Fin (m + 1)) K) ∈ BanachSeries K ρ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top F.2)
    (convNorm_wQ_le ρ d (F : MvPowerSeries (Fin (m + 1)) K))

theorem wR_mem_banachSeries (ρ : Radius (m + 1)) (d : ℕ) (F : BanachSeries K ρ) :
    wR d (F : MvPowerSeries (Fin (m + 1)) K) ∈ BanachSeries K ρ :=
  ne_top_of_le_ne_top F.2 (convNorm_wR_le ρ d (F : MvPowerSeries (Fin (m + 1)) K))

variable (K) in
/-- The quotient operator `Q = wQ d` as a linear map on `B_ρ`. -/
noncomputable def wQLinear (ρ : Radius (m + 1)) (d : ℕ)
    : BanachSeries K ρ →ₗ[K] BanachSeries K ρ where
  toFun F := ⟨wQ d (F : MvPowerSeries (Fin (m + 1)) K), wQ_mem_banachSeries ρ d F⟩
  map_add' F G := Subtype.ext (by simp [wQ_add])
  map_smul' c F := Subtype.ext (by simp [wQ_smul])

variable (K) in
/-- The remainder operator `R = wR d` as a linear map on `B_ρ`. -/
noncomputable def wRLinear (ρ : Radius (m + 1)) (d : ℕ)
    : BanachSeries K ρ →ₗ[K] BanachSeries K ρ where
  toFun F := ⟨wR d (F : MvPowerSeries (Fin (m + 1)) K), wR_mem_banachSeries ρ d F⟩
  map_add' F G := Subtype.ext (by simp [wR_add])
  map_smul' c F := Subtype.ext (by simp [wR_smul])

theorem norm_wQLinear_le (ρ : Radius (m + 1)) (d : ℕ) (F : BanachSeries K ρ) :
    ‖wQLinear K ρ d F‖ ≤ ((ρ 0 : ℝ)⁻¹) ^ d * ‖F‖ := by
  rw [BanachSeries.norm_def, BanachSeries.norm_def]
  change (ConvNorm ρ (wQ d (F : MvPowerSeries (Fin (m + 1)) K))).toReal ≤ _
  have hne : (((ρ 0)⁻¹ ^ d : ℝ≥0) : ℝ≥0∞) * ConvNorm ρ (F : MvPowerSeries (Fin (m + 1)) K) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top F.2
  calc (ConvNorm ρ (wQ d (F : MvPowerSeries (Fin (m + 1)) K))).toReal
      ≤ ((((ρ 0)⁻¹ ^ d : ℝ≥0) : ℝ≥0∞) * ConvNorm ρ (F : MvPowerSeries (Fin (m + 1)) K)).toReal :=
        ENNReal.toReal_mono hne (convNorm_wQ_le ρ d (F : MvPowerSeries (Fin (m + 1)) K))
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_pow, NNReal.coe_inv]

theorem norm_wRLinear_le (ρ : Radius (m + 1)) (d : ℕ) (F : BanachSeries K ρ) :
    ‖wRLinear K ρ d F‖ ≤ 1 * ‖F‖ := by
  rw [BanachSeries.norm_def, BanachSeries.norm_def, one_mul]
  exact ENNReal.toReal_mono F.2 (convNorm_wR_le ρ d (F : MvPowerSeries (Fin (m + 1)) K))

variable (K) in
/-- The operator bounds: `Q` and `R` are continuous linear operators on `B_ρ` with
`‖Q‖ ≤ ρ_0^{-d}` and `‖R‖ ≤ 1` [GR71, Kapitel I]. -/
theorem exists_splitting_clm (ρ : Radius (m + 1)) (d : ℕ) :
    ∃ (Q R : BanachSeries K ρ →L[K] BanachSeries K ρ),
      (∀ F : BanachSeries K ρ, (Q F : MvPowerSeries (Fin (m + 1)) K) = wQ d F) ∧
      (∀ F : BanachSeries K ρ, (R F : MvPowerSeries (Fin (m + 1)) K) = wR d F) ∧
      ‖Q‖ ≤ ((ρ 0 : ℝ)⁻¹) ^ d ∧ ‖R‖ ≤ 1 :=
  ⟨(wQLinear K ρ d).mkContinuous _ (norm_wQLinear_le ρ d),
    (wRLinear K ρ d).mkContinuous 1 (norm_wRLinear_le ρ d), fun _ => rfl, fun _ => rfl,
    LinearMap.mkContinuous_norm_le _ (by positivity) _,
    LinearMap.mkContinuous_norm_le _ zero_le_one _⟩

/-- Scaling the tail radii by `t ≤ 1` scales the norm of a series without pure `x_0`-terms by at
most `t`. -/
theorem convNorm_tailScale_le (ρ : Fin (m + 1) → ℝ≥0) {t : ℝ≥0} (ht : t ≤ 1)
    {h : MvPowerSeries (Fin (m + 1)) K} (h0 : TailVanishes h) :
    ConvNorm (fun k => if k = 0 then ρ 0 else t * ρ k) h ≤ t * ConvNorm ρ h := by
  unfold ConvNorm
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ν => ?_
  by_cases hν : ∀ j, j ≠ 0 → ν j = 0
  · rw [eq_single_zero_of_tail_eq_zero hν, h0 (ν 0)]
    simp
  · push Not at hν
    obtain ⟨j, hj, hνj⟩ := hν
    rw [mul_left_comm, ← ENNReal.coe_mul]
    exact mul_le_mul' le_rfl (ENNReal.coe_le_coe.mpr (monomialEval_tailScale_le ρ ht hj hνj))

/-- The smallness device: a convergent series without pure `x_0`-terms has norm `≤ ε` after
shrinking the tail radii, keeping `ρ_0`. -/
theorem exists_radius_convNorm_le {ρ : Radius (m + 1)} {h : MvPowerSeries (Fin (m + 1)) K}
    (hh : ConvNorm ρ h ≠ ⊤) (h0 : TailVanishes h) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ ρ' : Radius (m + 1), ρ' 0 = ρ 0 ∧ (∀ k, ρ' k ≤ ρ k) ∧ ConvNorm ρ' h ≤ ε := by
  classical
  obtain ⟨t, htpos, ht1, htε⟩ :
      ∃ t : ℝ≥0, 0 < t ∧ t ≤ 1 ∧ (t : ℝ≥0∞) * ConvNorm ρ h ≤ ε := by
    set M : ℝ≥0 := (ConvNorm ρ h).toNNReal with hM
    have hε'top : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    set ε' : ℝ≥0 := (min ε 1).toNNReal with hε'
    have hε'pos : 0 < ε' := ENNReal.toNNReal_pos (lt_min hε zero_lt_one).ne' hε'top
    refine ⟨min 1 (ε' / (M + 1)), lt_min one_pos (div_pos hε'pos (by positivity)),
      min_le_left _ _, ?_⟩
    rw [← ENNReal.coe_toNNReal hh, ← ENNReal.coe_mul]
    calc ((min 1 (ε' / (M + 1)) * M : ℝ≥0) : ℝ≥0∞) ≤ (ε' : ℝ≥0∞) := by
          apply ENNReal.coe_le_coe.mpr
          calc min 1 (ε' / (M + 1)) * M ≤ ε' / (M + 1) * (M + 1) :=
                mul_le_mul' (min_le_right _ _) (le_add_right le_rfl)
            _ = ε' := div_mul_cancel₀ _ (by positivity)
      _ ≤ ε := by rw [hε', ENNReal.coe_toNNReal hε'top]; exact min_le_left _ _
  refine ⟨⟨fun k => if k = 0 then ρ 0 else t * ρ k, fun k => ?_⟩, ?_, ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact ρ.pos 0
    · exact mul_pos htpos (ρ.pos k)
  · dsimp only
    exact ite_eq_left rfl
  · intro k
    dsimp only
    split_ifs with hk
    · rw [hk]
    · exact mul_le_of_le_one_left (zero_le) ht1
  · exact (convNorm_tailScale_le ρ ht1 h0).trans htε

end Analytic
