/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Weierstrass.Basic
public import Hironaka.Analytic.ConvSeries.ConvNorm
import Hironaka.Analytic.Weierstrass.Exponents
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Restriction to the distinguished axis

The regularity condition of the Weierstrass theorems, `f(0, …, 0, x_m) ∼ x_m^d` in the printed
form [BM88, proof of Theorem 4.4, p. 24], concerns the restriction of the series to the
distinguished axis. This module provides that restriction, `axis f := f(x_0, 0, …, 0)` as a series
in one variable, as a ring homomorphism `axisHom` (the antidiagonal of a pure power `x_0^k`
consists of pure powers, `Finsupp.antidiagonal_single`), together with its values on the lifts
`liftFirst` (inverse: `axis (liftFirst e) = e`) and `liftTail` (the constant term), and the
majorant-norm comparisons `‖axis f‖_{ρ_0} ≤ ‖f‖_ρ`, `‖liftFirst e‖_ρ = ‖e‖_{ρ_0}` that keep both
operations inside the convergent series.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

/-- Restriction of a series in `x_0, …, x_m` to the `x_0`-axis: `f(x_0, 0, …, 0)`. -/
noncomputable def axis (f : MvPowerSeries (Fin (m + 1)) K) : MvPowerSeries (Fin 1) K :=
  fun ν => coeff (Finsupp.single 0 (ν 0)) f

theorem coeff_axis (f : MvPowerSeries (Fin (m + 1)) K) (ν : Fin 1 →₀ ℕ) :
    coeff ν (axis f) = coeff (Finsupp.single 0 (ν 0)) f := rfl

theorem coeff_single_axis (f : MvPowerSeries (Fin (m + 1)) K) (k : ℕ) :
    coeff (Finsupp.single (0 : Fin 1) k) (axis f) = coeff (Finsupp.single 0 k) f := by
  rw [coeff_axis, Finsupp.single_eq_same]

theorem constantCoeff_axis (f : MvPowerSeries (Fin (m + 1)) K) :
    constantCoeff (axis f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_axis, Finsupp.zero_apply, Finsupp.single_zero,
    coeff_zero_eq_constantCoeff_apply]

theorem axis_zero : axis (0 : MvPowerSeries (Fin (m + 1)) K) = 0 := by
  ext ν; simp [coeff_axis]

theorem axis_add (f g : MvPowerSeries (Fin (m + 1)) K) : axis (f + g) = axis f + axis g := by
  ext ν; simp only [coeff_axis, map_add]

theorem axis_one : axis (1 : MvPowerSeries (Fin (m + 1)) K) = 1 := by
  classical
  ext ν
  rw [coeff_axis, coeff_one, coeff_one]
  have : (Finsupp.single (0 : Fin (m + 1)) (ν 0) = 0) ↔ ν = 0 := by
    rw [Finsupp.single_eq_zero, Fin1.eq_zero_iff]
  simp only [this]

/-- Restriction to the axis is multiplicative: the antidiagonal of `x_0^k` consists of pairs of
pure powers. -/
theorem axis_mul (f g : MvPowerSeries (Fin (m + 1)) K) : axis (f * g) = axis f * axis g := by
  classical
  ext ν
  have hν : ν = Finsupp.single 0 (ν 0) := Fin1.eq_single ν
  rw [coeff_axis, coeff_mul, coeff_mul, hν, Finsupp.single_eq_same, Finsupp.antidiagonal_single,
    Finsupp.antidiagonal_single, Finset.sum_map, Finset.sum_map]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Function.Embedding.coe_prodMap, Prod.map_fst, Prod.map_snd,
    Function.Embedding.coeFn_mk, coeff_single_axis]

variable (K) in
/-- Restriction to the `x_0`-axis as a ring homomorphism. -/
noncomputable def axisHom : MvPowerSeries (Fin (m + 1)) K →+* MvPowerSeries (Fin 1) K where
  toFun := axis
  map_one' := axis_one
  map_mul' := axis_mul
  map_zero' := axis_zero
  map_add' := axis_add

theorem axisHom_apply (f : MvPowerSeries (Fin (m + 1)) K) : axisHom K f = axis f := rfl

theorem axis_X_zero : axis (X 0 : MvPowerSeries (Fin (m + 1)) K) = X 0 := by
  classical
  ext ν
  rw [coeff_axis, coeff_X, coeff_X]
  have : (Finsupp.single (0 : Fin (m + 1)) (ν 0) = Finsupp.single 0 1) ↔
      ν = Finsupp.single 0 1 := by
    rw [(Finsupp.single_injective 0).eq_iff]
    constructor
    · intro h; rw [Fin1.eq_single ν, h]
    · intro h; rw [h, Finsupp.single_eq_same]
  simp only [this]

theorem axis_X_zero_pow (d : ℕ) : axis (X 0 ^ d : MvPowerSeries (Fin (m + 1)) K) = X 0 ^ d := by
  rw [← axisHom_apply, map_pow, axisHom_apply, axis_X_zero]

theorem axis_C (c : K) : axis (C c : MvPowerSeries (Fin (m + 1)) K) = C c := by
  classical
  ext ν
  rw [coeff_axis, coeff_C, coeff_C]
  have : (Finsupp.single (0 : Fin (m + 1)) (ν 0) = 0) ↔ ν = 0 := by
    rw [Finsupp.single_eq_zero, Fin1.eq_zero_iff]
  simp only [this]

/-! ### The lift of a one-variable series -/

theorem coeff_single_liftFirst (e : MvPowerSeries (Fin 1) K) (k : ℕ) :
    coeff (Finsupp.single 0 k) (liftFirst e : MvPowerSeries (Fin (m + 1)) K) =
      coeff (Finsupp.single 0 k) e := by
  have h := coeff_embDomain_rename (embFirst m) e (Finsupp.single 0 k)
  rw [Finsupp.embDomain_single] at h
  exact h

theorem constantCoeff_liftFirst (e : MvPowerSeries (Fin 1) K) :
    constantCoeff (liftFirst e : MvPowerSeries (Fin (m + 1)) K) = constantCoeff e := by
  have h := coeff_single_liftFirst (m := m) e 0
  rwa [Finsupp.single_zero, Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply,
    coeff_zero_eq_constantCoeff_apply] at h

theorem coeff_liftFirst_of_ne (e : MvPowerSeries (Fin 1) K) {μ : Fin (m + 1) →₀ ℕ}
    (hμ : μ ≠ Finsupp.single 0 (μ 0)) : coeff μ (liftFirst e) = 0 := by
  apply coeff_rename_eq_zero
  rintro ⟨y, hy⟩
  apply hμ
  have hy' : Finsupp.mapDomain (fun _ : Fin 1 => (0 : Fin (m + 1))) y =
      Finsupp.single 0 (y 0) := by
    conv_lhs => rw [Fin1.eq_single y]
    exact Finsupp.mapDomain_single
  rw [← hy, hy', Finsupp.single_eq_same]

theorem axis_liftFirst (e : MvPowerSeries (Fin 1) K) :
    axis (liftFirst e : MvPowerSeries (Fin (m + 1)) K) = e := by
  ext ν
  rw [coeff_axis, coeff_single_liftFirst, ← Fin1.eq_single]

theorem liftFirst_mul (e e' : MvPowerSeries (Fin 1) K) :
    (liftFirst (e * e') : MvPowerSeries (Fin (m + 1)) K) = liftFirst e * liftFirst e' :=
  map_mul _ _ _

theorem liftFirst_one : (liftFirst 1 : MvPowerSeries (Fin (m + 1)) K) = 1 :=
  map_one _

/-- The lift changes no weights: `‖liftFirst e‖_ρ = ‖e‖_{ρ_0}`. -/
theorem convNorm_liftFirst (ρ : Fin (m + 1) → ℝ≥0) (e : MvPowerSeries (Fin 1) K) :
    ConvNorm ρ (liftFirst e) = ConvNorm (fun _ => ρ 0) e := by
  unfold ConvNorm
  refine (Function.Injective.tsum_eq (f := fun μ : Fin (m + 1) →₀ ℕ =>
    ‖coeff μ (liftFirst e)‖ₑ * (monomialEval ρ μ : ℝ≥0∞)) Fin1.single_apply_injective ?_).symm.trans
    (tsum_congr fun ν => ?_)
  · intro μ hμ
    by_contra hμ'
    apply hμ
    have : μ ≠ Finsupp.single 0 (μ 0) := fun h => hμ' ⟨Finsupp.single 0 (μ 0), by
      beta_reduce
      rw [Finsupp.single_eq_same, ← h]⟩
    simp [coeff_liftFirst_of_ne e this]
  · rw [coeff_single_liftFirst, ← Fin1.eq_single, monomialEval_single_pow, monomialEval_fin1]

theorem liftFirst_mem_conv {e : MvPowerSeries (Fin 1) K} (he : e ∈ Conv K 1) :
    (liftFirst e : MvPowerSeries (Fin (m + 1)) K) ∈ Conv K (m + 1) := by
  obtain ⟨r, hr⟩ := he
  refine ⟨⟨fun _ => r 0, fun _ => r.pos 0⟩, ?_⟩
  change ConvNorm (fun _ => r 0) (liftFirst e) ≠ ⊤
  rw [convNorm_liftFirst]
  have : (fun _ : Fin 1 => r 0) = ⇑r := funext fun i => by rw [Subsingleton.elim i 0]
  rw [this]
  exact hr

/-- Restriction to the axis drops terms: `‖axis f‖_{ρ_0} ≤ ‖f‖_ρ`. -/
theorem convNorm_axis_le (ρ : Fin (m + 1) → ℝ≥0) (f : MvPowerSeries (Fin (m + 1)) K) :
    ConvNorm (fun _ => ρ 0) (axis f) ≤ ConvNorm ρ f := by
  unfold ConvNorm
  calc ∑' ν, ‖coeff ν (axis f)‖ₑ * (monomialEval (fun _ => ρ 0) ν : ℝ≥0∞)
      = ∑' ν : Fin 1 →₀ ℕ,
          (fun μ => ‖coeff μ f‖ₑ * (monomialEval ρ μ : ℝ≥0∞)) (Finsupp.single 0 (ν 0)) := by
        refine tsum_congr fun ν => ?_
        beta_reduce
        rw [coeff_axis, monomialEval_fin1, monomialEval_single_pow]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective Fin1.single_apply_injective
          (fun μ => ‖coeff μ f‖ₑ * (monomialEval ρ μ : ℝ≥0∞))

theorem axis_mem_conv {f : MvPowerSeries (Fin (m + 1)) K} (hf : f ∈ Conv K (m + 1)) :
    axis f ∈ Conv K 1 := by
  obtain ⟨ρ, hρ⟩ := hf
  exact ⟨⟨fun _ => ρ 0, fun _ => ρ.pos 0⟩, ne_top_of_le_ne_top hρ (convNorm_axis_le ρ f)⟩

/-! ### The lift of a tail series -/

theorem axis_liftTail (a : MvPowerSeries (Fin m) K) :
    axis (liftTail a : MvPowerSeries (Fin (m + 1)) K) = C (constantCoeff a) := by
  classical
  ext ν
  rw [coeff_axis, coeff_C]
  by_cases h : ν 0 = 0
  · rw [ite_eq_left ((Fin1.eq_zero_iff ν).mpr h), h, Finsupp.single_zero]
    have := coeff_embDomain_rename (Fin.succEmb m) a 0
    rw [Finsupp.embDomain_zero] at this
    exact this.trans (coeff_zero_eq_constantCoeff_apply a)
  · rw [ite_eq_right (fun h' => h ((Fin1.eq_zero_iff ν).mp h'))]
    apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    have h0 : (Finsupp.mapDomain Fin.succ y) 0 = (Finsupp.single (0 : Fin (m + 1)) (ν 0)) 0 :=
      congrArg (fun μ : Fin (m + 1) →₀ ℕ => μ 0) hy
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨j, hj⟩; exact Fin.succ_ne_zero j hj),
      Finsupp.single_eq_same] at h0
    exact h (h0.symm)

theorem constantCoeff_liftTail (a : MvPowerSeries (Fin m) K) :
    constantCoeff (liftTail a : MvPowerSeries (Fin (m + 1)) K) = constantCoeff a := by
  rw [← constantCoeff_axis, axis_liftTail, constantCoeff_C]

end Analytic
