/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import HironakaExamples.Balanced.PDeriv
import HironakaExamples.MaximalContact.Example11Charts
import HironakaExamples.MaximalContact.Example82
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 11: the `z`-chart and the second blow-up

[Kol07, Example 11] after the blow-up of the origin, on the `z`-chart: `f₁ = x₁² + y₁³z₁ − z₁⁴`
(Kollár writes `x₁² + (y₁³ − z₁³)z₁`), `H₁ = (x₁)`, `H₁' = (x₁ + y₁²z₁)`, `E₁ = (z₁)`. Computed
exactly: `I₁ = (f₁)` has order exactly `2` at the origin, which is its only `ℚ`-point of order
`≥ 2`; `MC(I₁) = D(I₁) = (x₁, y₁²z₁, y₁³ − 4z₁³, z₁⁴)`, so `x₁`, `x₁ + y₁²z₁ ∈ MC(I₁)`; the
restrictions `I₁|_{H₁} = (y₁³z₁ − z₁⁴)` and `I₁|_{H₁'} = (y₁⁴z₁² + y₁³z₁ − z₁⁴)` have the origin as
their only point of order `2`. The second point blow-up on the `z`-chart gives
`f₂ = x₂² + (y₂³ − 1)z₂²`, Kollár's display, whose locus of order `2` is the line
`x₂ = z₂ = 0 = E₂ ∩ H₂`; the trace `I₂|_{H₂} = ((y₂³ − 1)z₂²)` has order `3` at the three points
`y₂³ = 1` and order `2` at the origin.
-/

public section

open MvPolynomial Hironaka.Examples

namespace Hironaka.Examples.Example11Stages

/-- `x = X 0` in `ℚ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 1`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- `z = X 2`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 0` in `ℚ[y, z]`. -/
local notation "yR" => (X 0 : MvPolynomial (Fin 2) ℚ)
/-- `z = X 1` in `ℚ[y, z]`. -/
local notation "zR" => (X 1 : MvPolynomial (Fin 2) ℚ)
/-- The `z`-chart. -/
local notation "σz" => (aeval ![X 0 * X 2, X 1 * X 2, X 2] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- Restriction to `(x = 0)` into `ℚ[y, z]`. -/
local notation "ρH" => (aeval ![0, X 0, X 1] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ)


/-! ### The `z`-chart -/

/-- The `z`-chart of the blow-up of the origin: `σ f = z₁² f₁` with `f₁` Kollár's
`x₁² + (y₁³ − z₁³)z₁`, `σ x = z₁x₁`, `σ(x + y²) = z₁(x₁ + y₁²z₁)`. -/
theorem transform_example11_z :
    σz (x ^ 2 + y ^ 3 - z ^ 6) = z ^ 2 * (x ^ 2 + y ^ 3 * z - z ^ 4) ∧
      σz x = z * x ∧ σz (x + y ^ 2) = z * (x + y ^ 2 * z) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring

/-- `I₁ = (f₁)` has order exactly `2` at the origin (`∂²f₁/∂x₁² = 2`). -/
theorem ord_zero_example11_z :
    Ideal.span {x ^ 2 + y ^ 3 * z - z ^ 4} ≤ Ideal.span {x, y, z} ^ 2 ∧
      ¬ Ideal.span {x ^ 2 + y ^ 3 * z - z ^ 4} ≤ Ideal.span {x, y, z} ^ 3 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · refine Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.pow_mem_pow x_mem_m0 2) ?_) ?_
    · refine mem_pow_of_mem_pow_of_le (k := 3 + 1) (by norm_num) (mul_mem_pow_add ?_ ?_)
      · exact Ideal.pow_mem_pow y_mem_m0 3
      · rw [pow_one]; exact z_mem_m0
    · exact mem_pow_of_mem_pow_of_le (by norm_num) (Ideal.pow_mem_pow z_mem_m0 4)
  · have := eval_pderiv_pderiv_eq_zero_of_mem_m3_zero_cube
      ((Ideal.span_singleton_le_iff_mem _).mp h) 0 0
    simp at this

/-- The origin is the only `ℚ`-point of order `≥ 2`: `∂f₁/∂x₁ = 2x₁`, `∂f₁/∂y₁ = 3y₁²z₁`,
`∂f₁/∂z₁ = y₁³ − 4z₁³` vanish together only at `0`. -/
theorem cosupport_example11_z (a b c : ℚ)
    (h : Ideal.span {x ^ 2 + y ^ 3 * z - z ^ 4} ≤ Ideal.span {x - C a, y - C b, z - C c} ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨-, hd⟩ := vanish_of_mem_m3_sq a b c ((Ideal.span_singleton_le_iff_mem _).mp h)
  have ha : a = 0 := by simpa using hd 0
  have h1 : c = 0 ∨ b = 0 := by simpa using hd 1
  have h2 : b ^ 3 - 4 * c ^ 3 = 0 := by simpa using hd 2
  rcases h1 with hc | hb
  · subst hc
    have hb : b = 0 := by
      have : b ^ 3 = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    exact ⟨ha, hb, rfl⟩
  · subst hb
    have hc : c = 0 := by
      have : c ^ 3 = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    exact ⟨ha, rfl, hc⟩

/-- `MC(I₁) = D(f₁) = (x₁, y₁²z₁, y₁³ − 4z₁³, z₁⁴)`: the partials are `2x₁`, `3y₁²z₁`, `y₁³ − 4z₁³`,
and `3z₁⁴ = f₁ − x₁·x₁ − z₁(y₁³ − 4z₁³)`. -/
theorem derivative_example11_z :
    Ideal.derivative ℚ (Ideal.span {x ^ 2 + y ^ 3 * z - z ^ 4}) =
      Ideal.span {x, y ^ 2 * z, y ^ 3 - 4 * z ^ 3, z ^ 4} := by
  have h0 : pderiv 0 (x ^ 2 + y ^ 3 * z - z ^ 4) = C 2 * x := by simp [map_ofNat]
  have h1 : pderiv 1 (x ^ 2 + y ^ 3 * z - z ^ 4) = C 3 * (y ^ 2 * z) := by simp [map_ofNat]; ring
  have h2 : pderiv 2 (x ^ 2 + y ^ 3 * z - z ^ 4) = y ^ 3 - 4 * z ^ 3 := by simp
  rw [derivative_span_pderiv]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (hg | hg)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      have : x ^ 2 + y ^ 3 * z - z ^ 4 = x * x + z * (y ^ 3 - 4 * z ^ 3) + 3 * z ^ 4 := by ring
      rw [this]
      refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hg
      obtain ⟨i, g', rfl, rfl⟩ := hg
      match i with
      | 0 => rw [h0]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      | 1 => rw [h1]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      | 2 => rw [h2]; exact Ideal.subset_span (by simp)
  · set S : Set (MvPolynomial (Fin 3) ℚ) :=
      {x ^ 2 + y ^ 3 * z - z ^ 4} ∪ ⋃ i, pderiv i '' {x ^ 2 + y ^ 3 * z - z ^ 4} with hS
    have hf : x ^ 2 + y ^ 3 * z - z ^ 4 ∈ Ideal.span S := Ideal.subset_span (Or.inl rfl)
    have hmem : ∀ i : Fin 3, pderiv i (x ^ 2 + y ^ 3 * z - z ^ 4) ∈ Ideal.span S := fun i =>
      Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ rfl⟩))
    have hx : x ∈ Ideal.span S := by
      have h := hmem 0
      rw [h0] at h
      exact mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero h
    have hyz : y ^ 2 * z ∈ Ideal.span S := by
      have h := hmem 1
      rw [h1] at h
      exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero h
    have hyz3 : y ^ 3 - 4 * z ^ 3 ∈ Ideal.span S := by
      have h := hmem 2
      rwa [h2] at h
    have hz4 : z ^ 4 ∈ Ideal.span S := by
      have : C 3 * z ^ 4 = (x ^ 2 + y ^ 3 * z - z ^ 4) - x * x - z * (y ^ 3 - 4 * z ^ 3) := by
        simp only [map_ofNat]; ring
      exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero (this ▸ Ideal.sub_mem _
        (Ideal.sub_mem _ hf (Ideal.mul_mem_left _ _ hx)) (Ideal.mul_mem_left _ _ hyz3))
    rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hx
    · exact hyz
    · exact hyz3
    · exact hz4

/-- `x₁ ∈ MC(I₁)`: the strict transform `H₁` is of maximal contact. -/
theorem mem_derivative_example11_z_H :
    x ∈ Ideal.derivative ℚ (Ideal.span {x ^ 2 + y ^ 3 * z - z ^ 4}) := by
  rw [derivative_example11_z]
  exact Ideal.subset_span (by simp)

/-- `x₁ + y₁²z₁ ∈ MC(I₁)`: the strict transform `H₁'` is of maximal contact. -/
theorem mem_derivative_example11_z_H' :
    x + y ^ 2 * z ∈ Ideal.derivative ℚ (Ideal.span {x ^ 2 + y ^ 3 * z - z ^ 4}) := by
  rw [derivative_example11_z]
  exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))

/-- `I₁|_{H₁} = (y₁³z₁ − z₁⁴)`. -/
theorem map_example11_z_H :
    (Ideal.span {x ^ 2 + y ^ 3 * z - z ^ 4}).map ρH = Ideal.span {yR ^ 3 * zR - zR ^ 4} := by
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, zero_pow two_ne_zero, zero_add]

/-- `cosupp((I₁|_{H₁}, 2)) = {0}`: `y₁³z₁ − z₁⁴ ∈ 𝔪₀²`, and the partials `3y₁²z₁`, `y₁³ − 4z₁³`
vanish together only at `0`. -/
theorem cosupport_map_example11_z_H :
    Ideal.span {yR ^ 3 * zR - zR ^ 4} ≤ Ideal.span {yR, zR} ^ 2 ∧
    ∀ b c : ℚ, Ideal.span {yR ^ 3 * zR - zR ^ 4} ≤ Ideal.span {yR - C b, zR - C c} ^ 2 →
      b = 0 ∧ c = 0 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun b c h => ?_⟩
  · have : yR ^ 3 * zR - zR ^ 4 = yR ^ 2 * (yR * zR) - zR ^ 2 * zR ^ 2 := by ring
    rw [this]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · rw [sq]; exact Ideal.mul_mem_mul yR_mem_m0_fin2 zR_mem_m0_fin2
    · exact Ideal.pow_mem_pow zR_mem_m0_fin2 2
  · obtain ⟨-, hd⟩ := vanish_of_mem_m2_sq b c ((Ideal.span_singleton_le_iff_mem _).mp h)
    have h1 : c = 0 ∨ b = 0 := by simpa using hd 0
    have h2 : b ^ 3 - 4 * c ^ 3 = 0 := by simpa using hd 1
    rcases h1 with hc | hb
    · subst hc
      have : b ^ 3 = 0 := by linarith
      exact ⟨pow_eq_zero_iff (by norm_num) |>.mp this, rfl⟩
    · subst hb
      have : c ^ 3 = 0 := by linarith
      exact ⟨rfl, pow_eq_zero_iff (by norm_num) |>.mp this⟩

/-- `I₁|_{H₁'} = (y₁⁴z₁² + y₁³z₁ − z₁⁴)` (`x₁ ↦ −y₁²z₁`). -/
theorem map_example11_z_H' :
    (Ideal.span {x ^ 2 + y ^ 3 * z - z ^ 4}).map
        (aeval ![-(X 0) ^ 2 * X 1, X 0, X 1] :
          MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) =
      Ideal.span {yR ^ 4 * zR ^ 2 + yR ^ 3 * zR - zR ^ 4} := by
  have e : (aeval ![-(X 0) ^ 2 * X 1, X 0, X 1] :
      MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) (x ^ 2 + y ^ 3 * z - z ^ 4) =
      yR ^ 4 * zR ^ 2 + yR ^ 3 * zR - zR ^ 4 := by
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [Ideal.map_span, Set.image_singleton, e]

/-- `cosupp((I₁|_{H₁'}, 2)) = {0}`: at a `ℚ`-point of order `≥ 2`, `∂/∂y₁ = y₁²z₁(4y₁ + 3)` and
`∂/∂z₁ = 2y₁⁴z₁ + y₁³ − 4z₁³`; with `z₁ = 0` this gives `y₁ = 0`; with `z₁ ≠ 0` and `y₁ = 0` it
gives `z₁ = 0`; with `y₁z₁ = −3/4` the value becomes `−(3/16)y₁² − z₁⁴ < 0`. -/
theorem cosupport_map_example11_z_H' :
    Ideal.span {yR ^ 4 * zR ^ 2 + yR ^ 3 * zR - zR ^ 4} ≤ Ideal.span {yR, zR} ^ 2 ∧
    ∀ b c : ℚ, Ideal.span {yR ^ 4 * zR ^ 2 + yR ^ 3 * zR - zR ^ 4} ≤
      Ideal.span {yR - C b, zR - C c} ^ 2 → b = 0 ∧ c = 0 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun b c h => ?_⟩
  · have : yR ^ 4 * zR ^ 2 + yR ^ 3 * zR - zR ^ 4 =
        (yR ^ 3 * zR + yR ^ 2) * (yR * zR) - zR ^ 2 * zR ^ 2 := by ring
    rw [this]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · rw [sq]; exact Ideal.mul_mem_mul yR_mem_m0_fin2 zR_mem_m0_fin2
    · exact Ideal.pow_mem_pow zR_mem_m0_fin2 2
  · obtain ⟨hv, hd⟩ := vanish_of_mem_m2_sq b c ((Ideal.span_singleton_le_iff_mem _).mp h)
    have hv' : b ^ 4 * c ^ 2 + b ^ 3 * c - c ^ 4 = 0 := by simpa using hv
    have h0 : c ^ 2 * (4 * b ^ 3) + c * (3 * b ^ 2) = 0 := by simpa using hd 0
    have h1 : 2 * b ^ 4 * c + b ^ 3 - 4 * c ^ 3 = 0 := by
      have := hd 1
      simp at this
      linear_combination this
    by_cases hc : c = 0
    · subst hc
      have : b ^ 3 = 0 := by linarith
      exact ⟨pow_eq_zero_iff (by norm_num) |>.mp this, rfl⟩
    · exfalso
      have h0' : b ^ 2 * (4 * b * c + 3) = 0 := by
        have : c * (b ^ 2 * (4 * b * c + 3)) = 0 := by linear_combination h0
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hc
        · exact h
      rcases mul_eq_zero.mp h0' with hb | hbc
      · have hb0 : b = 0 := pow_eq_zero_iff two_ne_zero |>.mp hb
        subst hb0
        have : c ^ 3 = 0 := by linarith
        exact hc (pow_eq_zero_iff (by norm_num) |>.mp this)
      · -- `bc = −3/4`: the value is `(bc)²b² + (bc)b² − c⁴ = −(3/16)b² − c⁴`
        have hbc' : b * c = -3 / 4 := by linarith
        have hc4 : 0 < c ^ 4 := by positivity
        have : b ^ 4 * c ^ 2 + b ^ 3 * c - c ^ 4 = (b * c) ^ 2 * b ^ 2 + (b * c) * b ^ 2 - c ^ 4 :=
        by
          ring
        rw [this, hbc'] at hv'
        nlinarith [sq_nonneg b]

/-! ### The second blow-up on the `z`-chart -/

/-- The second blow-up: `σ f₁ = z₂² f₂` with `f₂` Kollár's `x₂² + (y₂³ − 1)z₂²`, `σ x₁ = z₂x₂`,
`σ(x₁ + y₁²z₁) = z₂(x₂ + y₂²z₂²)`. -/
theorem transform_example11_zz :
    σz (x ^ 2 + y ^ 3 * z - z ^ 4) = z ^ 2 * (x ^ 2 + (y ^ 3 - 1) * z ^ 2) ∧
      σz x = z * x ∧ σz (x + y ^ 2 * z) = z * (x + y ^ 2 * z ^ 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring

/-- The locus of order `2` contains the line `x₂ = z₂ = 0`: `f₂ ∈ 𝔪_{(0,b,0)}²` for every `b`. -/
theorem line_example11_zz (b : ℚ) :
    Ideal.span {x ^ 2 + (y ^ 3 - 1) * z ^ 2} ≤ Ideal.span {x, y - C b, z} ^ 2 := by
  refine (Ideal.span_singleton_le_iff_mem _).mpr ?_
  have hx : x ∈ Ideal.span {x, y - C b, z} := Ideal.subset_span (by simp)
  have hz : z ∈ Ideal.span {x, y - C b, z} := Ideal.subset_span (by simp)
  exact Ideal.add_mem _ (Ideal.pow_mem_pow hx 2) (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hz 2))

/-- The locus of order `2` lies in the line `x₂ = z₂ = 0`: `∂f₂/∂x₂ = 2x₂`, `∂f₂/∂y₂ = 3y₂²z₂²`,
`∂f₂/∂z₂ = 2(y₂³ − 1)z₂` force `x₂ = z₂ = 0` (a point with `z₂ ≠ 0` would need `y₂ = 0` and
`y₂³ = 1`). -/
theorem line_example11_zz' (a b c : ℚ)
    (h : Ideal.span {x ^ 2 + (y ^ 3 - 1) * z ^ 2} ≤ Ideal.span {x - C a, y - C b, z - C c} ^ 2) :
    a = 0 ∧ c = 0 := by
  obtain ⟨-, hd⟩ := vanish_of_mem_m3_sq a b c ((Ideal.span_singleton_le_iff_mem _).mp h)
  have ha : a = 0 := by simpa using hd 0
  have h1 : c = 0 ∨ b = 0 := by simpa using hd 1
  have h2 : b ^ 3 - 1 = 0 ∨ c = 0 := by simpa using hd 2
  refine ⟨ha, ?_⟩
  by_contra hc
  rcases h1 with h | hb
  · exact hc h
  · subst hb
    rcases h2 with h | h
    · norm_num at h
    · exact hc h

/-- `I₂|_{H₂} = ((y₂³ − 1)z₂²)`. -/
theorem map_example11_zz_H :
    (Ideal.span {x ^ 2 + (y ^ 3 - 1) * z ^ 2}).map ρH = Ideal.span {(yR ^ 3 - 1) * zR ^ 2} := by
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_sub, map_add, map_mul, map_pow, map_one, aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    zero_pow two_ne_zero, zero_add]

/-- At the `ℚ`-rational one of Kollár's three points `y₂³ = 1`: `(y₂³ − 1)z₂²` has order exactly
`3` at `(1, 0)`, since it is `(y − 1)(y² + y + 1)z²` and `∂³/∂y∂z² = 6y² = 6 ≠ 0`. -/
theorem ord_example11_zz_H_one :
    Ideal.span {(yR ^ 3 - 1) * zR ^ 2} ≤ Ideal.span {yR - 1, zR} ^ 3 ∧
      ¬ Ideal.span {(yR ^ 3 - 1) * zR ^ 2} ≤ Ideal.span {yR - 1, zR} ^ 4 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · have hy : yR - 1 ∈ Ideal.span {yR - 1, zR} := Ideal.subset_span (by simp)
    have hz : zR ∈ Ideal.span {yR - 1, zR} := Ideal.subset_span (by simp)
    have : (yR ^ 3 - 1) * zR ^ 2 = (yR ^ 2 + yR + 1) * ((yR - 1) * zR ^ 2) := by ring
    rw [this]
    refine Ideal.mul_mem_left _ _ (mem_pow_of_mem_pow_of_le (k := 1 + 2) le_rfl
      (mul_mem_pow_add ?_ (Ideal.pow_mem_pow hz 2)))
    rw [pow_one]; exact hy
  · have h0 : (yR ^ 3 - 1) * zR ^ 2 ∈ Ideal.span {yR - 1, zR} ^ (3 + 1) :=
      (Ideal.span_singleton_le_iff_mem _).mp h
    have h1 := pderiv_mem_pow_of_mem_pow_succ 1 h0
    have h2 := pderiv_mem_pow_of_mem_pow_succ 1 h1
    have h3 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 1) h2
    rw [pow_one] at h3
    have hgen : ∀ s ∈ ({yR - 1, zR} : Set (MvPolynomial (Fin 2) ℚ)), eval ![(1 : ℚ), 0] s = 0 := by
      rintro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl <;> simp
    have := eval_eq_zero_of_mem_span _ hgen h3
    simp at this

/-- Kollár's three points `y₂³ = 1`, over any field: for a field of characteristic zero and any
`ω` with `ω³ = 1`, `(y³ − 1)z²` has order exactly `3` at `(ω, 0)`. -/
theorem ord_example11_zz_H_root {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 3 = 1) :
    Ideal.span {((X 0 : MvPolynomial (Fin 2) K) ^ 3 - 1) * X 1 ^ 2} ≤
        Ideal.span {(X 0 : MvPolynomial (Fin 2) K) - C ω, X 1} ^ 3 ∧
      ¬ Ideal.span {((X 0 : MvPolynomial (Fin 2) K) ^ 3 - 1) * X 1 ^ 2} ≤
        Ideal.span {(X 0 : MvPolynomial (Fin 2) K) - C ω, X 1} ^ 4 := by
  have hC : (C ω : MvPolynomial (Fin 2) K) ^ 3 = 1 := by rw [← map_pow, hω, map_one]
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · have hy : (X 0 : MvPolynomial (Fin 2) K) - C ω ∈ Ideal.span
        {(X 0 : MvPolynomial (Fin 2) K) - C ω, X 1} := Ideal.subset_span (by simp)
    have hz : (X 1 : MvPolynomial (Fin 2) K) ∈ Ideal.span
        {(X 0 : MvPolynomial (Fin 2) K) - C ω, X 1} := Ideal.subset_span (by simp)
    have : ((X 0 : MvPolynomial (Fin 2) K) ^ 3 - 1) * X 1 ^ 2 =
        (X 0 ^ 2 + C ω * X 0 + C ω ^ 2) * ((X 0 - C ω) * X 1 ^ 2) := by
      linear_combination (X 1 : MvPolynomial (Fin 2) K) ^ 2 * hC
    rw [this]
    refine Ideal.mul_mem_left _ _ (mem_pow_of_mem_pow_of_le (k := 1 + 2) le_rfl
      (mul_mem_pow_add ?_ (Ideal.pow_mem_pow hz 2)))
    rw [pow_one]; exact hy
  · have h0 : ((X 0 : MvPolynomial (Fin 2) K) ^ 3 - 1) * X 1 ^ 2 ∈
        Ideal.span {(X 0 : MvPolynomial (Fin 2) K) - C ω, X 1} ^ (3 + 1) :=
      (Ideal.span_singleton_le_iff_mem _).mp h
    have h1 := pderiv_mem_pow_of_mem_pow_succ 1 h0
    have h2 := pderiv_mem_pow_of_mem_pow_succ 1 h1
    have h3 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 1) h2
    rw [pow_one] at h3
    have hgen : ∀ s ∈ ({(X 0 : MvPolynomial (Fin 2) K) - C ω, X 1} : Set (MvPolynomial (Fin 2) K)),
        eval ![ω, 0] s = 0 := by
      rintro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl <;> simp
    have := eval_eq_zero_of_mem_span _ hgen h3
    have hω0 : ω ≠ 0 := by rintro rfl; simp at hω
    simp [hω0] at this

/-- Away from the three points the trace has order `2`: `(y₂³ − 1)z₂²` has order exactly `2` at
`0`. -/
theorem ord_example11_zz_H_zero :
    Ideal.span {(yR ^ 3 - 1) * zR ^ 2} ≤ Ideal.span {yR, zR} ^ 2 ∧
      ¬ Ideal.span {(yR ^ 3 - 1) * zR ^ 2} ≤ Ideal.span {yR, zR} ^ 3 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow zR_mem_m0_fin2 2)
  · have := eval_pderiv_pderiv_eq_zero_of_mem_m2_zero_cube
      ((Ideal.span_singleton_le_iff_mem _).mp h) 1 1
    simp at this

end Hironaka.Examples.Example11Stages
