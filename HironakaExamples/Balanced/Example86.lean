/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Algebra.Local.BirationalTransform
import Hironaka.Algebra.Local.Transform
import HironakaExamples.Balanced.PDeriv
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Kollár's Example 86.1: the birational transform of a D-balanced ideal need not be D-balanced

[Kol07, 86]: interchanging `(π₀)⁻¹_*` and `Dⁱ` on the left-hand side of the inequality of
[Kol07, Theorem 76] makes it go "the wrong way", and "in general the birational transform is not
D-balanced". [Kol07, Example 86.1]: the ideal `(x², xyᵐ, y^{m+1})` is D-balanced, but after blowing
up the origin one of the charts gives `(x₁², x₁y₁^{m−1}, y₁^{m−1})`, which is not.

In `ℚ[x, y]` with `x = X 0`, `y = X 1`:

* `D(x², xyᵐ, y^{m+1}) ⊆ (x, yᵐ)`: every generator and every partial derivative of a generator lies
  in `(x, yᵐ)`, and `(x, yᵐ)² ⊆ (x², xyᵐ, y^{m+1})` since `y^{2m} = y^{m−1} · y^{m+1}`
  (`isDBalanced_example86`, `1 ≤ m`).
* The chart `x = x₁ y₁`, `y = y₁` is the chart ring of `ℚ[x, y]` with pivot `y` and centre `(x, y)`
  (`IsLocalRing.chartRing`); the marked transform of `((x², xyᵐ, y^{m+1}), 2)` there is
  `(x₁², x₁y₁^{m−1}, y₁^{m−1})` (`transformIdeal_example86`), by the uniqueness `y₁² · J = I R'` of
  the transformed ideal (`Hironaka.Algebra.Local.Transform`).
* In `ℚ[x₁, y₁]`, `x₁ ∈ D(J)` (from `∂_{x₁} x₁² = 2x₁`) and `y₁^{m−2} ∈ D(J)` (from
  `∂_{y₁} y₁^{m−1} = (m−1) y₁^{m−2}`), so `x₁ y₁^{m−2} ∈ D(J)²`, but `x₁ y₁^{m−2} ∉ J` — no
  generator's exponent divides `(1, m−2)` (`not_isDBalanced_example86`, `2 ≤ m`).
-/

@[expose] public section

open MvPolynomial IsLocalRing

namespace Hironaka.Balanced

/-- Kollár's `x = X 0` in `ℚ[x, y]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 2) ℚ)
/-- Kollár's `y = X 1` in `ℚ[x, y]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 2) ℚ)

/-- The ideal `I = (x², xyᵐ, y^{m+1})` of Example 86.1. -/
noncomputable abbrev example86 (m : ℕ) : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {x ^ 2, x * y ^ m, y ^ (m + 1)}

/-- The chart ideal `J = (x₁², x₁y₁^{m−1}, y₁^{m−1})` of Example 86.1, in `ℚ[x₁, y₁]`. -/
noncomputable abbrev example86Chart (m : ℕ) : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {x ^ 2, x * y ^ (m - 1), y ^ (m - 1)}

section Balanced

variable (m : ℕ)

theorem x_mem_span_pair : x ∈ Ideal.span {x, y ^ m} := Ideal.subset_span (Set.mem_insert _ _)

theorem y_pow_mem_span_pair : y ^ m ∈ Ideal.span {x, y ^ m} :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- `D(x², xyᵐ, y^{m+1}) ⊆ (x, yᵐ)`: every generator and every partial derivative of a generator
lies in `(x, yᵐ)`. -/
theorem derivative_example86_le :
    Ideal.derivative ℚ (example86 m) ≤ Ideal.span {x, y ^ m} := by
  rw [example86, derivative_span_pderiv, Ideal.span_le]
  rintro g (hg | hg)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [pow_two]; exact Ideal.mul_mem_left _ _ (x_mem_span_pair m)
    · exact Ideal.mul_mem_left _ _ (y_pow_mem_span_pair m)
    · rw [pow_succ]; exact Ideal.mul_mem_right _ _ (y_pow_mem_span_pair m)
  · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    obtain ⟨i, g', hg', rfl⟩ := hg
    match i with
    | 0 =>
      rcases hg' with rfl | rfl | rfl
      · rw [pderiv_pow, pderiv_X_self, show 2 - 1 = 1 from rfl, pow_one]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (x_mem_span_pair m))
      · rw [pderiv_mul, pderiv_X_self, pderiv_pow, pderiv_X_of_ne (by decide), mul_zero, mul_zero,
          add_zero, one_mul]
        exact y_pow_mem_span_pair m
      · rw [pderiv_pow, pderiv_X_of_ne (by decide), mul_zero]
        exact Ideal.zero_mem _
    | 1 =>
      rcases hg' with rfl | rfl | rfl
      · rw [pderiv_pow, pderiv_X_of_ne (by decide), mul_zero]
        exact Ideal.zero_mem _
      · rw [pderiv_mul, pderiv_X_of_ne (by decide), zero_mul, zero_add, pderiv_pow, pderiv_X_self]
        exact Ideal.mul_mem_right _ _ (x_mem_span_pair m)
      · rw [pderiv_pow, pderiv_X_self, Nat.add_sub_cancel]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (y_pow_mem_span_pair m))

/-- `(x, yᵐ)² ⊆ (x², xyᵐ, y^{m+1})` for `1 ≤ m` (`y^{2m} = y^{m-1} · y^{m+1}`). -/
theorem span_pair_sq_le_example86 (hm : 1 ≤ m) : Ideal.span {x, y ^ m} ^ 2 ≤ example86 m := by
  rw [pow_two, Ideal.span_mul_span, Ideal.span_le]
  rintro g ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  dsimp only
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rw [← pow_two]; exact Ideal.subset_span (Set.mem_insert _ _)
  · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · rw [mul_comm]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · rw [← pow_add, show m + m = (m - 1) + (m + 1) by omega, pow_add]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ rfl)))

/-- [Kol07, Example 86.1]: `(x², xyᵐ, y^{m+1})` is D-balanced with respect to `2`, for `1 ≤ m`. -/
theorem isDBalanced_example86 (hm : 1 ≤ m) : Ideal.IsDBalanced ℚ (example86 m) 2 := by
  intro i hi
  interval_cases i
  · exact le_rfl
  · rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Ideal.derivativeIter, Function.iterate_one]
    exact (Ideal.pow_right_mono (derivative_example86_le m) 2).trans
      (span_pair_sq_le_example86 m hm)

end Balanced

section Chart

/-- The chart ring of `ℚ[x, y]` with pivot `y` (the chart `x = x₁ y₁`, `y = y₁` of the blow-up of
the origin), `IsLocalRing.chartRing`. -/
noncomputable abbrev chart86 : Subalgebra (MvPolynomial (Fin 2) ℚ)
    (Localization.Away (X 1 : MvPolynomial (Fin 2) ℚ)) :=
  chartRing (X : Fin 2 → MvPolynomial (Fin 2) ℚ) 1

/-- The coordinates `x₁ = x / y`, `y₁ = y` of the chart. -/
noncomputable abbrev chartCoord : Fin 2 → chart86 := chartYR (X : Fin 2 → MvPolynomial (Fin 2) ℚ) 1

/-- The image `ȳ` of `y` in the chart ring. -/
noncomputable abbrev ybar : chart86 := algebraMap (MvPolynomial (Fin 2) ℚ) chart86 y

/-- `y₁ = y` in the chart ring: the pivot coordinate is its own image. -/
theorem chartCoord_one : chartCoord 1 = ybar := by
  apply Subtype.ext
  rw [chartCoord, chartYR, coe_chartYROf, chartYOf_self, ybar, Subalgebra.coe_algebraMap]

/-- `x = y · x₁` in the chart ring. -/
theorem algebraMap_x_eq : algebraMap (MvPolynomial (Fin 2) ℚ) chart86 x = ybar * chartCoord 0 :=
  algebraMap_x_eq_mul_chartYR (X : Fin 2 → MvPolynomial (Fin 2) ℚ) 1 (by decide)

/-- [Kol07, Example 86.1] ("after blowing up the origin, one of the charts gives
`(x₁², x₁y₁^{m−1}, y₁^{m−1})`"): in the chart of `ℚ[x, y]` with pivot `y` and centre `(x, y)`, the
marked transform of `((x², xyᵐ, y^{m+1}), 2)` is `(x₁², x₁y₁^{m−1}, y₁^{m−1})`, for `1 ≤ m` — by the
uniqueness `y₁² · J = I R'` of the transformed ideal. -/
theorem transformIdeal_example86 (m : ℕ) (hm : 1 ≤ m) :
    transformIdeal (X : Fin 2 → MvPolynomial (Fin 2) ℚ) 1 (example86 m) 2 =
      Ideal.span {chartCoord 0 ^ 2, chartCoord 0 * chartCoord 1 ^ (m - 1),
        chartCoord 1 ^ (m - 1)} := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hx : x ∈ chartCenter (X : Fin 2 → MvPolynomial (Fin 2) ℚ) 1 :=
    x_mem_chartCenter X 1 (by decide)
  have hy : y ∈ chartCenter (X : Fin 2 → MvPolynomial (Fin 2) ℚ) 1 := x_mem_chartCenter X 1 le_rfl
  have hI : example86 (m + 1) ≤ chartCenter (X : Fin 2 → MvPolynomial (Fin 2) ℚ) 1 ^ 2 := by
    rw [example86, Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [pow_two, pow_two]; exact Ideal.mul_mem_mul hx hx
    · rw [pow_succ y m, mul_comm (y ^ m) y, ← mul_assoc, pow_two]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hx hy)
    · rw [show m + 1 + 1 = 2 + m by omega, pow_add y 2 m, pow_two, pow_two]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hy hy)
  symm
  apply eq_transformIdeal_of_span_pow_mul_eq X 1 hI
  rw [Ideal.span_singleton_pow, Ideal.span_mul_span, Set.singleton_mul, example86, Ideal.map_span,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton, chartCoord_one]
  congr 1
  have e1 : algebraMap (MvPolynomial (Fin 2) ℚ) chart86 (x ^ 2) = ybar ^ 2 * chartCoord 0 ^ 2 := by
    rw [map_pow, algebraMap_x_eq, mul_pow]
  have e2 : algebraMap (MvPolynomial (Fin 2) ℚ) chart86 (x * y ^ (m + 1)) =
      ybar ^ 2 * (chartCoord 0 * ybar ^ m) := by
    rw [map_mul, map_pow, algebraMap_x_eq]; ring
  have e3 : algebraMap (MvPolynomial (Fin 2) ℚ) chart86 (y ^ (m + 1 + 1)) =
      ybar ^ 2 * ybar ^ m := by
    rw [map_pow]; ring
  rw [e1, e2, e3]

end Chart

section NotBalanced

variable (m : ℕ)

/-- `x₁ ∈ D(J)`, from `∂_{x₁} x₁² = 2 x₁`. -/
theorem x_mem_derivative_example86Chart : x ∈ Ideal.derivative ℚ (example86Chart m) := by
  have h : pderiv 0 (x ^ 2) ∈ Ideal.derivative ℚ (example86Chart m) := by
    rw [example86Chart, derivative_span_pderiv]
    exact Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨0, Set.mem_image_of_mem _
      (Set.mem_insert _ _)⟩))
  rw [pderiv_pow, pderiv_X_self, mul_one, show 2 - 1 = 1 from rfl, pow_one] at h
  refine mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero ?_
  rw [map_ofNat]
  exact_mod_cast h

/-- `y₁^{m−2} ∈ D(J)` for `2 ≤ m`, from `∂_{y₁} y₁^{m−1} = (m−1) y₁^{m−2}`. -/
theorem y_pow_mem_derivative_example86Chart (hm : 2 ≤ m) :
    y ^ (m - 2) ∈ Ideal.derivative ℚ (example86Chart m) := by
  have h : pderiv 1 (y ^ (m - 1)) ∈ Ideal.derivative ℚ (example86Chart m) := by
    rw [example86Chart, derivative_span_pderiv]
    exact Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨1, Set.mem_image_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))⟩))
  rw [pderiv_pow, pderiv_X_self, mul_one, show m - 1 - 1 = m - 2 by omega] at h
  refine mem_of_C_mul_mem (q := ((m - 1 : ℕ) : ℚ)) (Nat.cast_ne_zero.mpr (by omega)) ?_
  rwa [map_natCast]

/-- `x₁ y₁^{m−2} ∉ (x₁², x₁y₁^{m−1}, y₁^{m−1})` for `2 ≤ m`: no generator divides it. -/
theorem not_mem_example86Chart (hm : 2 ≤ m) : x * y ^ (m - 2) ∉ example86Chart m := by
  have hJ : example86Chart m = Ideal.span ((fun s => monomial s (1 : ℚ)) ''
      {Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 (m - 1),
        Finsupp.single 1 (m - 1)}) := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, example86Chart,
      X_pow_eq_monomial, X_pow_eq_monomial, monomial_single_add, pow_one]
  have hx : x * y ^ (m - 2) = monomial (Finsupp.single 0 1 + Finsupp.single 1 (m - 2)) (1 : ℚ) := by
    rw [monomial_single_add, pow_one, X_pow_eq_monomial]
  rw [hJ, hx, mem_ideal_span_monomial_image]
  intro h
  obtain ⟨si, hsi, hle⟩ := h (Finsupp.single 0 1 + Finsupp.single 1 (m - 2))
    (by rw [support_monomial, ite_eq_right one_ne_zero]; exact Finset.mem_singleton_self _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsi
  rcases hsi with rfl | rfl | rfl
  · have := hle 0
    simp at this
  · have := hle 1
    simp at this
    omega
  · have := hle 1
    simp at this
    omega

/-- [Kol07, Example 86.1] ("which is not D-balanced"; the remark of [Kol07, 86]): the chart ideal
`(x₁², x₁y₁^{m−1}, y₁^{m−1})` is not D-balanced with respect to `2`, for `2 ≤ m`. -/
theorem not_isDBalanced_example86 (hm : 2 ≤ m) : ¬ Ideal.IsDBalanced ℚ (example86Chart m) 2 := by
  intro h
  have h1 := h 1 (by norm_num)
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Ideal.derivativeIter, Function.iterate_one] at h1
  have hmem : x * y ^ (m - 2) ∈ Ideal.derivative ℚ (example86Chart m) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (x_mem_derivative_example86Chart m)
      (y_pow_mem_derivative_example86Chart m hm)
  exact not_mem_example86Chart m hm (h1 hmem)

end NotBalanced

end Hironaka.Balanced
