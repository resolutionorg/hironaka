/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
import HironakaExamples.Balanced.PDeriv
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 52.2: `I + D(I)²` for the double point `I = (xy − zⁿ)`

[Kol07, Example 52.2] starts with the double point ideal `I = (xy − zⁿ)`: restricting to
`S = (x = 0)` gives an `n`-fold line, and blowing up this line "is not an order 2 blow-up for `I`";
the ideal `I + D(I)² = (xy, x², y², xz^{n−1}, yz^{n−1}, zⁿ)` is D-balanced, and its restriction to
`(x = 0)` is `(y², yz^{n−1}, zⁿ)`.

In `ℚ[x, y, z]` with `x = X 0`, `y = X 1`, `z = X 2` and `2 ≤ n`:

* `D(I) = (x, y, z^{n−1})` — the partial derivatives of `xy − zⁿ` are `y`, `x`, `−n z^{n−1}`
  (`derivative_example52`);
* `I + D(I)² = (xy, x², y², xz^{n−1}, yz^{n−1}, zⁿ)` (`example52_eq`): `zⁿ = xy − (xy − zⁿ)` and
  `z^{2n−2} = z^{n−2} · zⁿ`;
* `D(I + D(I)²) ⊆ (x, y, z^{n−1})` and `(x, y, z^{n−1})² ⊆ I + D(I)²`, so `I + D(I)²` is D-balanced
  with respect to `2` (`isDBalanced_example52`);
* the image under `x ↦ 0`, `y ↦ y`, `z ↦ z` is `(y², yz^{n−1}, zⁿ)` (`map_example52`).
-/

@[expose] public section

open MvPolynomial

namespace Hironaka.Balanced

/-- `x = X 0` in `ℚ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 1` in `ℚ[x, y, z]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- `z = X 2` in `ℚ[x, y, z]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℚ)

/-- The double point ideal `I = (xy − zⁿ)` of Example 52.2. -/
noncomputable abbrev example52 (n : ℕ) : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span {x * y - z ^ n}

/-- The ideal `(x, y, z^{n−1}) = D(I)`. -/
noncomputable abbrev example52D (n : ℕ) : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span {x, y, z ^ (n - 1)}

/-- Kollár's `I + D(I)² = (xy, x², y², xz^{n−1}, yz^{n−1}, zⁿ)`. -/
noncomputable abbrev example52T (n : ℕ) : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span {x * y, x ^ 2, y ^ 2, x * z ^ (n - 1), y * z ^ (n - 1), z ^ n}

section Derivative

variable (n : ℕ)

theorem x_mem_D : x ∈ example52D n := Ideal.subset_span (by simp)
theorem y_mem_D : y ∈ example52D n := Ideal.subset_span (by simp)
theorem z_pow_mem_D : z ^ (n - 1) ∈ example52D n := Ideal.subset_span (by simp)

theorem pderiv_zero_gen : pderiv 0 (x * y - z ^ n) = y := by
  rw [map_sub, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide), pderiv_pow,
    pderiv_X_of_ne (by decide)]
  ring

theorem pderiv_one_gen : pderiv 1 (x * y - z ^ n) = x := by
  rw [map_sub, pderiv_mul, pderiv_X_of_ne (by decide), pderiv_X_self, pderiv_pow,
    pderiv_X_of_ne (by decide)]
  ring

theorem pderiv_two_gen :
    pderiv 2 (x * y - z ^ n) = -((n : MvPolynomial (Fin 3) ℚ) * z ^ (n - 1)) := by
  rw [map_sub, pderiv_mul, pderiv_X_of_ne (by decide), pderiv_X_of_ne (by decide), pderiv_pow,
    pderiv_X_self]
  ring

/-- The derivative in [Kol07, Example 52.2]: `D(xy − zⁿ) = (x, y, z^{n−1})` for `2 ≤ n` (also
[Kol07, Example 82]: "`D(I) = (x, y, z^{n−1})`"). -/
theorem derivative_example52 (hn : 2 ≤ n) :
    Ideal.derivative ℚ (example52 n) = example52D n := by
  rw [example52, derivative_span_pderiv]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (hg | hg)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (x_mem_D n)) ?_
      have hz : z ^ n = z ^ (n - 1) * z := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hz]
      exact Ideal.mul_mem_right _ _ (z_pow_mem_D n)
    · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hg
      obtain ⟨i, g', rfl, rfl⟩ := hg
      match i with
      | 0 => rw [pderiv_zero_gen]; exact y_mem_D n
      | 1 => rw [pderiv_one_gen]; exact x_mem_D n
      | 2 =>
        rw [pderiv_two_gen]
        exact neg_mem_iff.mpr (Ideal.mul_mem_left _ _ (z_pow_mem_D n))
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hmem : ∀ i : Fin 3, pderiv i (x * y - z ^ n) ∈
        Ideal.span ({x * y - z ^ n} ∪ ⋃ i, pderiv i '' {x * y - z ^ n}) := fun i =>
      Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ rfl⟩))
    rcases hg with rfl | rfl | rfl
    · have h := hmem 1
      rwa [pderiv_one_gen] at h
    · have h := hmem 0
      rwa [pderiv_zero_gen] at h
    · have h := hmem 2
      rw [pderiv_two_gen, neg_mem_iff] at h
      refine mem_of_C_mul_mem (q := (n : ℚ)) (Nat.cast_ne_zero.mpr (by omega)) ?_
      rwa [map_natCast]

end Derivative

section Balanced

variable (n : ℕ)

/-- `(x, y, z^{n−1})² ⊆ (xy, x², y², xz^{n−1}, yz^{n−1}, zⁿ)` for `2 ≤ n`
(`z^{2n−2} = z^{n−2} · zⁿ`). -/
theorem D_sq_le_T (hn : 2 ≤ n) : example52D n ^ 2 ≤ example52T n := by
  rw [pow_two, Ideal.span_mul_span, Ideal.span_le]
  rintro g ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  dsimp only
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rw [← pow_two]; exact Ideal.subset_span (by simp)
  · exact Ideal.subset_span (by simp)
  · exact Ideal.subset_span (by simp)
  · rw [mul_comm]; exact Ideal.subset_span (by simp)
  · rw [← pow_two]; exact Ideal.subset_span (by simp)
  · exact Ideal.subset_span (by simp)
  · rw [mul_comm]; exact Ideal.subset_span (by simp)
  · rw [mul_comm]; exact Ideal.subset_span (by simp)
  · rw [← pow_add, show n - 1 + (n - 1) = (n - 2) + n by omega, pow_add]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- [Kol07, Example 52.2]: `I + D(I)² = (xy, x², y², xz^{n−1}, yz^{n−1}, zⁿ)` for `2 ≤ n`. -/
theorem example52_eq (hn : 2 ≤ n) :
    example52 n ⊔ Ideal.derivative ℚ (example52 n) ^ 2 = example52T n := by
  rw [derivative_example52 n hn]
  apply le_antisymm
  · refine sup_le ?_ (D_sq_le_T n hn)
    rw [example52, Ideal.span_le]
    rintro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact Ideal.sub_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  · rw [example52T, Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul (x_mem_D n) (y_mem_D n))
    · exact Ideal.mem_sup_right (by
        rw [pow_two, pow_two]; exact Ideal.mul_mem_mul (x_mem_D n) (x_mem_D n))
    · exact Ideal.mem_sup_right (by
        rw [pow_two, pow_two]; exact Ideal.mul_mem_mul (y_mem_D n) (y_mem_D n))
    · exact Ideal.mem_sup_right (by
        rw [pow_two]; exact Ideal.mul_mem_mul (x_mem_D n) (z_pow_mem_D n))
    · exact Ideal.mem_sup_right (by
        rw [pow_two]; exact Ideal.mul_mem_mul (y_mem_D n) (z_pow_mem_D n))
    · have : z ^ n = x * y - (x * y - z ^ n) := by ring
      rw [this]
      exact Ideal.sub_mem _
        (Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul (x_mem_D n) (y_mem_D n)))
        (Ideal.mem_sup_left (Ideal.subset_span rfl))

/-- `D(I + D(I)²) ⊆ (x, y, z^{n−1})` for `2 ≤ n`: `D(I) = (x, y, z^{n−1})` and, by the Leibniz rule,
`D(M²) ⊆ D(M) M + M D(M) ⊆ M` (`derivative_mul_le`). -/
theorem derivative_T_le (hn : 2 ≤ n) : Ideal.derivative ℚ (example52T n) ≤ example52D n := by
  rw [← example52_eq n hn, Ideal.derivative_sup, derivative_example52 n hn, pow_two]
  exact sup_le le_rfl ((Ideal.derivative_mul_le _ _).trans
    (sup_le Ideal.mul_le_right Ideal.mul_le_left))

/-- [Kol07, Example 52.2] ("`I + D(I)²` … is D-balanced"): with respect to the mark `2`, for
`2 ≤ n`. -/
theorem isDBalanced_example52 (hn : 2 ≤ n) :
    Ideal.IsDBalanced ℚ (example52 n ⊔ Ideal.derivative ℚ (example52 n) ^ 2) 2 := by
  rw [example52_eq n hn]
  intro i hi
  interval_cases i
  · exact le_rfl
  · rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Ideal.derivativeIter, Function.iterate_one]
    exact (Ideal.pow_right_mono (derivative_T_le n hn) 2).trans (D_sq_le_T n hn)

end Balanced

section Restriction

variable (n : ℕ)

/-- [Kol07, Example 52.2] ("If we restrict `I + D(I)²` to `(x = 0)`, we get the ideal
`(y², yz^{n−1}, zⁿ)`"): the image under `x ↦ 0`, `y ↦ X 0`, `z ↦ X 1` onto `ℚ[y, z]`, for `2 ≤ n`.
-/
theorem map_example52 (hn : 2 ≤ n) :
    (example52 n ⊔ Ideal.derivative ℚ (example52 n) ^ 2).map
        (aeval ![0, X 0, X 1] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) =
      Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ) ^ 2, X 0 * X 1 ^ (n - 1), X 1 ^ n} := by
  rw [example52_eq n hn, example52T, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_pow, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, zero_mul, zero_pow two_ne_zero]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Ideal.zero_mem _ | exact Ideal.subset_span (by simp)
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl <;> exact Ideal.subset_span (by simp)

end Restriction

end Hironaka.Balanced
