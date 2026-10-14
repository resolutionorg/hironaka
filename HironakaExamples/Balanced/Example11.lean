/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import HironakaExamples.Balanced.PDeriv
import HironakaExamples.MaximalContact.Example82
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 11: the tuned ideal of `I = (x² + y³ − z⁶)`

[Kol07, Example 11] resolves `S := (x² + y³ − z⁶ = 0) ⊂ 𝔸³` through the hypersurface `H := (x = 0)`
and the trace `S ∩ H = (y³ − z⁶ = 0) ⊂ 𝔸²`, which has multiplicity `3` although "we came from a
multiplicity `2` situation". The tuning step of the order reduction on this example, computed
exactly in `ℚ[x, y, z]`:

* `D(I) = (x, y², z⁵)` — the partial derivatives of `x² + y³ − z⁶` are `2x`, `3y²`, `−6z⁵`
  (`derivative_example11`, by `derivative_span_pderiv`);
* the tuned ideal `W(I) = W_2(I) = I + D(I)² = (x², xy², xz⁵, y⁴, y²z⁵, y³z⁴, z⁶ − y³)`
  (`tuned_example11`): the six products of `x, y², z⁵` are generators except
  `z¹⁰ = z⁴(z⁶ − y³) + y³z⁴`, and conversely `y³z⁴ = z⁴(x² + y³ − z⁶) − x²z⁴ + z¹⁰`,
  `z⁶ − y³ = x² − (x² + y³ − z⁶)`;
* `I` and `W(I)` have order exactly `2` at the origin (`ord_zero_example11`,
  `ord_zero_tuned_example11`): both lie in `𝔪₀²`, and `x² ∉ 𝔪₀³` (two partial derivatives and the
  evaluation at `0`);
* the order-2 locus `V(D(I))` has the origin as its only `ℚ`-point (`cosupport_example11`), and it
  is also `cosupp(W(I), 2)` since `D(W(I)) = D(I)` (`derivative_sup_derivative_sq`);
* `I` itself is neither D-balanced nor MC-invariant with respect to `2`
  (`not_isDBalanced_example11`, `not_mcInvariant_example11`): `x·x ∈ D(I)²`, but `x² ∉ I` — at the
  point `(1, 0, 1)`, a zero of `x² + y³ − z⁶`, `x²` evaluates to `1`;
* the restrictions of `W(I)` to `H = (x = 0)` and to `H' = (x + y² = 0)` — the images under `x ↦ 0`
  and `x ↦ −y²` into `ℚ[y, z]` — are both `(y⁴, y²z⁵, y³z⁴, z⁶ − y³)` (`map_tuned_example11_H`,
  `map_tuned_example11_H'`), and that ideal's order-2 locus has the origin as its only `ℚ`-point
  (`cosupport_tuned_example11_H`: `−3y²` and `6z⁵` are among its partial derivatives).
-/

@[expose] public section

open MvPolynomial Hironaka.Examples

namespace Hironaka.Examples.Example11

/-- `x = X 0` in `ℚ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 1` in `ℚ[x, y, z]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- `z = X 2` in `ℚ[x, y, z]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℚ)

/-- Kollár's `I = (x² + y³ − z⁶)`. -/
noncomputable abbrev I11 : Ideal (MvPolynomial (Fin 3) ℚ) := Ideal.span {x ^ 2 + y ^ 3 - z ^ 6}

/-- `D(I) = (x, y², z⁵)`. -/
noncomputable abbrev D11 : Ideal (MvPolynomial (Fin 3) ℚ) := Ideal.span {x, y ^ 2, z ^ 5}

/-- The tuned ideal `W(I) = (x², xy², xz⁵, y⁴, y²z⁵, y³z⁴, z⁶ − y³)`. -/
noncomputable abbrev T11 : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span {x ^ 2, x * y ^ 2, x * z ^ 5, y ^ 4, y ^ 2 * z ^ 5, y ^ 3 * z ^ 4, z ^ 6 - y ^ 3}

/-- The maximal ideal of the origin, `𝔪₀ = (x, y, z)`. -/
noncomputable abbrev m0 : Ideal (MvPolynomial (Fin 3) ℚ) := Ideal.span {x, y, z}

section Derivative

theorem pderiv_zero_ex11 : pderiv 0 (x ^ 2 + y ^ 3 - z ^ 6) = C 2 * x := by
  rw [map_sub, map_add, pderiv_pow, pderiv_pow, pderiv_pow, pderiv_X_self,
    pderiv_X_of_ne (by decide), pderiv_X_of_ne (by decide)]
  simp only [map_ofNat]
  ring

theorem pderiv_one_ex11 : pderiv 1 (x ^ 2 + y ^ 3 - z ^ 6) = C 3 * y ^ 2 := by
  rw [map_sub, map_add, pderiv_pow, pderiv_pow, pderiv_pow, pderiv_X_self,
    pderiv_X_of_ne (by decide), pderiv_X_of_ne (by decide)]
  simp only [map_ofNat]
  ring

theorem pderiv_two_ex11 : pderiv 2 (x ^ 2 + y ^ 3 - z ^ 6) = -(C 6 * z ^ 5) := by
  rw [map_sub, map_add, pderiv_pow, pderiv_pow, pderiv_pow, pderiv_X_self,
    pderiv_X_of_ne (by decide), pderiv_X_of_ne (by decide)]
  simp only [map_ofNat]
  ring

theorem x_mem_D11 : x ∈ D11 := Ideal.subset_span (by simp)
theorem y_sq_mem_D11 : y ^ 2 ∈ D11 := Ideal.subset_span (by simp)
theorem z_five_mem_D11 : z ^ 5 ∈ D11 := Ideal.subset_span (by simp)

/-- `D(x² + y³ − z⁶) = (x, y², z⁵)`. -/
theorem derivative_example11 : Ideal.derivative ℚ I11 = D11 := by
  rw [I11, derivative_span_pderiv]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (hg | hg)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      have : x ^ 2 + y ^ 3 - z ^ 6 = x * x + y * y ^ 2 - z * z ^ 5 := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ x_mem_D11)
        (Ideal.mul_mem_left _ _ y_sq_mem_D11)) (Ideal.mul_mem_left _ _ z_five_mem_D11)
    · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hg
      obtain ⟨i, g', rfl, rfl⟩ := hg
      match i with
      | 0 => rw [pderiv_zero_ex11]; exact Ideal.mul_mem_left _ _ x_mem_D11
      | 1 => rw [pderiv_one_ex11]; exact Ideal.mul_mem_left _ _ y_sq_mem_D11
      | 2 => rw [pderiv_two_ex11]; exact neg_mem_iff.mpr (Ideal.mul_mem_left _ _ z_five_mem_D11)
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hmem : ∀ i : Fin 3, pderiv i (x ^ 2 + y ^ 3 - z ^ 6) ∈
        Ideal.span ({x ^ 2 + y ^ 3 - z ^ 6} ∪ ⋃ i, pderiv i '' {x ^ 2 + y ^ 3 - z ^ 6}) := fun i =>
      Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ rfl⟩))
    rcases hg with rfl | rfl | rfl
    · have h := hmem 0
      rw [pderiv_zero_ex11] at h
      exact mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero h
    · have h := hmem 1
      rw [pderiv_one_ex11] at h
      exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero h
    · have h := hmem 2
      rw [pderiv_two_ex11, neg_mem_iff] at h
      exact mem_of_C_mul_mem (q := (6 : ℚ)) (by norm_num) h

end Derivative

section Tuned

theorem x_sq_mem_T11 : x ^ 2 ∈ T11 := Ideal.subset_span (by simp)
theorem xy_sq_mem_T11 : x * y ^ 2 ∈ T11 := Ideal.subset_span (by simp)
theorem xz_five_mem_T11 : x * z ^ 5 ∈ T11 := Ideal.subset_span (by simp)
theorem y_four_mem_T11 : y ^ 4 ∈ T11 := Ideal.subset_span (by simp)
theorem y_sq_z_five_mem_T11 : y ^ 2 * z ^ 5 ∈ T11 := Ideal.subset_span (by simp)
theorem y_cube_z_four_mem_T11 : y ^ 3 * z ^ 4 ∈ T11 := Ideal.subset_span (by simp)
theorem z_six_sub_mem_T11 : z ^ 6 - y ^ 3 ∈ T11 := Ideal.subset_span (by simp)

/-- `z¹⁰ = z⁴(z⁶ − y³) + y³z⁴ ∈ W(I)`. -/
theorem z_ten_mem_T11 : z ^ 10 ∈ T11 := by
  have : z ^ 10 = z ^ 4 * (z ^ 6 - y ^ 3) + y ^ 3 * z ^ 4 := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ z_six_sub_mem_T11) y_cube_z_four_mem_T11

/-- `(x, y², z⁵)² ⊆ W(I)`. -/
theorem D11_sq_le_T11 : D11 ^ 2 ≤ T11 := by
  rw [pow_two, Ideal.span_mul_span, Ideal.span_le]
  rintro g ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  dsimp only
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rw [← pow_two]; exact x_sq_mem_T11
  · exact xy_sq_mem_T11
  · exact xz_five_mem_T11
  · rw [mul_comm]; exact xy_sq_mem_T11
  · rw [← pow_add]; exact y_four_mem_T11
  · exact y_sq_z_five_mem_T11
  · rw [mul_comm]; exact xz_five_mem_T11
  · rw [mul_comm]; exact y_sq_z_five_mem_T11
  · rw [← pow_add]; exact z_ten_mem_T11

/-- `W(I) = I + D(I)² = (x², xy², xz⁵, y⁴, y²z⁵, y³z⁴, z⁶ − y³)`. -/
theorem tuned_example11 : I11 ⊔ Ideal.derivative ℚ I11 ^ 2 = T11 := by
  rw [derivative_example11]
  apply le_antisymm
  · refine sup_le ?_ D11_sq_le_T11
    rw [I11, Ideal.span_le]
    rintro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have : x ^ 2 + y ^ 3 - z ^ 6 = x ^ 2 - (z ^ 6 - y ^ 3) := by ring
    rw [this]
    exact Ideal.sub_mem _ x_sq_mem_T11 z_six_sub_mem_T11
  · have hD : ∀ a ∈ D11, ∀ b ∈ D11, a * b ∈ I11 ⊔ D11 ^ 2 := fun a ha b hb =>
      Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)
    rw [T11, Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show x ^ 2 = x * x by ring]; exact hD _ x_mem_D11 _ x_mem_D11
    · exact hD _ x_mem_D11 _ y_sq_mem_D11
    · exact hD _ x_mem_D11 _ z_five_mem_D11
    · rw [show y ^ 4 = y ^ 2 * y ^ 2 by ring]; exact hD _ y_sq_mem_D11 _ y_sq_mem_D11
    · exact hD _ y_sq_mem_D11 _ z_five_mem_D11
    · have : y ^ 3 * z ^ 4 = z ^ 4 * (x ^ 2 + y ^ 3 - z ^ 6) - x * (x * z ^ 4) + z ^ 5 * z ^ 5 := by
        ring
      rw [this]
      refine Ideal.add_mem _ (Ideal.sub_mem _ ?_ ?_) (hD _ z_five_mem_D11 _ z_five_mem_D11)
      · exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
      · exact hD _ x_mem_D11 _ (Ideal.mul_mem_right _ _ x_mem_D11)
    · have : z ^ 6 - y ^ 3 = x * x - (x ^ 2 + y ^ 3 - z ^ 6) := by ring
      rw [this]
      exact Ideal.sub_mem _ (hD _ x_mem_D11 _ x_mem_D11)
        (Ideal.mem_sup_left (Ideal.subset_span rfl))

end Tuned

section Order

/-- `x² ∉ 𝔪₀³`: differentiate twice in `x` and evaluate at the origin. -/
theorem x_sq_notMem_m0_cube : x ^ 2 ∉ m0 ^ 3 := by
  intro h
  have h1 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 2) h
  have h2 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 1) h1
  rw [pow_one] at h2
  have := eval_eq_zero_of_mem_span (![0, 0, 0] : Fin 3 → ℚ) (by simp) h2
  simp at this

/-- `I = (x² + y³ − z⁶)` has order exactly `2` at the origin. -/
theorem ord_zero_example11 : I11 ≤ m0 ^ 2 ∧ ¬ I11 ≤ m0 ^ 3 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · refine Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.pow_mem_pow x_mem_m0 2) ?_) ?_
    · exact mem_pow_of_mem_pow_of_le (k := 3) (by norm_num) (Ideal.pow_mem_pow y_mem_m0 3)
    · exact mem_pow_of_mem_pow_of_le (k := 6) (by norm_num) (Ideal.pow_mem_pow z_mem_m0 6)
  · have h0 : x ^ 2 + y ^ 3 - z ^ 6 ∈ m0 ^ 3 := (Ideal.span_singleton_le_iff_mem _).mp h
    have hy : y ^ 3 ∈ m0 ^ 3 := Ideal.pow_mem_pow y_mem_m0 3
    have hz : z ^ 6 ∈ m0 ^ 3 :=
      mem_pow_of_mem_pow_of_le (k := 6) (by norm_num) (Ideal.pow_mem_pow z_mem_m0 6)
    have : x ^ 2 = (x ^ 2 + y ^ 3 - z ^ 6) - y ^ 3 + z ^ 6 := by ring
    exact x_sq_notMem_m0_cube (this ▸ Ideal.add_mem _ (Ideal.sub_mem _ h0 hy) hz)

/-- `W(I) ⊆ 𝔪₀²`: every generator has degree `≥ 2`. -/
theorem T11_le_m0_sq : T11 ≤ m0 ^ 2 := by
  rw [T11, Ideal.span_le]
  rintro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have hy2 : y ^ 2 ∈ m0 ^ 2 := Ideal.pow_mem_pow y_mem_m0 2
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ideal.pow_mem_pow x_mem_m0 2
  · exact Ideal.mul_mem_left _ _ hy2
  · exact Ideal.mul_mem_left _ _
      (mem_pow_of_mem_pow_of_le (k := 5) (by norm_num) (Ideal.pow_mem_pow z_mem_m0 5))
  · exact mem_pow_of_mem_pow_of_le (k := 4) (by norm_num) (Ideal.pow_mem_pow y_mem_m0 4)
  · exact Ideal.mul_mem_right _ _ hy2
  · exact Ideal.mul_mem_right _ _
      (mem_pow_of_mem_pow_of_le (k := 3) (by norm_num) (Ideal.pow_mem_pow y_mem_m0 3))
  · exact Ideal.sub_mem _
      (mem_pow_of_mem_pow_of_le (k := 6) (by norm_num) (Ideal.pow_mem_pow z_mem_m0 6))
      (mem_pow_of_mem_pow_of_le (k := 3) (by norm_num) (Ideal.pow_mem_pow y_mem_m0 3))

/-- The tuned ideal `W(I)` has order exactly `2` at the origin. -/
theorem ord_zero_tuned_example11 : T11 ≤ m0 ^ 2 ∧ ¬ T11 ≤ m0 ^ 3 :=
  ⟨T11_le_m0_sq, fun h => x_sq_notMem_m0_cube (h x_sq_mem_T11)⟩

/-- `cosupp(I, 2) = V(D(I))` has the origin as its only `ℚ`-point. -/
theorem cosupport_example11 (a b c : ℚ)
    (h : ∀ g ∈ Ideal.derivative ℚ I11, eval ![a, b, c] g = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [derivative_example11] at h
  have ha : a = 0 := by simpa using h x x_mem_D11
  have hb : b ^ 2 = 0 := by simpa using h (y ^ 2) y_sq_mem_D11
  have hc : c ^ 5 = 0 := by simpa using h (z ^ 5) z_five_mem_D11
  exact ⟨ha, pow_eq_zero_iff two_ne_zero |>.mp hb, pow_eq_zero_iff (by norm_num) |>.mp hc⟩

end Order

section Negative

/-- `x² ∉ I`: at `(1, 0, 1)`, a zero of `x² + y³ − z⁶`, `x²` evaluates to `1`. -/
theorem x_sq_notMem_I11 : x ^ 2 ∉ I11 := by
  intro h
  have := eval_eq_zero_of_mem_span (![1, 0, 1] : Fin 3 → ℚ) (by simp) h
  simp at this

/-- `I` is not D-balanced with respect to `2`. -/
theorem not_isDBalanced_example11 : ¬ Ideal.IsDBalanced ℚ I11 2 := by
  intro h
  have h1 := h 1 (by norm_num)
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero,
    derivative_example11] at h1
  exact x_sq_notMem_I11 (h1 (by rw [pow_two, pow_two]; exact Ideal.mul_mem_mul x_mem_D11 x_mem_D11))

/-- `I` is not MC-invariant with respect to `2`. -/
theorem not_mcInvariant_example11 :
    ¬ (Ideal.derivative ℚ I11 * Ideal.derivative ℚ I11 ≤ I11) := by
  intro h
  rw [derivative_example11] at h
  exact x_sq_notMem_I11 (h (by rw [pow_two]; exact Ideal.mul_mem_mul x_mem_D11 x_mem_D11))

end Negative

section Restriction

/-- The common restriction `(y⁴, y²z⁵, y³z⁴, z⁶ − y³)` in `ℚ[y, z]` (`y = X 0`, `z = X 1`). -/
noncomputable abbrev TH11 : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ) ^ 4, X 0 ^ 2 * X 1 ^ 5, X 0 ^ 3 * X 1 ^ 4,
    X 1 ^ 6 - X 0 ^ 3}

/-- `W(I)|_H` for `H = (x = 0)` is `(y⁴, y²z⁵, y³z⁴, z⁶ − y³)`. -/
theorem map_tuned_example11_H :
    T11.map (aeval ![0, X 0, X 1] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) =
      TH11 := by
  rw [T11, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, map_sub, map_mul, map_pow, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, zero_mul, zero_pow two_ne_zero]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Ideal.zero_mem _ | exact Ideal.subset_span (by simp)
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact Ideal.subset_span (by simp)

/-- `W(I)|_{H'}` for `H' = (x + y² = 0)` is the same ideal `(y⁴, y²z⁵, y³z⁴, z⁶ − y³)`: `x ↦ −y²`
sends `x² ↦ y⁴`, `xy² ↦ −y⁴`, `xz⁵ ↦ −y²z⁵`. -/
theorem map_tuned_example11_H' :
    T11.map (aeval ![-(X 0) ^ 2, X 0, X 1] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) =
      TH11 := by
  rw [T11, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, map_sub, map_mul, map_pow, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  have hy4 : (X 0 : MvPolynomial (Fin 2) ℚ) ^ 4 ∈ TH11 := Ideal.subset_span (by simp)
  have hy2z5 : (X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 * X 1 ^ 5 ∈ TH11 := Ideal.subset_span (by simp)
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show (-(X 0 : MvPolynomial (Fin 2) ℚ) ^ 2) ^ 2 = X 0 ^ 4 by ring]; exact hy4
    · rw [show -(X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 * X 0 ^ 2 = -(X 0 ^ 4) by ring]
      exact neg_mem_iff.mpr hy4
    · rw [show -(X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 * X 1 ^ 5 = -(X 0 ^ 2 * X 1 ^ 5) by ring]
      exact neg_mem_iff.mpr hy2z5
    all_goals exact Ideal.subset_span (by simp)
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact Ideal.subset_span (by simp)

/-- The order-2 locus of `(y⁴, y²z⁵, y³z⁴, z⁶ − y³)` has the origin as its only `ℚ`-point: `−3y²`
and `6z⁵` are partial derivatives of `z⁶ − y³`. -/
theorem cosupport_tuned_example11_H (b c : ℚ)
    (h : ∀ g ∈ Ideal.derivative ℚ TH11, eval ![b, c] g = 0) : b = 0 ∧ c = 0 := by
  rw [TH11, derivative_span_pderiv] at h
  have hmem : ∀ i : Fin 2, pderiv i ((X 1 : MvPolynomial (Fin 2) ℚ) ^ 6 - X 0 ^ 3) ∈
      Ideal.span (({(X 0 : MvPolynomial (Fin 2) ℚ) ^ 4, X 0 ^ 2 * X 1 ^ 5, X 0 ^ 3 * X 1 ^ 4,
        X 1 ^ 6 - X 0 ^ 3} : Set (MvPolynomial (Fin 2) ℚ)) ∪
        ⋃ i, pderiv i '' {(X 0 : MvPolynomial (Fin 2) ℚ) ^ 4, X 0 ^ 2 * X 1 ^ 5, X 0 ^ 3 * X 1 ^ 4,
          X 1 ^ 6 - X 0 ^ 3}) := fun i =>
    Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ (by simp)⟩))
  have h0 : b = 0 := by
    have := h _ (hmem 0)
    rw [map_sub, pderiv_pow, pderiv_pow, pderiv_X_of_ne (by decide), pderiv_X_self] at this
    simpa using this
  have h1 : c = 0 := by
    have := h _ (hmem 1)
    rw [map_sub, pderiv_pow, pderiv_pow, pderiv_X_self, pderiv_X_of_ne (by decide)] at this
    simpa using this
  exact ⟨h0, h1⟩

end Restriction

end Hironaka.Examples.Example11
