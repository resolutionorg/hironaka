/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.CoordinateSubspace.Exceptional

/-!
# Remark 33 on the affine model: the chart computations

[Kol07, Remark 33] blows up the origin `p = V(x, y, z)` of `𝔸³` and then the birational transform
`C'` of the `z`-axis `C = V(x, y)`. The one computation behind "it is easy to see that
`X_2 ≅ X_2'`" is that the total transform of `C` under the point blow-up is the exceptional
divisor times the birational transform, `(x, y)·𝒪 = E_0 · C'`, i.e. that `C` passes through `p`
with multiplicity one. On the three charts of the model blow-up `B_p 𝔸³` (the chart of `x_j` is
`Spec k[x_0, x_1, x_2]` with the substitution `x_i ↦ x_i x_j` for `i ≠ j`,
[Hau14, Definition 4.12]) this is elementary commutative algebra, collected here:

* in the chart of `z` the ideal `(x, y)` becomes `(xz, yz) = (z) · (x, y)`, the exceptional ideal
  is `(z)`, and `(x, y)` is a prime ideal not containing `z`, so the `(z)`-saturation of
  `(z)·(x, y)` is `(x, y)` (`colon_map_two_le`);
* in the charts of `x` and of `y` the ideal `(x, y)` becomes `(x, yx) = (x)`, resp. `(y)`, the
  exceptional ideal itself, whose saturation is the unit ideal.

The sheaf-level consequences on the blow-up `blowUp` used throughout the library are drawn in
`HironakaExamples/Sequence/Remark33Iso.lean`.
-/

@[expose] public section

universe u

open MvPolynomial AlgebraicGeometry CoordinateSubspace affineBlowUpAlgebra

namespace Hironaka.Sequence.Remark33

variable (k : Type u) [Field k]

/-- The chart substitution of the `x_j`-chart of `B_p 𝔸³` [Hau14, Definition 4.12]:
`x_i ↦ x_i x_j` for `i ≠ j`, `x_j ↦ x_j`. -/
noncomputable abbrev subst (j : Fin 3) : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  chartSubst k (center 3 3) j

theorem subst_X (j i : Fin 3) :
    subst k j (X i) = if i ≠ j then X i * X j else X i := by
  rw [subst, chartSubst_X k 3 3 j i]
  simp only [i.isLt, true_and]

/-- The origin's ideal `(x, y, z)` becomes `(x_j)` in the chart of `x_j`: the exceptional ideal. -/
theorem map_centerIdeal_three_subst (j : Fin 3) :
    (centerIdeal k 3 3).map (subst k j) = Ideal.span {X j} := by
  apply le_antisymm
  · rw [centerIdeal, coordinateIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, -, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, subst_X]
    split_ifs with h
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [not_ne_iff] at h
      subst h
      exact Ideal.mem_span_singleton_self _
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have h : (X j : MvPolynomial (Fin 3) k) = subst k j (X j) := by
      rw [subst_X, ite_eq_right (fun h => h rfl)]
    rw [h]
    exact Ideal.mem_map_of_mem _ (X_mem_centerIdeal k 3 3 j.isLt)

/-- The `z`-axis' ideal `(x, y)` becomes `(x_j)` in the chart of `x_j` for `j = x, y`: the
birational transform of `C` misses these charts. -/
theorem map_centerIdeal_two_subst_of_lt (j : Fin 3) (hj : j.val < 2) :
    (centerIdeal k 3 2).map (subst k j) = Ideal.span {X j} := by
  apply le_antisymm
  · rw [centerIdeal, coordinateIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, -, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, subst_X]
    split_ifs with h
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [not_ne_iff] at h
      subst h
      exact Ideal.mem_span_singleton_self _
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have h : (X j : MvPolynomial (Fin 3) k) = subst k j (X j) := by
      rw [subst_X, ite_eq_right (fun h => h rfl)]
    rw [h]
    exact Ideal.mem_map_of_mem _ (X_mem_centerIdeal k 3 2 hj)

/-- The `z`-axis' ideal `(x, y)` becomes `(xz, yz) = (z) · (x, y)` in the chart of `z`. -/
theorem map_centerIdeal_two_subst_two :
    (centerIdeal k 3 2).map (subst k 2) = Ideal.span {X 2} * centerIdeal k 3 2 := by
  rw [centerIdeal, coordinateIdeal, Ideal.map_span, Ideal.span_mul_span, Set.singleton_mul,
    Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun i hi => ?_
  have hi2 : i ≠ 2 := by
    rintro rfl
    exact absurd hi (by decide)
  rw [subst_X, ite_eq_left hi2, mul_comm]

/-- `(x, y)` is the kernel of killing the variables `x` and `y` (`killPred`). -/
theorem centerIdeal_two_eq_ker :
    centerIdeal k 3 2 =
      RingHom.ker (killPred k (fun i : Fin 3 => 2 ≤ i.val) :
        MvPolynomial (Fin 3) k →+* MvPolynomial {i : Fin 3 // 2 ≤ i.val} k) := by
  rw [ker_killPred, centerIdeal]
  congr 1
  ext i
  change i.val < 2 ↔ ¬ 2 ≤ i.val
  exact not_le.symm

/-- `(x, y)` is a prime ideal of `k[x, y, z]`: the kernel of killing `x` and `y`. -/
theorem isPrime_centerIdeal_two : (centerIdeal k 3 2).IsPrime := by
  rw [centerIdeal_two_eq_ker]
  exact RingHom.ker_isPrime _

/-- `z ∉ (x, y)`. -/
theorem X_two_notMem_centerIdeal_two : (X 2 : MvPolynomial (Fin 3) k) ∉ centerIdeal k 3 2 := by
  rw [centerIdeal_two_eq_ker, RingHom.mem_ker, RingHom.coe_coe, killPred_X_of k _ (le_refl 2)]
  exact X_ne_zero _

/-- The chart form of the total transform of `C`. -/
noncomputable abbrev totalChart (j : Fin 3) : Ideal (MvPolynomial (Fin 3) k) :=
  (centerIdeal k 3 2).map (subst k j)

/-- The chart form of the exceptional ideal. -/
noncomputable abbrev excChart (j : Fin 3) : Ideal (MvPolynomial (Fin 3) k) :=
  (centerIdeal k 3 3).map (subst k j)

/-- The `(z)`-saturation of `(z) · (x, y)` stops at the first step: an element `f` with
`f z² ∈ (z)·(x, y)` already has `f z ∈ (z)·(x, y)`, because `z` is a nonzerodivisor and `(x, y)`
is a prime ideal not containing `z`. -/
theorem colon_map_two_le :
    (totalChart k 2).colon (↑(excChart k 2 ^ 2) : Set (MvPolynomial (Fin 3) k)) ≤
      (totalChart k 2).colon (↑(excChart k 2) : Set (MvPolynomial (Fin 3) k)) := by
  rw [totalChart, excChart, map_centerIdeal_two_subst_two, map_centerIdeal_three_subst,
    Ideal.span_singleton_pow, Ideal.colon_span, Ideal.colon_span]
  intro f hf
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hf ⊢
  -- `f z² ∈ (z)(x, y)`: `f z² = z q` with `q ∈ (x, y)`, so `q = f z ∈ (x, y)`, so `f ∈ (x, y)`
  obtain ⟨q, hq, hzq⟩ := Ideal.mem_span_singleton_mul.mp hf
  have hz : (X 2 : MvPolynomial (Fin 3) k) ≠ 0 := X_ne_zero _
  have hfz : f * X 2 ∈ centerIdeal k 3 2 := by
    have h1 : X 2 * q = X 2 * (f * X 2) := by rw [hzq, pow_two]; ring
    rwa [mul_left_cancel₀ hz h1] at hq
  have hf' : f ∈ centerIdeal k 3 2 :=
    ((isPrime_centerIdeal_two k).mem_or_mem hfz).resolve_right (X_two_notMem_centerIdeal_two k)
  exact Ideal.mem_span_singleton_mul.mpr ⟨f, hf', mul_comm _ _⟩

/-- In the charts of `x` and `y` the total transform of `C` is the exceptional ideal, whose
saturation is everything. -/
theorem colon_map_of_lt_le (j : Fin 3) (hj : j.val < 2) :
    (totalChart k j).colon (↑(excChart k j ^ 2) : Set (MvPolynomial (Fin 3) k)) ≤
      (totalChart k j).colon (↑(excChart k j) : Set (MvPolynomial (Fin 3) k)) := by
  rw [totalChart, excChart, map_centerIdeal_two_subst_of_lt k j hj, map_centerIdeal_three_subst]
  intro f _
  exact Submodule.mem_colon.mpr fun p hp => Ideal.mul_mem_left _ f hp

/-- The saturation of the total transform of `C` by the exceptional ideal stops at the first step
on every chart of `B_p 𝔸³` (the `(z)`-saturation on the chart of `z`, trivially on the others). -/
theorem colon_map_le (j : Fin 3) :
    (totalChart k j).colon (↑(excChart k j ^ 2) : Set (MvPolynomial (Fin 3) k)) ≤
      (totalChart k j).colon (↑(excChart k j) : Set (MvPolynomial (Fin 3) k)) := by
  by_cases hj : j.val < 2
  · exact colon_map_of_lt_le k j hj
  · have h2 : j = 2 := by
      ext
      have := j.isLt
      omega
    subst h2
    exact colon_map_two_le k

end Hironaka.Sequence.Remark33
