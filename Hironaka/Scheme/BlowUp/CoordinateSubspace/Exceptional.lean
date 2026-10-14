/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Exceptional
public import Hironaka.Scheme.BlowUp.CoordinateSubspace.Charts
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth
import Hironaka.Scheme.BlowUp.InverseImage

/-!
# The exceptional divisor of the model blow-up in a chart

The exceptional divisor `E = π⁻¹(Z)` [Hau14, Definition 4.7], a hypersurface
[Hau14, Example 5.9], computed in the chart `U_j`: the exceptional ideal `I·𝒪_B` pulls back along
`U_j` to the ideal sheaf of `(x_j)` — on the chart of `x_j` the exceptional ideal is `(x_j)` in
`A[x][L/x_j]` (`affineBlowUp.comap_exceptionalIdeal_chart`), and `x_j ↦ x_j` under the
identification with `A[x]`.  The quotient `A[x]/(x_j)` is the polynomial ring over `A` in the
remaining variables, through Mathlib's `killCompl` (kill the variable `x_j`), whose kernel is
`(x_j)`: a polynomial is congruent modulo `(x_j)` to the renaming of its image, because a monomial
either avoids `x_j` (and is recovered from its image) or is divisible by `x_j`.  Hence
`F ∩ U_j ≅ 𝔸^{n-1}_A`, smooth of relative dimension `n - 1` (the standard smoothness of polynomial
rings, `Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth`), and through the chart map `π_j` it is
the affine space `𝔸^{r-1}_L` over the centre.  The quotient identifications are used for the
exceptional divisor of blow-ups of smooth centres (`Hironaka.Scheme.Smooth.ExceptionalModel`) and in
the worked examples (`HironakaExamples.Sequence.Remark33Charts`,
`HironakaExamples.OrderReduction.Example106BlowUp`).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory MvPolynomial Scheme.IdealSheafData

namespace AlgebraicGeometry.CoordinateSubspace

open affineBlowUpAlgebra

variable (A : Type u) [CommRing A] (n r : ℕ)

/-- In the chart `U_j` the exceptional divisor is `V(x_j)` [Hau14, Definition 4.7]. -/
theorem comap_exceptionalIdeal_modelChart (j : Fin n) (hj : j.val < r) :
    (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).comap (modelChart A n r j hj) =
      Scheme.IdealSheafData.ofIdealTop ((Ideal.span {(X j : MvPolynomial (Fin n) A)}).map
        (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) A))).inv.hom) := by
  rw [modelChart, Scheme.IdealSheafData.comap_comp, affineBlowUp.comap_exceptionalIdeal_chart,
      Scheme.IdealSheafData.comap_ofIdealTop_Spec_map,
    Ideal.map_span, Set.image_singleton]
  congr 3
  have := congrArg (fun φ : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) A => φ (X j))
    (chartRingIso_hom_comp_algebraMap A n r j)
  simpa [chartSubst_X_self] using this

section KillVariables

variable {n} (p : Fin n → Prop)

/-- Killing the variables `x_i` with `¬ p i`: the `A`-algebra map
`A[x_0, …, x_{n-1}] → A[x_i : p i]` (Mathlib's `killCompl` for the inclusion of the subtype). -/
noncomputable abbrev killPred : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial {i : Fin n // p i} A :=
  killCompl
    (Subtype.val_injective : Function.Injective (Subtype.val : {i : Fin n // p i} → Fin n))

theorem killPred_X_of {i : Fin n} (h : p i) : killPred A p (X i) = X ⟨i, h⟩ := by
  rw [killPred, killCompl, aeval_X, dite_eq_left ⟨⟨i, h⟩, rfl⟩]
  congr 1
  exact Equiv.ofInjective_symm_apply Subtype.val_injective ⟨i, h⟩

theorem killPred_X_of_not {i : Fin n} (h : ¬ p i) : killPred A p (X i) = 0 := by
  rw [killPred, killCompl, aeval_X, dite_eq_right]
  rintro ⟨⟨i', hi'⟩, h'⟩
  exact h (h' ▸ hi')

theorem killPred_surjective : Function.Surjective (killPred A p) := fun q =>
  ⟨rename Subtype.val q, killCompl_rename_app _ q⟩

/-- A polynomial is congruent modulo `(x_i : ¬ p i)` to the renaming of its image under
`killPred`. -/
theorem sub_rename_killPred_mem (q : MvPolynomial (Fin n) A) :
    q - rename Subtype.val (killPred A p q) ∈ coordinateIdeal A {i | ¬ p i} := by
  induction q using MvPolynomial.induction_on' with
  | monomial v c =>
    by_cases hv :
        (↑v.support : Set (Fin n)) ⊆ Set.range (Subtype.val : {i : Fin n // p i} → Fin n)
    · rw [killPred, killCompl_monomial_eq_monomial_comapDomain_of_subset _ _ hv, rename_monomial,
        Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective _ hv, sub_self]
      exact zero_mem _
    · rw [killPred, killCompl_monomial_eq_zero_of_not_subset _ _ hv, map_zero, sub_zero]
      obtain ⟨a, ha, hnot⟩ := Set.not_subset.mp hv
      have hpa : ¬ p a := fun h => hnot ⟨⟨a, h⟩, rfl⟩
      obtain ⟨q, hq⟩ : (X a : MvPolynomial (Fin n) A) ∣ monomial v c :=
        X_dvd_monomial.mpr (Or.inr (Finsupp.mem_support_iff.mp ha))
      rw [hq]
      exact (coordinateIdeal A {i | ¬ p i}).mul_mem_right q (Ideal.subset_span ⟨a, hpa, rfl⟩)
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq

theorem ker_killPred :
    RingHom.ker (killPred A p : MvPolynomial (Fin n) A →+* MvPolynomial {i : Fin n // p i} A) =
      coordinateIdeal A {i | ¬ p i} := by
  apply le_antisymm
  · intro q hq
    rw [RingHom.mem_ker, RingHom.coe_coe] at hq
    have := sub_rename_killPred_mem A p q
    rwa [hq, map_zero, sub_zero] at this
  · rw [coordinateIdeal, Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.coe_coe]
    exact killPred_X_of_not A p hi

/-- `A[x]/(x_i : ¬ p i) ≃ A[x_i : p i]`, `x_i ↦ x_i`. -/
noncomputable def quotientCoordinateIdealAlgEquiv :
    (MvPolynomial (Fin n) A ⧸ coordinateIdeal A {i | ¬ p i}) ≃ₐ[A]
      MvPolynomial {i : Fin n // p i} A :=
  (Ideal.quotientEquivAlgOfEq A (ker_killPred A p).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (killPred_surjective A p))

theorem quotientCoordinateIdealAlgEquiv_mk_X {i : Fin n} (h : p i) :
    quotientCoordinateIdealAlgEquiv A p (Ideal.Quotient.mk _ (X i)) = X ⟨i, h⟩ := by
  change Ideal.quotientKerAlgEquivOfSurjective (killPred_surjective A p)
    (Ideal.quotientEquivAlgOfEq A (ker_killPred A p).symm (Ideal.Quotient.mk _ (X i))) = X ⟨i, h⟩
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact (Ideal.quotientKerAlgEquivOfSurjective_mk (killPred_surjective A p) (X i)).trans
    (killPred_X_of A p h)

end KillVariables

section KillVariable

variable {n} (j : Fin n)

/-- Killing the variable `x_j`: the `A`-algebra map `A[x_0, …, x_{n-1}] → A[x_i : i ≠ j]`. -/
noncomputable abbrev killX : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial {i : Fin n // i ≠ j} A :=
  killPred A (· ≠ j)

theorem killX_X_of_ne {i : Fin n} (h : i ≠ j) : killX A j (X i) = X ⟨i, h⟩ :=
  killPred_X_of A (· ≠ j) h

theorem killX_X_self : killX A j (X j) = 0 :=
  killPred_X_of_not A (· ≠ j) fun h => h rfl

theorem killX_surjective : Function.Surjective (killX A j) := killPred_surjective A (· ≠ j)

theorem ker_killX :
    RingHom.ker (killX A j : MvPolynomial (Fin n) A →+* MvPolynomial {i : Fin n // i ≠ j} A) =
      Ideal.span {(X j : MvPolynomial (Fin n) A)} := by
  rw [killX, ker_killPred, show {i : Fin n | ¬ i ≠ j} = {j} from Set.ext fun _ => not_not,
    coordinateIdeal, Set.image_singleton]

/-- `A[x]/(x_j) ≃ A[x_i : i ≠ j]`, `x_i ↦ x_i`. -/
noncomputable def quotientSpanXAlgEquiv :
    (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)}) ≃ₐ[A]
      MvPolynomial {i : Fin n // i ≠ j} A :=
  (Ideal.quotientEquivAlgOfEq A (ker_killX A j).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (killX_surjective A j))

theorem quotientSpanXAlgEquiv_mk_X {i : Fin n} (h : i ≠ j) :
    quotientSpanXAlgEquiv A j (Ideal.Quotient.mk _ (X i)) = X ⟨i, h⟩ := by
  change Ideal.quotientKerAlgEquivOfSurjective (killX_surjective A j)
    (Ideal.quotientEquivAlgOfEq A (ker_killX A j).symm (Ideal.Quotient.mk _ (X i))) = X ⟨i, h⟩
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact (Ideal.quotientKerAlgEquivOfSurjective_mk (killX_surjective A j) (X i)).trans
    (killX_X_of_ne A j h)

theorem exists_algEquiv_quotient_span_X :
    ∃ e : (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)}) ≃ₐ[A]
        MvPolynomial {i : Fin n // i ≠ j} A,
      ∀ i (h : i ≠ j), e (Ideal.Quotient.mk _ (X i)) = X ⟨i, h⟩ :=
  ⟨quotientSpanXAlgEquiv A j, fun _ h => quotientSpanXAlgEquiv_mk_X A j h⟩

theorem card_ne : Nat.card {i : Fin n // i ≠ j} = n - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]

/-- `F ∩ U_j ≅ 𝔸^{n-1}_A` is smooth over `A` of relative dimension `n - 1`. -/
theorem smoothOfRelativeDimension_quotient_span_X :
    SmoothOfRelativeDimension (n - 1) (Spec.map (CommRingCat.ofHom
      (algebraMap A (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)})))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{u} (n - 1)),
    CommRingCat.hom_ofHom]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  have h := ringHom_isStandardSmoothOfRelativeDimension_algebraMap_mvPolynomial A
    {i : Fin n // i ≠ j}
  rw [card_ne] at h
  exact isStandardSmoothOfRelativeDimension_algebraMap_of_algEquiv
    (quotientSpanXAlgEquiv A j).symm h

end KillVariable

section Center

theorem centerIdeal_eq_coordinateIdeal_not_not :
    centerIdeal A n r = coordinateIdeal A {i : Fin n | ¬ ¬ i.val < r} :=
  congrArg (coordinateIdeal A) (Set.ext fun _ => ⟨not_not_intro, not_not.mp⟩)

/-- `A[x]/I ≃ A[x_i : r ≤ i]`: the coordinate subspace `L` is `𝔸^{n-r}_A`. -/
noncomputable def quotientCenterAlgEquiv :
    (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) ≃ₐ[A]
      MvPolynomial {i : Fin n // ¬ i.val < r} A :=
  (Ideal.quotientEquivAlgOfEq A (centerIdeal_eq_coordinateIdeal_not_not A n r)).trans
    (quotientCoordinateIdealAlgEquiv A fun i => ¬ i.val < r)

theorem quotientCenterAlgEquiv_mk_X {i : Fin n} (h : ¬ i.val < r) :
    quotientCenterAlgEquiv A n r (Ideal.Quotient.mk _ (X i)) = X ⟨i, h⟩ := by
  rw [quotientCenterAlgEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact quotientCoordinateIdealAlgEquiv_mk_X A _ h

variable (j : Fin n) (hj : j.val < r)

/-- The variables `x_i`, `i ≠ j`, split into the fibre directions `i < r` and the directions
`r ≤ i` of the base `L`. -/
def splitVars :
    {i : Fin n // i.val < r ∧ i ≠ j} ⊕ {i : Fin n // ¬ i.val < r} ≃ {i : Fin n // i ≠ j} where
  toFun := Sum.elim (fun i => ⟨i.1, i.2.2⟩) fun i => ⟨i.1, fun h => i.2 (by rw [h]; exact hj)⟩
  invFun i := if h : i.1.val < r then Sum.inl ⟨i.1, h, i.2⟩ else Sum.inr ⟨i.1, h⟩
  left_inv := by
    rintro (i | i)
    · exact dite_eq_left i.2.1
    · exact dite_eq_right i.2
  right_inv i := by
    by_cases h : i.1.val < r
    · exact congrArg _ (dite_eq_left h)
    · exact congrArg _ (dite_eq_right h)

theorem splitVars_symm_of_lt {i : Fin n} (hij : i ≠ j) (h : i.val < r) :
    (splitVars n r j hj).symm ⟨i, hij⟩ = Sum.inl ⟨i, h, hij⟩ := dite_eq_left h

theorem splitVars_symm_of_not_lt {i : Fin n} (hij : i ≠ j) (h : ¬ i.val < r) :
    (splitVars n r j hj).symm ⟨i, hij⟩ = Sum.inr ⟨i, h⟩ := dite_eq_right h

/-- `A[x]/(x_j) ≃ (A[x]/I)[x_i : i < r, i ≠ j]` as `A`-algebras. -/
noncomputable def fibreAlgEquiv :
    (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)}) ≃ₐ[A]
      MvPolynomial {i : Fin n // i.val < r ∧ i ≠ j} (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) :=
  (quotientSpanXAlgEquiv A j).trans <| (renameEquiv A (splitVars n r j hj).symm).trans <|
    (sumAlgEquiv A _ _).trans <| mapAlgEquiv _ (quotientCenterAlgEquiv A n r).symm

theorem fibreAlgEquiv_mk_X_of {i : Fin n} (h : i.val < r ∧ i ≠ j) :
    fibreAlgEquiv A n r j hj (Ideal.Quotient.mk _ (X i)) = X ⟨i, h⟩ := by
  rw [fibreAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    quotientSpanXAlgEquiv_mk_X A j h.2]
  change mapAlgEquiv _ _ (sumAlgEquiv A _ _ (rename _ (X _))) = _
  rw [rename_X, splitVars_symm_of_lt n r j hj h.2 h.1, sumAlgEquiv_X_inl, mapAlgEquiv_apply, map_X]

theorem fibreAlgEquiv_mk_X_of_not_lt {i : Fin n} (h : ¬ i.val < r) :
    fibreAlgEquiv A n r j hj (Ideal.Quotient.mk _ (X i)) = C (Ideal.Quotient.mk _ (X i)) := by
  have hij : i ≠ j := fun e => h (by rw [e]; exact hj)
  rw [fibreAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    quotientSpanXAlgEquiv_mk_X A j hij]
  change mapAlgEquiv _ _ (sumAlgEquiv A _ _ (rename _ (X _))) = _
  rw [rename_X, splitVars_symm_of_not_lt n r j hj hij h, sumAlgEquiv_X_inr, mapAlgEquiv_apply,
    map_C]
  congr 1
  rw [RingHom.coe_coe, AlgEquiv.symm_apply_eq, quotientCenterAlgEquiv_mk_X]

/-- The chart map `π_j` followed by `A[x]/(x_j) ≃ (A[x]/I)[x_i : i < r, i ≠ j]` is the structure map
of the polynomial ring over `A[x]/I`: it kills `x_i` for `i < r` and sends `x_i` to the constant
`x_i` for `r ≤ i`. -/
theorem fibreAlgEquiv_comp_mk_comp_chartSubst :
    ((fibreAlgEquiv A n r j hj).toAlgHom.comp
        ((Ideal.Quotient.mkₐ A _).comp (chartSubst A (center n r) j))) =
      (IsScalarTower.toAlgHom A (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) _).comp
        (Ideal.Quotient.mkₐ A (centerIdeal A n r)) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom',
    AlgEquiv.coe_toAlgHom, chartSubst_X]
  by_cases hi : i.val < r
  · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (X_mem_centerIdeal A n r hi), map_zero]
    split_ifs with h
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)), map_zero]
    · have hij : i = j := by
        by_contra hne
        exact h ⟨hi, hne⟩
      rw [hij, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  · rw [ite_eq_right fun h => hi h.1, fibreAlgEquiv_mk_X_of_not_lt A n r j hj hi, algebraMap_eq]

/-- `A[x]/(x_j) ≃ (A[x]/I)[x_i : i < r, i ≠ j]` as algebras over `𝒪(L) = A[x]/I`, the structure of
`A[x]/(x_j)` over `A[x]/I` being through the chart map `π_j` [Hau14, Example 5.9]. -/
noncomputable def fibreAlgEquivOverCenter :
    letI : Algebra (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)
        (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)}) :=
      (Ideal.quotientMap (Ideal.span {(X j : MvPolynomial (Fin n) A)})
        (affineBlowUpAlgebra.chartSubst A (center n r) j).toRingHom
        (centerIdeal_le_comap_chartSubst A n r j)).toAlgebra
    (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)})
        ≃ₐ[MvPolynomial (Fin n) A ⧸ centerIdeal A n r]
      MvPolynomial {i : Fin n // i.val < r ∧ i ≠ j} (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) :=
  letI : Algebra (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)
      (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)}) :=
    (Ideal.quotientMap (Ideal.span {(X j : MvPolynomial (Fin n) A)})
      (affineBlowUpAlgebra.chartSubst A (center n r) j).toRingHom
      (centerIdeal_le_comap_chartSubst A n r j)).toAlgebra
  AlgEquiv.ofRingEquiv (f := (fibreAlgEquiv A n r j hj).toRingEquiv) fun q => by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    have := AlgHom.congr_fun (fibreAlgEquiv_comp_mk_comp_chartSubst A n r j hj) q
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom',
      AlgEquiv.coe_toAlgHom] at this
    rw [RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk]
    exact this

include hj in
/-- **The exceptional divisor in a chart is an affine space over the centre** [Hau14, Example 5.9]:
through the chart map `π_j`, `A[x]/(x_j)` is the polynomial ring over `𝒪(L) = A[x]/I` in the
`r - 1` variables `x_i`, `i < r`, `i ≠ j`. -/
theorem exists_algEquiv_quotient_span_X_over_center :
    letI : Algebra (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)
        (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)}) :=
      (Ideal.quotientMap (Ideal.span {(X j : MvPolynomial (Fin n) A)})
        (affineBlowUpAlgebra.chartSubst A (center n r) j).toRingHom
        (centerIdeal_le_comap_chartSubst A n r j)).toAlgebra
    ∃ e : (MvPolynomial (Fin n) A ⧸ Ideal.span {(X j : MvPolynomial (Fin n) A)})
        ≃ₐ[MvPolynomial (Fin n) A ⧸ centerIdeal A n r]
          MvPolynomial {i : Fin n // i.val < r ∧ i ≠ j}
            (MvPolynomial (Fin n) A ⧸ centerIdeal A n r),
      ∀ i (h : i.val < r ∧ i ≠ j), e (Ideal.Quotient.mk _ (X i)) = X ⟨i, h⟩ :=
  ⟨fibreAlgEquivOverCenter A n r j hj, fun _ h => fibreAlgEquiv_mk_X_of A n r j hj h⟩

end Center

end AlgebraicGeometry.CoordinateSubspace
