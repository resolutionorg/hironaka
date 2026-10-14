/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineAlgebra
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# The model case: blowing up a coordinate subspace

For `R = A[xᵢ : i ∈ σ]`, `I = (xᵢ : i ∈ S)` and `j ∈ S`, the chart `R[I/xⱼ]` is again a polynomial
ring over `A` in the variables `σ`, via `xᵢ/xⱼ ↦ xᵢ` for `i ∈ S`, `i ≠ j`, `xⱼ ↦ xⱼ` and `xᵢ ↦ xᵢ`
for `i ∉ S`; under this identification the inclusion `R → R[I/xⱼ]` is Hauser's chart map `πⱼ`:
`xᵢ ↦ xᵢ xⱼ` for `i ∈ S`, `i ≠ j`, and `xᵢ ↦ xᵢ` otherwise [Hau14, Definition 4.12 and
Example 4.42].

## Main declarations

* `Hironaka.BlowUp.affineBlowUpAlgebra.coordinateSubspaceEquiv A S j :
    affineBlowUpAlgebra (Ideal.span (X '' S)) (X (R := A) j) ≃ₐ[A] MvPolynomial σ A`, with
  `coordinateSubspaceEquiv_frac`, `coordinateSubspaceEquiv_algebraMap_X_of_mem`,
  `coordinateSubspaceEquiv_algebraMap_X_of_not` and `coordinateSubspaceEquiv_unique`.

## The argument

Let `L = R[1/xⱼ]`.  The `A`-algebra map `α : A[xᵢ] → L`, `xᵢ ↦ xᵢ/xⱼ` (`i ∈ S`, `i ≠ j`),
`xᵢ ↦ xᵢ` otherwise, and the chart map `γ : A[xᵢ] → R → L`, `xᵢ ↦ xᵢ xⱼ` (`i ∈ S`, `i ≠ j`),
`xᵢ ↦ xᵢ` otherwise, both send `xⱼ` to the unit `xⱼ` of `L` and so extend to endomorphisms
`α', γ'` of `L`, which are inverse to each other (check on the generators: `α'γ'(xᵢ) =
(xᵢ/xⱼ) xⱼ = xᵢ` and `γ'α'(xᵢ) = (xᵢ xⱼ)/xⱼ = xᵢ`).  Hence `α'` is bijective, and `α = α' ∘ (R → L)`
is injective because `xⱼ` is a nonzerodivisor of the polynomial ring.  The image of `α` is
`R[I/xⱼ]`: its generators land there, and conversely `R[I/xⱼ]` is generated over `R` by the
`xᵢ/xⱼ = α(xᵢ)`, `i ∈ S`, while `R` itself is the image of `γ`, i.e. `α ∘ (substitution)`.  So
`α` is an isomorphism of `A[xᵢ]` onto `R[I/xⱼ]`, and the equivalence is its inverse
[Hau14, Example 4.42].

## Conventions

The variable type `σ` and the centre `S ⊆ σ` are arbitrary (Hauser has `n` variables and
`S = {1, …, k}`); the proofs do not use finiteness.  The hypothesis `j ∈ S` of the source is not
used by the construction (for `j ∉ S` the same map is still an isomorphism, with `xⱼ ∉ I`).

## Boundary cases

`S = {j}`: `I = (xⱼ)` and `R[I/xⱼ] ≃ R` is the identity on the variables.  `S = univ`: every
variable except `xⱼ` becomes a ratio.  `A = 0`: everything is the zero ring.
-/

@[expose] public section

universe u v w

namespace AlgebraicGeometry.affineBlowUpAlgebra

open MvPolynomial IsLocalization.Away

variable (A : Type u) [CommRing A] {σ : Type v} (S : Set σ) (j : σ)

/-- Two `A`-algebra maps out of `R[I/a]`, for an `A`-algebra `R`, agreeing on the image of `R` and
on the generators `x/a` are equal. -/
theorem algHom_ext_of_tower {R : Type v} [CommRing R] [Algebra A R] {I : Ideal R} {a : R}
    {Q : Type w} [Semiring Q] [Algebra A Q] {φ ψ : affineBlowUpAlgebra I a →ₐ[A] Q}
    (h₁ : ∀ r, φ (algebraMap R (affineBlowUpAlgebra I a) r) =
      ψ (algebraMap R (affineBlowUpAlgebra I a) r))
    (h₂ : ∀ x (hx : x ∈ I), φ (frac hx) = ψ (frac hx)) : φ = ψ := by
  refine AlgHom.ext fun z => ?_
  obtain ⟨z, hz⟩ := z
  induction hz using induction_on with
  | mem x hx => exact h₂ x hx
  | algebraMap r => exact h₁ r
  | add y z hy hz ihy ihz =>
    change φ (⟨y, hy⟩ + ⟨z, hz⟩) = ψ (⟨y, hy⟩ + ⟨z, hz⟩)
    rw [map_add, map_add, ihy, ihz]
  | mul y z hy hz ihy ihz =>
    change φ (⟨y, hy⟩ * ⟨z, hz⟩) = ψ (⟨y, hy⟩ * ⟨z, hz⟩)
    rw [map_mul, map_mul, ihy, ihz]

/-- The centre `I = (xᵢ : i ∈ S)`. -/
noncomputable def coordinateIdeal : Ideal (MvPolynomial σ A) := Ideal.span (X '' S)

theorem X_mem_coordinateIdeal {i : σ} (hi : i ∈ S) :
    (X i : MvPolynomial σ A) ∈ coordinateIdeal A S :=
  Ideal.subset_span ⟨i, hi, rfl⟩

open scoped Classical in
/-- The substitution `xᵢ ↦ xᵢ xⱼ` (`i ∈ S`, `i ≠ j`), `xᵢ ↦ xᵢ` otherwise: Hauser's chart map
`πⱼ` [Hau14, Definition 4.12] on the polynomial ring. -/
noncomputable def chartSubst : MvPolynomial σ A →ₐ[A] MvPolynomial σ A :=
  aeval fun i : σ => (if i ∈ S ∧ i ≠ j then X (R := A) i * X (R := A) j else X i : MvPolynomial σ A)

open scoped Classical in
/-- The map `α : A[xᵢ] → R[1/xⱼ]`, `xᵢ ↦ xᵢ/xⱼ` (`i ∈ S`, `i ≠ j`), `xᵢ ↦ xᵢ` otherwise. -/
noncomputable def modelAux :
    MvPolynomial σ A →ₐ[A] Localization.Away (X j : MvPolynomial σ A) :=
  aeval fun i : σ => (if i ∈ S ∧ i ≠ j then
    algebraMap (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A)) (X (R := A) i) *
      invSelf (X j : MvPolynomial σ A)
  else algebraMap (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A)) (X (R := A) i) :
    Localization.Away (X j : MvPolynomial σ A))

theorem modelAux_X_of_mem {i : σ} (hi : i ∈ S) (hij : i ≠ j) :
    modelAux A S j (X (R := A) i) =
      algebraMap (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A)) (X (R := A) i) *
        invSelf (X j : MvPolynomial σ A) := by
  rw [modelAux, aeval_X, ite_eq_left ⟨hi, hij⟩]

theorem modelAux_X_of_not {i : σ} (h : ¬(i ∈ S ∧ i ≠ j)) :
    modelAux A S j (X (R := A) i) =
      algebraMap (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A))
        (X (R := A) i) := by
  rw [modelAux, aeval_X, ite_eq_right h]

theorem modelAux_X_self :
    modelAux A S j (X (R := A) j) =
      algebraMap (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A)) (X (R := A) j) :=
  modelAux_X_of_not A S j fun h => h.2 rfl

theorem chartSubst_X_of_mem {i : σ} (hi : i ∈ S) (hij : i ≠ j) :
    chartSubst A S j (X (R := A) i) = X (R := A) i * X j := by
  rw [chartSubst, aeval_X, ite_eq_left ⟨hi, hij⟩]

theorem chartSubst_X_of_not {i : σ} (h : ¬(i ∈ S ∧ i ≠ j)) :
    chartSubst A S j (X (R := A) i) = X i := by
  rw [chartSubst, aeval_X, ite_eq_right h]

theorem chartSubst_X_self : chartSubst A S j (X (R := A) j) = X j :=
  chartSubst_X_of_not A S j fun h => h.2 rfl

/-- `α ∘ πⱼ` is the localization map `R → R[1/xⱼ]`. -/
theorem modelAux_comp_chartSubst :
    (modelAux A S j).comp (chartSubst A S j) =
      IsScalarTower.toAlgHom A (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A)) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  by_cases h : i ∈ S ∧ i ≠ j
  · rw [chartSubst_X_of_mem A S j h.1 h.2, map_mul, modelAux_X_of_mem A S j h.1 h.2,
      modelAux_X_self, mul_assoc, mul_comm (invSelf _), mul_invSelf, mul_one]
  · rw [chartSubst_X_of_not A S j h, modelAux_X_of_not A S j h]

theorem modelAux_chartSubst (p : MvPolynomial σ A) :
    modelAux A S j (chartSubst A S j p) = algebraMap _ _ p :=
  AlgHom.congr_fun (modelAux_comp_chartSubst A S j) p

theorem isUnit_modelAux_X : IsUnit (modelAux A S j (X (R := A) j)) := by
  rw [modelAux_X_self]; exact algebraMap_isUnit _

/-- The extension of `α` to an endomorphism of `R[1/xⱼ]`. -/
noncomputable def modelAux' :
    Localization.Away (X j : MvPolynomial σ A) →ₐ[A] Localization.Away (X j : MvPolynomial σ A) :=
  IsLocalization.Away.liftAlgHom (X (R := A) j) (f := modelAux A S j) (isUnit_modelAux_X A S j)

theorem modelAux'_algebraMap (p : MvPolynomial σ A) :
    modelAux' A S j (algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j)) p) =
      modelAux A S j p := by
  rw [modelAux', IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The extension of `πⱼ` to an endomorphism of `R[1/xⱼ]`. -/
noncomputable def chartSubst' :
    Localization.Away (X j : MvPolynomial σ A) →ₐ[A] Localization.Away (X j : MvPolynomial σ A) :=
  IsLocalization.Away.liftAlgHom (X (R := A) j)
    (f := (IsScalarTower.toAlgHom A (MvPolynomial σ A)
      (Localization.Away (X j : MvPolynomial σ A))).comp (chartSubst A S j))
    (by
      rw [AlgHom.comp_apply, chartSubst_X_self, IsScalarTower.coe_toAlgHom']
      exact algebraMap_isUnit _)

theorem chartSubst'_algebraMap (p : MvPolynomial σ A) :
    chartSubst' A S j (algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j)) p) =
      algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j)) (chartSubst A S j p) := by
  rw [chartSubst', IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

theorem chartSubst'_invSelf :
    chartSubst' A S j (invSelf (X (R := A) j)) = invSelf (X (R := A) j) := by
  have hu : IsUnit (algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j))
      (X (R := A) j)) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (X (R := A) j)) (X (R := A) j)
  apply hu.mul_left_injective
  change chartSubst' A S j (invSelf (X (R := A) j)) *
      algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j)) (X (R := A) j) =
    invSelf (X (R := A) j) *
      algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j)) (X (R := A) j)
  have h := chartSubst'_algebraMap A S j (X (R := A) j)
  rw [chartSubst_X_self] at h
  rw [mul_comm (invSelf _), mul_invSelf, ← h, ← map_mul, mul_comm, mul_invSelf, map_one]

theorem modelAux'_chartSubst' (z : Localization.Away (X j : MvPolynomial σ A)) :
    modelAux' A S j (chartSubst' A S j z) = z := by
  have hcomp : (((modelAux' A S j).comp (chartSubst' A S j) :
      Localization.Away (X (R := A) j) →ₐ[A] Localization.Away (X (R := A) j)) :
        Localization.Away (X (R := A) j) →+* Localization.Away (X (R := A) j)).comp
      (algebraMap (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A))) =
      (RingHom.id _).comp
        (algebraMap (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A))) :=
    RingHom.ext fun p => by
      change modelAux' A S j (chartSubst' A S j
          (algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j)) p)) =
        algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j)) p
      rw [chartSubst'_algebraMap, modelAux'_algebraMap, modelAux_chartSubst]
  exact RingHom.congr_fun
    (IsLocalization.ringHom_ext (Submonoid.powers (X j : MvPolynomial σ A)) hcomp) z

theorem chartSubst'_comp_modelAux :
    (chartSubst' A S j).comp (modelAux A S j) =
      IsScalarTower.toAlgHom A (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A)) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  by_cases h : i ∈ S ∧ i ≠ j
  · rw [modelAux_X_of_mem A S j h.1 h.2, map_mul, chartSubst'_algebraMap,
      chartSubst_X_of_mem A S j h.1 h.2, chartSubst'_invSelf, map_mul, mul_assoc, mul_invSelf,
      mul_one]
  · rw [modelAux_X_of_not A S j h, chartSubst'_algebraMap, chartSubst_X_of_not A S j h]

theorem chartSubst'_modelAux' (z : Localization.Away (X j : MvPolynomial σ A)) :
    chartSubst' A S j (modelAux' A S j z) = z := by
  have hcomp : (((chartSubst' A S j).comp (modelAux' A S j) :
      Localization.Away (X (R := A) j) →ₐ[A] Localization.Away (X (R := A) j)) :
        Localization.Away (X (R := A) j) →+* Localization.Away (X (R := A) j)).comp
      (algebraMap (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A))) =
      (RingHom.id _).comp
        (algebraMap (MvPolynomial σ A) (Localization.Away (X j : MvPolynomial σ A))) :=
    RingHom.ext fun p => by
      change chartSubst' A S j (modelAux' A S j
          (algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j)) p)) =
        algebraMap (MvPolynomial σ A) (Localization.Away (X (R := A) j)) p
      rw [modelAux'_algebraMap]
      exact AlgHom.congr_fun (chartSubst'_comp_modelAux A S j) p
  exact RingHom.congr_fun
    (IsLocalization.ringHom_ext (Submonoid.powers (X j : MvPolynomial σ A)) hcomp) z

theorem modelAux'_injective : Function.Injective (modelAux' A S j) :=
  Function.LeftInverse.injective (chartSubst'_modelAux' A S j)

/-- `α` is injective: `xⱼ` is a nonzerodivisor of the polynomial ring, and `α` extends to the
automorphism `α'` of `R[1/xⱼ]`. -/
theorem modelAux_injective : Function.Injective (modelAux A S j) := by
  intro p q h
  apply IsLocalization.injective (M := Submonoid.powers (X j : MvPolynomial σ A))
    (Localization.Away (X j : MvPolynomial σ A))
    (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp isRegular_X))
  apply modelAux'_injective A S j
  rwa [modelAux'_algebraMap, modelAux'_algebraMap]

theorem modelAux_mem (p : MvPolynomial σ A) :
    modelAux A S j p ∈ affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [modelAux, aeval_C, IsScalarTower.algebraMap_apply A (MvPolynomial σ A)]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    by_cases h : i ∈ S ∧ i ≠ j
    · rw [modelAux_X_of_mem A S j h.1 h.2]
      exact mul_invSelf_mem (X_mem_coordinateIdeal A S h.1)
    · rw [modelAux_X_of_not A S j h]
      exact Subalgebra.algebraMap_mem _ _

/-- `α` with values in `R[I/xⱼ]`. -/
noncomputable def modelHom :
    MvPolynomial σ A →ₐ[A] affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) where
  toFun p := ⟨modelAux A S j p, modelAux_mem A S j p⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by
    change modelAux A S j (algebraMap A (MvPolynomial σ A) r) = _
    rw [AlgHom.commutes]; rfl)

@[simp]
theorem coe_modelHom (p : MvPolynomial σ A) :
    (modelHom A S j p : Localization.Away (X j : MvPolynomial σ A)) = modelAux A S j p := rfl

theorem modelHom_injective : Function.Injective (modelHom A S j) := fun _ _ h =>
  modelAux_injective A S j (congrArg Subtype.val h)

theorem exists_modelAux_eq_frac {x : MvPolynomial σ A} (hx : x ∈ coordinateIdeal A S) :
    ∃ p, modelAux A S j p = algebraMap _ _ x * invSelf (X (R := A) j) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    by_cases hij : i = j
    · subst hij
      exact ⟨1, by rw [map_one, mul_invSelf]⟩
    · exact ⟨X (R := A) i, modelAux_X_of_mem A S j hi hij⟩
  | zero => exact ⟨0, by rw [map_zero, map_zero, zero_mul]⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    exact ⟨p + q, by rw [map_add, hp, hq, map_add, add_mul]⟩
  | smul q y _ hy =>
    obtain ⟨p, hp⟩ := hy
    exact ⟨chartSubst A S j q * p, by
      rw [map_mul, hp, modelAux_chartSubst, smul_eq_mul, map_mul, mul_assoc]⟩

theorem modelHom_surjective : Function.Surjective (modelHom A S j) := by
  rintro ⟨z, hz⟩
  suffices h : ∃ p, modelAux A S j p = z from h.imp fun p hp => Subtype.ext hp
  induction hz using induction_on with
  | mem x hx => exact exists_modelAux_eq_frac A S j hx
  | algebraMap q => exact ⟨chartSubst A S j q, modelAux_chartSubst A S j q⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    exact ⟨p + q, by rw [map_add, hp, hq]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    exact ⟨p * q, by rw [map_mul, hp, hq]⟩

/-- The chart `R[I/xⱼ]` of the blow-up of `A[xᵢ : i ∈ σ]` along `(xᵢ : i ∈ S)` is the polynomial
ring `A[xᵢ : i ∈ σ]`, via `xᵢ/xⱼ ↦ xᵢ` for `i ∈ S`, `i ≠ j` [Hau14, Example 4.42]. -/
noncomputable def coordinateSubspaceEquiv :
    affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) ≃ₐ[A] MvPolynomial σ A :=
  (AlgEquiv.ofBijective (modelHom A S j) ⟨modelHom_injective A S j, modelHom_surjective A S j⟩).symm

theorem coordinateSubspaceEquiv_modelHom (p : MvPolynomial σ A) :
    coordinateSubspaceEquiv A S j (modelHom A S j p) = p := by
  rw [coordinateSubspaceEquiv,
    ← AlgEquiv.ofBijective_apply (modelHom A S j)
      ⟨modelHom_injective A S j, modelHom_surjective A S j⟩,
    AlgEquiv.symm_apply_apply]

/-- `xᵢ/xⱼ ↦ xᵢ` for `i ∈ S`, `i ≠ j`. -/
theorem coordinateSubspaceEquiv_frac {i : σ} (hi : i ∈ S) (hij : i ≠ j)
    (hi' : (X i : MvPolynomial σ A) ∈ coordinateIdeal A S) :
    coordinateSubspaceEquiv A S j (frac (a := X (R := A) j) hi') = X i := by
  have : frac (a := X (R := A) j) hi' = modelHom A S j (X (R := A) i) :=
    Subtype.ext (by rw [coe_frac, coe_modelHom, modelAux_X_of_mem A S j hi hij])
  rw [this, coordinateSubspaceEquiv_modelHom]

/-- Under the identification, the inclusion `R → R[I/xⱼ]` is `xᵢ ↦ xᵢ xⱼ` for `i ∈ S`, `i ≠ j`:
Hauser's chart map `πⱼ` [Hau14, Definition 4.12]. -/
theorem coordinateSubspaceEquiv_algebraMap_X_of_mem {i : σ} (hi : i ∈ S) (hij : i ≠ j) :
    coordinateSubspaceEquiv A S j (algebraMap (MvPolynomial σ A) _ (X (R := A) i)) =
      X (R := A) i * X j := by
  have : algebraMap (MvPolynomial σ A) (affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j))
      (X (R := A) i) = modelHom A S j (X (R := A) i * X (R := A) j) := Subtype.ext (by
    rw [Subalgebra.coe_algebraMap, coe_modelHom, map_mul, modelAux_X_of_mem A S j hi hij,
      modelAux_X_self, mul_assoc, mul_comm (invSelf _), mul_invSelf, mul_one])
  rw [this, coordinateSubspaceEquiv_modelHom]

/-- The inclusion `R → R[I/xⱼ]` is `xᵢ ↦ xᵢ` for `i = j` and for `i ∉ S`. -/
theorem coordinateSubspaceEquiv_algebraMap_X_of_not {i : σ} (h : ¬(i ∈ S ∧ i ≠ j)) :
    coordinateSubspaceEquiv A S j (algebraMap (MvPolynomial σ A) _ (X (R := A) i)) = X i := by
  have : algebraMap (MvPolynomial σ A) (affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j))
      (X (R := A) i) = modelHom A S j (X (R := A) i) :=
    Subtype.ext (by rw [Subalgebra.coe_algebraMap, coe_modelHom, modelAux_X_of_not A S j h])
  rw [this, coordinateSubspaceEquiv_modelHom]

theorem frac_add' {R : Type w} [CommRing R] {I : Ideal R} {a x y : R} (hx : x ∈ I) (hy : y ∈ I) :
    frac (a := a) (I.add_mem hx hy) = frac hx + frac hy :=
  Subtype.ext (by rw [Subalgebra.coe_add, coe_frac, coe_frac, coe_frac, map_add, add_mul])

theorem frac_mul_left' {R : Type w} [CommRing R] {I : Ideal R} {a x : R} (r : R) (hx : x ∈ I) :
    frac (a := a) (I.mul_mem_left r hx) = algebraMap R _ r * frac hx :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, coe_frac, coe_frac, map_mul, mul_assoc])

theorem frac_zero' {R : Type w} [CommRing R] {I : Ideal R} {a : R} :
    frac (a := a) I.zero_mem = 0 :=
  Subtype.ext (by rw [coe_frac, map_zero, zero_mul]; rfl)

theorem frac_self' {R : Type w} [CommRing R] {I : Ideal R} {a : R} (ha : a ∈ I) :
    frac (a := a) ha = 1 :=
  Subtype.ext (by rw [coe_frac, mul_invSelf]; rfl)

/-- The identification is the unique `A`-algebra isomorphism with the values of
[Hau14, Example 4.42] on the variables. -/
theorem coordinateSubspaceEquiv_unique
    (e : affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) ≃ₐ[A] MvPolynomial σ A)
    (h₁ : ∀ i ∈ S, i ≠ j → ∀ hi : (X i : MvPolynomial σ A) ∈ coordinateIdeal A S,
      e (frac hi) = X (R := A) i)
    (h₂ : ∀ i ∈ S, i ≠ j →
      e (algebraMap (MvPolynomial σ A) _ (X (R := A) i)) = X (R := A) i * X (R := A) j)
    (h₃ : e (algebraMap (MvPolynomial σ A) _ (X (R := A) j)) = X (R := A) j)
    (h₄ : ∀ i ∉ S, e (algebraMap (MvPolynomial σ A) _ (X (R := A) i)) = X (R := A) i) :
    e = coordinateSubspaceEquiv A S j := by
  have hgen : (e : affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) →ₐ[A]
      MvPolynomial σ A).comp
      (IsScalarTower.toAlgHom A (MvPolynomial σ A) _) =
      (coordinateSubspaceEquiv A S j :
        affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) →ₐ[A] MvPolynomial σ A).comp
        (IsScalarTower.toAlgHom A (MvPolynomial σ A) _) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_toAlgHom,
      AlgEquiv.coe_toAlgHom]
    by_cases h : i ∈ S ∧ i ≠ j
    · rw [h₂ i h.1 h.2, coordinateSubspaceEquiv_algebraMap_X_of_mem A S j h.1 h.2]
    · rw [coordinateSubspaceEquiv_algebraMap_X_of_not A S j h]
      by_cases hi : i ∈ S
      · have hij : i = j := by
          by_contra hne
          exact h ⟨hi, hne⟩
        subst hij
        exact h₃
      · exact h₄ i hi
  have key : (e : affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) →ₐ[A] MvPolynomial σ A) =
      (coordinateSubspaceEquiv A S j :
        affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) →ₐ[A] MvPolynomial σ A) := by
    refine algHom_ext_of_tower A (fun r => AlgHom.congr_fun hgen r) fun x hx => ?_
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      by_cases hij : i = j
      · subst hij
        have h1 : frac (a := X (R := A) i) (X_mem_coordinateIdeal A S hi) = 1 := frac_self' _
        rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom]
        change e (frac (X_mem_coordinateIdeal A S hi)) =
          coordinateSubspaceEquiv A S i (frac (X_mem_coordinateIdeal A S hi))
        rw [h1, map_one, map_one]
      · rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom]
        exact (h₁ i hi hij _).trans (coordinateSubspaceEquiv_frac A S j hi hij _).symm
    | zero => rw [frac_zero' (I := coordinateIdeal A S), map_zero, map_zero]
    | add y z hy hz ihy ihz =>
      rw [frac_add' (I := coordinateIdeal A S) hy hz, map_add, map_add, ihy, ihz]
    | smul q y hy ihy =>
      change (e : affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) →ₐ[A] MvPolynomial σ A)
          (frac (a := X (R := A) j) (Ideal.mul_mem_left (coordinateIdeal A S) q hy)) =
        (coordinateSubspaceEquiv A S j :
          affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) →ₐ[A] MvPolynomial σ A)
          (frac (a := X (R := A) j) (Ideal.mul_mem_left (coordinateIdeal A S) q hy))
      rw [frac_mul_left' (I := coordinateIdeal A S) q hy, map_mul, map_mul, ihy,
        show (e : affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) →ₐ[A] MvPolynomial σ A)
            (algebraMap (MvPolynomial σ A) _ q) =
          (coordinateSubspaceEquiv A S j :
            affineBlowUpAlgebra (coordinateIdeal A S) (X (R := A) j) →ₐ[A] MvPolynomial σ A)
            (algebraMap (MvPolynomial σ A) _ q) from AlgHom.congr_fun hgen q]
  exact AlgEquiv.ext fun z => AlgHom.congr_fun key z

end AlgebraicGeometry.affineBlowUpAlgebra
