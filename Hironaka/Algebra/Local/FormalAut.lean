/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Valuation.ValuationRing
import Hironaka.Algebra.Local.PowerSeries
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Substitution automorphisms of `K⟦X₁, …, Xₙ⟧`

Kollár fixes `R = K⟦x₁, …, xₙ⟧` with maximal ideal `𝔪` and describes its automorphisms
`xᵢ ↦ gᵢ` [Kol07, Notation 93]: they are automorphisms iff the linear parts of the `gᵢ` are
linearly independent, and the *automorphisms of the form `1 + B`* (`B ≤ 𝔪` an ideal) are
those with `gᵢ = xᵢ + λᵢ bᵢ`, `bᵢ ∈ B`.  Proposition 94 characterizes the ideals invariant
under them (`Hironaka/Algebra/Local/Prop94.lean`); through the Cohen structure theorem the
characterization applies to the completed local rings of a smooth variety, where it is used in
the study of hypersurfaces of maximal contact (`Hironaka/Resolution/Algebraic/MaximalContact/`).

This file sets up the vocabulary on Mathlib's `MvPowerSeries.substAlgHom`:

* `linearSubst A`, the family `Xᵢ ↦ ∑ⱼ Aᵢⱼ Xⱼ`;
* `linearPart a`, the matrix `(coeff (single j 1) (a i))ᵢⱼ` of linear parts;
* `shiftSubst i c`, the family `Xᵢ ↦ Xᵢ + c`, `Xⱼ ↦ Xⱼ` for `j ≠ i`;
* `IsOnePlus B g` and `IsInvariantOnePlus I B`.

The theorems (continuous endomorphisms are substitutions; unipotent and linear substitutions
are automorphisms; the criterion of Notation 93; the shift automorphisms of the form `1 + B`)
follow in this file.  The workhorse is the description of the powers of the maximal
ideal, `f ∈ 𝔪^k ↔ k ≤ order f` (`MvPowerSeries.mem_span_range_X_pow_iff_le_order`, in
`Hironaka/Algebra/Local/PowerSeries.lean`).
-/

@[expose] public section

namespace IsLocalRing

open MvPowerSeries IsLocalRing

variable {K : Type*} [Field K] {n : ℕ}

/-- The linear family `Xᵢ ↦ ∑ⱼ Aᵢⱼ Xⱼ` attached to a matrix `A`. -/
noncomputable def linearSubst (A : Matrix (Fin n) (Fin n) K) : Fin n → MvPowerSeries (Fin n) K :=
  fun i => ∑ j, A i j • X j

@[simp]
theorem constantCoeff_linearSubst (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    constantCoeff (linearSubst A i) = 0 := by
  simp [linearSubst, map_sum, MvPowerSeries.smul_eq_C_mul]

/-- The linear family is substitutable. -/
theorem hasSubst_linearSubst (A : Matrix (Fin n) (Fin n) K) : HasSubst (linearSubst A) :=
  hasSubst_of_constantCoeff_zero fun i => constantCoeff_linearSubst A i

/-- The matrix of linear parts `(coeff (single j 1) (a i))ᵢⱼ` of a family `a` ("the linear parts
of the `gᵢ`" of [Kol07, Notation 93]). -/
noncomputable def linearPart (a : Fin n → MvPowerSeries (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => coeff (Finsupp.single j 1) (a i)

@[simp]
theorem linearPart_apply (a : Fin n → MvPowerSeries (Fin n) K) (i j : Fin n) :
    linearPart a i j = coeff (Finsupp.single j 1) (a i) := rfl

/-- The family `Xᵢ ↦ Xᵢ + c`, `Xⱼ ↦ Xⱼ` for `j ≠ i` (Kollár's "`xᵢ ↦ xᵢ + λᵢ bᵢ`",
[Kol07, Notation 93]). -/
noncomputable def shiftSubst (i : Fin n) (c : MvPowerSeries (Fin n) K) :
    Fin n → MvPowerSeries (Fin n) K :=
  Function.update X i (X i + c)

/-- An automorphism `g` of `K⟦X⟧` is *of the form `1 + B`* [Kol07, Notation 93] if it is a
substitution automorphism and `g (Xᵢ) - Xᵢ ∈ B` for every `i`.  Kollár writes these as
`xᵢ ↦ xᵢ + λᵢ bᵢ` (`bᵢ ∈ B`); the two descriptions agree (`λᵢ = 1`, `bᵢ = g (Xᵢ) - Xᵢ`). -/
def IsOnePlus (B : Ideal (MvPowerSeries (Fin n) K))
    (g : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K) : Prop :=
  (∃ (a : Fin n → MvPowerSeries (Fin n) K) (ha : HasSubst a),
    (g : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K) = substAlgHom ha) ∧
    ∀ i, g (X i) - X i ∈ B

/-- `I` is invariant under the automorphisms of the form `1 + B` (clause (1) of
[Kol07, Proposition 94]) if `I.map g ≤ I` for every such `g`.  The primitive is `≤`, not `=`
(the set of such `g` is not obviously closed under inverses; Proposition 94 proves and uses
only `≤`). -/
def IsInvariantOnePlus (I B : Ideal (MvPowerSeries (Fin n) K)) : Prop :=
  ∀ g : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K, IsOnePlus B g →
    I.map (g : MvPowerSeries (Fin n) K →+* MvPowerSeries (Fin n) K) ≤ I

section Subst

variable {a : Fin n → MvPowerSeries (Fin n) K} (ha : HasSubst a)
include ha

/-- Over a field, a substitutable family has zero constant coefficients. -/
theorem constantCoeff_eq_zero_of_hasSubst (i : Fin n) : constantCoeff (a i) = 0 :=
  (ha.const_coeff i).eq_zero

theorem mem_maximalIdeal_of_hasSubst (i : Fin n) :
    a i ∈ maximalIdeal (MvPowerSeries (Fin n) K) := by
  rw [maximalIdeal_eq_span_range_X]
  exact mem_span_range_X_of_constantCoeff_eq_zero (constantCoeff_eq_zero_of_hasSubst ha i)

/-- A substitution maps the maximal ideal into itself. -/
theorem map_maximalIdeal_le_of_hasSubst :
    (maximalIdeal (MvPowerSeries (Fin n) K)).map (substAlgHom (R := K) ha) ≤
      maximalIdeal (MvPowerSeries (Fin n) K) := by
  rw [Ideal.map_le_iff_le_comap]
  conv_lhs => rw [maximalIdeal_eq_span_range_X]
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, substAlgHom_X]
  exact mem_maximalIdeal_of_hasSubst ha i

/-- A substitution maps every power of the maximal ideal into itself. -/
theorem substAlgHom_mem_maximalIdeal_pow {k : ℕ} {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k) :
    substAlgHom (R := K) ha f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k := by
  have h1 : (maximalIdeal (MvPowerSeries (Fin n) K) ^ k).map (substAlgHom (R := K) ha) ≤
      maximalIdeal (MvPowerSeries (Fin n) K) ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_maximalIdeal_le_of_hasSubst ha) k
  exact h1 (Ideal.mem_map_of_mem _ hf)

/-- A substitution maps the maximal ideal into itself, elementwise. -/
theorem substAlgHom_mem_maximalIdeal {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    substAlgHom (R := K) ha f ∈ maximalIdeal (MvPowerSeries (Fin n) K) := by
  have := substAlgHom_mem_maximalIdeal_pow ha (k := 1) (by rwa [pow_one])
  rwa [pow_one] at this

/-- The defect `φ(fg) - fg` of a substitution `φ` on a product. -/
theorem substAlgHom_mul_sub (f g : MvPowerSeries (Fin n) K) :
    substAlgHom (R := K) ha (f * g) - f * g =
      (substAlgHom (R := K) ha f - f) * substAlgHom (R := K) ha g +
        f * (substAlgHom (R := K) ha g - g) := by
  rw [map_mul]; ring

end Subst

/-! ### Unipotent substitutions are automorphisms

Let `φ = substAlgHom ha` with `a i ≡ Xᵢ (mod 𝔪²)`.  The defect `φ f - f` raises the `𝔪`-adic
order: `f ∈ 𝔪^k` implies `φ f - f ∈ 𝔪^(k+1)`.  This is proved by induction on `k` from the two
base facts `φ r - r ∈ 𝔪` (every `r`) and `φ x - x ∈ 𝔪²` (`x ∈ 𝔪`), both by induction over the
generators `Xᵢ` of `𝔪` using the product formula `substAlgHom_mul_sub`.  Injectivity then
follows because a series killed by `φ` lies in every `𝔪^k`, and `K⟦X⟧` is `𝔪`-adically
Hausdorff; surjectivity by successive approximation `u₀ = 0`, `uₖ₊₁ = uₖ + (f - φ uₖ)`, whose
residuals `f - φ uₖ` lie in `𝔪^k`, so that the sequence converges by `𝔪`-adic completeness to a
preimage of `f`. -/

section Unipotent

variable {a : Fin n → MvPowerSeries (Fin n) K} (ha : HasSubst a)
include ha

theorem substAlgHom_sub_mem_of_mem (h : ∀ i, a i - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K))
    {x : MvPowerSeries (Fin n) K} (hx : x ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    substAlgHom (R := K) ha x - x ∈ maximalIdeal (MvPowerSeries (Fin n) K) := by
  rw [maximalIdeal_eq_span_range_X] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [substAlgHom_X]
    exact h i
  | zero => rw [map_zero, sub_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    convert Ideal.add_mem _ hx hy using 1
    ring
  | smul r x hx' hx =>
    rw [smul_eq_mul, substAlgHom_mul_sub]
    have hφx : substAlgHom (R := K) ha x ∈ maximalIdeal (MvPowerSeries (Fin n) K) :=
      substAlgHom_mem_maximalIdeal ha (by rw [maximalIdeal_eq_span_range_X]; exact hx')
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hφx) (Ideal.mul_mem_left _ _ hx)

/-- If the `a i` are congruent to `Xᵢ` modulo `𝔪`, the substitution changes every series by an
element of `𝔪`. -/
theorem substAlgHom_sub_mem (h : ∀ i, a i - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K))
    (r : MvPowerSeries (Fin n) K) :
    substAlgHom (R := K) ha r - r ∈ maximalIdeal (MvPowerSeries (Fin n) K) := by
  have hr : r - C (constantCoeff r) ∈ maximalIdeal (MvPowerSeries (Fin n) K) := by
    rw [maximalIdeal_eq_span_range_X]
    exact mem_span_range_X_of_constantCoeff_eq_zero (by simp)
  have hC : substAlgHom (R := K) ha (C (constantCoeff r)) = C (constantCoeff r) := by
    rw [c_eq_algebraMap]
    exact AlgHom.commutes _ _
  have := substAlgHom_sub_mem_of_mem ha h hr
  rwa [map_sub, hC, sub_sub_sub_cancel_right] at this

/-- If the `a i` are congruent to `Xᵢ` modulo `𝔪²`, the substitution changes every element of
`𝔪` by an element of `𝔪²`. -/
theorem substAlgHom_sub_mem_sq
    (h₂ : ∀ i, a i - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2)
    {x : MvPowerSeries (Fin n) K} (hx : x ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    substAlgHom (R := K) ha x - x ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 := by
  have h₁ : ∀ i, a i - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) := fun i =>
    Ideal.pow_le_self two_ne_zero (h₂ i)
  rw [maximalIdeal_eq_span_range_X] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [substAlgHom_X]
    exact h₂ i
  | zero => rw [map_zero, sub_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    convert Ideal.add_mem _ hx hy using 1
    ring
  | smul r x hx' hx =>
    rw [smul_eq_mul, substAlgHom_mul_sub]
    have hφx : substAlgHom (R := K) ha x ∈ maximalIdeal (MvPowerSeries (Fin n) K) :=
      substAlgHom_mem_maximalIdeal ha (by rw [maximalIdeal_eq_span_range_X]; exact hx')
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hx)
    rw [pow_two]
    exact Ideal.mul_mem_mul (substAlgHom_sub_mem ha h₁ r) hφx

/-- The defect of a unipotent substitution raises the `𝔪`-adic order by one. -/
theorem substAlgHom_sub_mem_pow_succ
    (h₂ : ∀ i, a i - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2) (k : ℕ)
    {f : MvPowerSeries (Fin n) K} (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k) :
    substAlgHom (R := K) ha f - f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ (k + 1) := by
  induction k generalizing f with
  | zero =>
    rw [zero_add, pow_one]
    exact substAlgHom_sub_mem ha (fun i => Ideal.pow_le_self two_ne_zero (h₂ i)) f
  | succ k ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun r hr s hs => ?_) (fun x y hx hy => ?_)
    · rw [substAlgHom_mul_sub]
      have hφs : substAlgHom (R := K) ha s ∈ maximalIdeal (MvPowerSeries (Fin n) K) :=
        substAlgHom_mem_maximalIdeal ha hs
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (ih hr) hφs
      · rw [show k + 1 + 1 = k + 2 by ring, pow_add]
        exact Ideal.mul_mem_mul hr (substAlgHom_sub_mem_sq ha h₂ hs)
    · rw [map_add]
      convert Ideal.add_mem _ hx hy using 1
      ring

theorem substAlgHom_injective_of_sub_X_mem_sq
    (h₂ : ∀ i, a i - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2) :
    Function.Injective (substAlgHom (R := K) ha) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hk : ∀ k, f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := substAlgHom_sub_mem_pow_succ ha h₂ k ih
      rwa [hf, zero_sub, Ideal.neg_mem_iff] at this
  rw [maximalIdeal_eq_span_range_X] at hk
  exact IsHausdorff.haus
    (inferInstance : IsHausdorff (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) K)))
      (MvPowerSeries (Fin n) K)) f fun k => by
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact hk k

theorem substAlgHom_surjective_of_sub_X_mem_sq
    (h₂ : ∀ i, a i - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2) :
    Function.Surjective (substAlgHom (R := K) ha) := by
  intro f
  set φ := substAlgHom (R := K) ha with hφ
  set I : Ideal (MvPowerSeries (Fin n) K) := Ideal.span (Set.range X) with hI
  have hmI : maximalIdeal (MvPowerSeries (Fin n) K) = I := maximalIdeal_eq_span_range_X _ _
  -- successive approximation
  let u : ℕ → MvPowerSeries (Fin n) K := fun k => Nat.rec 0 (fun _ v => v + (f - φ v)) k
  have huS : ∀ k, u (k + 1) = u k + (f - φ (u k)) := fun k => rfl
  have hres : ∀ k, f - φ (u k) ∈ I ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := substAlgHom_sub_mem_pow_succ ha h₂ k (hmI ▸ ih)
      rw [hmI, map_sub] at this
      rw [huS, map_add, map_sub, ← Ideal.neg_mem_iff]
      convert this using 1
      ring
  have hcauchy : ∀ m k, m ≤ k → u k - u m ∈ I ^ m := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      rw [huS, add_sub_right_comm]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmk (hres k))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec
    (inferInstance : IsPrecomplete I (MvPowerSeries (Fin n) K)) (f := u) fun {m k} hmk => by
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.neg_mem_iff, neg_sub]
      exact hcauchy m k hmk
  refine ⟨L, ?_⟩
  have hLk : ∀ k, φ L - f ∈ I ^ k := by
    intro k
    have h1 : u k - L ∈ I ^ k := by
      have := hL k
      rwa [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at this
    have h2 : φ (L - u k) ∈ I ^ k := by
      rw [← hmI] at h1 ⊢
      exact substAlgHom_mem_maximalIdeal_pow ha (by rw [← Ideal.neg_mem_iff, neg_sub]; exact h1)
    have := Ideal.sub_mem _ h2 (hres k)
    rwa [map_sub, sub_sub_sub_cancel_right] at this
  have := IsHausdorff.haus (inferInstance : IsHausdorff I (MvPowerSeries (Fin n) K)) (φ L - f)
    fun k => by
      rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact hLk k
  exact sub_eq_zero.mp this

/-- A substitution `Xᵢ ↦ a i` with `a i ≡ Xᵢ (mod 𝔪²)` is an automorphism of `K⟦X⟧` (one half
of the criterion of [Kol07, Notation 93]). -/
theorem bijective_substAlgHom_of_sub_X_mem_sq
    (h₂ : ∀ i, a i - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2) :
    Function.Bijective (substAlgHom (R := K) ha) :=
  ⟨substAlgHom_injective_of_sub_X_mem_sq ha h₂, substAlgHom_surjective_of_sub_X_mem_sq ha h₂⟩

end Unipotent

/-! ### Linear substitutions

`linearSubst A` is the family `Xᵢ ↦ ∑ⱼ Aᵢⱼ Xⱼ`.  Substituting `linearSubst B` into `linearSubst A`
gives `linearSubst (A * B)`, so the substitutions by `A` and `A⁻¹` are mutually inverse when `A`
is invertible (`subst_self` for `linearSubst 1 = X`). -/

section Linear

theorem linearSubst_one : linearSubst (1 : Matrix (Fin n) (Fin n) K) = X := by
  funext i
  simp [linearSubst, Matrix.one_apply, ite_smul]

theorem substAlgHom_linearSubst_linearSubst (A B : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    substAlgHom (R := K) (hasSubst_linearSubst B) (linearSubst A i) = linearSubst (A * B) i := by
  simp only [linearSubst, map_sum, map_smul, substAlgHom_X, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_smul]

theorem substAlgHom_linearSubst_comp (A B : Matrix (Fin n) (Fin n) K)
    (f : MvPowerSeries (Fin n) K) :
    substAlgHom (R := K) (hasSubst_linearSubst B)
      (substAlgHom (R := K) (hasSubst_linearSubst A) f) =
      substAlgHom (R := K) (hasSubst_linearSubst (A * B)) f := by
  rw [substAlgHom_comp_substAlgHom_apply, substAlgHom_apply, substAlgHom_apply]
  congr 1
  funext i
  exact substAlgHom_linearSubst_linearSubst A B i

/-- The substitution by `A⁻¹` undoes the substitution by `A`. -/
theorem substAlgHom_linearSubst_inv_apply (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A)
    (f : MvPowerSeries (Fin n) K) :
    substAlgHom (R := K) (hasSubst_linearSubst A⁻¹)
      (substAlgHom (R := K) (hasSubst_linearSubst A) f) = f := by
  rw [substAlgHom_linearSubst_comp,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA), substAlgHom_apply]
  have : linearSubst (1 : Matrix (Fin n) (Fin n) K) = X := linearSubst_one
  rw [this, subst_self, id]

theorem substAlgHom_linearSubst_apply_inv (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A)
    (f : MvPowerSeries (Fin n) K) :
    substAlgHom (R := K) (hasSubst_linearSubst A)
      (substAlgHom (R := K) (hasSubst_linearSubst A⁻¹) f) = f := by
  rw [substAlgHom_linearSubst_comp,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA), substAlgHom_apply]
  have : linearSubst (1 : Matrix (Fin n) (Fin n) K) = X := linearSubst_one
  rw [this, subst_self, id]

/-- The linear substitution by an invertible matrix is an automorphism. -/
theorem bijective_substAlgHom_linearSubst (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A) :
    Function.Bijective (substAlgHom (R := K) (hasSubst_linearSubst A)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨substAlgHom (R := K) (hasSubst_linearSubst A⁻¹),
      substAlgHom_linearSubst_inv_apply A hA, substAlgHom_linearSubst_apply_inv A hA⟩

end Linear

/-! ### Continuous endomorphisms are substitutions

With the coefficientwise topology (`K` discrete), Mathlib's `continuous_subst` says a
substitution is continuous, and `aeval_unique` says a continuous `K`-algebra endomorphism is the
evaluation at the images of the variables; under the discrete topology "evaluable" and
"substitutable" agree (`hasSubst_iff_hasEval_of_discreteTopology`). -/

section Continuity

open scoped MvPowerSeries.WithPiTopology

variable [UniformSpace K] [DiscreteUniformity K]

/-- A `K`-algebra endomorphism of `K⟦X⟧` is continuous iff it is a substitution `xᵢ ↦ gᵢ` (the
maps of [Kol07, Notation 93]). -/
theorem continuous_iff_exists_substAlgHom
    (ε : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K) :
    Continuous ε ↔
      ∃ (a : Fin n → MvPowerSeries (Fin n) K) (ha : HasSubst a), ε = substAlgHom (R := K) ha := by
  constructor
  · intro hε
    have hE : HasEval (fun i => ε (X i)) := HasEval.X.map hε
    have ha : HasSubst (fun i => ε (X i)) := hasSubst_iff_hasEval_of_discreteTopology.mpr hE
    refine ⟨_, ha, ?_⟩
    apply DFunLike.coe_injective
    rw [substAlgHom_eq_aeval ha]
    exact congrArg DFunLike.coe (aeval_unique hε).symm
  · rintro ⟨a, ha, rfl⟩
    rw [coe_substAlgHom]
    exact continuous_subst ha

end Continuity

/-! ### The criterion of Notation 93

A family `a` with `constantCoeff (a i) = 0` splits as `a = φ_b ∘ linearSubst A` where
`A = linearPart a` is the matrix of linear parts and `b = A⁻¹ a` is unipotent (`b j ≡ Xⱼ mod 𝔪²`),
so `Xᵢ ↦ a i` is an automorphism when `A` is invertible (the two preceding sections).
Conversely, if `A` is singular, a nonzero linear form `ℓ = ∑ vᵢ Xᵢ` with `v ᵥ* A = 0` is sent
into `𝔪²`; an automorphism preserves `𝔪` and hence `𝔪²`, so `ℓ ∈ 𝔪²`, which is absurd. -/

section Criterion

/-- Monomials of degree less than two: the constant one and the variables. -/
theorem degree_lt_two_iff (d : Fin n →₀ ℕ) :
    d.degree < 2 ↔ d = 0 ∨ ∃ l, d = Finsupp.single l 1 := by
  constructor
  · intro hd
    rcases (Nat.lt_succ_iff.mp hd).lt_or_eq with h1 | h1
    · left
      exact (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp h1)
    · right
      have hne : d ≠ 0 := fun h => by simp [h] at h1
      obtain ⟨l, hl⟩ := Finsupp.support_nonempty_iff.mpr hne
      refine ⟨l, ?_⟩
      have hsplit : d = d.erase l + Finsupp.single l (d l) := by
        rw [← Finsupp.update_eq_erase_add_single, Finsupp.update_self]
      have hdeg : (d.erase l).degree + (Finsupp.single l (d l)).degree = 1 := by
        rw [← map_add, ← hsplit, h1]
      rw [Finsupp.degree_single] at hdeg
      have hl1 : 1 ≤ d l := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hl)
      have hdl : d l = 1 := by omega
      have herase : (d.erase l).degree = 0 := by omega
      rw [Finsupp.degree_eq_zero_iff] at herase
      rw [hsplit, herase, zero_add, hdl]
  · rintro (rfl | ⟨l, rfl⟩)
    · simp
    · simp [Finsupp.degree_single]

theorem coeff_single_linearSubst (A : Matrix (Fin n) (Fin n) K) (i l : Fin n) :
    coeff (Finsupp.single l 1) (linearSubst A i) = A i l := by
  classical
  simp [linearSubst, map_sum, coeff_X, Finsupp.single_left_inj]

/-- A substitutable family differs from its linear part by elements of `𝔪²`. -/
theorem sub_linearSubst_linearPart_mem_sq {a : Fin n → MvPowerSeries (Fin n) K}
    (ha : HasSubst a) (i : Fin n) :
    a i - linearSubst (linearPart a) i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 := by
  rw [maximalIdeal_eq_span_range_X, mem_span_range_X_pow_iff_le_order]
  apply le_order
  intro d hd
  have hd2 : d.degree < 2 := by exact_mod_cast hd
  rw [map_sub]
  rcases (degree_lt_two_iff d).mp hd2 with rfl | ⟨l, rfl⟩
  · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_eq_zero_of_hasSubst ha, constantCoeff_linearSubst, sub_zero]
  · rw [coeff_single_linearSubst, linearPart_apply, sub_self]

/-- The "⇐" of the criterion of [Kol07, Notation 93]: if the linear parts are linearly
independent, the substitution is an automorphism. -/
theorem bijective_substAlgHom_of_isUnit_linearPart {a : Fin n → MvPowerSeries (Fin n) K}
    (ha : HasSubst a) (hA : IsUnit (linearPart a)) :
    Function.Bijective (substAlgHom (R := K) ha) := by
  set A := linearPart a with hAdef
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  set b : Fin n → MvPowerSeries (Fin n) K := fun j => ∑ i, A⁻¹ j i • a i with hb
  have hbc : ∀ j, constantCoeff (b j) = 0 := by
    intro j
    simp [hb, map_sum, constantCoeff_smul, constantCoeff_eq_zero_of_hasSubst ha]
  have hbS : HasSubst b := hasSubst_of_constantCoeff_zero hbc
  have hb2 : ∀ j, b j - X j ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 := by
    intro j
    have key : b j - X j = ∑ i, A⁻¹ j i • (a i - linearSubst A i) := by
      simp only [hb, smul_sub, Finset.sum_sub_distrib]
      congr 1
      simp only [linearSubst, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have : ∀ l, ∑ i, (A⁻¹ j i * A i l) • (X l : MvPowerSeries (Fin n) K) =
          (A⁻¹ * A) j l • (X l : MvPowerSeries (Fin n) K) := fun l => by
        rw [Matrix.mul_apply, Finset.sum_smul]
      simp only [this, Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [key]
    exact Ideal.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (sub_linearSubst_linearPart_mem_sq ha i)
  have hcomp : ∀ f, substAlgHom (R := K) ha f =
      substAlgHom (R := K) hbS (substAlgHom (R := K) (hasSubst_linearSubst A) f) := by
    intro f
    rw [substAlgHom_comp_substAlgHom_apply, substAlgHom_apply, substAlgHom_apply]
    congr 1
    funext i
    simp only [linearSubst, map_sum, map_smul, substAlgHom_X, hb, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ j, (A i j * A⁻¹ j l) • a l = (A * A⁻¹) i l • a l := fun l => by
      rw [Matrix.mul_apply, Finset.sum_smul]
    simp only [this, Matrix.mul_nonsing_inv _ hdet, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hfun : ⇑(substAlgHom (R := K) ha) =
      ⇑(substAlgHom (R := K) hbS) ∘ ⇑(substAlgHom (R := K) (hasSubst_linearSubst A)) :=
    funext hcomp
  rw [hfun]
  exact (bijective_substAlgHom_of_sub_X_mem_sq hbS hb2).comp
    (bijective_substAlgHom_linearSubst A hA)

/-- The "⇒" of the criterion of [Kol07, Notation 93]: an automorphism `Xᵢ ↦ a i` has linearly
independent linear parts. -/
theorem isUnit_linearPart_of_bijective {a : Fin n → MvPowerSeries (Fin n) K} (ha : HasSubst a)
    (hbij : Function.Bijective (substAlgHom (R := K) ha)) : IsUnit (linearPart a) := by
  classical
  by_contra hA
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hA
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hA
  set ℓ : MvPowerSeries (Fin n) K := ∑ i, v i • X i with hℓ
  have hφℓ : substAlgHom (R := K) ha ℓ ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 := by
    rw [maximalIdeal_eq_span_range_X, mem_span_range_X_pow_iff_le_order]
    apply le_order
    intro d hd
    have hd2 : d.degree < 2 := by exact_mod_cast hd
    simp only [hℓ, map_sum, map_smul, substAlgHom_X, smul_eq_mul]
    rcases (degree_lt_two_iff d).mp hd2 with rfl | ⟨l, rfl⟩
    · simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_eq_zero_of_hasSubst ha]
    · have := congr_fun hv l
      simpa only [Matrix.vecMul, dotProduct, linearPart_apply, Pi.zero_apply] using this
  let e : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K := AlgEquiv.ofBijective _ hbij
  have hmap : (maximalIdeal (MvPowerSeries (Fin n) K) ^ 2).map
      (e : MvPowerSeries (Fin n) K ≃+* MvPowerSeries (Fin n) K) =
        maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 := by
    rw [Ideal.map_pow, map_ringEquiv_maximalIdeal]
  have hℓ2 : ℓ ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 := by
    have h1 : (e : MvPowerSeries (Fin n) K ≃+* MvPowerSeries (Fin n) K) ℓ ∈
        (maximalIdeal (MvPowerSeries (Fin n) K) ^ 2).map
          (e : MvPowerSeries (Fin n) K ≃+* MvPowerSeries (Fin n) K) := by
      rw [hmap]; exact hφℓ
    obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_of_equiv _ _).mp h1
    have : x = ℓ := e.injective hxe
    rwa [this] at hx
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  apply hi
  rw [maximalIdeal_eq_span_range_X, mem_span_range_X_pow_iff_le_order] at hℓ2
  have hlt : ((Finsupp.single i 1 : Fin n →₀ ℕ).degree : ℕ∞) < ℓ.order :=
    lt_of_lt_of_le (by simp [Finsupp.degree_single]) hℓ2
  have := coeff_of_lt_order hlt
  simpa [hℓ, map_sum, coeff_smul, coeff_X, Finsupp.single_left_inj] using this

/-- The criterion of [Kol07, Notation 93]: `Xᵢ ↦ a i` is an automorphism iff the matrix of
linear parts is invertible. -/
theorem bijective_substAlgHom_iff_isUnit_linearPart {a : Fin n → MvPowerSeries (Fin n) K}
    (ha : HasSubst a) :
    Function.Bijective (substAlgHom (R := K) ha) ↔ IsUnit (linearPart a) :=
  ⟨isUnit_linearPart_of_bijective ha, bijective_substAlgHom_of_isUnit_linearPart ha⟩

end Criterion

/-! ### The shift automorphisms of the form `1 + B`

The family `Xᵢ ↦ Xᵢ + c` (other variables fixed) has linear-part matrix `1 + eᵢ βᵀ`, `β` the
vector of linear coefficients of `c`, whose determinant is `1 + βᵢ` (matrix determinant lemma).
With `c = q • b`, `q ∈ ℚ`, the determinant `1 + q βᵢ` vanishes for at most one `q`. -/

section Shift

theorem shiftSubst_self (i : Fin n) (c : MvPowerSeries (Fin n) K) : shiftSubst i c i = X i + c :=
  Function.update_self ..

theorem shiftSubst_of_ne {i j : Fin n} (h : j ≠ i) (c : MvPowerSeries (Fin n) K) :
    shiftSubst i c j = X j :=
  Function.update_of_ne h ..

theorem hasSubst_shiftSubst (i : Fin n) {c : MvPowerSeries (Fin n) K} (hc : constantCoeff c = 0) :
    HasSubst (shiftSubst i c) := by
  apply hasSubst_of_constantCoeff_zero
  intro j
  by_cases h : j = i
  · subst h; simp [shiftSubst_self, hc]
  · simp [shiftSubst_of_ne h]

theorem linearPart_shiftSubst (i : Fin n) (c : MvPowerSeries (Fin n) K) :
    linearPart (shiftSubst i c) = 1 + Matrix.replicateCol Unit (Pi.single i (1 : K)) *
      Matrix.replicateRow Unit (fun l => coeff (Finsupp.single l 1) c) := by
  classical
  ext j l
  rw [linearPart_apply, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_unique,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h
    rw [shiftSubst_self, map_add, coeff_X, Pi.single_eq_same, one_mul]
    by_cases hl : j = l
    · subst hl; simp
    · rw [ite_eq_right hl,
        ite_eq_right fun h' => hl (Finsupp.single_left_injective one_ne_zero h').symm]
  · rw [shiftSubst_of_ne h, coeff_X, Pi.single_eq_of_ne h, zero_mul, add_zero]
    by_cases hl : j = l
    · subst hl; simp
    · rw [ite_eq_right hl,
        ite_eq_right fun h' => hl (Finsupp.single_left_injective one_ne_zero h').symm]

theorem det_linearPart_shiftSubst (i : Fin n) (c : MvPowerSeries (Fin n) K) :
    (linearPart (shiftSubst i c)).det = 1 + coeff (Finsupp.single i 1) c := by
  rw [linearPart_shiftSubst, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Pi.single_apply]

variable [CharZero K]

/-- The rational scalars act on `K⟦X⟧` through their casts. -/
theorem rat_smul_eq_cast_smul (q : ℚ) (b : MvPowerSeries (Fin n) K) : q • b = (q : K) • b := by
  rw [← algebraMap_smul K q b, eq_ratCast]

/-- For `b ∈ B ≤ 𝔪` and all `q ∈ ℚ` except at most one, `Xᵢ ↦ Xᵢ + q b`, `Xⱼ ↦ Xⱼ` (`j ≠ i`) is
an automorphism of the form `1 + B`: Kollár's "`xᵢ ↦ xᵢ + λᵢ bᵢ` gives an automorphism for
general `λᵢ`" [Kol07, Notation 93], as used in the proof of [Kol07, Proposition 94]. -/
theorem exists_onePlus_shift (B : Ideal (MvPowerSeries (Fin n) K))
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K)) (i : Fin n)
    {b : MvPowerSeries (Fin n) K} (hb : b ∈ B) :
    ∃ q₀ : ℚ, ∀ q : ℚ, q ≠ q₀ →
      ∃ g : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K,
        IsOnePlus B g ∧ ∀ f, g f = subst (shiftSubst i (q • b)) f := by
  classical
  set β : K := coeff (Finsupp.single i 1) b with hβ
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℚ, ∀ q : ℚ, 1 + (q : K) * β = 0 → q = q₀ := by
    by_cases hex : ∃ q : ℚ, 1 + (q : K) * β = 0
    · obtain ⟨q₁, hq₁⟩ := hex
      refine ⟨q₁, fun q hq => ?_⟩
      have hβ0 : β ≠ 0 := fun h => by
        rw [h, mul_zero, add_zero] at hq₁
        exact one_ne_zero hq₁
      have : (q : K) = q₁ := mul_right_cancel₀ hβ0 (add_left_cancel (hq.trans hq₁.symm))
      exact_mod_cast this
    · exact ⟨0, fun q hq => (hex ⟨q, hq⟩).elim⟩
  refine ⟨q₀, fun q hq => ?_⟩
  have hbc : constantCoeff b = 0 := by
    have hbm := hB hb
    rw [maximalIdeal_eq_span_range_X] at hbm
    have h1 := (mem_span_range_X_pow_iff_le_order 1 b).mp (by rwa [pow_one])
    rwa [Nat.cast_one, one_le_order_iff_constCoeff_eq_zero] at h1
  have hc0 : constantCoeff (q • b) = 0 := by
    rw [rat_smul_eq_cast_smul, constantCoeff_smul, hbc, smul_zero]
  have hS := hasSubst_shiftSubst i hc0
  have hunit : IsUnit (linearPart (shiftSubst i (q • b))) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_linearPart_shiftSubst, isUnit_iff_ne_zero,
      rat_smul_eq_cast_smul, coeff_smul]
    exact fun h0 => hq (hq₀ q h0)
  have hbij := bijective_substAlgHom_of_isUnit_linearPart hS hunit
  refine ⟨AlgEquiv.ofBijective _ hbij, ⟨⟨_, hS, ?_⟩, ?_⟩, fun f => ?_⟩
  · ext f
    rfl
  · intro j
    change substAlgHom (R := K) hS (X j) - X j ∈ B
    rw [substAlgHom_X]
    by_cases h : j = i
    · subst h
      rw [shiftSubst_self, add_sub_cancel_left]
      exact B.smul_of_tower_mem q hb
    · rw [shiftSubst_of_ne h, sub_self]
      exact B.zero_mem
  · exact substAlgHom_apply hS f

end Shift

end IsLocalRing
