/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineAlgebra
public import Mathlib.RingTheory.Flat.Basic

/-!
# Base change of the affine blow-up algebra

For a ring map `R → S`, `J = IS` and `b` the image of `a`, the induced map `R[I/a] → S[J/b]`
and the `S`-algebra map `S ⊗[R] R[I/a] → S[J/b]`, which is surjective with kernel the `b`-power
torsion [Sta, Tag 0BIP], and is an isomorphism when `S` is flat over `R` (the ring-level form of
the compatibility of blow-ups with flat base change [Sta, Tag 0805]: flatness preserves the
injectivity of multiplication by `a`).

## Main declarations

* `AlgebraicGeometry.awayMapₐ S a : Localization.Away a →ₐ[R] Localization.Away (algebraMap R S a)`,
  the map of localizations induced by `R → S`.
* `affineBlowUpAlgebra.baseChangeHom I a S : R[I/a] →ₐ[R] S[IS/b]` with `baseChangeHom_frac`
  and `baseChangeHom_unique`.
* `affineBlowUpAlgebra.tensorHom I a S : S ⊗[R] R[I/a] →ₐ[S] S[IS/b]` with `tensorHom_tmul_frac`,
  `tensorHom_unique`, `tensorHom_surjective`, `tensorHom_apply_eq_zero_iff` and
  `tensorHom_bijective_of_flat`.

## The arguments

*The induced map.*  `R_a → S_b` sends `x/a` to `(image of x)/b`, so it maps the generators of
`R[I/a]` into `S[J/b]`.

*Surjectivity.*  `S[J/b]` is generated over `S` by the `y/b`, `y ∈ J = IS`, and
`y = ∑ sᵢ (image of xᵢ)` gives `y/b = ∑ sᵢ · (image of xᵢ)/b`, the image of `∑ sᵢ ⊗ xᵢ/a`.

*Kernel.*  Every element `w` of `S ⊗[R] R[I/a]` satisfies `bⁿ w = p ⊗ 1` for some `n` and
`p ∈ S`: for a pure tensor `s ⊗ z` with `z aⁿ = r` in `R_a` (`z ∈ R[I/a] ⊆ R_a`) one has
`bⁿ (s ⊗ z) = s ⊗ aⁿ z = s ⊗ r = (image of r) s ⊗ 1`, and the property is additive.  If `w` maps
to `0` then `p` maps to `0` in `S_b`, so `bᵏ p = 0` and `bⁿ⁺ᵏ w = 0`.  Conversely `b` is a
nonzerodivisor of `S[J/b]` (`affineBlowUpAlgebra.algebraMap_mem_nonZeroDivisors`), so `b`-power
torsion maps to `0`.  The Stacks Project proves the kernel statement by constructing the inverse
map on `S[J/b]`; the common-denominator computation above is the same identity
`bⁿ (s ⊗ x/aⁿ) = s x ⊗ 1` read forwards.

*Flat case.*  If `S` is flat over `R`, multiplication by `a` on `R[I/a]` (injective) stays
injective after `S ⊗[R] -`, and it is multiplication by `b` on the tensor product; so the
`b`-power torsion vanishes and the surjection is bijective.

## Conventions

No hypothesis `a ∈ I` is needed ([Sta, Tag 0BIP] assumes it; it is not used here).  The
`b`-power torsion of the `S`-module `S ⊗[R] R[I/a]` is written `∃ k, bᵏ • w = 0`.

## Boundary cases

`S = 0`: both sides are the zero ring.  `a = 0`: `S[J/0]` is the zero ring and every `w` is
`0`-power torsion (`0¹ • w = 0`), consistently.
-/

@[expose] public section

universe u v

open TensorProduct

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a : R)

/-- The map `R_a → S_b` induced by `R → S` on localizations, as an `R`-algebra map. -/
noncomputable def awayMapₐ : Localization.Away a →ₐ[R] Localization.Away (algebraMap R S a) :=
  IsLocalization.Away.liftAlgHom a (f := Algebra.ofId R (Localization.Away (algebraMap R S a)))
    (by
      rw [Algebra.ofId_apply,
        IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S a))]
      exact IsLocalization.Away.algebraMap_isUnit _)

theorem awayMapₐ_algebraMap (r : R) :
    awayMapₐ S a (algebraMap R (Localization.Away a) r) =
      algebraMap S (Localization.Away (algebraMap R S a)) (algebraMap R S r) := by
  rw [awayMapₐ, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
    ← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S a))]
  rfl

theorem awayMapₐ_invSelf :
    awayMapₐ S a (IsLocalization.Away.invSelf a) =
      IsLocalization.Away.invSelf (algebraMap R S a) := by
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (algebraMap R S a)) (algebraMap R S a)
  have h1 : awayMapₐ S a (IsLocalization.Away.invSelf a) *
      algebraMap S (Localization.Away (algebraMap R S a)) (algebraMap R S a) = 1 := by
    rw [← awayMapₐ_algebraMap, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  have h2 : IsLocalization.Away.invSelf (algebraMap R S a) *
      algebraMap S (Localization.Away (algebraMap R S a)) (algebraMap R S a) = 1 := by
    rw [mul_comm, IsLocalization.Away.mul_invSelf]
  exact hu.mul_left_injective (h1.trans h2.symm)

namespace affineBlowUpAlgebra

variable (I : Ideal R)

theorem awayMapₐ_mem (z : affineBlowUpAlgebra I a) :
    awayMapₐ S a z ∈ affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a) := by
  obtain ⟨z, hz⟩ := z
  induction hz using induction_on with
  | mem x hx =>
    change awayMapₐ S a (algebraMap R (Localization.Away a) x * IsLocalization.Away.invSelf a) ∈ _
    rw [map_mul, awayMapₐ_algebraMap, awayMapₐ_invSelf]
    exact mul_invSelf_mem (Ideal.mem_map_of_mem _ hx)
  | algebraMap r =>
    change awayMapₐ S a (algebraMap R (Localization.Away a) r) ∈ _
    rw [awayMapₐ_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz =>
    change awayMapₐ S a (y + z) ∈ _
    rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz =>
    change awayMapₐ S a (y * z) ∈ _
    rw [map_mul]; exact mul_mem hy hz

/-- The induced map `R[I/a] → S[IS/b]`, `x/a ↦ (image of x)/b` [Sta, Tag 0BIP]. -/
noncomputable def baseChangeHom :
    affineBlowUpAlgebra I a →ₐ[R] affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a)
    where
  toFun z := ⟨awayMapₐ S a z, awayMapₐ_mem S a I z⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by
    change awayMapₐ S a (algebraMap R (Localization.Away a) r) = _
    rw [awayMapₐ_algebraMap, ← IsScalarTower.algebraMap_apply]
    rfl)

@[simp]
theorem coe_baseChangeHom (z : affineBlowUpAlgebra I a) :
    (baseChangeHom S a I z : Localization.Away (algebraMap R S a)) = awayMapₐ S a z :=
  rfl

theorem baseChangeHom_frac {x : R} (hx : x ∈ I) :
    baseChangeHom S a I (frac hx) = frac (Ideal.mem_map_of_mem (algebraMap R S) hx) := by
  apply Subtype.ext
  change awayMapₐ S a (algebraMap R (Localization.Away a) x * IsLocalization.Away.invSelf a) = _
  rw [map_mul, awayMapₐ_algebraMap, awayMapₐ_invSelf]
  rfl

/-- The induced map is the unique `R`-algebra map with `x/a ↦ (image of x)/b`. -/
theorem baseChangeHom_unique
    (ψ : affineBlowUpAlgebra I a →ₐ[R]
      affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a))
    (hψ : ∀ x (hx : x ∈ I), ψ (frac hx) = frac (Ideal.mem_map_of_mem (algebraMap R S) hx)) :
    ψ = baseChangeHom S a I :=
  algHom_ext fun x hx => by rw [hψ x hx, baseChangeHom_frac]

/-- The `S`-algebra map `S ⊗[R] R[I/a] → S[IS/b]` [Sta, Tag 0BIP]. -/
noncomputable def tensorHom :
    S ⊗[R] affineBlowUpAlgebra I a →ₐ[S]
      affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (baseChangeHom S a I) fun _ _ => Commute.all _ _

@[simp]
theorem tensorHom_tmul (s : S) (z : affineBlowUpAlgebra I a) :
    tensorHom S a I (s ⊗ₜ z) = algebraMap S _ s * baseChangeHom S a I z := by
  rw [tensorHom, Algebra.TensorProduct.lift_tmul]
  rfl

theorem tensorHom_tmul_frac {x : R} (hx : x ∈ I) :
    tensorHom S a I (1 ⊗ₜ frac hx) = frac (Ideal.mem_map_of_mem (algebraMap R S) hx) := by
  rw [tensorHom_tmul, map_one, one_mul, baseChangeHom_frac]

/-- The tensor map is the unique `S`-algebra map with `1 ⊗ x/a ↦ (image of x)/b`. -/
theorem tensorHom_unique
    (Ψ : S ⊗[R] affineBlowUpAlgebra I a →ₐ[S]
      affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a))
    (hΨ : ∀ x (hx : x ∈ I),
      Ψ (1 ⊗ₜ frac hx) = frac (Ideal.mem_map_of_mem (algebraMap R S) hx)) :
    Ψ = tensorHom S a I := by
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (algHom_ext fun x hx => ?_)
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars',
    Algebra.TensorProduct.includeRight_apply, hΨ x hx, tensorHom_tmul_frac]

/-- `S ⊗[R] R[I/a] → S[IS/b]` is surjective [Sta, Tag 0BIP]. -/
theorem tensorHom_surjective : Function.Surjective (tensorHom S a I) := by
  intro w
  have key : ∀ y ∈ I.map (algebraMap R S),
      algebraMap S (Localization.Away (algebraMap R S a)) y *
        IsLocalization.Away.invSelf (algebraMap R S a) ∈
          (tensorHom S a I).range.map (affineBlowUpAlgebra _ _).val := by
    intro y hy
    rw [Ideal.map] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨_, ⟨1 ⊗ₜ frac hx, tensorHom_tmul_frac S a I hx⟩, rfl⟩
    | zero => simp only [map_zero, zero_mul]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add, add_mul]; exact add_mem hy hz
    | smul s y _ hy =>
      rw [smul_eq_mul, map_mul, mul_assoc]
      exact mul_mem ⟨_, ⟨algebraMap S _ s, AlgHom.commutes _ _⟩, rfl⟩ hy
  have hle : affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a) ≤
      (tensorHom S a I).range.map (affineBlowUpAlgebra _ _).val :=
    (affineBlowUpAlgebra_eq_adjoin _ _).le.trans
      (Algebra.adjoin_le fun _ ⟨y, hy, hyz⟩ => hyz ▸ key y hy)
  obtain ⟨v, ⟨q, hq⟩, hv⟩ := hle w.2
  exact ⟨q, Subtype.ext ((congrArg Subtype.val hq).trans hv)⟩

/-- Common denominators: `bⁿ • w = p ⊗ 1` for some `n` and `p ∈ S`. -/
theorem exists_pow_smul_eq_tmul_one (w : S ⊗[R] affineBlowUpAlgebra I a) :
    ∃ (n : ℕ) (p : S), algebraMap R S a ^ n • w = p ⊗ₜ 1 := by
  induction w using TensorProduct.inductionOn with
  | tmul s z =>
    obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj (S := Localization.Away a) a
      (z : Localization.Away a)
    have hz : algebraMap R (affineBlowUpAlgebra I a) (a ^ n) * z =
        algebraMap R (affineBlowUpAlgebra I a) r := Subtype.ext (by
      rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, map_pow,
        mul_comm]
      exact hr)
    refine ⟨n, algebraMap R S r * s, ?_⟩
    calc algebraMap R S a ^ n • (s ⊗ₜ z) = ((a ^ n) • s) ⊗ₜ[R] z := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def, map_pow]
      _ = s ⊗ₜ ((a ^ n) • z) := TensorProduct.smul_tmul _ _ _
      _ = s ⊗ₜ algebraMap R (affineBlowUpAlgebra I a) r := by rw [Algebra.smul_def, hz]
      _ = (algebraMap R S r * s) ⊗ₜ 1 := by
          rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def]
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨n₁, p₁, h₁⟩ := h₁
    obtain ⟨n₂, p₂, h₂⟩ := h₂
    refine ⟨n₁ + n₂, algebraMap R S a ^ n₂ * p₁ + algebraMap R S a ^ n₁ * p₂, ?_⟩
    have e₁ : algebraMap R S a ^ (n₁ + n₂) • w₁ = (algebraMap R S a ^ n₂ * p₁) ⊗ₜ 1 := by
      rw [pow_add, mul_comm (algebraMap R S a ^ n₁), mul_smul, h₁, TensorProduct.smul_tmul',
        smul_eq_mul]
    have e₂ : algebraMap R S a ^ (n₁ + n₂) • w₂ = (algebraMap R S a ^ n₁ * p₂) ⊗ₜ 1 := by
      rw [pow_add, mul_smul, h₂, TensorProduct.smul_tmul', smul_eq_mul]
    rw [smul_add, e₁, e₂, TensorProduct.add_tmul]

/-- The kernel of `S ⊗[R] R[I/a] → S[IS/b]` is the `b`-power torsion [Sta, Tag 0BIP]. -/
theorem tensorHom_apply_eq_zero_iff (w : S ⊗[R] affineBlowUpAlgebra I a) :
    tensorHom S a I w = 0 ↔ ∃ k : ℕ, algebraMap R S a ^ k • w = 0 := by
  constructor
  · intro hw
    obtain ⟨n, p, hp⟩ := exists_pow_smul_eq_tmul_one S a I w
    have h1 : algebraMap S (affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a)) p
        = 0 := by
      have := congrArg (tensorHom S a I) hp
      rw [← AlgHom.toLinearMap_apply, LinearMap.map_smul, AlgHom.toLinearMap_apply, hw,
        smul_zero, tensorHom_tmul, map_one, mul_one] at this
      exact this.symm
    have h2 : algebraMap S (Localization.Away (algebraMap R S a)) p = 0 := congrArg Subtype.val h1
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R S a)) _ p).mp h2
    have hk' : algebraMap R S a ^ k * p = 0 := hk
    refine ⟨k + n, ?_⟩
    rw [pow_add, mul_smul, hp, TensorProduct.smul_tmul', smul_eq_mul, hk',
      TensorProduct.zero_tmul]
  · rintro ⟨k, hk⟩
    have : algebraMap S (affineBlowUpAlgebra (I.map (algebraMap R S)) (algebraMap R S a))
        (algebraMap R S a) ^ k * tensorHom S a I w = 0 := by
      have h := congrArg (tensorHom S a I) hk
      rwa [← AlgHom.toLinearMap_apply, LinearMap.map_smul, AlgHom.toLinearMap_apply, map_zero,
        Algebra.smul_def, map_pow] at h
    exact (mem_nonZeroDivisors_iff.mp (pow_mem (algebraMap_mem_nonZeroDivisors
      (I := I.map (algebraMap R S)) (a := algebraMap R S a)) k)).1 _ this

/-- Multiplication by `b` on `S ⊗[R] R[I/a]` is `S ⊗ (multiplication by `a` on `R[I/a]`)`. -/
theorem smul_eq_lTensor_mulLeft (w : S ⊗[R] affineBlowUpAlgebra I a) :
    algebraMap R S a • w =
      LinearMap.lTensor S (LinearMap.mulLeft R (algebraMap R (affineBlowUpAlgebra I a) a)) w := by
  induction w using TensorProduct.inductionOn with
  | tmul s z =>
    rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, TensorProduct.smul_tmul', smul_eq_mul,
      ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def]
  | add w₁ w₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂]

/-- The flat case: for `S` flat over `R`, `S ⊗[R] R[I/a] → S[IS/b]` is an isomorphism, because
multiplication by `a` on `R[I/a]` is injective and stays injective after `S ⊗[R] -` (the
ring-level form of the compatibility of blow-ups with flat base change [Sta, Tag 0805]). -/
theorem tensorHom_bijective_of_flat [Module.Flat R S] : Function.Bijective (tensorHom S a I) := by
  refine ⟨?_, tensorHom_surjective S a I⟩
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨k, hk⟩ := (tensorHom_apply_eq_zero_iff S a I w).mp hw
  have hmul : Function.Injective
      (LinearMap.mulLeft R (algebraMap R (affineBlowUpAlgebra I a) a)) := fun x y hxy =>
    (mul_cancel_left_mem_nonZeroDivisors (algebraMap_mem_nonZeroDivisors (I := I) (a := a))).mp
      hxy
  have hinj : Function.Injective fun v : S ⊗[R] affineBlowUpAlgebra I a =>
      algebraMap R S a • v := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := S) _ hmul
    convert this using 1
    funext v
    exact smul_eq_lTensor_mulLeft S a I v
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    apply ih
    apply hinj
    change algebraMap R S a • (algebraMap R S a ^ k • w) = algebraMap R S a • (0 : S ⊗[R] _)
    rw [← mul_smul, ← pow_succ', hk, smul_zero]

end affineBlowUpAlgebra

end AlgebraicGeometry
