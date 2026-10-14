/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The complexification `A ⊗_ℝ ℂ = A[i]` of a commutative ring

Hironaka: for a preanalytic `ℝ`-space `X = (X, 𝒪_X)`, "`(X, 𝒪_X ⊗_ℝ ℂ)` is a `ℂ`-local-ringed
space, which will be denoted by `X(ℂ)`" [Hir64, Ch. 0, §1, p. 120]. Since `ℂ = ℝ ⊕ ℝ i` is free of
rank two over `ℝ`, the tensor product `A ⊗_ℝ ℂ` of a commutative ring `A` (with an `ℝ`-structure)
is the ring `A[i] = {a + b i : a, b ∈ A}` of Gaussian pairs with `i² = -1`, and it is this ring —
which needs no `ℝ`-structure on `A` to be formed — that the complexification uses sectionwise:
`Γ(U, 𝒪_X ⊗_ℝ ℂ) = Γ(U, 𝒪_X)[i]`. The identification with Mathlib's tensor product is the
`ℝ`-algebra isomorphism `tensorEquiv : Complexified A ≃ₐ[ℝ] A ⊗[ℝ] ℂ`, `a + b i ↦ a ⊗ 1 + b ⊗ i`.

## Main definitions

In the namespace `Hironaka.AnalyticSpace.Complexified`:

* `Complexified A`: the pairs `⟨re, im⟩`, a commutative ring with
  `(a + bi)(c + di) = (ac - bd) + (ad + bc) i`; `ofReal : A →+* Complexified A` (`a ↦ a + 0 i`),
  `I` (`0 + 1 i`), `I_mul_I`, `re_add_im`; the `R`-algebra structure induced from one on `A`;
* `map (f : A →+* B) : Complexified A →+* Complexified B` (componentwise; functorial), `mapEquiv`;
* `algebraMapComplex (φ : ℝ →+* A) : ℂ →+* Complexified A`, `c ↦ φ(Re c) + φ(Im c) i`: the
  `ℂ`-structure of `X(ℂ)` from the `ℝ`-structure of `X`;
* `norm z = z.re² + z.im²` and `isUnit_iff_isUnit_norm`; the local-ring theorem
  `isLocalRing_of_exists_sub_mem`: if `A` is a local ring whose residue field is `ℝ` (every
  element is congruent to a constant `φ c` modulo `𝔪_A`), then `Complexified A` is a local ring —
  the stalks `𝒪_{X,x} ⊗_ℝ ℂ` of `X(ℂ)` are local because the residue fields of a preanalytic
  `ℝ`-space are `ℝ`; `isLocalHom_map`: a local homomorphism complexifies to a local
  homomorphism;
* `tensorEquiv`: the identification with `A ⊗[ℝ] ℂ` (the standard `ℂ = ℝ[i]`);
* `A[i]` is a finite `A`-module, hence Noetherian when `A` is.

The complexification of a space is built on this in `Hironaka/AnalyticSpace/Complexify.lean`.
-/

@[expose] public section

universe u v

namespace AnalyticSpace

/-- The complexification `A ⊗_ℝ ℂ = A[i]` of a commutative ring `A`, realised as Gaussian pairs
`a + b i` (Hironaka's `𝒪_X ⊗_ℝ ℂ` [Hir64, Ch. 0, §1, p. 120], sectionwise). -/
@[ext]
structure Complexified (A : Type u) where
  /-- The real part. -/
  re : A
  /-- The imaginary part. -/
  im : A

namespace Complexified

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

instance : Zero (Complexified A) := ⟨⟨0, 0⟩⟩
instance : One (Complexified A) := ⟨⟨1, 0⟩⟩
instance : Add (Complexified A) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg (Complexified A) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (Complexified A) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Mul (Complexified A) :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : SMul ℕ (Complexified A) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : SMul ℤ (Complexified A) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : NatCast (Complexified A) := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast (Complexified A) := ⟨fun n => ⟨n, 0⟩⟩

@[simp] theorem zero_re : (0 : Complexified A).re = 0 := rfl
@[simp] theorem zero_im : (0 : Complexified A).im = 0 := rfl
@[simp] theorem one_re : (1 : Complexified A).re = 1 := rfl
@[simp] theorem one_im : (1 : Complexified A).im = 0 := rfl
@[simp] theorem add_re (z w : Complexified A) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : Complexified A) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : Complexified A) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : Complexified A) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : Complexified A) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : Complexified A) : (z - w).im = z.im - w.im := rfl
@[simp] theorem mul_re (z w : Complexified A) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : Complexified A) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem nsmul_re (n : ℕ) (z : Complexified A) : (n • z).re = n • z.re := rfl
@[simp] theorem nsmul_im (n : ℕ) (z : Complexified A) : (n • z).im = n • z.im := rfl
@[simp] theorem zsmul_re (n : ℤ) (z : Complexified A) : (n • z).re = n • z.re := rfl
@[simp] theorem zsmul_im (n : ℤ) (z : Complexified A) : (n • z).im = n • z.im := rfl
@[simp] theorem natCast_re (n : ℕ) : (n : Complexified A).re = n := rfl
@[simp] theorem natCast_im (n : ℕ) : (n : Complexified A).im = 0 := rfl
@[simp] theorem intCast_re (n : ℤ) : (n : Complexified A).re = n := rfl
@[simp] theorem intCast_im (n : ℤ) : (n : Complexified A).im = 0 := rfl

instance instCommRing : CommRing (Complexified A) where
  add_assoc := by intros; ext <;> simp [add_assoc]
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp [add_comm]
  nsmul := (· • ·)
  nsmul_zero := by intros; ext <;> simp
  nsmul_succ := by intros; ext <;> simp [add_mul]
  zsmul := (· • ·)
  zsmul_zero' := by intros; ext <;> simp
  zsmul_succ' := by intros; ext <;> simp [add_mul]
  zsmul_neg' := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; ext <;> simp [sub_eq_add_neg]
  natCast_zero := by ext <;> simp
  natCast_succ := by intros; ext <;> simp
  intCast_ofNat := by intros; ext <;> simp
  intCast_negSucc := by intros; ext <;> simp [Int.cast_negSucc]
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  mul_comm := by intros; ext <;> simp <;> ring

instance instNontrivial [Nontrivial A] : Nontrivial (Complexified A) :=
  ⟨⟨0, 1, fun h => zero_ne_one (congrArg re h)⟩⟩

/-- The canonical inclusion `A → A ⊗_ℝ ℂ`, `a ↦ a ⊗ 1 = a + 0 i`. -/
def ofReal : A →+* Complexified A where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

@[simp] theorem ofReal_re (a : A) : (ofReal a).re = a := rfl
@[simp] theorem ofReal_im (a : A) : (ofReal a).im = 0 := rfl

theorem ofReal_injective : Function.Injective (ofReal : A → Complexified A) :=
  fun _ _ h => congrArg re h

/-- The imaginary unit `i = 1 ⊗ i` of `A ⊗_ℝ ℂ`. -/
def I : Complexified A := ⟨0, 1⟩

@[simp] theorem I_re : (I : Complexified A).re = 0 := rfl
@[simp] theorem I_im : (I : Complexified A).im = 1 := rfl

theorem I_mul_I : (I : Complexified A) * I = -1 := by ext <;> simp

theorem re_add_im (z : Complexified A) : ofReal z.re + ofReal z.im * I = z := by ext <;> simp

theorem mk_eq (a b : A) : (⟨a, b⟩ : Complexified A) = ofReal a + ofReal b * I := by ext <;> simp

/-- The complexification of a ring homomorphism, componentwise. -/
def map (f : A →+* B) : Complexified A →+* Complexified B where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp

@[simp] theorem map_re (f : A →+* B) (z : Complexified A) : (map f z).re = f z.re := rfl
@[simp] theorem map_im (f : A →+* B) (z : Complexified A) : (map f z).im = f z.im := rfl

@[simp]
theorem map_id : map (RingHom.id A) = RingHom.id (Complexified A) :=
  RingHom.ext fun _ => rfl

theorem map_comp {C : Type*} [CommRing C] (g : B →+* C) (f : A →+* B) :
    map (g.comp f) = (map g).comp (map f) :=
  RingHom.ext fun _ => rfl

theorem map_comp_apply {C : Type*} [CommRing C] (g : B →+* C) (f : A →+* B) (z : Complexified A) :
    map g (map f z) = map (g.comp f) z := rfl

@[simp] theorem map_ofReal (f : A →+* B) (a : A) : map f (ofReal a) = ofReal (f a) := by
  ext <;> simp

@[simp] theorem map_I (f : A →+* B) : map f (I : Complexified A) = I := by ext <;> simp

theorem map_injective {f : A →+* B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun z w h => by
    ext
    · exact hf (congrArg re h)
    · exact hf (congrArg im h)

theorem map_surjective {f : A →+* B} (hf : Function.Surjective f) : Function.Surjective (map f) :=
  fun w => by
    obtain ⟨a, ha⟩ := hf w.re
    obtain ⟨b, hb⟩ := hf w.im
    exact ⟨⟨a, b⟩, by ext <;> simp [ha, hb]⟩

theorem map_bijective {f : A →+* B} (hf : Function.Bijective f) : Function.Bijective (map f) :=
  ⟨map_injective hf.1, map_surjective hf.2⟩

/-- The complexification of a ring isomorphism. -/
noncomputable def mapEquiv (e : A ≃+* B) : Complexified A ≃+* Complexified B :=
  RingEquiv.ofBijective (map e.toRingHom) (map_bijective e.bijective)

@[simp] theorem mapEquiv_apply (e : A ≃+* B) (z : Complexified A) :
    mapEquiv e z = map e.toRingHom z := rfl

/-- The `ℂ`-structure of `A ⊗_ℝ ℂ` induced by an `ℝ`-structure `φ : ℝ →+* A` of `A`:
`c ↦ φ(Re c) + φ(Im c) i`. -/
def algebraMapComplex (φ : ℝ →+* A) : ℂ →+* Complexified A where
  toFun c := ⟨φ c.re, φ c.im⟩
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp [Complex.mul_re, Complex.mul_im]
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp

@[simp] theorem algebraMapComplex_re (φ : ℝ →+* A) (c : ℂ) :
    (algebraMapComplex φ c).re = φ c.re := rfl
@[simp] theorem algebraMapComplex_im (φ : ℝ →+* A) (c : ℂ) :
    (algebraMapComplex φ c).im = φ c.im := rfl

theorem algebraMapComplex_ofReal (φ : ℝ →+* A) (r : ℝ) :
    algebraMapComplex φ (r : ℂ) = ofReal (φ r) := by ext <;> simp

theorem algebraMapComplex_I (φ : ℝ →+* A) : algebraMapComplex φ Complex.I = I := by ext <;> simp

theorem map_comp_algebraMapComplex (f : A →+* B) (φ : ℝ →+* A) :
    (map f).comp (algebraMapComplex φ) = algebraMapComplex (f.comp φ) :=
  RingHom.ext fun c => Complexified.ext (by simp) (by simp)

section Algebra

variable {R : Type*} [CommSemiring R] [Algebra R A]

instance instSMul : SMul R (Complexified A) := ⟨fun r z => ⟨r • z.re, r • z.im⟩⟩

@[simp] theorem smul_re (r : R) (z : Complexified A) : (r • z).re = r • z.re := rfl
@[simp] theorem smul_im (r : R) (z : Complexified A) : (r • z).im = r • z.im := rfl

/-- The `R`-algebra structure of `A ⊗_ℝ ℂ` from one of `A` (through `ofReal`). -/
instance instAlgebra : Algebra R (Complexified A) where
  algebraMap := ofReal.comp (algebraMap R A)
  commutes' _ _ := mul_comm _ _
  smul := (· • ·)
  smul_def' r z := by ext <;> simp [Algebra.smul_def]

@[simp]
theorem algebraMap_apply (r : R) :
    algebraMap R (Complexified A) r = ofReal (algebraMap R A r) := rfl

/-- `ofReal` as an `R`-algebra homomorphism. -/
def ofRealAlgHom : A →ₐ[R] Complexified A := { ofReal with commutes' := fun _ => rfl }

@[simp] theorem ofRealAlgHom_apply (a : A) :
    (ofRealAlgHom : A →ₐ[R] Complexified A) a = ofReal a := rfl

end Algebra

/-! ### The norm `a² + b²`, units and the local-ring theorem -/

/-- The norm `N(a + bi) = a² + b²`, multiplicative. -/
def norm (z : Complexified A) : A := z.re * z.re + z.im * z.im

theorem norm_mul (z w : Complexified A) : norm (z * w) = norm z * norm w := by
  simp only [norm, mul_re, mul_im]; ring

theorem norm_one : norm (1 : Complexified A) = 1 := by simp [norm]

/-- The conjugate `a - bi`. -/
def conj (z : Complexified A) : Complexified A := ⟨z.re, -z.im⟩

theorem mul_conj (z : Complexified A) : z * conj z = ofReal (norm z) := by
  ext
  · simp only [mul_re, conj, norm, ofReal_re, mul_neg, sub_neg_eq_add]
  · simp only [mul_im, conj, ofReal_im, mul_neg]; ring

theorem isUnit_iff_isUnit_norm (z : Complexified A) : IsUnit z ↔ IsUnit (norm z) := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : norm (u : Complexified A) * norm (↑u⁻¹ : Complexified A) = 1 := by
      rw [← norm_mul, Units.mul_inv, norm_one]
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  · rintro ⟨u, hu⟩
    refine isUnit_iff_exists_inv.mpr ⟨conj z * ofReal (↑u⁻¹ : A), ?_⟩
    rw [← mul_assoc, mul_conj, ← map_mul, ← hu, Units.mul_inv, map_one]

theorem isUnit_ofReal_iff (a : A) : IsUnit (ofReal a) ↔ IsUnit a := by
  rw [isUnit_iff_isUnit_norm]
  simp [norm]

/-- The local-ring theorem behind Hironaka's "`(X, 𝒪_X ⊗_ℝ ℂ)` is a `ℂ`-local-ringed space"
[Hir64, Ch. 0, §1, p. 120]: if `A` is a local ring with residue field `ℝ` — every element is
congruent modulo `𝔪_A` to a constant `φ c`, `φ : ℝ →+* A` — then `A ⊗_ℝ ℂ = A[i]` is a local
ring. Proof: for `z = a + bi` with `a ≡ φ α`, `b ≡ φ β`, the norm `a² + b² ≡ φ(α² + β²)`; if
`(α, β) ≠ 0` this is a unit of `A` (a constant outside `𝔪_A`), so `z` is a unit; otherwise
`a, b ∈ 𝔪_A` and `1 - z` has norm `≡ 1`, a unit. -/
theorem isLocalRing_of_exists_sub_mem [IsLocalRing A] (φ : ℝ →+* A)
    (h : ∀ a : A, ∃ c : ℝ, a - φ c ∈ IsLocalRing.maximalIdeal A) :
    IsLocalRing (Complexified A) := by
  have hunit : ∀ c : ℝ, c ≠ 0 → IsUnit (φ c) := fun c hc => by
    have : φ c * φ c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    exact isUnit_iff_exists_inv.mpr ⟨_, this⟩
  -- an element congruent to a nonzero constant is a unit
  have hcong : ∀ (a : A) (c : ℝ), c ≠ 0 → a - φ c ∈ IsLocalRing.maximalIdeal A → IsUnit a := by
    intro a c hc hm
    by_contra ha
    have hmem : a ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr ha)
    have hφ : φ c ∈ IsLocalRing.maximalIdeal A := by
      have := Ideal.sub_mem _ hmem hm
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hφ (hunit c hc))
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨α, hα⟩ := h z.re
  obtain ⟨β, hβ⟩ := h z.im
  -- the norm is congruent to `φ(α² + β²)`
  have hnorm : ∀ (a b : A) (α β : ℝ), a - φ α ∈ IsLocalRing.maximalIdeal A →
      b - φ β ∈ IsLocalRing.maximalIdeal A →
      (a * a + b * b) - φ (α * α + β * β) ∈ IsLocalRing.maximalIdeal A := by
    intro a b α β ha hb
    have e : (a * a + b * b) - φ (α * α + β * β) =
        (a - φ α) * (a + φ α) + (b - φ β) * (b + φ β) := by
      simp only [map_add, map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
  by_cases hαβ : α * α + β * β = 0
  · -- both residues vanish: `1 - z` is a unit
    right
    have hα0 : α = 0 := by nlinarith [mul_self_nonneg α, mul_self_nonneg β]
    have hβ0 : β = 0 := by nlinarith [mul_self_nonneg α, mul_self_nonneg β]
    subst hα0; subst hβ0
    rw [isUnit_iff_isUnit_norm]
    refine hcong _ 1 one_ne_zero ?_
    have := hnorm (1 - z).re (1 - z).im 1 0 ?_ ?_
    · simpa [norm] using this
    · simp only [sub_re, one_re, map_one]
      have : (1 - z.re) - 1 = -(z.re - φ 0) := by rw [map_zero]; ring
      rw [this]; exact neg_mem hα
    · simp only [sub_im, one_im, map_zero, zero_sub]
      have : -z.im - 0 = -(z.im - φ 0) := by rw [map_zero]; ring
      rw [this]; exact neg_mem hβ
  · left
    rw [isUnit_iff_isUnit_norm]
    exact hcong _ _ hαβ (hnorm z.re z.im α β hα hβ)

/-- A local homomorphism complexifies to a local homomorphism. -/
theorem isLocalHom_map (f : A →+* B) [IsLocalHom f] :
    IsLocalHom (map f) where
  map_nonunit z hz := by
    rw [isUnit_iff_isUnit_norm] at hz ⊢
    have : norm (map f z) = f (norm z) := by simp [norm]
    rw [this] at hz
    exact IsLocalHom.map_nonunit _ hz

/-! ### The identification with Mathlib's tensor product `A ⊗[ℝ] ℂ` -/

section Tensor

open TensorProduct

variable [Algebra ℝ A]

/-- The `ℂ`-structure of `A ⊗_ℝ ℂ` as an `ℝ`-algebra homomorphism `ℂ →ₐ[ℝ] A[i]`. -/
noncomputable def algebraMapComplexAlgHom : ℂ →ₐ[ℝ] Complexified A :=
  { algebraMapComplex (algebraMap ℝ A) with
    commutes' := fun r =>
      Complexified.ext (by simp) (by simp) }

@[simp] theorem algebraMapComplexAlgHom_apply (c : ℂ) :
    (algebraMapComplexAlgHom : ℂ →ₐ[ℝ] Complexified A) c =
      ⟨algebraMap ℝ A c.re, algebraMap ℝ A c.im⟩ :=
  rfl

/-- `A ⊗[ℝ] ℂ → A[i]`: `a ⊗ c ↦ a · (Re c + Im c · i)`. -/
noncomputable def ofTensor : A ⊗[ℝ] ℂ →ₐ[ℝ] Complexified A :=
  Algebra.TensorProduct.productMap ofRealAlgHom algebraMapComplexAlgHom

@[simp] theorem ofTensor_tmul (a : A) (c : ℂ) :
    ofTensor (a ⊗ₜ c) = ofReal a * ⟨algebraMap ℝ A c.re, algebraMap ℝ A c.im⟩ := by
  rw [ofTensor, Algebra.TensorProduct.productMap_apply_tmul]
  rfl

/-- `A[i] → A ⊗[ℝ] ℂ`: `a + b i ↦ a ⊗ 1 + b ⊗ i`. -/
noncomputable def toTensor : Complexified A →ₐ[ℝ] A ⊗[ℝ] ℂ where
  toFun z := z.re ⊗ₜ 1 + z.im ⊗ₜ Complex.I
  map_one' := by simp [Algebra.TensorProduct.one_def]
  map_mul' z w := by
    simp only [mul_re, mul_im, sub_tmul, add_tmul, add_mul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Complex.I_mul_I, tmul_neg]
    abel
  map_zero' := by simp
  map_add' z w := by
    simp only [add_re, add_im, add_tmul]
    abel
  commutes' r := by
    simp [Algebra.TensorProduct.algebraMap_apply]

@[simp] theorem toTensor_apply (z : Complexified A) :
    toTensor z = z.re ⊗ₜ 1 + z.im ⊗ₜ Complex.I := rfl

theorem toTensor_ofTensor (t : A ⊗[ℝ] ℂ) : toTensor (ofTensor t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    simp only [ofTensor_tmul, toTensor_apply, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul,
      sub_zero, add_zero]
    rw [mul_comm a, mul_comm a, ← Algebra.smul_def, ← Algebra.smul_def, smul_tmul, smul_tmul,
      ← tmul_add, Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
  | add x y hx hy => simp [map_add, hx, hy]

theorem ofTensor_toTensor (z : Complexified A) : ofTensor (toTensor z) = z := by
  simp only [toTensor_apply, map_add, ofTensor_tmul]
  ext <;> simp

/-- The identification `A[i] ≅ A ⊗[ℝ] ℂ` (Hironaka's `𝒪_X ⊗_ℝ ℂ` read sectionwise as `𝒪_X[i]`):
`a + b i ↦ a ⊗ 1 + b ⊗ i`. -/
noncomputable def tensorEquiv : Complexified A ≃ₐ[ℝ] A ⊗[ℝ] ℂ :=
  AlgEquiv.ofAlgHom toTensor ofTensor (AlgHom.ext toTensor_ofTensor) (AlgHom.ext ofTensor_toTensor)

@[simp] theorem tensorEquiv_apply (z : Complexified A) :
    tensorEquiv z = z.re ⊗ₜ 1 + z.im ⊗ₜ Complex.I := rfl

theorem tensorEquiv_ofReal (a : A) : tensorEquiv (ofReal a) = a ⊗ₜ 1 := by simp

theorem tensorEquiv_I : tensorEquiv (I : Complexified A) = 1 ⊗ₜ Complex.I := by simp

end Tensor

/-! ### Noetherianity: `A[i]` is Noetherian when `A` is -/

section Noetherian

variable {A : Type u} [CommRing A]

/-- `A[i]` is generated by `1` and `i` as an `A`-module: the image of `A × A`. -/
theorem surjective_ofRealPair :
    Function.Surjective (fun p : A × A => (ofReal p.1 + ofReal p.2 * I : Complexified A)) := by
  intro z
  refine ⟨(z.re, z.im), ?_⟩
  ext <;> simp

/-- The `A`-linear map `A × A → A[i]`, `(a, b) ↦ a + b i`. -/
def ofRealPairLinear : (A × A) →ₗ[A] Complexified A where
  toFun p := ofReal p.1 + ofReal p.2 * I
  map_add' p q := by ext <;> simp [add_mul]
  map_smul' c p := by ext <;> simp [Algebra.smul_def]

theorem surjective_ofRealPairLinear : Function.Surjective (ofRealPairLinear (A := A)) :=
  surjective_ofRealPair

instance instModuleFinite : Module.Finite A (Complexified A) :=
  Module.Finite.of_surjective ofRealPairLinear surjective_ofRealPairLinear

/-- `A[i] = A ⊗_ℝ ℂ` is Noetherian when `A` is (a finite `A`-module). -/
instance instIsNoetherianRing [IsNoetherianRing A] : IsNoetherianRing (Complexified A) :=
  IsNoetherianRing.of_finite A (Complexified A)

end Noetherian

end Complexified

end AnalyticSpace
