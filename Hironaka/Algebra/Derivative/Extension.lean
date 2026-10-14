/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# The derivative of an ideal under a formally smooth extension

[Kol07, Lemma 74 (4)]: "if `f : Y → X` is smooth, then `D(f^*I) = f^*(D(I))`". This module is the
affine-local layer: for a scalar tower `k → A → B` of commutative rings with `φ = algebraMap A B`
and an ideal `J` of `A`, `D(J B) = D(J) B` when `B` is formally smooth over `A` and `Ω_{A/k}` is
finite projective (`Ideal.derivative_map_of_formallySmooth`).

* `D(J) B ⊆ D(J B)` holds as soon as every `k`-derivation `δ` of `A` extends to a `k`-derivation
  `δ̃` of `B`, `δ̃ ∘ φ = φ ∘ δ`: then `φ(δ f) = δ̃(φ f) ∈ D(J B)`
  (`Ideal.map_derivative_le_of_forall_exists_extension`). For `B` formally smooth over `A` such
  extensions exist (`Derivation.exists_extension_of_formallySmooth`): the Jacobi–Zariski
  sequence `H¹(L_{B/A}) → B ⊗_A Ω_{A/k} → Ω_{B/k} → Ω_{B/A} → 0` is exact ([Sta, Tag 00S2];
  Mathlib's `Algebra.H1Cotangent.exact_δ_mapBaseChange` and
  `KaehlerDifferential.exact_mapBaseChange_map`), `H¹(L_{B/A}) = 0` and `Ω_{B/A}` is projective
  for `B` formally smooth over `A` ([Sta, Tag 00TI]), so `B ⊗_A Ω_{A/k} → Ω_{B/k}` is a split
  injection (`Derivation.exists_retraction_mapBaseChange`), and composing a retraction with
  `B ⊗_A Ω_{A/k} → B`, `b ⊗ da ↦ b φ(δ a)`, gives `δ̃` through `Der_k(B, B) ≅ Hom_B(Ω_{B/k}, B)`.
* `D(J B) ⊆ D(J) B` holds as soon as every `k`-derivation `A → B` is a `B`-combination of the
  `φ ∘ ∂`, `∂ ∈ Der_k(A, A)` (`Ideal.derivative_map_le_of_forall_mem_span`): for a `k`-derivation
  `δ` of `B` and `f ∈ J`, `δ(φ f) = ∑ bᵢ φ(∂ᵢ f) ∈ D(J) B`, and Leibniz extends this from the
  generators `φ f` to all of `J B`. The spanning holds when `Ω_{A/k}` is finite projective
  (`Derivation.mem_span_range_compDer_of_projective`): `Ω_{A/k}` is a retract of a finite free
  module `Aⁿ`, so an `A`-linear map `Ω_{A/k} → B` is `∑ᵢ bᵢ · (φ ∘ ℓᵢ)` with `ℓᵢ : Ω_{A/k} → A`.
  This inclusion needs no hypothesis on `B`, only that `Ω_{A/k}` is finite projective (Kollár's `X`
  is smooth over `k`); the étale case is [Wlo05, Lemma 2.6.5], proved there through the
  completions.
* The polynomial algebra `B = A[y₁, …, y_m]` is formally smooth over `A`
  (`Ideal.derivative_map_mvPolynomial`).

The sheaf form is `Hironaka/Scheme/IdealSheaf/Derivative/Pullback.lean`; the extension of
derivations is also used for étale parameters (`Hironaka/Scheme/Snc/EtaleParameters.lean`).
-/

public section

open KaehlerDifferential
open scoped TensorProduct

namespace Derivation

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-- For `B` formally smooth over `A`, the base-change map `B ⊗_A Ω_{A/k} → Ω_{B/k}` is a split
injection: it is injective because `H¹(L_{B/A}) = 0` (the Jacobi–Zariski sequence,
[Sta, Tag 00S2]), its cokernel `Ω_{B/A}` is projective, and a section of `Ω_{B/k} → Ω_{B/A}` gives
a retraction (Mathlib's splitting lemma). -/
theorem exists_retraction_mapBaseChange [Algebra.FormallySmooth A B] :
    ∃ r : Ω[B⁄k] →ₗ[B] B ⊗[A] Ω[A⁄k], r ∘ₗ mapBaseChange k A B = LinearMap.id := by
  have hinj : Function.Injective (mapBaseChange k A B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k A B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hsurj : Function.Surjective (map k A B B) := map_surjective k A B
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (map k A B B) LinearMap.id hsurj
  have h01 := ((exact_mapBaseChange_map k A B).split_tfae hinj hsurj).out 1 2
  exact h01.mp ⟨s, hs⟩

/-- For `B` formally smooth over `A`, every `k`-derivation `δ` of `A` extends to a `k`-derivation
`δ̃` of `B`, `δ̃ ∘ φ = φ ∘ δ`: compose a retraction of `B ⊗_A Ω_{A/k} → Ω_{B/k}` with
`b ⊗ da ↦ b φ(δ a)`. -/
theorem exists_extension_of_formallySmooth [Algebra.FormallySmooth A B] (δ : Derivation k A A) :
    ∃ δ' : Derivation k B B, ∀ a : A, δ' (algebraMap A B a) = algebraMap A B (δ a) := by
  obtain ⟨r, hr⟩ := exists_retraction_mapBaseChange (k := k) (A := A) (B := B)
  let ℓ : B ⊗[A] Ω[A⁄k] →ₗ[B] B :=
    ((Algebra.linearMap A B).compDer δ).liftKaehlerDifferential.liftBaseChange B
  refine ⟨linearMapEquivDerivation k B (ℓ ∘ₗ r), fun a => ?_⟩
  have h1 : linearMapEquivDerivation k B (ℓ ∘ₗ r) (algebraMap A B a) =
      ℓ (r (D k B (algebraMap A B a))) := rfl
  have h2 : D k B (algebraMap A B a) = mapBaseChange k A B (1 ⊗ₜ D k A a) := by
    rw [mapBaseChange_tmul, one_smul, map_D]
  have h3 : r (mapBaseChange k A B (1 ⊗ₜ D k A a)) = 1 ⊗ₜ D k A a := by
    simpa using LinearMap.congr_fun hr (1 ⊗ₜ D k A a)
  rw [h1, h2, h3]
  simp [ℓ, LinearMap.liftBaseChange_tmul, liftKaehlerDifferential_comp_D]

/-- When `Ω_{A/k}` is finite projective, every `k`-derivation `d : A → B` is a `B`-linear
combination of the `φ ∘ ∂`, `∂ ∈ Der_k(A, A)`, that is, `Der_k(A, B) = B ⊗_A Der_k(A, A)`. Through
`Der_k(A, B) ≅ Hom_A(Ω_{A/k}, B)`: `Ω_{A/k}` is a retract of a finite free module `Aⁿ`
(`g ∘ s = id`), so `ℓ = ℓ ∘ g ∘ s = ∑ᵢ ℓ(g eᵢ) · (φ ∘ (prᵢ ∘ s))`. -/
theorem mem_span_range_compDer_of_projective [Module.Finite A (Ω[A⁄k])]
    [Module.Projective A (Ω[A⁄k])] (d : Derivation k A B) :
    d ∈ Submodule.span B
      (Set.range fun δ : Derivation k A A => (Algebra.linearMap A B).compDer δ) := by
  classical
  obtain ⟨n, g, s, -, -, hgs⟩ := Module.Finite.exists_comp_eq_id_of_projective A (Ω[A⁄k])
  set ℓ : Ω[A⁄k] →ₗ[A] B := d.liftKaehlerDifferential with hℓ
  let der : Fin n → Derivation k A A := fun i =>
    linearMapEquivDerivation k A (LinearMap.proj i ∘ₗ s)
  have key : d = ∑ i, ℓ (g (Pi.single i 1)) • (Algebra.linearMap A B).compDer (der i) := by
    ext a
    have h1 : d a = ℓ (D k A a) := (d.liftKaehlerDifferential_comp_D a).symm
    have h2 : D k A a = g (s (D k A a)) := by
      rw [← LinearMap.comp_apply, hgs, LinearMap.id_apply]
    have h3 : s (D k A a) = ∑ i, s (D k A a) i • Pi.single i (1 : A) := by
      have := ((Pi.basisFun A (Fin n)).sum_repr (s (D k A a))).symm
      simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using this
    have hL : d a = ∑ i, ℓ (g (Pi.single i 1)) * algebraMap A B (s (D k A a) i) := by
      rw [h1]
      conv_lhs => rw [h2, h3]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul, LinearMap.map_smul, Algebra.smul_def, mul_comm]
    have hc : (⇑(∑ i, ℓ (g (Pi.single i 1)) • (Algebra.linearMap A B).compDer (der i)) : A → B) =
        ∑ i, ⇑(ℓ (g (Pi.single i 1)) • (Algebra.linearMap A B).compDer (der i)) :=
      map_sum Derivation.coeFnAddMonoidHom _ _
    rw [hL, hc, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [key]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨der i, rfl⟩)

end Derivation

namespace Ideal

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

omit [IsScalarTower k A B] in
/-- If every `k`-derivation of `A` extends to `B`, then `D(J) B ⊆ D(J B)`: `φ(δ f) = δ̃(φ f)` is a
derivative of an element of `J B`. -/
theorem map_derivative_le_of_forall_exists_extension
    (h : ∀ δ : Derivation k A A, ∃ δ' : Derivation k B B,
      ∀ a : A, δ' (algebraMap A B a) = algebraMap A B (δ a))
    (J : Ideal A) :
    (derivative k J).map (algebraMap A B) ≤ derivative k (J.map (algebraMap A B)) := by
  rw [Ideal.map_le_iff_le_comap]
  refine derivative_le_iff.mpr ⟨fun f hf => Ideal.mem_comap.mpr
    (le_derivative _ (Ideal.mem_map_of_mem _ hf)), fun δ f hf => ?_⟩
  obtain ⟨δ', hδ'⟩ := h δ
  rw [Ideal.mem_comap, ← hδ' f]
  exact derivation_apply_mem_derivative δ' (Ideal.mem_map_of_mem _ hf)

/-- `D(J) B ⊆ D(J B)` for `B` formally smooth over `A`. -/
theorem map_derivative_le_derivative_map_of_formallySmooth [Algebra.FormallySmooth A B]
    (J : Ideal A) :
    (derivative k J).map (algebraMap A B) ≤ derivative k (J.map (algebraMap A B)) :=
  map_derivative_le_of_forall_exists_extension
    (fun δ => δ.exists_extension_of_formallySmooth (B := B)) J

/-- If every `k`-derivation `A → B` is a `B`-combination of the `φ ∘ ∂`, then `D(J B) ⊆ D(J) B`:
on the generators `δ(φ f) = ∑ bᵢ φ(∂ᵢ f)`, and `δ(φ(f) b) = b δ(φ f) + φ(f) δ(b) ∈ φ(D(J)) B`. -/
theorem derivative_map_le_of_forall_mem_span
    (h : ∀ d : Derivation k A B, d ∈ Submodule.span B
      (Set.range fun δ : Derivation k A A => (Algebra.linearMap A B).compDer δ))
    (J : Ideal A) :
    derivative k (J.map (algebraMap A B)) ≤ (derivative k J).map (algebraMap A B) := by
  refine derivative_le_iff.mpr ⟨Ideal.map_mono (le_derivative J), fun δ' x hx => ?_⟩
  have key : ∀ f ∈ J, δ' (algebraMap A B f) ∈ (derivative k J).map (algebraMap A B) := by
    intro f hf
    have hspan : ∀ d ∈ Submodule.span B
        (Set.range fun δ : Derivation k A A => (Algebra.linearMap A B).compDer δ),
        d f ∈ (derivative k J).map (algebraMap A B) := by
      intro d hd
      induction hd using Submodule.span_induction with
      | mem d hd =>
        obtain ⟨δ, rfl⟩ := hd
        exact Ideal.mem_map_of_mem _ (derivation_apply_mem_derivative δ hf)
      | zero => simp
      | add d₁ d₂ _ _ h1 h2 => rw [Derivation.add_apply]; exact Ideal.add_mem _ h1 h2
      | smul b d _ hd => rw [Derivation.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ hd
    exact hspan _ (h (δ'.compAlgebraMap A))
  change x ∈ Ideal.span (algebraMap A B '' (J : Set A)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact key f hf
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | smul b x hx' hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx)
      (Ideal.mul_mem_right _ _ (Ideal.map_mono (le_derivative J) hx'))

/-- `D(J B) ⊆ D(J) B` when `Ω_{A/k}` is finite projective, for every `A`-algebra `B`; the étale
case and the polynomial case are instances. -/
theorem derivative_map_le_map_derivative_of_projective [Module.Finite A (Ω[A⁄k])]
    [Module.Projective A (Ω[A⁄k])] (J : Ideal A) :
    derivative k (J.map (algebraMap A B)) ≤ (derivative k J).map (algebraMap A B) :=
  derivative_map_le_of_forall_mem_span (fun d => d.mem_span_range_compDer_of_projective) J

/-- [Kol07, Lemma 74 (4)], affine-local form: for `B` formally smooth over `A` and `Ω_{A/k}`
finite projective, `D(J B) = D(J) B`. -/
theorem derivative_map_of_formallySmooth [Algebra.FormallySmooth A B]
    [Module.Finite A (Ω[A⁄k])] [Module.Projective A (Ω[A⁄k])] (J : Ideal A) :
    derivative k (J.map (algebraMap A B)) = (derivative k J).map (algebraMap A B) :=
  le_antisymm (derivative_map_le_map_derivative_of_projective J)
    (map_derivative_le_derivative_map_of_formallySmooth J)

/-- The polynomial case: for `B = A[yⱼ : j ∈ σ]` and `Ω_{A/k}` finite projective,
`D(J B) = D(J) B`. -/
theorem derivative_map_mvPolynomial {σ : Type*} [Module.Finite A (Ω[A⁄k])]
    [Module.Projective A (Ω[A⁄k])] (J : Ideal A) :
    derivative k (J.map (algebraMap A (MvPolynomial σ A))) =
      (derivative k J).map (algebraMap A (MvPolynomial σ A)) :=
  derivative_map_of_formallySmooth J

end Ideal
