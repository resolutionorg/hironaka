/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.DerivationLocalization
public import Hironaka.Algebra.Derivative.Basic
public import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The derivative of an ideal commutes with localization

For a localization `B = M⁻¹A` of a `k`-algebra `A`, `D(J B) = D(J) B` (`Ideal.derivative_map`):
the compatibility that makes the derivative of an ideal a sheaf ([Kol07, Definition 73] defines
`D(I)` through the sheaf `Der_X`; `Hironaka/Scheme/IdealSheaf/Derivative/Sheaf.lean`).

* `⊇`: a `k`-derivation of `A` extends to `B` by the quotient rule (as the `∂/∂uᵢ` extend to the
  function field in the proof of [Wlo05, Lemma 2.6.3]): `Derivation.localization` of
  `Hironaka/Algebra/DerivationLocalization.lean` for `Localization M`, transported to an arbitrary
  `B` with `IsLocalization M B` along Mathlib's `IsLocalization.algEquiv`
  (`Derivation.extendToLocalization`, `extendToLocalization_algebraMap`); so
  `φ (δ f) = δ̃ (φ f) ∈ D(J B)` (`derivative_map_le`).
* `⊆`: when `Ω_{A/k}` is finitely presented, every `k`-derivation `δ'` of `B` is, up to a unit, an
  extension: its restriction `d : A → B` corresponds under `linearMapEquivDerivation` to an
  `A`-linear map `Ω_{A/k} → B`, which by Mathlib's
  `Module.FinitePresentation.exists_lift_of_isLocalizedModule` is `s⁻¹ · (φ ∘ h)` for some
  `h : Ω_{A/k} → A` and `s ∈ M` (`exists_derivation_smul_eq`); so
  `δ' (φ f) = φ(s)⁻¹ φ(δ_h f) ∈ D(J) B` for `f ∈ J`, and Leibniz extends this to all of `J B`.

Used for the derivative ideal sheaf (`Hironaka/Scheme/IdealSheaf/Derivative/Sheaf.lean`), its
logarithmic version (`Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicLocalization.lean`), for
Theorem 76 on schemes (`Hironaka/Scheme/BlowUpSequence/TransformDerivative.lean`), on affine space
(`Hironaka/Scheme/IdealSheaf/Order/AffineSpace.lean`) and on analytic spaces
(`Hironaka/Analytic/Rueckert/Hypersurface.lean`). The statement is not in the sources.
-/

@[expose] public section

namespace Derivation

variable (k : Type*) {A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A]
  [Algebra A B] [Algebra k B] [IsScalarTower k A B] (M : Submonoid A) [IsLocalization M B]

/-- The `k`-algebra equivalence `Localization M ≃ B` of an abstract localization. -/
noncomputable def localizationAlgEquiv : Localization M ≃ₐ[k] B :=
  (IsLocalization.algEquiv M (Localization M) B).restrictScalars k

theorem localizationAlgEquiv_algebraMap (a : A) :
    localizationAlgEquiv k (B := B) M (algebraMap A (Localization M) a) = algebraMap A B a :=
  (IsLocalization.algEquiv M (Localization M) B).commutes a

theorem localizationAlgEquiv_symm_algebraMap (a : A) :
    (localizationAlgEquiv k (B := B) M).symm (algebraMap A B a) =
      algebraMap A (Localization M) a :=
  (IsLocalization.algEquiv M (Localization M) B).symm.commutes a

variable {k}

/-- **Extension of a derivation to an abstract localization**: `Derivation.localization` of
`Hironaka/Algebra/DerivationLocalization.lean` transported along `IsLocalization.algEquiv`. -/
noncomputable def extendToLocalization (D : Derivation k A A) : Derivation k B B where
  toLinearMap := (localizationAlgEquiv k (B := B) M).toLinearEquiv.toLinearMap ∘ₗ
    (D.localization M).toLinearMap ∘ₗ
      (localizationAlgEquiv k (B := B) M).symm.toLinearEquiv.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a b := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      AlgEquiv.toLinearEquiv_apply, map_mul, Derivation.coeFn_coe, Derivation.leibniz, map_add,
      smul_eq_mul, AlgEquiv.apply_symm_apply]

theorem extendToLocalization_apply (D : Derivation k A A) (b : B) :
    D.extendToLocalization M b =
      localizationAlgEquiv k (B := B) M
        (D.localization M ((localizationAlgEquiv k (B := B) M).symm b)) :=
  rfl

/-- The extension agrees with `D` on the image of `A`. -/
@[simp]
theorem extendToLocalization_algebraMap (D : Derivation k A A) (a : A) :
    D.extendToLocalization M (algebraMap A B a) = algebraMap A B (D a) := by
  rw [extendToLocalization_apply, localizationAlgEquiv_symm_algebraMap, localization_algebraMap,
    localizationAlgEquiv_algebraMap]

end Derivation

namespace Ideal

open KaehlerDifferential

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra A B]
  [Algebra k B] [IsScalarTower k A B]

/-- The inclusion `D(J) B ⊆ D(J B)`: derivations of `A` extend to `B`. -/
theorem derivative_map_le (M : Submonoid A) [IsLocalization M B] (J : Ideal A) :
    (derivative k J).map (algebraMap A B) ≤ derivative k (J.map (algebraMap A B)) := by
  rw [Ideal.map_le_iff_le_comap]
  refine derivative_le_iff.mpr ⟨fun f hf => Ideal.mem_comap.mpr
    (le_derivative _ (Ideal.mem_map_of_mem _ hf)), fun δ f hf => ?_⟩
  rw [Ideal.mem_comap, ← δ.extendToLocalization_algebraMap M]
  exact derivation_apply_mem_derivative _ (Ideal.mem_map_of_mem _ hf)

/-- Every `k`-derivation of the localization `B` is, up to a unit `φ s`, the extension of a
`k`-derivation of `A`, when `Ω_{A/k}` is finitely presented (Mathlib's
`Module.FinitePresentation.exists_lift_of_isLocalizedModule` for `Hom_A(Ω_{A/k}, B)`). -/
theorem exists_derivation_smul_eq (M : Submonoid A) [IsLocalization M B]
    [Module.FinitePresentation A (Ω[A⁄k])] (δ' : Derivation k B B) :
    ∃ (δ : Derivation k A A) (s : M), ∀ a : A,
      algebraMap A B (δ a) = algebraMap A B s * δ' (algebraMap A B a) := by
  let d : Derivation k A B := δ'.compAlgebraMap A
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule M
    (Algebra.linearMap A B) d.liftKaehlerDifferential
  refine ⟨linearMapEquivDerivation k A h, s, fun a => ?_⟩
  have h1 := LinearMap.congr_fun hs (D k A a)
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
    Derivation.liftKaehlerDifferential_comp_D, Submonoid.smul_def, Algebra.smul_def] at h1
  have h2 : (linearMapEquivDerivation k A h) a = h (D k A a) := rfl
  rw [h2, h1]
  simp [d]

/-- `D(J B) = D(J) B` for a localization `B = M⁻¹A` when `Ω_{A/k}` is finitely presented. -/
theorem derivative_map (M : Submonoid A) [IsLocalization M B]
    [Module.FinitePresentation A (Ω[A⁄k])] (J : Ideal A) :
    derivative k (J.map (algebraMap A B)) = (derivative k J).map (algebraMap A B) := by
  refine le_antisymm (derivative_le_iff.mpr ⟨Ideal.map_mono (le_derivative J), fun δ' x hx => ?_⟩)
    (derivative_map_le M J)
  obtain ⟨δ, s, hδ⟩ := exists_derivation_smul_eq (k := k) (B := B) M δ'
  have hu : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
  have key : ∀ f ∈ J, δ' (algebraMap A B f) ∈ (derivative k J).map (algebraMap A B) := by
    intro f hf
    have : δ' (algebraMap A B f) = hu.unit⁻¹ * algebraMap A B (δ f) := by
      rw [hδ f, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (derivation_apply_mem_derivative δ hf))
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

end Ideal
