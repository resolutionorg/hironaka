/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Algebra.Derivative.Extension
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.BaseChangeParameters
import Hironaka.Scheme.IdealSheaf.Derivative.Pullback
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The derivative ideal under a change of the base field

[Kol07, Lemma 74 (4)] says that the derivative ideal commutes with smooth pull-back
(`Hironaka/Scheme/IdealSheaf/Derivative/Pullback.lean`). Kollár also asks that resolution commute
with a change of fields `σ : k → L` ([Kol07, 34.2]: the fibre product `X_L = X ×_{Spec k} Spec L`,
with `I_L` and `E_L`), and the functoriality of order reduction under such a change needs the
derivative ideals, and with them the tuning ideal, to commute with it. This module proves that fact:
for `k` of characteristic zero and `X` smooth over `k`, on a cartesian square
`sq : IsPullback p g' f (Spec.map σ)` with `p : X_L → X` the projection and `g' : X_L → Spec L` the
base-changed structure morphism,

  `D_L(p^* I) = p^* D_k(I)`, hence `D_L^r(p^* I) = p^* D_k^r(I)`

(`derivative_comap_of_isPullback_specMap`, `derivativeIter_comap_of_isPullback_specMap`), where
`D_L` is the derivative ideal of the `L`-scheme `X_L` and `D_k` that of the `k`-scheme `X`. The
statement is not in the sources; Włodarczyk's [Wlo05, Lemma 2.9.3] is the analogous compatibility
of the homogenized ideal with smooth morphisms.

## The argument

Both inclusions are checked on stalks (`ext_stalkIdeal`), through `stalkIdeal_derivative` and
`stalkIdeal_comap`: at `y ∈ X_L` with `x = p y`, `A = 𝒪_{X, x}` is a `k`-algebra, `B = 𝒪_{X_L, y}`
an `L`-algebra, and `φ : A → B` the stalk map; to show: `D_L(J B) = D_k(J) B` for `J = I_x`.

* `D_L(J B) ⊆ D_k(J) B`: an `L`-derivation of `B` is a `k`-derivation (`Derivation.restrictScalars`,
  the tower `k → L → B` coming from the commutativity of the square), so
  `D_L(J B) ⊆ D_k(J B)`, and `D_k(J B) = D_k(J) B` is `Ideal.derivative_map_of_formallySmooth` of
  `Hironaka/Algebra/Derivative/Extension.lean`: `φ` is formally smooth
  (`formallySmooth_stalkMap_of_isPullback_specMap`,
  `Hironaka/Scheme/BlowUpSequence/BaseChangeParameters.lean`, where `[CharZero k]` enters) and
  `Ω_{A/k}` is finite projective (`X` smooth over `k`).
* `D_k(J) B ⊆ D_L(J B)`: it suffices that every `k`-derivation `δ` of `A` lifts to an
  `L`-derivation `δ'` of `B` with `δ' ∘ φ = φ ∘ δ`, for then `φ(δ f) = δ'(φ f) ∈ D_L(J B)`. Such
  lifts exist for a base change `B = L ⊗_k A` (Mathlib's `Algebra.IsPushout k L A B`): the
  canonical isomorphism `B ⊗_A Ω_{A/k} ≅ Ω_{B/L}` (`KaehlerDifferential.tensorKaehlerEquiv`) turns
  the `A`-linear map `Ω_{A/k} → B`, `da ↦ φ(δ a)`, into a `B`-linear map `Ω_{B/L} → B`, that is, an
  `L`-derivation of `B` (`Derivation.exists_extension_of_isPushout`). The stalks are not a pushout,
  so this inclusion is proved on sections: for an affine `U ∋ x`, `p⁻¹U = U ×_{Spec k} Spec L` is
  affine and `Γ(p⁻¹U) = L ⊗_k Γ(U)`, by Mathlib's `isPushout_appTop_of_isPullback` for the
  restricted square, transported to `Γ(X, U) → Γ(X_L, p⁻¹U)` along the `ΓSpecIso` and `topIso`
  isomorphisms and read as `Algebra.IsPushout` by `CommRingCat.isPushout_iff_isPushout`
  (`isPushout_appLE_of_isPullback_specMap`). The section-level inclusion
  `D_k(I(U)) Γ(p⁻¹U) ⊆ D_L(I(U) Γ(p⁻¹U))` then passes to the stalk through `stalkIdeal_eq_map_germ`,
  `ideal_comap_of_le` (`Hironaka/Scheme/BlowUp/InverseImage.lean`) and `ideal_derivative`
  (`Hironaka/Scheme/IdealSheaf/Derivative/Sheaf.lean`).

Used for the functoriality of order reduction under a change of fields
(`Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean`,
`Hironaka/Resolution/Algebraic/OrderReduction/Step3Clauses.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/BaseChangeParameters.lean`,
`Hironaka/Resolution/Algebraic/Tuning/Pullback.lean`,
`Hironaka/Resolution/Algebraic/BoundaryClearing/FunctorialityBaseChange.lean`).
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential
open scoped TensorProduct

/-! ### Algebra: derivations along a base change -/

namespace Derivation

variable {k L A B : Type*} [CommRing k] [CommRing L] [CommRing A] [CommRing B] [Algebra k L]
  [Algebra k A] [Algebra k B] [Algebra A B] [Algebra L B] [IsScalarTower k A B]
  [IsScalarTower k L B]

/-- For `B = L ⊗_k A` a base change of the `k`-algebra `A` along `k → L`, every `k`-derivation `δ`
of `A` lifts to an `L`-derivation `δ'` of `B` with `δ' ∘ φ = φ ∘ δ`: under
`Ω_{B/L} ≅ B ⊗_A Ω_{A/k}` (`KaehlerDifferential.tensorKaehlerEquiv`), `δ'` is the `B`-linear map
`b ⊗ da ↦ b φ(δ a)`. -/
theorem exists_extension_of_isPushout [Algebra.IsPushout k L A B] (δ : Derivation k A A) :
    ∃ δ' : Derivation L B B, ∀ a : A, δ' (algebraMap A B a) = algebraMap A B (δ a) := by
  let ℓ : B ⊗[A] Ω[A⁄k] →ₗ[B] B :=
    ((Algebra.linearMap A B).compDer δ).liftKaehlerDifferential.liftBaseChange B
  refine ⟨linearMapEquivDerivation L B (ℓ ∘ₗ (tensorKaehlerEquiv k L A B).symm.toLinearMap),
    fun a => ?_⟩
  have h1 : linearMapEquivDerivation L B (ℓ ∘ₗ (tensorKaehlerEquiv k L A B).symm.toLinearMap)
      (algebraMap A B a) = ℓ ((tensorKaehlerEquiv k L A B).symm (D L B (algebraMap A B a))) :=
    rfl
  have h2 : (tensorKaehlerEquiv k L A B).symm (D L B (algebraMap A B a)) = 1 ⊗ₜ D k A a := by
    rw [LinearEquiv.symm_apply_eq, tensorKaehlerEquiv_tmul_D, one_smul]
  rw [h1, h2]
  simp [ℓ, LinearMap.liftBaseChange_tmul, liftKaehlerDifferential_comp_D]

end Derivation

namespace Ideal

variable {k L A B : Type*} [CommRing k] [CommRing L] [CommRing A] [CommRing B] [Algebra k L]
  [Algebra k A] [Algebra k B] [Algebra A B] [Algebra L B] [IsScalarTower k A B]
  [IsScalarTower k L B]

/-- `D_k(J) B ⊆ D_L(J B)` for `B = L ⊗_k A`: the `L`-derivation lifts of
`Derivation.exists_extension_of_isPushout` carry `φ(δ f) = δ'(φ f)` into `D_L(J B)` (the argument
of `map_derivative_le_of_forall_exists_extension` in `Hironaka/Algebra/Derivative/Extension.lean`,
with `L`-derivations of `B`). -/
theorem map_derivative_le_derivative_map_of_isPushout [Algebra.IsPushout k L A B] (J : Ideal A) :
    (derivative k J).map (algebraMap A B) ≤ derivative L (J.map (algebraMap A B)) := by
  rw [Ideal.map_le_iff_le_comap]
  refine derivative_le_iff.mpr ⟨fun f hf => Ideal.mem_comap.mpr
    (le_derivative _ (Ideal.mem_map_of_mem _ hf)), fun δ f hf => ?_⟩
  obtain ⟨δ', hδ'⟩ := Derivation.exists_extension_of_isPushout (L := L) (B := B) δ
  rw [Ideal.mem_comap, ← hδ' f]
  exact derivation_apply_mem_derivative δ' (Ideal.mem_map_of_mem _ hf)

/-- `D_L(J B) ⊆ D_k(J) B` for a tower `k → L → B`, `k → A → B` with `B` formally smooth over `A`
and `Ω_{A/k}` finite projective: an `L`-derivation of `B` is a `k`-derivation, so
`D_L(J B) ⊆ D_k(J B)`, and `D_k(J B) = D_k(J) B` is `derivative_map_of_formallySmooth`. -/
theorem derivative_map_le_map_derivative_of_restrictScalars [Algebra.FormallySmooth A B]
    [Module.Finite A (Ω[A⁄k])] [Module.Projective A (Ω[A⁄k])] (J : Ideal A) :
    derivative L (J.map (algebraMap A B)) ≤ (derivative k J).map (algebraMap A B) := by
  rw [← derivative_map_of_formallySmooth (k := k) J]
  exact derivative_le_iff.mpr ⟨le_derivative _, fun δ f hf =>
    derivation_apply_mem_derivative (δ.restrictScalars k) hf⟩

end Ideal

/-! ### Geometry: the algebra structures of a base-change square -/

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {L : Type u} [Field L] {X Y : Scheme.{u}}

/-- `Γ(Spec σ)` read through the `ΓSpecIso` identifications is `σ`
(`Scheme.ΓSpecIso_naturality`). -/
theorem ΓSpecIso_inv_comp_appTop_specMap (σ : k →+* L) :
    (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map (CommRingCat.ofHom σ)).appTop =
      CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (.of L)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The `k`-algebra structure of `Γ(Y, V)` induced by `g' ≫ Spec σ` is the `L`-algebra structure
induced by `g'` restricted along `σ`: the tower `k → L → Γ(Y, V)`. -/
theorem Scheme.Hom.algebraMap_sectionsAlgebra_comp_specMap (g' : Y ⟶ Spec (.of L)) (σ : k →+* L)
    (V : Y.Opens) :
    letI := (g' ≫ Spec.map (CommRingCat.ofHom σ)).sectionsAlgebra V
    letI := g'.sectionsAlgebra V
    algebraMap k Γ(Y, V) = (algebraMap L Γ(Y, V)).comp σ := by
  have h : (g' ≫ Spec.map (CommRingCat.ofHom σ)).appLE ⊤ V le_top =
      (Spec.map (CommRingCat.ofHom σ)).appTop ≫ g'.appLE ⊤ V le_top :=
    Scheme.Hom.comp_appLE g' (Spec.map (CommRingCat.ofHom σ)) ⊤ V le_top
  change ((Scheme.ΓSpecIso (.of k)).inv ≫
      (g' ≫ Spec.map (CommRingCat.ofHom σ)).appLE ⊤ V le_top).hom =
    (CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (.of L)).inv ≫ g'.appLE ⊤ V le_top).hom
  rw [h, ← Category.assoc, ΓSpecIso_inv_comp_appTop_specMap, Category.assoc]

/-- The stalk form of `algebraMap_sectionsAlgebra_comp_specMap`: the tower `k → L → 𝒪_{Y, y}`. -/
theorem Scheme.Hom.algebraMap_stalkAlgebra_comp_specMap (g' : Y ⟶ Spec (.of L)) (σ : k →+* L)
    (y : Y) :
    letI := (g' ≫ Spec.map (CommRingCat.ofHom σ)).stalkAlgebra y
    letI := g'.stalkAlgebra y
    algebraMap k (Y.presheaf.stalk y) = (algebraMap L (Y.presheaf.stalk y)).comp σ := by
  rw [← (g' ≫ Spec.map (CommRingCat.ofHom σ)).germ_comp_algebraMap_sectionsAlgebra ⊤ (x := y)
    trivial, ← g'.germ_comp_algebraMap_sectionsAlgebra ⊤ (x := y) trivial, RingHom.comp_assoc,
    Scheme.Hom.algebraMap_sectionsAlgebra_comp_specMap]

/-- The scalar tower `k → Γ(X, U) → Γ(Y, V)` for the structures induced by `fX`, `f ≫ fX` and the
map on sections `f.appLE U V e` (the sections form of `isScalarTower_stalkAlgebra_stalkMap` in
`Hironaka/Scheme/IdealSheaf/Derivative/Pullback.lean`). -/
theorem Scheme.Hom.isScalarTower_sectionsAlgebra_appLE (fX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    letI := fX.sectionsAlgebra U
    letI := (f ≫ fX).sectionsAlgebra V
    letI := (f.appLE U V e).hom.toAlgebra
    IsScalarTower k Γ(X, U) Γ(Y, V) :=
  letI := fX.sectionsAlgebra U
  letI := (f ≫ fX).sectionsAlgebra V
  letI := (f.appLE U V e).hom.toAlgebra
  IsScalarTower.of_algebraMap_eq' (by
    have h : fX.appLE ⊤ U le_top ≫ f.appLE U V e = (f ≫ fX).appLE ⊤ V le_top :=
      Scheme.Hom.appLE_comp_appLE f fX ⊤ U V le_top e
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ fX).appLE ⊤ V le_top).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appLE ⊤ U le_top ≫ f.appLE U V e).hom
    rw [h])

/-- Global sections of the open subscheme `V`, followed by `topIso`, are the sections over `V`:
`Γ(V.ι ≫ g) ≫ V.topIso.hom = g.appLE ⊤ V`. -/
theorem Scheme.Opens.ι_comp_appTop_topIso_hom {S : Scheme.{u}} (g : X ⟶ S) (V : X.Opens) :
    (V.ι ≫ g).appTop ≫ V.topIso.hom = g.appLE ⊤ V le_top := by
  change g.appLE ⊤ (V.ι ''ᵁ ⊤) le_top ≫ X.presheaf.map (eqToHom V.ι_image_top.symm).op = _
  exact Scheme.Hom.appLE_map' g le_top V.ι_image_top.symm

/-- The restriction `p ∣_ U` on global sections, read through the `topIso` identifications, is
`p.appLE U (p⁻¹U)`. -/
theorem morphismRestrict_appTop_comp_topIso_hom (p : Y ⟶ X) (U : X.Opens) :
    (p ∣_ U).appTop ≫ (p ⁻¹ᵁ U).topIso.hom = U.topIso.hom ≫ p.appLE U (p ⁻¹ᵁ U) le_rfl := by
  have e0 : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ (U.ι ''ᵁ ⊤) := by rw [Scheme.Opens.ι_image_top]
  have h1 : (p ∣_ U).appTop = p.appLE (U.ι ''ᵁ ⊤) ((p ⁻¹ᵁ U).ι ''ᵁ ⊤) _ :=
    (Scheme.Hom.appLE_eq_app _).symm.trans (morphismRestrict_appLE p U ⊤ ⊤ le_rfl)
  rw [h1]
  change p.appLE (U.ι ''ᵁ ⊤) ((p ⁻¹ᵁ U).ι ''ᵁ ⊤) _ ≫
      Y.presheaf.map (eqToHom (p ⁻¹ᵁ U).ι_image_top.symm).op =
    X.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ p.appLE U (p ⁻¹ᵁ U) le_rfl
  exact (Scheme.Hom.appLE_map' p e0 (p ⁻¹ᵁ U).ι_image_top.symm).trans
    (Scheme.Hom.map_appLE' p e0 U.ι_image_top.symm).symm

variable {p : Y ⟶ X} {g' : Y ⟶ Spec (.of L)} {f : X ⟶ Spec (.of k)} {σ : k →+* L}

/-- On the base-change square, the `k`-algebra structure of `Γ(Y, V)` induced by `p ≫ f` is the
`L`-structure induced by `g'` restricted along `σ` (`p ≫ f = g' ≫ Spec σ`). -/
theorem Scheme.Hom.algebraMap_sectionsAlgebra_of_isPullback_specMap
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) (V : Y.Opens) :
    letI := (p ≫ f).sectionsAlgebra V
    letI := g'.sectionsAlgebra V
    algebraMap k Γ(Y, V) = (algebraMap L Γ(Y, V)).comp σ := by
  rw [sq.w]
  exact Scheme.Hom.algebraMap_sectionsAlgebra_comp_specMap g' σ V

/-- The stalk form of `algebraMap_sectionsAlgebra_of_isPullback_specMap`. -/
theorem Scheme.Hom.algebraMap_stalkAlgebra_of_isPullback_specMap
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) (y : Y) :
    letI := (p ≫ f).stalkAlgebra y
    letI := g'.stalkAlgebra y
    algebraMap k (Y.presheaf.stalk y) = (algebraMap L (Y.presheaf.stalk y)).comp σ := by
  rw [sq.w]
  exact Scheme.Hom.algebraMap_stalkAlgebra_comp_specMap g' σ y

/-- Over an affine open `U ⊆ X`, the sections of the base change `X_L → X` of [Kol07, 34.2] form a
pushout of rings, `Γ(X_L, p⁻¹U) = L ⊗_k Γ(X, U)`: Mathlib's `isPushout_appTop_of_isPullback` for
the restricted square `p⁻¹U = U ×_{Spec k} Spec L`, transported along the `ΓSpecIso` and `topIso`
identifications of its corners. -/
theorem isPushout_appLE_of_isPullback_specMap
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) {U : X.Opens}
    (hU : IsAffineOpen U) :
    IsPushout ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top) (CommRingCat.ofHom σ)
      (p.appLE U (p ⁻¹ᵁ U) le_rfl)
      ((Scheme.ΓSpecIso (.of L)).inv ≫ g'.appLE ⊤ (p ⁻¹ᵁ U) le_top) := by
  have : IsAffineHom p := property_of_isPullback @IsAffineHom sq inferInstance
  have hW : IsAffineOpen (p ⁻¹ᵁ U) := hU.preimage p
  have : IsAffine (U : Scheme.{u}) := hU
  have : IsAffine ((p ⁻¹ᵁ U : Y.Opens) : Scheme.{u}) := hW
  have sq' : IsPullback (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ g') (U.ι ≫ f)
      (Spec.map (CommRingCat.ofHom σ)) :=
    (isPullback_morphismRestrict p U).paste_vert sq
  refine (isPushout_appTop_of_isPullback sq').of_iso (Scheme.ΓSpecIso (.of k)) U.topIso
    (Scheme.ΓSpecIso (.of L)) (p ⁻¹ᵁ U).topIso ?_ ?_ ?_ ?_
  · rw [Iso.hom_inv_id_assoc]
    exact Scheme.Opens.ι_comp_appTop_topIso_hom f U
  · exact Scheme.ΓSpecIso_naturality _
  · exact morphismRestrict_appTop_comp_topIso_hom p U
  · rw [Iso.hom_inv_id_assoc]
    exact Scheme.Opens.ι_comp_appTop_topIso_hom g' _

namespace Scheme.IdealSheafData

/-- **The derivative ideal commutes with a change of the base field** ([Kol07, Lemma 74 (4)] for
the base change of [Kol07, 34.2]): on the base-change square `p : X_L → X` along `σ : k → L` with
`k` of characteristic zero and `X` smooth over `k`, `D_L(p^* I) = p^* D_k(I)`. Stalkwise:
`D_L(J B) ⊆ D_k(J) B` since `L`-derivations are `k`-derivations and the stalk map is formally
smooth; `D_k(J) B ⊆ D_L(J B)` on the sections over an affine `U ∋ p y`, where
`Γ(p⁻¹U) = L ⊗_k Γ(U)` lifts `k`-derivations to `L`-derivations. -/
theorem derivative_comap_of_isPullback_specMap [CharZero k]
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) [Smooth f] (I : X.IdealSheafData) :
    (I.comap p).derivative g' = (I.derivative f).comap p := by
  have hg' : Smooth g' := smooth_of_isPullback_specMap sq
  refine ext_stalkIdeal fun y => le_antisymm ?_ ?_
  · let _ := f.stalkAlgebra (p y)
    let _ := g'.stalkAlgebra y
    let _ := (p ≫ f).stalkAlgebra y
    let _ := (p.stalkMap y).hom.toAlgebra
    let _ := σ.toAlgebra
    have := Scheme.Hom.isScalarTower_stalkAlgebra_stalkMap f p y
    have : IsScalarTower k L (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq'
      (Scheme.Hom.algebraMap_stalkAlgebra_of_isPullback_specMap sq y)
    have : Algebra.FormallySmooth (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) :=
      RingHom.formallySmooth_algebraMap.mp
        (formallySmooth_stalkMap_of_isPullback_specMap sq y)
    have := f.formallySmooth_stalk (p y)
    have := f.essFiniteType_stalk (p y)
    rw [stalkIdeal_derivative g' (I.comap p) y, stalkIdeal_comap, stalkIdeal_comap,
      stalkIdeal_derivative f I (p y)]
    exact Ideal.derivative_map_le_map_derivative_of_restrictScalars (k := k) (L := L)
      (I.stalkIdeal (p y))
  · obtain ⟨U, hxU⟩ := exists_affineOpens_mem (p y)
    have hU : IsAffineOpen U.1 := U.2
    have : IsAffineHom p := property_of_isPullback @IsAffineHom sq inferInstance
    have hV : IsAffineOpen (p ⁻¹ᵁ U.1) := hU.preimage p
    have hy : y ∈ p ⁻¹ᵁ U.1 := hxU
    rw [stalkIdeal_eq_map_germ ((derivative f I).comap p) ⟨_, hV⟩ hy,
      stalkIdeal_eq_map_germ (derivative g' (I.comap p)) ⟨_, hV⟩ hy,
      ideal_comap_of_le (derivative f I) p U ⟨_, hV⟩ le_rfl,
      ideal_derivative g' (I.comap p) ⟨_, hV⟩, ideal_comap_of_le I p U ⟨_, hV⟩ le_rfl,
      ideal_derivative f I U]
    refine Ideal.map_mono ?_
    let _ := f.sectionsAlgebra U.1
    let _ := g'.sectionsAlgebra (p ⁻¹ᵁ U.1)
    let _ := (p ≫ f).sectionsAlgebra (p ⁻¹ᵁ U.1)
    let _ := (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
    let _ := σ.toAlgebra
    have := Scheme.Hom.isScalarTower_sectionsAlgebra_appLE f p U.1 (p ⁻¹ᵁ U.1) le_rfl
    have : IsScalarTower k L Γ(Y, p ⁻¹ᵁ U.1) := IsScalarTower.of_algebraMap_eq'
      (Scheme.Hom.algebraMap_sectionsAlgebra_of_isPullback_specMap sq _)
    have : Algebra.IsPushout k L Γ(X, U.1) Γ(Y, p ⁻¹ᵁ U.1) :=
      (CommRingCat.isPushout_iff_isPushout.mp (isPushout_appLE_of_isPullback_specMap sq hU)).symm
    exact Ideal.map_derivative_le_derivative_map_of_isPushout (I.ideal U)

/-- The iterates: `D_L^r(p^* I) = p^* D_k^r(I)` along a change of fields. -/
theorem derivativeIter_comap_of_isPullback_specMap [CharZero k]
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) [Smooth f] (r : ℕ)
    (I : X.IdealSheafData) :
    (I.comap p).derivativeIter g' r = (I.derivativeIter f r).comap p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [derivativeIter_succ, derivativeIter_succ, ih, derivative_comap_of_isPullback_specMap sq]

end Scheme.IdealSheafData

end AlgebraicGeometry
