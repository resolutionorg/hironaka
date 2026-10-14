/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Hironaka.Algebra.Local.OrderFlat
public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Algebra.Local.OrderSmooth
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Invariance of the order under smooth morphisms

[Hau03, Appendix A]: the order is invariant "more generally, with respect to smooth morphisms".
For `f : Y → X` smooth, `ord_y (f⁻¹ I) = ord_{f y} I` (`ord_comap_of_smooth`), and the local
statement `ord (J 𝒪_{Y,y}) = ord J` for every ideal `J` of `𝒪_{X, f y}`
(`ord_map_stalkMap_of_smooth`).

The stalk of `f⁻¹ I` at `y` is the image of `I_{f y}` under the stalk map (`stalkIdeal_comap`,
`Hironaka/Scheme/IdealSheaf/StalkIdeal.lean`), and the order does not drop under a local map
(`ord_le_ord_map`, `Hironaka/Algebra/Local/Order.lean`); the reverse inequality is the content. On
affine opens `f y ∈ U ⊆ X`, `y ∈ V ⊆ f⁻¹U`, the stalk map is the localization `Γ(U)_p → Γ(V)_q` of
the smooth ring map `Γ(U) → Γ(V)` at the primes of `y` and `f y` (Mathlib's
`IsAffineOpen.arrowStalkMapIso`), which reflects the powers of the maximal ideal by the local
statement of `Hironaka/Algebra/Local/OrderSmooth.lean` (`ordFaithful_localRingHom_of_isSmoothAt`:
the polynomial case and the étale case); `OrdFaithful` transports along isomorphisms of arrows
(`OrdFaithful.of_arrow_iso`). Hauser lists the invariance among the functorial properties of the
order; the argument here is the library's own.

Used for the pull-back of the resolution data along smooth morphisms
(`Hironaka/Scheme/BlowUpSequence/PullbackInduced.lean`,
`Hironaka/Scheme/BlowUpSequence/PullbackSnc.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Parameters.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothLoop.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/UpToUnits.lean`).
-/

public section

namespace IsLocalRing

open CategoryTheory

/-- `OrdFaithful` transports along an isomorphism of arrows of commutative rings: if
`ψ = e₂ ∘ φ ∘ e₁⁻¹` for ring isomorphisms `e₁`, `e₂`, then `ψ` reflects the powers of the maximal
ideal when `φ` does. -/
theorem OrdFaithful.of_arrow_iso {A B A' B' : CommRingCat} [IsLocalRing A] [IsLocalRing B]
    [IsLocalRing A'] [IsLocalRing B'] {φ : A ⟶ B} {ψ : A' ⟶ B'} (i : Arrow.mk φ ≅ Arrow.mk ψ)
    (h : OrdFaithful φ.hom) : OrdFaithful ψ.hom := by
  have hw : i.hom.left ≫ ψ = φ ≫ i.hom.right := Arrow.w i.hom
  have hl : i.inv.left ≫ i.hom.left = 𝟙 A' := by
    rw [← Arrow.comp_left, i.inv_hom_id]
    rfl
  have hψ : ψ = i.inv.left ≫ φ ≫ i.hom.right := by
    rw [← hw, ← Category.assoc, hl]
    exact (Category.id_comp ψ).symm
  have hr : i.hom.right ≫ i.inv.right = 𝟙 B := by
    rw [← Arrow.comp_right, i.hom_inv_id]
    rfl
  have hr' : i.inv.right ≫ i.hom.right = 𝟙 B' := by
    rw [← Arrow.comp_right, i.inv_hom_id]
    rfl
  have hl' : i.hom.left ≫ i.inv.left = 𝟙 A := by
    rw [← Arrow.comp_left, i.hom_inv_id]
    rfl
  let eL : A' ≃+* A := (Iso.mk i.inv.left i.hom.left hl hl').commRingCatIsoToRingEquiv
  let eR : B ≃+* B' := (Iso.mk i.hom.right i.inv.right hr hr').commRingCatIsoToRingEquiv
  have hψ' : ψ.hom = (eR : B →+* B').comp (φ.hom.comp (eL : A' →+* A)) := by
    rw [hψ]
    rfl
  rw [hψ']
  exact (h.ringEquiv_comp eL).comp_ringEquiv eR

end IsLocalRing

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The local statement: the stalk map of a smooth morphism preserves the order of every ideal of
the local ring `𝒪_{X, f y}`.  On affine opens `f y ∈ U`, `y ∈ V ⊆ f⁻¹U`, the stalk
map is the localization of the smooth ring map `Γ(U) → Γ(V)` at the primes of `y` and `f y`
(Mathlib's `IsAffineOpen.arrowStalkMapIso`), which reflects the powers of the maximal ideal
(`ordFaithful_localRingHom_of_isSmoothAt`). -/
theorem ord_map_stalkMap_of_smooth {Y : Scheme.{u}} (f : Y ⟶ X) [Smooth f] (y : Y)
    (J : Ideal (X.presheaf.stalk (f y))) :
    IsLocalRing.ord (J.map (f.stalkMap y).hom) = IsLocalRing.ord J := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (U.2.preimage f.continuous)
  have hsm : (f.appLE U V hVU).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ hVU
  algebraize [(f.appLE U V hVU).hom]
  have hOF : OrdFaithful (Localization.localRingHom _ _ (f.appLE U V hVU).hom
      congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hyV).1).symm) :=
    ordFaithful_localRingHom_of_isSmoothAt _ _
  exact ord_map_eq_of_ordFaithful (OrdFaithful.of_arrow_iso
    (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hyV).symm hOF) J

/-- [Hau03, Appendix A], invariant "more generally, with respect to smooth morphisms": pullback
along a smooth morphism preserves the order, `ord_y (f⁻¹ I) = ord_{f y} I`. -/
theorem ord_comap_of_smooth {Y : Scheme.{u}} (f : Y ⟶ X) [Smooth f] (y : Y) :
    (I.comap f).ord y = I.ord (f y) := by
  rw [ord_eq_ord_stalkIdeal, ord_eq_ord_stalkIdeal, stalkIdeal_comap]
  exact ord_map_stalkMap_of_smooth f y _

/-- Pullback along an étale morphism preserves the order. -/
theorem ord_comap_of_etale {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] (y : Y) :
    (I.comap f).ord y = I.ord (f y) :=
  ord_comap_of_smooth I f y

end AlgebraicGeometry.Scheme.IdealSheafData
