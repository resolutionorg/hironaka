/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Trivial blow-ups, the isomorphism off the centre, degenerate centres, isomorphisms of the base

Consequences of the universal property of the blow-up (`blowUp.lift`, `blowUp.hom_ext`) and of the
affine degenerate case (`affineBlowUp.isEmpty_bot`):

* Trivial blow-ups [Kol07, Warning 20]: if the centre is a Cartier divisor (`I` invertible) the
  blow-up map is an isomorphism — `𝟙 X` is admissible and lifts, and the two composites are
  identities by uniqueness — and then the exceptional divisor is the centre
  (`(I.comap π).map π = I`).  In particular the empty blow-up (`I = ⊤`) is an isomorphism
  [Sta, Tag 02OS].
* The blow-up map is an isomorphism over the complement `W` of the centre [Sta, Tag 02OS]:
  `I·𝒪_W = 𝒪_W` (the support of `I.comap W.ι` is empty), so `W → X` is
  admissible, lifts into `π⁻¹(W)`, and the two composites with `π ∣_ W` are identities by
  uniqueness.  Hence every point off the centre has a preimage in the blow-up.
* The blow-up along the zero ideal sheaf (the centre is all of `X`) is empty
  [Hau14, Definition 6.2]: every point lies in some `π⁻¹(U) ≅ affineBlowUp (I.ideal U)`, which
  is empty by `affineBlowUp.isEmpty_bot`.
* An isomorphism `e : X ≅ Y` with `I = J.comap e.hom` induces a canonical isomorphism of blow-ups
  over `e` [Hau14, Corollary 5.2 (d)], the lift of `π ≫ e.hom`, unique among the morphisms over
  `e`.
-/

public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

section IdealSheaf

variable {Y Z : Scheme.{u}}

/-- For an isomorphism `e`, `map · e` inverts `comap · e`. -/
theorem Scheme.IdealSheafData.map_comap_of_isIso (J : Z.IdealSheafData)
    (e : Y ⟶ Z) [IsIso e] : (J.comap e).map e = J := by
  refine le_antisymm ?_ (le_map_comap (f := e) J)
  calc (J.comap e).map e = (((J.comap e).map e).comap e).comap (inv e) := by
        rw [← comap_comp, IsIso.inv_hom_id, comap_id]
    _ ≤ (J.comap e).comap (inv e) := comap_mono (f := inv e) (comap_map_le (f := e) _)
    _ = J := by rw [← comap_comp, IsIso.inv_hom_id, comap_id]

end IdealSheaf

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- For a trivial blow-up — the centre a Cartier divisor, `I` invertible — the blow-up map is an
isomorphism, its inverse being the lift of `𝟙 X` [Kol07, Warning 20]. -/
theorem Scheme.IdealSheafData.blowUp.isIso_π_of_isInvertible (h : I.IsInvertible) : IsIso
    (blowUpπ I) := by
  have hid : (I.comap (𝟙 X)).IsInvertible := by rw [comap_id]; exact h
  refine ⟨⟨blowUp.lift I (𝟙 X) hid, ?_, blowUp.lift_π I (𝟙 X) hid⟩⟩
  exact blowUp.hom_ext I (blowUpπ I) (blowUp.isInvertible_comap_π I) _ _
    (by rw [Category.assoc, blowUp.lift_π, Category.comp_id]) (Category.id_comp _)

/-- For a trivial blow-up the exceptional divisor is the centre [Kol07, Warning 20 (2)]: the
scheme-theoretic image of `I·𝒪_B` under the isomorphism `π` is `I`. -/
theorem Scheme.IdealSheafData.blowUp.map_exceptionalDivisor_of_isInvertible (h : I.IsInvertible) :
    I.exceptionalDivisor.map (blowUpπ I) = I := by
  have := blowUp.isIso_π_of_isInvertible I h
  exact map_comap_of_isIso I (blowUpπ I)

/-- The empty blow-up [Kol07, Warning 20]; [Sta, Tag 02OS]: the blow-up along the unit ideal
sheaf is an isomorphism. -/
theorem Scheme.IdealSheafData.blowUp.isIso_π_top : IsIso (blowUpπ (⊤ : X.IdealSheafData)) :=
  blowUp.isIso_π_of_isInvertible ⊤ isInvertible_top

/-- The inverse image of `I` on the complement `W` of its support is the unit ideal sheaf. -/
theorem comap_ι_compl_support_eq_top :
    I.comap (Scheme.Opens.ι (I.support.compl : X.Opens)) = ⊤ := by
  rw [← support_eq_bot_iff, support_comap]
  refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx => (Set.notMem_empty x hx).elim⟩
  have hmem : Scheme.Opens.ι (I.support.compl : X.Opens) x ∈
      ((I.support.compl : X.Opens) : Set X) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  exact absurd (SetLike.mem_coe.mpr hx) hmem

/-- **The blow-up is an isomorphism off the centre** [Sta, Tag 02OS]:
over `W = X ∖ Z` the inverse image of `I` is the unit ideal sheaf, so `W → X` is admissible and
its lift into `π⁻¹(W)` inverts `π ∣_ W`. -/
theorem Scheme.IdealSheafData.blowUp.isIso_π_restrict_compl_support : IsIso
    (blowUpπ I ∣_ I.support.compl) := by
  set W : X.Opens := I.support.compl with hW_def
  have hadm : (I.comap W.ι).IsInvertible := by
    rw [comap_ι_compl_support_eq_top]
    exact isInvertible_top
  set s := blowUp.lift I W.ι hadm with hs_def
  have hrange : Set.range s ⊆ Set.range (blowUpπ I ⁻¹ᵁ W).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change blowUpπ I (s w) ∈ W
    rw [← Scheme.Hom.comp_apply, blowUp.lift_π]
    have hw : W.ι w ∈ (W : Set X) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
    exact hw
  set s' := IsOpenImmersion.lift (blowUpπ I ⁻¹ᵁ W).ι s hrange with hs'_def
  have hs' : s' ≫ (blowUpπ I ⁻¹ᵁ W).ι = s := IsOpenImmersion.lift_fac _ _ _
  have hadm' : (I.comap ((blowUpπ I ⁻¹ᵁ W).ι ≫ blowUpπ I)).IsInvertible := by
    rw [comap_comp]
    exact (blowUp.isInvertible_comap_π I).comap_of_isOpenImmersion _
  refine ⟨⟨s', ?_, ?_⟩⟩
  · rw [← cancel_mono (blowUpπ I ⁻¹ᵁ W).ι, Category.assoc, hs', Category.id_comp]
    exact blowUp.hom_ext I _ hadm' _ _
      (by rw [Category.assoc, blowUp.lift_π, morphismRestrict_ι]) rfl
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hs',
      blowUp.lift_π, Category.id_comp]

/-- If every affine piece is empty, so is the blow-up. -/
theorem Scheme.IdealSheafData.blowUp.isEmpty_of_forall (h : ∀ U : X.affineOpens, IsEmpty
    (affineBlowUp (I.ideal U))) :
    IsEmpty (blowUp I) :=
  ⟨fun b => by
    obtain ⟨U, hU⟩ := blowUp.exists_mem_opensRange_ι I b
    obtain ⟨b', -⟩ := Scheme.Hom.mem_opensRange.mp hU
    exact (h U).elim b'⟩

/-- The blow-up along the zero ideal sheaf — the centre is all of `X` — is empty
[Hau14, Definition 6.2]. -/
theorem Scheme.IdealSheafData.blowUp.isEmpty_bot : IsEmpty (blowUp (⊥ : X.IdealSheafData)) :=
  blowUp.isEmpty_of_forall ⊥ fun U => affineBlowUp.isEmpty_bot (R := Γ(X, U))

/-- A point off the centre has a preimage in the blow-up: the blow-up is an isomorphism over the
complement of the centre. -/
theorem exists_π_eq_of_notMem_support (Z : X.IdealSheafData) {x : X}
    (hx : x ∉ Z.support) :
    ∃ x' : blowUp Z, blowUpπ Z x' = x := by
  set W : X.Opens := Z.support.compl with hW
  have hxW : x ∈ (W : Set X) := hx
  have := blowUp.isIso_π_restrict_compl_support Z
  obtain ⟨w, hw⟩ := (Scheme.Opens.range_ι W).symm ▸ hxW
  obtain ⟨v, hv⟩ := (blowUpπ Z ∣_ W).homeomorph.surjective w
  refine ⟨(blowUpπ Z ⁻¹ᵁ W).ι v, ?_⟩
  rw [Scheme.Hom.homeomorph_apply] at hv
  rw [← hw, ← hv, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]

section MapIso

variable {Y : Scheme.{u}}

/-- An isomorphism `e : X ≅ Y` carrying `I` to `J` (`I = J.comap e.hom`) induces a canonical
isomorphism of the blow-ups over `e` — the lift of `π ≫ e.hom`, the only morphism over `e`
[Hau14, Corollary 5.2 (d)]. -/
theorem Scheme.IdealSheafData.blowUp.exists_mapIso (e : X ≅ Y) (J : Y.IdealSheafData)
    (hIJ : I = J.comap e.hom) :
    ∃ φ : blowUp I ≅ blowUp J,
      φ.hom ≫ blowUpπ J = blowUpπ I ≫ e.hom ∧
      ∀ ψ : blowUp I ⟶ blowUp J, ψ ≫ blowUpπ J = blowUpπ I ≫ e.hom → ψ = φ.hom := by
  have h1 : (J.comap (blowUpπ I ≫ e.hom)).IsInvertible := by
    rw [comap_comp, ← hIJ]
    exact blowUp.isInvertible_comap_π I
  have hJI : J = I.comap e.inv := by
    rw [hIJ, ← comap_comp, Iso.inv_hom_id, comap_id]
  have h2 : (I.comap (blowUpπ J ≫ e.inv)).IsInvertible := by
    rw [comap_comp, ← hJI]
    exact blowUp.isInvertible_comap_π J
  refine ⟨⟨blowUp.lift J _ h1, blowUp.lift I _ h2, ?_, ?_⟩, blowUp.lift_π J _ h1,
    fun ψ hψ => blowUp.eq_lift J _ h1 ψ hψ⟩
  · exact blowUp.hom_ext I (blowUpπ I) (blowUp.isInvertible_comap_π I) _ _
      (by rw [Category.assoc, blowUp.lift_π, ← Category.assoc, blowUp.lift_π, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]) (Category.id_comp _)
  · exact blowUp.hom_ext J (blowUpπ J) (blowUp.isInvertible_comap_π J) _ _
      (by rw [Category.assoc, blowUp.lift_π, ← Category.assoc, blowUp.lift_π, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]) (Category.id_comp _)

end MapIso

end AlgebraicGeometry
