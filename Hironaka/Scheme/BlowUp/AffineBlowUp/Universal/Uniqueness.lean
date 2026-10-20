/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Kernel
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-!
# Uniqueness of lifts to the affine blow-up

* `affineBlowUp.hom_ext_chart` [Hau14, Theorem 4.18, proof (d)] ("by construction, `γ` is unique
  with this property"): on an affine open `V ⊆ Y` on which `f♯a` is a nonzerodivisor generating
  `I·Γ(Y, V)`, two morphisms `V ⟶ Spec R[I/a]` over `V ⟶ Y ⟶ Spec R` are equal — they are `Spec` of
  ring maps `R[I/a] → Γ(Y, V)` extending `f♯`, and such a map is unique
  (`affineBlowUpAlgebra.lift_unique`).
* `affineBlowUp.hom_ext` [Hau14, Theorem 4.18, proof (a)]; [Sta, Tag 0806]: two lifts `g, g'` of
  an admissible `f : Y ⟶ Spec R` are equal, for every scheme `Y`.  For `y ∈ Y`,
  `exists_affineOpen_generator` gives an affine `V ∋ y` and `a ∈ I` with `(I·𝒪_Y)(V) = (f♯a)`,
  `f♯a` a nonzerodivisor; then `a` generates the stalk of `I·𝒪_Y` at every point of `V`, so by
  `affineBlowUp.mem_chart_of_generates` both `g` and `g'` map `V` into the chart of `a`, and their
  restrictions factor through the open immersion `chart a` as morphisms `V ⟶ Spec R[I/a]` over
  `V ⟶ Spec R`, equal by the first item.  Conclude with `Scheme.hom_ext_of_forall`.  The sources'
  argument (scheme-theoretic density of `Y ∖ D` and separatedness) is replaced by this chartwise
  one, which needs no reducedness of `Y`.
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {Y : Scheme.{u}}

/-- For `f : Y ⟶ Spec R` admissible for `I` and `y ∈ Y`, there are an affine open `V ∋ y` and
`a ∈ I` such that `f♯a = sectionsHom f V a` is a nonzerodivisor of `Γ(Y, V)` generating
`I·Γ(Y, V)` (`exists_affineOpen_generator_of_isInvertible` for the base `Spec R`). -/
theorem exists_affineOpen_generator (f : Y ⟶ Spec (.of R))
    (hf : ((specIdealSheaf I).comap f).IsInvertible) (y : Y) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧ ∃ a : I,
      sectionsHom f V.1 a ∈ nonZeroDivisors Γ(Y, V) ∧
        I.map (sectionsHom f V.1) = Ideal.span {sectionsHom f V.1 a} := by
  obtain ⟨V, hyV, e, a', ha', hJ, hnz⟩ :=
      Scheme.IdealSheafData.exists_affineOpen_generator_of_isInvertible
    (specIdealSheaf I) f hf ⟨⊤, isAffineOpen_top _⟩ y (Opens.mem_top y)
  rw [specIdealSheaf_ideal_top] at ha'
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective (Scheme.ΓSpecIso (.of R)).inv.hom
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.surjective).mp ha'
  refine ⟨V, hyV, ⟨a, ha⟩, hnz, ?_⟩
  rw [← ideal_comap_specIdealSheaf]
  exact hJ

/-- If `f♯a` generates `I·Γ(Y, V)`, the image of `a` generates the stalk of `I·𝒪_Y` at every point
of `V`. -/
theorem stalkIdeal_comap_specIdealSheaf_eq_span (f : Y ⟶ Spec (.of R)) (V : Y.affineOpens)
    (a : I) (hI : I.map (sectionsHom f V.1) = Ideal.span {sectionsHom f V.1 a}) {z : Y}
    (hz : z ∈ V.1) :
    ((specIdealSheaf I).comap f).stalkIdeal z =
      Ideal.span
        {f.stalkMap z ((Spec (.of R)).presheaf.germ ⊤ (f z) (Opens.mem_top _)
          ((Scheme.ΓSpecIso (.of R)).inv.hom a))} := by
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ _ V hz, ideal_comap_specIdealSheaf, hI,
      Ideal.map_span,
    Set.image_singleton]
  congr 2
  exact f.germ_appLE_apply ⊤ V.1 le_top hz (Opens.mem_top _) ((Scheme.ΓSpecIso (.of R)).inv.hom a)

/-- Local uniqueness [Hau14, Theorem 4.18, proof (d)]: on an affine open `V ⊆ Y` on which `f♯a`
is a nonzerodivisor generating `I·Γ(Y, V)`, two morphisms `V ⟶ Spec R[I/a]` over `V ⟶ Y ⟶ Spec R`
are equal (from `affineBlowUpAlgebra.lift_unique`). -/
theorem affineBlowUp.hom_ext_chart (f : Y ⟶ Spec (.of R)) (V : Y.affineOpens) (a : I)
    (hβa : sectionsHom f V.1 a ∈ nonZeroDivisors Γ(Y, V))
    (hI : I.map (sectionsHom f V.1) = Ideal.span {sectionsHom f V.1 a})
    (u u' : (V.1 : Scheme.{u}) ⟶ Spec (.of (affineBlowUpAlgebra I a)))
    (hu : u ≫ Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I a))) = V.1.ι ≫ f)
    (hu' : u' ≫ Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I a))) =
      V.1.ι ≫ f) :
    u = u' := by
  have key : ∀ v : (V.1 : Scheme.{u}) ⟶ Spec (.of (affineBlowUpAlgebra I a)),
      v ≫ Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I a))) = V.1.ι ≫ f →
      v = V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (affineBlowUpAlgebra.lift (sectionsHom f V.1) a.2 hβa hI)) := by
    intro v hv
    set δ := Spec.preimage (V.2.isoSpec.inv ≫ v) with hδ_def
    have hδ : Spec.map δ = V.2.isoSpec.inv ≫ v := Spec.map_preimage _
    have hv' : v = V.2.isoSpec.hom ≫ Spec.map δ := by rw [hδ, Iso.hom_inv_id_assoc]
    have hcomp : CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I a)) ≫ δ =
        CommRingCat.ofHom (sectionsHom f V.1) := by
      apply Spec.map_injective
      rw [Spec.map_comp, ← Iso.cancel_iso_hom_left V.2.isoSpec, ← Category.assoc, ← hv', hv,
        isoSpec_hom_specMap_sectionsHom f V]
    have hlift : δ.hom = affineBlowUpAlgebra.lift (sectionsHom f V.1) a.2 hβa hI :=
      affineBlowUpAlgebra.lift_unique _ a.2 hβa hI δ.hom (congrArg CommRingCat.Hom.hom hcomp)
    have hδ' : δ = CommRingCat.ofHom (affineBlowUpAlgebra.lift (sectionsHom f V.1) a.2 hβa hI) :=
      CommRingCat.hom_ext hlift
    rw [hv', hδ']
  rw [key u hu, key u' hu']

/-- **Uniqueness of the lift** [Hau14, Theorem 4.18, proof (a) and (d)]; [Sta, Tag 0806]: two
lifts of an admissible `f : Y ⟶ Spec R` to the affine blow-up are equal, for every scheme `Y`. -/
theorem affineBlowUp.hom_ext (f : Y ⟶ Spec (.of R))
    (hf : ((specIdealSheaf I).comap f).IsInvertible) (g g' : Y ⟶ affineBlowUp I)
    (e : g ≫ affineBlowUp.π I = f) (e' : g' ≫ affineBlowUp.π I = f) : g = g' := by
  apply Scheme.hom_ext_of_forall
  intro y
  obtain ⟨V, hyV, a, hβa, hI⟩ := exists_affineOpen_generator I f hf y
  refine ⟨V.1, hyV, ?_⟩
  have hrange : ∀ h : Y ⟶ affineBlowUp I, h ≫ affineBlowUp.π I = f →
      Set.range (V.1.ι ≫ h) ⊆ Set.range (affineBlowUp.chart I a) := by
    intro h hh
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact affineBlowUp.mem_chart_of_generates I f hf h hh (V.1.ι z) a
      (stalkIdeal_comap_specIdealSheaf_eq_span I f V a hI z.2)
  have hu : ∀ (h : Y ⟶ affineBlowUp I) (hh : h ≫ affineBlowUp.π I = f),
      IsOpenImmersion.lift (affineBlowUp.chart I a) (V.1.ι ≫ h) (hrange h hh) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I a))) = V.1.ι ≫ f := by
    intro h hh
    rw [← affineBlowUp.chart_π, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hh]
  calc V.1.ι ≫ g
      = IsOpenImmersion.lift (affineBlowUp.chart I a) (V.1.ι ≫ g) (hrange g e) ≫
          affineBlowUp.chart I a := (IsOpenImmersion.lift_fac _ _ _).symm
    _ = IsOpenImmersion.lift (affineBlowUp.chart I a) (V.1.ι ≫ g') (hrange g' e') ≫
          affineBlowUp.chart I a := by
        rw [affineBlowUp.hom_ext_chart I f V a hβa hI _ _ (hu g e) (hu g' e')]
    _ = V.1.ι ≫ g' := IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry
