/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Hironaka.Algebra.Smooth.StandardSmoothLift
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Kollár's Lemma 41: the local ambient lift of a smooth morphism

`exists_smooth_ambient_lift` is [Kol07, Lemma 41]: for `h : Y ⟶ X` smooth, `y : Y` and a closed
immersion `emb : X ⟶ A`, there are opens `UA ∋ emb (h y)` of `A` and `V ∋ y` of `Y`, a scheme `AY`
over `k`, a smooth surjective `hA : AY ⟶ UA` of constant relative dimension and a closed immersion
`j : V ⟶ AY` with `IsPullback j (h.resLE (emb ⁻¹ᵁ UA) V hV) hA (emb.resLE UA (emb ⁻¹ᵁ UA) le_rfl)`:
a smooth morphism to an embedded scheme is, locally, the restriction of a smooth morphism between
ambient schemes.

**The proof**, by the local structure of smooth algebras rather than Kollár's general projection.

1. *Affine reduction.* An affine `UA₀ ∋ emb (h y)` (`exists_isAffineOpen_mem_and_subset`);
   `X₀ := emb ⁻¹ᵁ UA₀` is affine (closed immersions are affine, `IsAffineOpen.preimage`); an affine
   `V₀ ∋ y` inside `h ⁻¹ᵁ X₀`.
2. *The local presentation.* Mathlib's `Smooth h` says that `Γ(X, X₀) → Γ(Y, V₀)` is a smooth ring
   map (`Smooth.smooth_appLE`), hence locally standard smooth
   (`RingHom.smooth_iff_locally_isStandardSmooth`): on a basic open `V := D(t) ∋ y` of `V₀` the
   map `Γ(X, X₀) → Γ(Y, V)` is standard smooth (`exists_basicOpen_isStandardSmooth_appLE`), with
   a submersive presentation `P`. This replaces Kollár's writing of `Y` near `y` as an open of a
   hypersurface in `X × 𝔸^{d+1}` after a general projection, which needs an infinite field.
3. *The lifted ambient* (`Hironaka/Algebra/Smooth/StandardSmoothLift.lean`). `Γ(A, UA₀) ↠ Γ(X, X₀)`
   (`Scheme.Hom.app_surjective`) lifts the relations of `P` (Kollár's extension of the coefficients
   `φ_I` to `Φ_I` on the ambient); `AY := Spec (T[1/Δ])` is standard smooth of relative dimension
   `P.dimension` over `Γ(A, UA₀)`;
   `Spec Γ(Y, V) = Spec Γ(X, X₀) ×_{Spec Γ(A, UA₀)} Spec T` (`isPullback_SpecMap_of_isPushout`) is
   cut at the open `D(Δ)` (`IsPullback.of_comp_mono_fst`) and transported along the `isoSpec`s to
   the `resLE` square (`exists_affine_ambient`, `SpecMap_appLE_isoSpec_inv`); `j` is a closed
   immersion since `T[1/Δ] → Γ(Y, V)` is surjective.
4. *Shrinking to a surjection.* The image of `AY → UA₀ ↪ A` is open (smooth morphisms are flat and
   locally of finite presentation, hence universally open); `UA` is that image, `hA` the lift of
   `AY → UA₀` to `UA` (`IsOpenImmersion.lift`), surjective by construction and still smooth of the
   same relative dimension (`MorphismProperty.IsStableUnderBaseChange` along the square
   `IsPullback (𝟙 AY) hA hA₀ (A.homOfLE _)`); `V ≤ h ⁻¹ᵁ (emb ⁻¹ᵁ UA)` since `emb ∘ h` factors
   through `hA ∘ j` on `V`; the square over `UA` is the restriction of the square over `UA₀`
   (`IsPullback.of_right` against the `homOfLE` square of `emb`).
5. *Over `k`* (`exists_smooth_ambient_lift`). `AY ↘ Spec k := hA ≫ (UA.ι ≫ (A ↘ Spec k))`; as an
   affine scheme over the affine `Spec k`, `AY` is quasi-compact and separated over `k`
   (`isAffineHom_of_isAffine`).

The hypotheses `[CharZero k]`, `[LocallyOfFiniteType]`, `[h.IsOver]`, `[emb.IsOver]` of the main
statement are Kollár's setting for Lemma 41 (schemes of finite type over a field of characteristic
zero, morphisms over `k`) and are kept so that the theorem reads as printed; the proof does not
need them, because it replaces Kollár's general projection, which needs the field infinite, by
Mathlib's local structure of smooth algebras, valid over any base: the field-free form
`exists_smooth_ambient_lift'` is proved first and the main statement is its specialisation. The
conclusion adds to Kollár's the quasi-compactness and separatedness of `AY` over `k` and the
constancy of the relative dimension of `hA`, all read off his construction; `AY` is in fact
affine, which the statement does not record. Compare [Wlo05, Lemma 4.9.1], the extension of an
étale morphism of embedded affine varieties to the ambient spaces. The smooth charts of the
functorial resolution use the field-free form
(`Hironaka/Resolution/Algebraic/Kol07/Thm36/SmoothCharts.lean`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Algebra.StandardSmoothLift

namespace AlgebraicGeometry

/-- A pullback square whose top map factors through a mono can be cut at the mono:
`Spec S = Spec R ×_{Spec R'} Spec T` and `Spec S → Spec T` lands in the open `D(Δ)`, so
`Spec S = Spec R ×_{Spec R'} D(Δ)`. -/
theorem _root_.CategoryTheory.IsPullback.of_comp_mono_fst {C : Type*} [Category C]
    {P X X' Y Z : C} {fst : P ⟶ X} {i : X ⟶ X'} [Mono i] {snd : P ⟶ Y} {f : X' ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback (fst ≫ i) snd f g) : IsPullback fst snd (i ≫ f) g := by
  refine IsPullback.of_isLimit' ⟨by rw [← Category.assoc, H.w]⟩ ?_
  refine PullbackCone.IsLimit.mk _
    (fun s => H.lift (s.fst ≫ i) s.snd (by rw [Category.assoc, s.condition])) ?_ ?_ ?_
  · intro s
    rw [← cancel_mono i, Category.assoc, H.lift_fst]
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h₁ h₂
    apply H.hom_ext
    · rw [H.lift_fst, ← Category.assoc, h₁]
    · rw [H.lift_snd, h₂]

/-- `Spec.map (f.appLE U V e) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ f.resLE U V e` for affine
opens: the comparison of the affine `Spec` square with the `resLE` square. -/
theorem SpecMap_appLE_isoSpec_inv {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    Spec.map (f.appLE U V e) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ f.resLE U V e := by
  rw [← cancel_epi hV.isoSpec.hom, Iso.hom_inv_id_assoc, hV.isoSpec_hom,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- Given affine `U ⊆ X` and affine `V₀ ⊆ h ⁻¹ᵁ U` containing `y`, there is a basic open
`D(t) ⊆ V₀` containing `y` with `Γ(X, U) → Γ(Y, D(t))` standard smooth: Mathlib's `Smooth h` is
`RingHom.Smooth` of every affine `appLE`, and a smooth ring map is locally standard smooth on the
target (the local presentation of `Y` near `y` in the proof of [Kol07, Lemma 41]). -/
theorem exists_basicOpen_isStandardSmooth_appLE {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    {U : X.Opens} (hU : IsAffineOpen U) {V₀ : Y.Opens} (hV₀ : IsAffineOpen V₀)
    (e : V₀ ≤ h ⁻¹ᵁ U) {y : Y} (hy : y ∈ V₀) :
    ∃ t : Γ(Y, V₀), y ∈ Y.basicOpen t ∧
      (h.appLE U (Y.basicOpen t) ((Y.basicOpen_le t).trans e)).hom.IsStandardSmooth := by
  have hsm : (h.appLE U V₀ e).hom.Smooth := Smooth.smooth_appLE h hU hV₀ e
  rw [RingHom.smooth_iff_locally_isStandardSmooth,
    RingHom.locally_iff_isLocalization RingHom.isStandardSmooth_respectsIso] at hsm
  obtain ⟨s, hs, H⟩ := hsm
  have hy' : y ∈ ⨆ i ∈ (s : Set Γ(Y, V₀)), Y.basicOpen i := by
    rwa [iSup_basicOpen_of_span_eq_top V₀ _ hs]
  simp only [TopologicalSpace.Opens.mem_iSup] at hy'
  obtain ⟨t, ht, hyt⟩ := hy'
  refine ⟨t, hyt, ?_⟩
  let : Algebra Γ(Y, V₀) Γ(Y, Y.basicOpen t) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le t)).op).hom.toAlgebra
  have : IsLocalization.Away t Γ(Y, Y.basicOpen t) :=
    hV₀.isLocalization_of_eq_basicOpen t (homOfLE (Y.basicOpen_le t)) rfl
  have := H t ht Γ(Y, Y.basicOpen t)
  rwa [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map] at this

/-- The affine chart of [Kol07, Lemma 41]: over an affine `UA ⊆ A` with
`Γ(X, emb ⁻¹ᵁ UA) → Γ(Y, V)` standard smooth, the lifted presentation gives an affine
`AY = Spec (T[1/Δ])`, smooth of relative dimension `P.dimension` over `UA`, and a closed immersion
`V ↪ AY` making `V` the fibre product `emb ⁻¹ᵁ UA ×_{UA} AY`. -/
theorem exists_affine_ambient {X Y A : Scheme.{u}} (h : Y ⟶ X) (emb : X ⟶ A)
    [IsClosedImmersion emb] {UA : A.Opens} (hUA : IsAffineOpen UA) {V : Y.Opens}
    (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ (emb ⁻¹ᵁ UA))
    (hstd : (h.appLE (emb ⁻¹ᵁ UA) V e).hom.IsStandardSmooth) :
    ∃ (AY : Scheme.{u}) (_ : IsAffine AY) (hA : AY ⟶ (UA : Scheme.{u})) (_ : Smooth hA)
      (_ : ∃ d : ℕ, SmoothOfRelativeDimension d hA) (j : (V : Scheme.{u}) ⟶ AY)
      (_ : IsClosedImmersion j),
      IsPullback j (h.resLE (emb ⁻¹ᵁ UA) V e) hA (emb.resLE UA (emb ⁻¹ᵁ UA) le_rfl) := by
  have hX₀ : IsAffineOpen (emb ⁻¹ᵁ UA) := hUA.preimage emb
  let : Algebra Γ(A, UA) Γ(X, emb ⁻¹ᵁ UA) := (emb.appLE UA (emb ⁻¹ᵁ UA) le_rfl).hom.toAlgebra
  let : Algebra Γ(X, emb ⁻¹ᵁ UA) Γ(Y, V) := (h.appLE (emb ⁻¹ᵁ UA) V e).hom.toAlgebra
  let : Algebra Γ(A, UA) Γ(Y, V) :=
    ((h.appLE (emb ⁻¹ᵁ UA) V e).hom.comp (emb.appLE UA (emb ⁻¹ᵁ UA) le_rfl).hom).toAlgebra
  have : IsScalarTower Γ(A, UA) Γ(X, emb ⁻¹ᵁ UA) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hφ : Function.Surjective (algebraMap Γ(A, UA) Γ(X, emb ⁻¹ᵁ UA)) := by
    change Function.Surjective (emb.appLE UA (emb ⁻¹ᵁ UA) le_rfl).hom
    rw [Scheme.Hom.appLE_eq_app]
    exact emb.app_surjective UA hUA
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hstd.toAlgebra.out
  have := hσ
  have := hι
  have := isStandardSmooth_ambient hφ P
  -- the Spec square from the pushout, cut at the basic open `D(Δ)`
  have sq₁ : IsPullback (Spec.map (CommRingCat.ofHom (liftedToS hφ P).toRingHom))
      (Spec.map (h.appLE (emb ⁻¹ᵁ UA) V e))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(A, UA) (LiftedQuot hφ P))))
      (Spec.map (emb.appLE UA (emb ⁻¹ᵁ UA) le_rfl)) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_liftedQuot hφ P)).flip
  have hfac : Spec.map (CommRingCat.ofHom (liftedToS hφ P).toRingHom) =
      Spec.map (CommRingCat.ofHom (ambientToS hφ P)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (LiftedQuot hφ P) (Ambient hφ P))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ambientToS_comp_algebraMap]
  have hfac' : Spec.map (CommRingCat.ofHom (algebraMap (LiftedQuot hφ P) (Ambient hφ P))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(A, UA) (LiftedQuot hφ P))) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(A, UA) (Ambient hφ P))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (LiftedQuot hφ P) (Ambient hφ P)))) :=
    IsOpenImmersion.of_isLocalization (liftedJac hφ P)
  rw [hfac] at sq₁
  have sq₂ := sq₁.of_comp_mono_fst
  rw [hfac'] at sq₂
  -- the affine ambient and its structure maps
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap Γ(A, UA) (Ambient hφ P)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : SmoothOfRelativeDimension P.dimension
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(A, UA) (Ambient hφ P)))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension P.dimension)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).mpr
          (isStandardSmoothOfRelativeDimension_ambient hφ P)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (ambientToS hφ P))) :=
    IsClosedImmersion.spec_of_surjective _ (ambientToS_surjective hφ P)
  have : IsIso V.toSpecΓ := inferInstanceAs (IsIso hV.isoSpec.hom)
  refine ⟨Spec (CommRingCat.of (Ambient hφ P)), inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap Γ(A, UA) (Ambient hφ P))) ≫ hUA.isoSpec.inv,
    inferInstance, ⟨P.dimension + 0, inferInstance⟩,
    V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ambientToS hφ P)), inferInstance, ?_⟩
  refine sq₂.of_iso hV.isoSpec.symm (Iso.refl _) hX₀.isoSpec.symm hUA.isoSpec.symm ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← hV.isoSpec_hom, Iso.inv_hom_id_assoc]
  · rw [Iso.symm_hom, Iso.symm_hom, SpecMap_appLE_isoSpec_inv]
  · rw [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
  · rw [Iso.symm_hom, Iso.symm_hom, SpecMap_appLE_isoSpec_inv]

/-- [Kol07, Lemma 41] without the base field: the affine chart shrunk to the (open) image of
`AY → UA`, so that `hA` is surjective; `AY` is affine. -/
theorem exists_smooth_ambient_lift' {X Y A : Scheme.{u}} (h : Y ⟶ X) [Smooth h] (y : Y)
    (emb : X ⟶ A) [IsClosedImmersion emb] :
    ∃ (UA : A.Opens) (V : Y.Opens) (_ : y ∈ V) (hV : V ≤ h ⁻¹ᵁ (emb ⁻¹ᵁ UA))
      (AY : Scheme.{u}) (_ : IsAffine AY) (hA : AY ⟶ (UA : Scheme.{u})) (_ : Smooth hA)
      (_ : ∃ d : ℕ, SmoothOfRelativeDimension d hA) (_ : Function.Surjective hA)
      (j : (V : Scheme.{u}) ⟶ AY) (_ : IsClosedImmersion j),
      IsPullback j (h.resLE (emb ⁻¹ᵁ UA) V hV) hA (emb.resLE UA (emb ⁻¹ᵁ UA) le_rfl) := by
  obtain ⟨UA₀, hUA₀, hyUA₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := A) (x := emb (h y)) (U := ⊤) trivial
  have hX₀ : IsAffineOpen (emb ⁻¹ᵁ UA₀) := hUA₀.preimage emb
  obtain ⟨V₀, hV₀, hyV₀, hV₀le⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := h ⁻¹ᵁ (emb ⁻¹ᵁ UA₀)) hyUA₀
  obtain ⟨t, hyt, hstd⟩ := exists_basicOpen_isStandardSmooth_appLE h hX₀ hV₀ hV₀le hyV₀
  have hV : IsAffineOpen (Y.basicOpen t) := hV₀.basicOpen t
  have e : Y.basicOpen t ≤ h ⁻¹ᵁ (emb ⁻¹ᵁ UA₀) := (Y.basicOpen_le t).trans hV₀le
  obtain ⟨AY, hAY, hA₀, hsm, hrel, j, hj, sq⟩ := exists_affine_ambient h emb hUA₀ hV e hstd
  -- shrink `UA₀` to the (open) image of `AY`
  obtain ⟨UA, hUAc⟩ : ∃ UA : A.Opens, (UA : Set A) = Set.range (hA₀ ≫ UA₀.ι) :=
    ⟨⟨_, (hA₀ ≫ UA₀.ι).isOpenMap.isOpen_range⟩, rfl⟩
  have hmem : ∀ x, x ∈ UA ↔ ∃ p, (hA₀ ≫ UA₀.ι) p = x := fun x => by
    rw [← SetLike.mem_coe, hUAc]
    exact Set.mem_range
  have hle : UA ≤ UA₀ := by
    intro x hx
    obtain ⟨p, rfl⟩ := (hmem x).mp hx
    rw [Scheme.Hom.comp_apply]
    exact (hA₀ p).2
  obtain ⟨hA, hA_ι⟩ : ∃ hA : AY ⟶ (UA : Scheme.{u}), hA ≫ UA.ι = hA₀ ≫ UA₀.ι :=
    ⟨_, IsOpenImmersion.lift_fac UA.ι (hA₀ ≫ UA₀.ι) (by rw [Scheme.Opens.range_ι, hUAc])⟩
  have hA_comp : hA ≫ A.homOfLE hle = hA₀ := by
    rw [← cancel_mono UA₀.ι, Category.assoc, Scheme.homOfLE_ι, hA_ι]
  have hsurj : Function.Surjective hA := by
    intro a
    obtain ⟨p, hp⟩ := (hmem a.1).mp a.2
    refine ⟨p, UA.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hA_ι, hp]
    rfl
  have hV' : Y.basicOpen t ≤ h ⁻¹ᵁ (emb ⁻¹ᵁ UA) := by
    intro v hv
    have key : j ≫ hA₀ ≫ UA₀.ι = (Y.basicOpen t).ι ≫ h ≫ emb := by
      rw [sq.w_assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage]
    refine (hmem _).mpr ⟨j ⟨v, hv⟩, ?_⟩
    have e₁ : (hA₀ ≫ UA₀.ι) (j ⟨v, hv⟩) = (j ≫ hA₀ ≫ UA₀.ι) ⟨v, hv⟩ :=
      (Scheme.Hom.comp_apply _ _ _).symm
    rw [e₁, key]
    exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.Hom.comp_apply _ _ _)
  -- the restricted square, by pasting with the `homOfLE` square
  have t_sq : IsPullback (X.homOfLE (emb.preimage_mono hle)) (emb.resLE UA (emb ⁻¹ᵁ UA) le_rfl)
      (emb.resLE UA₀ (emb ⁻¹ᵁ UA₀) le_rfl) (A.homOfLE hle) := by
    refine IsPullback.of_right (h₁₂ := (emb ⁻¹ᵁ UA₀).ι) (v₁₃ := emb) (h₂₂ := UA₀.ι) ?_
      (by rw [Scheme.Hom.map_resLE, Scheme.Hom.resLE_map]) ?_
    · rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι, Scheme.Hom.resLE_eq_morphismRestrict]
      exact (isPullback_morphismRestrict emb UA).flip
    · rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact (isPullback_morphismRestrict emb UA₀).flip
  have s_sq : IsPullback
      (h.resLE (emb ⁻¹ᵁ UA) (Y.basicOpen t) hV' ≫ X.homOfLE (emb.preimage_mono hle)) j
      (emb.resLE UA₀ (emb ⁻¹ᵁ UA₀) le_rfl) (hA ≫ A.homOfLE hle) := by
    rw [Scheme.Hom.resLE_map, hA_comp]
    exact sq.flip
  have p : h.resLE (emb ⁻¹ᵁ UA) (Y.basicOpen t) hV' ≫ emb.resLE UA (emb ⁻¹ᵁ UA) le_rfl =
      j ≫ hA := by
    rw [← cancel_mono UA.ι]
    simp only [Category.assoc, hA_ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
      sq.w_assoc]
  have hsq_id : IsPullback (𝟙 AY) hA hA₀ (A.homOfLE hle) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hA_comp]⟩
  have : Smooth hA :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth) hsq_id hsm
  have hrel' : ∃ d : ℕ, SmoothOfRelativeDimension d hA := by
    obtain ⟨d, hd⟩ := hrel
    have := smoothOfRelativeDimension_isStableUnderBaseChange d
    exact ⟨d, MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @SmoothOfRelativeDimension d) hsq_id hd⟩
  exact ⟨UA, Y.basicOpen t, hyt, hV', AY, hAY, hA, inferInstance, hrel', hsurj, j, hj,
    (IsPullback.of_right s_sq p t_sq).flip⟩

/-- [Kol07, Lemma 41], over the base field `k`: for `h : Y ⟶ X` smooth, `y : Y` and a closed
immersion `emb : X ⟶ A` of schemes over `k`, opens `UA ∋ emb (h y)`, `V ∋ y`, a scheme `AY` over
`k` (through `hA` and `UA`; quasi-compact and separated over `k` as an affine scheme over the
affine `Spec k`), a smooth surjective `hA : AY ⟶ UA` of constant relative dimension and a closed
immersion `j : V ⟶ AY` making `V` the fibre product of `emb ⁻¹ᵁ UA` and `AY` over `UA`. -/
theorem exists_smooth_ambient_lift {k : Type u} [Field k]
    (X : Scheme.{u})
    (Y : Scheme.{u})
    (h : Y ⟶ X) [Smooth h] (y : Y)
    (A : Scheme.{u}) [A.Over (Spec (CommRingCat.of k))] (emb : X ⟶ A) [IsClosedImmersion emb] :
    ∃ (UA : A.Opens) (V : Y.Opens) (_ : y ∈ V) (hV : V ≤ h ⁻¹ᵁ (emb ⁻¹ᵁ UA))
      (AY : Scheme.{u}) (_ : AY.Over (Spec (CommRingCat.of k)))
      (_ : QuasiCompact (AY ↘ Spec (CommRingCat.of k)))
      (_ : IsSeparated (AY ↘ Spec (CommRingCat.of k))) (hA : AY ⟶ (UA : Scheme.{u}))
      (_ : Smooth hA) (_ : ∃ d : ℕ, SmoothOfRelativeDimension d hA) (_ : Function.Surjective hA)
      (j : (V : Scheme.{u}) ⟶ AY) (_ : IsClosedImmersion j),
      hA ≫ (UA.ι ≫ (A ↘ Spec (CommRingCat.of k))) = AY ↘ Spec (CommRingCat.of k) ∧
        IsPullback j (h.resLE (emb ⁻¹ᵁ UA) V hV) hA (emb.resLE UA (emb ⁻¹ᵁ UA) le_rfl) := by
  obtain ⟨UA, V, hyV, hV, AY, hAY, hA, hsm, hrel, hsurj, j, hj, sq⟩ :=
    exists_smooth_ambient_lift' h y emb
  have := hAY
  let : AY.Over (Spec (CommRingCat.of k)) := ⟨hA ≫ (UA.ι ≫ (A ↘ Spec (CommRingCat.of k)))⟩
  exact ⟨UA, V, hyV, hV, AY, inferInstance, inferInstance, inferInstance, hA, hsm, hrel, hsurj,
    j, hj, rfl, sq⟩

end AlgebraicGeometry
