/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# The hypotheses of Theorem 105: classes of morphisms, global and local triples

Kollár's globalization theorem [Kol07, Theorem 105] assumes (1) a class `M` of smooth morphisms
closed under fibre products and coproducts, (2) two classes of triples, the global triples `GT`
and the local triples `LT`, such that every point of a global triple has an `M`-neighbourhood
that is a local triple and `LT` is closed under disjoint unions, and (3) a blow-up sequence
functor on `LT` commuting with the surjections in `M`. The definitions (`IsGlobalizationClass`,
`openImmersionCoprods`, `Triple.GlobalizationData`, `CommutesWithSurjectionsIn`) are in
`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean`; this module proves the elementary facts
about them and exhibits Kollár's three examples of classes `M`.

## The three examples

Kollár's parenthetical "for instance, `M` could be all smooth morphisms, all étale morphisms or
all open immersions" in [Kol07, Theorem 105] asks, for each class, for three facts: its members
are smooth, it is stable under base change, and the morphism `∐ᵢ Uᵢ → X` induced by members
`Uᵢ → X` is a member.
For smooth and for étale morphisms the first two are Mathlib's (`Etale → Smooth`,
`smooth_isStableUnderBaseChange`, `etale_isStableUnderBaseChange`) and the third is locality on the
source (`IsZariskiLocalAtSource.sigmaDesc`: both properties are `HasRingHomProperty` classes).

The third class needs care. The open immersions themselves are *not* closed under coproducts
(`not_isGlobalizationClass_isOpenImmersion`): for a nonempty scheme `X`, the morphism
`X ⊔ X → X` induced by two copies of the identity identifies the two copies of a point, so it is
not a monomorphism, and open immersions are monomorphisms. What Kollár uses (his `g : X' → X`
and the projections `τ₁, τ₂` of `X' ×_X X'` in the proof of Theorem 105; the "coproduct of the
injections" of [Kol07, 104, Step 3]) is the class of **coproducts of open immersions**,
`openImmersionCoprods`: `f : Y ⟶ X` such that `Y` is a coproduct of schemes `Uᵢ`, along a colimit
cofan `ιᵢ : Uᵢ ⟶ Y`, with every `ιᵢ ≫ f` an open immersion.

The single tool for this class is Mathlib's characterization of colimit cofans of schemes: a cofan
`ι` on `Y` is a colimit iff the induced `Sigma.desc ι : ∐ᵢ Uᵢ ⟶ Y` is an isomorphism
(`Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`), together with the point-set description of `∐ᵢ Uᵢ`
(`sigmaMk`, `sigmaι_eq_iff`) and the converse criterion `nonempty_isColimit_cofanMk_of` (a family of
open immersions with disjoint images covering `Y` is a colimit cofan). From the first we read off
that the injections `ιᵢ` of a colimit cofan are open immersions, jointly surjective and pairwise
disjoint on points (`isOpenImmersion_of_isColimit_cofan`, `exists_eq_of_isColimit_cofan`,
`ne_of_isColimit_cofan`); the second, in its point-set form
(`nonempty_isColimit_cofanMk_of_range`), builds the new cofans.

* Étaleness (`openImmersionCoprods_etale`): `f = (Sigma.desc ι)⁻¹ ≫ Sigma.desc (ιᵢ ≫ f)`, and the
  second factor is étale by locality on the source, its pieces being open immersions.
* Base change (`isStableUnderBaseChange_openImmersionCoprods`): for the pullback `P = X ×_S Y` of
  `g : Y → S` along `f : X → S`, the schemes `Wᵢ := P ×_Y Uᵢ` with their first projections
  `Wᵢ → P` form a cofan of open immersions (base changes of `ιᵢ`), covering `P` (a point of `P`
  over `ιᵢ(x)` lifts to `Wᵢ`, `Scheme.Pullback.exists_preimage_pullback`) and pairwise disjoint
  (their images map to the disjoint images of the `ιᵢ`), hence a colimit cofan; and
  `Wᵢ → P → X` is the base change of the open immersion `ιᵢ ≫ g : Uᵢ → S` along `f` (the two
  squares paste, `IsPullback.paste_horiz`). Mathlib's `IsStableUnderBaseChange.mk'` reduces the
  general pullback square to this canonical one, given `RespectsIso`
  (`respectsIso_openImmersionCoprods`: transport the cofan along the isomorphism).
* Coproducts (`sigmaDesc_openImmersionCoprods`): if each `gᵢ : Uᵢ → X` is a coproduct of open
  immersions along `κᵢⱼ : Vᵢⱼ → Uᵢ`, then `∐ᵢ Uᵢ` is the coproduct of the `Vᵢⱼ` along
  `κᵢⱼ ≫ Sigma.ι Uᵢ` (index type `Σ i, τᵢ`), and `(κᵢⱼ ≫ Sigma.ι Uᵢ) ≫ Sigma.desc g = κᵢⱼ ≫ gᵢ`.

## The data and the functor hypothesis

`Triple.GlobalizationData M GT LT` is monotone in `M` and antitone in `GT` (its clause (i)
quantifies over `GT` and asks for a member of `M`). `CommutesWithSurjectionsIn B M` is antitone
in `M`; for `M` = all smooth morphisms it is `CommutesWithSmoothSurjections` (the instance binder
`[Smooth h]` against the hypothesis `@Smooth _ _ h`), and a functor commuting with all smooth
surjections commutes with the surjections in every class of Theorem 105, whose members are
smooth.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Hironaka TopologicalSpace

namespace Hironaka.Sequence

/-! ### Colimit cofans of schemes, read on points -/

section Cofan

variable {σ : Type u} {U : σ → Scheme.{u}} {Y : Scheme.{u}} (ι : ∀ i, U i ⟶ Y)

/-- A colimit cofan of schemes is the canonical coproduct up to the isomorphism `Sigma.desc ι`
(Mathlib's `Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`). -/
theorem isIso_sigmaDesc_of_isColimit_cofan (h : Nonempty (IsColimit (Cofan.mk Y ι))) :
    IsIso (Sigma.desc ι) :=
  (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk Y ι)).mp h

/-- The injections of a colimit cofan of schemes are open immersions. -/
theorem isOpenImmersion_of_isColimit_cofan (h : Nonempty (IsColimit (Cofan.mk Y ι))) (i : σ) :
    IsOpenImmersion (ι i) := by
  have := isIso_sigmaDesc_of_isColimit_cofan ι h
  rw [← Sigma.ι_comp_desc ι i]
  infer_instance

/-- The injections of a colimit cofan of schemes are jointly surjective. -/
theorem exists_eq_of_isColimit_cofan (h : Nonempty (IsColimit (Cofan.mk Y ι))) (y : Y) :
    ∃ (i : σ) (x : U i), ι i x = y := by
  have := isIso_sigmaDesc_of_isColimit_cofan ι h
  obtain ⟨z, rfl⟩ := (Sigma.desc ι).surjective y
  obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk U).surjective z
  exact ⟨i, x, by rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩

/-- The injections of a colimit cofan of schemes have pairwise disjoint images. -/
theorem ne_of_isColimit_cofan (h : Nonempty (IsColimit (Cofan.mk Y ι))) {i j : σ} (hij : i ≠ j)
    (x : U i) (x' : U j) : ι i x ≠ ι j x' := by
  have := isIso_sigmaDesc_of_isColimit_cofan ι h
  intro hx
  rw [← Sigma.ι_comp_desc ι i, ← Sigma.ι_comp_desc ι j, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply] at hx
  have hx' := (Sigma.desc ι).isOpenEmbedding.injective hx
  rw [sigmaι_eq_iff] at hx'
  exact hij (Sigma.mk.inj_iff.mp hx').1

/-- Mathlib's `nonempty_isColimit_cofanMk_of` on points: a family of open immersions into `S`
that covers `S` and has pairwise disjoint images is a colimit cofan. -/
theorem nonempty_isColimit_cofanMk_of_range {S : Scheme.{u}} (f : ∀ i, U i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hcov : ∀ s : S, ∃ (i : σ) (x : U i), f i x = s)
    (hdisj : ∀ i j, i ≠ j → ∀ (x : U i) (y : U j), f i x ≠ f j y) :
    Nonempty (IsColimit (Cofan.mk S f)) := by
  refine nonempty_isColimit_cofanMk_of f ?_ ?_
  · refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨i, x, rfl⟩ := hcov s
    exact Opens.mem_iSup.mpr ⟨i, x, rfl⟩
  · intro i j hij
    have : Disjoint (Set.range (f i)) (Set.range (f j)) := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
      exact hdisj i j hij x y hy.symm
    simpa [Function.onFun_apply, disjoint_iff, Opens.ext_iff] using this

end Cofan

/-! ### Kollár's three examples of classes -/

section Examples

/-- The first example of a class in [Kol07, Theorem 105 (1)]: all smooth morphisms. -/
theorem isGlobalizationClass_smooth : IsGlobalizationClass.{u} @Smooth where
  smooth _ hf := hf
  isStableUnderBaseChange := inferInstance
  sigmaDesc _ hg :=
    have : IsZariskiLocalAtSource @Smooth :=
      @HasRingHomProperty.instIsZariskiLocalAtSource @Smooth _ inferInstance
    IsZariskiLocalAtSource.sigmaDesc hg

/-- The second example of a class in [Kol07, Theorem 105 (1)]: all étale morphisms. -/
theorem isGlobalizationClass_etale : IsGlobalizationClass.{u} @Etale where
  smooth _ hf := have := hf; inferInstance
  isStableUnderBaseChange := inferInstance
  sigmaDesc _ hg :=
    have : IsZariskiLocalAtSource @Etale :=
      @HasRingHomProperty.instIsZariskiLocalAtSource @Etale _ inferInstance
    IsZariskiLocalAtSource.sigmaDesc hg

/-- An open immersion is a coproduct of open immersions with one summand. -/
theorem openImmersionCoprods_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : openImmersionCoprods f := by
  refine ⟨PUnit, fun _ => X, fun _ => 𝟙 X, ?_, fun _ => by rw [Category.id_comp]; infer_instance⟩
  refine nonempty_isColimit_cofanMk_of_range (fun _ : PUnit.{u + 1} => 𝟙 X)
    (fun x => ⟨⟨⟩, x, by simp⟩) fun i j hij => absurd (Subsingleton.elim i j) hij

/-- The morphism `∐ᵢ Uᵢ → X` induced by open immersions `Uᵢ → X` (the "coproduct of the
injections" of [Kol07, 104, Step 3]) is a coproduct of open immersions. -/
theorem openImmersionCoprods_sigmaDesc {σ : Type u} {U : σ → Scheme.{u}} {X : Scheme.{u}}
    (g : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (g i)] : openImmersionCoprods (Sigma.desc g) :=
  ⟨σ, U, Sigma.ι U, ⟨coproductIsCoproduct U⟩, fun i => by rw [Sigma.ι_comp_desc]; infer_instance⟩

/-- A coproduct of open immersions is étale. -/
theorem openImmersionCoprods_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : openImmersionCoprods f) : Etale f := by
  obtain ⟨σ, U, ι, hc, hι⟩ := hf
  have := isIso_sigmaDesc_of_isColimit_cofan ι hc
  have hdesc : Sigma.desc ι ≫ f = Sigma.desc fun i => ι i ≫ f := by
    ext i
    simp
  have : IsZariskiLocalAtSource @Etale :=
    @HasRingHomProperty.instIsZariskiLocalAtSource @Etale _ inferInstance
  have h1 : Etale (Sigma.desc fun i => ι i ≫ f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun i => have := hι i; inferInstance
  have h2 : Etale (inv (Sigma.desc ι) ≫ Sigma.desc ι ≫ f) := by
    rw [hdesc]
    infer_instance
  rwa [IsIso.inv_hom_id_assoc] at h2

/-- Coproducts of open immersions respect isomorphisms: transport the cofan. -/
theorem respectsIso_openImmersionCoprods : openImmersionCoprods.{u}.RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ ?_ ?_
  · rintro X Y Z e f ⟨σ, U, ι, hc, hι⟩
    have := isIso_sigmaDesc_of_isColimit_cofan ι hc
    refine ⟨σ, U, fun i => ι i ≫ e.inv, ?_, fun i => ?_⟩
    · rw [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc]
      have : Sigma.desc (fun i => ι i ≫ e.inv) = Sigma.desc ι ≫ e.inv := by
        ext i
        simp
      change IsIso (Sigma.desc fun i => ι i ≫ e.inv)
      rw [this]
      infer_instance
    · have : (ι i ≫ e.inv) ≫ e.hom ≫ f = ι i ≫ f := by simp
      rw [this]
      exact hι i
  · rintro X Y Z e f ⟨σ, U, ι, hc, hι⟩
    exact ⟨σ, U, ι, hc, fun i => by
      have := hι i
      rw [← Category.assoc]
      infer_instance⟩

/-- Coproducts of open immersions are stable under base change: the pullback of `Y = ∐ᵢ Uᵢ → S`
along `f : X → S` is covered by the disjoint open subschemes `P ×_Y Uᵢ`, each mapping to `X` by
the base change of the open immersion `Uᵢ → S`. -/
theorem isStableUnderBaseChange_openImmersionCoprods :
    openImmersionCoprods.{u}.IsStableUnderBaseChange := by
  have := respectsIso_openImmersionCoprods.{u}
  refine MorphismProperty.IsStableUnderBaseChange.mk' fun X Y S f g _ hg => ?_
  obtain ⟨σ, U, ι, hc, hι⟩ := hg
  have hιo : ∀ i, IsOpenImmersion (ι i) := isOpenImmersion_of_isColimit_cofan ι hc
  have : ∀ i, IsOpenImmersion (pullback.fst (pullback.snd f g) (ι i)) := fun i =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.of_hasPullback _ _).flip (hιo i)
  refine ⟨σ, fun i => pullback (pullback.snd f g) (ι i), fun i => pullback.fst _ _, ?_,
    fun i => ?_⟩
  · refine nonempty_isColimit_cofanMk_of_range _ ?_ ?_
    · intro p
      obtain ⟨i, x, hx⟩ := exists_eq_of_isColimit_cofan ι hc (pullback.snd f g p)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback p x hx.symm
      exact ⟨i, w, hw⟩
    · intro i j hij w w' hww
      apply ne_of_isColimit_cofan ι hc hij (pullback.snd (pullback.snd f g) (ι i) w)
        (pullback.snd (pullback.snd f g) (ι j) w')
      have h1 : ι i (pullback.snd (pullback.snd f g) (ι i) w) =
          pullback.snd f g (pullback.fst (pullback.snd f g) (ι i) w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      have h2 : ι j (pullback.snd (pullback.snd f g) (ι j) w') =
          pullback.snd f g (pullback.fst (pullback.snd f g) (ι j) w') := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      rw [h1, h2, hww]
  · have sq := (IsPullback.of_hasPullback (pullback.snd f g) (ι i)).paste_horiz
      (IsPullback.of_hasPullback f g)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) sq.flip
      (hι i)

/-- Coproducts of open immersions are closed under coproducts: a coproduct of coproducts is a
coproduct, indexed by the sigma type. -/
theorem sigmaDesc_openImmersionCoprods {σ : Type u} {U : σ → Scheme.{u}} {X : Scheme.{u}}
    (g : ∀ i, U i ⟶ X) (hg : ∀ i, openImmersionCoprods (g i)) :
    openImmersionCoprods (Sigma.desc g) := by
  choose τ V κ hc hκ using hg
  have hκo : ∀ i j, IsOpenImmersion (κ i j) := fun i j =>
    isOpenImmersion_of_isColimit_cofan (κ i) (hc i) j
  refine ⟨Σ i, τ i, fun p => V p.1 p.2, fun p => κ p.1 p.2 ≫ Sigma.ι U p.1, ?_, fun p => ?_⟩
  · refine nonempty_isColimit_cofanMk_of_range _ ?_ ?_
    · intro z
      obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk U).surjective z
      obtain ⟨j, v, rfl⟩ := exists_eq_of_isColimit_cofan (κ i) (hc i) x
      exact ⟨⟨i, j⟩, v, by rw [sigmaMk_mk, Scheme.Hom.comp_apply]⟩
    · rintro ⟨i, j⟩ ⟨i', j'⟩ hne v v' hvv
      simp only [Scheme.Hom.comp_apply] at hvv
      rw [sigmaι_eq_iff] at hvv
      obtain ⟨rfl, hv⟩ := Sigma.mk.inj_iff.mp hvv
      exact ne_of_isColimit_cofan (κ i) (hc i) (fun h => hne (Sigma.ext rfl (heq_of_eq h))) v v'
        (eq_of_heq hv)
  · have := hκ p.1 p.2
    rw [Category.assoc, Sigma.ι_comp_desc]
    infer_instance

/-- The third example of a class in [Kol07, Theorem 105 (1)], read as the proof uses it: the
coproducts of open immersions. -/
theorem isGlobalizationClass_openImmersionCoprods :
    IsGlobalizationClass.{u} openImmersionCoprods where
  smooth f hf := have := openImmersionCoprods_etale f hf; inferInstance
  isStableUnderBaseChange := isStableUnderBaseChange_openImmersionCoprods
  sigmaDesc g hg := sigmaDesc_openImmersionCoprods g hg

/-- For a nonempty scheme `X`, the morphism `X ⊔ X → X` induced by two copies of the identity is
not an open immersion: it identifies the two copies of a point, so it is not a monomorphism. -/
theorem not_isOpenImmersion_sigmaDesc_id {X : Scheme.{u}} [Nonempty X] :
    ¬ IsOpenImmersion (Sigma.desc fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} => 𝟙 X) := by
  intro hoi
  obtain ⟨x⟩ := ‹Nonempty X›
  have heq : Sigma.ι (fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} => X) (Sum.inl PUnit.unit) =
      Sigma.ι (fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} => X) (Sum.inr PUnit.unit) := by
    rw [← cancel_mono (Sigma.desc fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} => 𝟙 X)]
    simp
  have hx : (Sigma.ι (fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} => X) (Sum.inl PUnit.unit)) x =
      (Sigma.ι (fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} => X) (Sum.inr PUnit.unit)) x := by
    rw [heq]
  rw [sigmaι_eq_iff] at hx
  exact Sum.inl_ne_inr (Sigma.mk.inj_iff.mp hx).1

/-- The open immersions are not closed under coproducts, so they are not, as they stand, a class
of [Kol07, Theorem 105]; the class the proof uses is `openImmersionCoprods`. -/
theorem not_isGlobalizationClass_isOpenImmersion :
    ¬ IsGlobalizationClass.{u} @IsOpenImmersion := by
  intro h
  have : Nonempty ↥(Spec (CommRingCat.of (ULift.{u} ℤ))) := inferInstance
  exact not_isOpenImmersion_sigmaDesc_id
    (h.sigmaDesc (fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} => 𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ))))
      fun _ => inferInstance)

end Examples

end Hironaka.Sequence

namespace Hironaka

/-- A class of Theorem 105 respects isomorphisms (Mathlib: base-change stability gives
`RespectsIso`). -/
theorem IsGlobalizationClass.respectsIso {M : MorphismProperty Scheme.{u}}
    (hM : IsGlobalizationClass M) : M.RespectsIso :=
  have := hM.isStableUnderBaseChange
  inferInstance

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

/-- The data (2) of [Kol07, Theorem 105] is monotone in the class `M`. -/
theorem GlobalizationData.of_le {M M' : MorphismProperty Scheme.{u}} {GT LT : Triple k → Prop}
    (hle : M ≤ M') (hD : GlobalizationData M GT LT) : GlobalizationData M' GT LT where
  exists_isPullbackOf T hT x := by
    obtain ⟨T', g, hg, hx, hp, hL⟩ := hD.exists_isPullbackOf T hT x
    exact ⟨T', g, hle _ hg, hx, hp, hL⟩
  closedUnderSigma := hD.closedUnderSigma

/-- The data (2) of [Kol07, Theorem 105] restricts to a smaller class of global triples. -/
theorem GlobalizationData.restrict {M : MorphismProperty Scheme.{u}} {GT GT' LT : Triple k → Prop}
    (hle : ∀ T, GT' T → GT T) (hD : GlobalizationData M GT LT) : GlobalizationData M GT' LT where
  exists_isPullbackOf T hT x := hD.exists_isPullbackOf T (hle T hT) x
  closedUnderSigma := hD.closedUnderSigma

end AlgebraicGeometry.Triple

namespace Hironaka

namespace OrderSeqAssignment

variable {k : Type u} [Field k] {m : ℕ} {Dom : Triple k → Prop}

/-- The hypothesis (3) of [Kol07, Theorem 105] with `M` = all smooth morphisms is the first
bullet of [Kol07, 34.1], commutation with smooth surjections. -/
theorem commutesWithSurjectionsIn_smooth_iff (B : OrderSeqAssignment k m Dom) :
    B.CommutesWithSurjectionsIn @Smooth ↔ B.CommutesWithSmoothSurjections := by
  constructor
  · intro H T T' h hsm hs hp
    exact H T T' h hsm hs hp
  · intro H T T' h hsm hs hp
    exact @H T T' h hsm hs hp

/-- Commuting with the surjections in `M` is antitone in `M`. -/
theorem CommutesWithSurjectionsIn.mono {B : OrderSeqAssignment k m Dom}
    {M M' : MorphismProperty Scheme.{u}} (hle : M' ≤ M) (hB : B.CommutesWithSurjectionsIn M) :
    B.CommutesWithSurjectionsIn M' :=
  fun T T' h hh hs hp => hB T T' h (hle _ hh) hs hp

/-- A functor commuting with smooth surjections commutes with the surjections in every class of
Theorem 105. -/
theorem CommutesWithSmoothSurjections.commutesWithSurjectionsIn {B : OrderSeqAssignment k m Dom}
    (hB : B.CommutesWithSmoothSurjections) {M : MorphismProperty Scheme.{u}}
    (hM : IsGlobalizationClass M) : B.CommutesWithSurjectionsIn M :=
  fun T T' h hh hs hp => @hB T T' h (hM.smooth h hh) hs hp

/-- The unfolding of `CommutesWithSurjectionsIn`. -/
theorem CommutesWithSurjectionsIn.commutesWith {B : OrderSeqAssignment k m Dom}
    {M : MorphismProperty Scheme.{u}} (hB : B.CommutesWithSurjectionsIn M) {T T' : Triple k}
    {h : T'.X.left ⟶ T.X.left} (hM : M h) (hs : Function.Surjective h) (hT : T'.IsPullbackOf T h) :
    B.CommutesWith h :=
  hB T T' h hM hs hT

end OrderSeqAssignment

namespace OrderGeSeqAssignment

variable {k : Type u} [Field k] {Dom : MarkedTriple k → Prop}

/-- The hypothesis (3) of [Kol07, Theorem 105] with `M` = all smooth morphisms, for marked
functors: commutation with smooth surjections. -/
theorem commutesWithSurjectionsIn_smooth_iff (B : OrderGeSeqAssignment k Dom) :
    B.CommutesWithSurjectionsIn @Smooth ↔ B.CommutesWithSmoothSurjections := by
  constructor
  · intro H T T' h hsm hs hp
    exact H T T' h hsm hs hp
  · intro H T T' h hsm hs hp
    exact @H T T' h hsm hs hp

/-- Commuting with the surjections in `M` is antitone in `M` (marked functors). -/
theorem CommutesWithSurjectionsIn.mono {B : OrderGeSeqAssignment k Dom}
    {M M' : MorphismProperty Scheme.{u}} (hle : M' ≤ M) (hB : B.CommutesWithSurjectionsIn M) :
    B.CommutesWithSurjectionsIn M' :=
  fun T T' h hh hs hp => hB T T' h (hle _ hh) hs hp

/-- A marked functor commuting with smooth surjections commutes with the surjections in every
class of Theorem 105. -/
theorem CommutesWithSmoothSurjections.commutesWithSurjectionsIn {B : OrderGeSeqAssignment k Dom}
    (hB : B.CommutesWithSmoothSurjections) {M : MorphismProperty Scheme.{u}}
    (hM : IsGlobalizationClass M) : B.CommutesWithSurjectionsIn M :=
  fun T T' h hh hs hp => @hB T T' h (hM.smooth h hh) hs hp

/-- The unfolding of `CommutesWithSurjectionsIn` for marked functors. -/
theorem CommutesWithSurjectionsIn.commutesWith {B : OrderGeSeqAssignment k Dom}
    {M : MorphismProperty Scheme.{u}} (hB : B.CommutesWithSurjectionsIn M) {T T' : MarkedTriple k}
    {h : T'.X.left ⟶ T.X.left} (hM : M h) (hs : Function.Surjective h) (hT : T'.IsPullbackOf T h) :
    B.CommutesWith h :=
  hB T T' h hM hs hT

end OrderGeSeqAssignment

end Hironaka
