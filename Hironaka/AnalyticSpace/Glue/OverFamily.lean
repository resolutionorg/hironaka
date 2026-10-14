/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Over
public import Hironaka.AnalyticSpace.SncFamily
import Hironaka.AnalyticSpace.Glue.Constants
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Closed subspaces and labelled families descend along a gluing over a base

The resolution of an analytic space comes with its exceptional divisor, a locally finite family of
smooth hypersurfaces with simple normal crossings ([Kol07, Definition 24]; [Kol07, Theorem 45, (3)];
[Wlo09, Theorem 2.0.1, (2)]). The sources glue the spaces only: Włodarczyk's `Ṽ` is "obtained by
gluing `Ṽ_i` along `Ṽ_i ∩ Ṽ_j`", and the construction "commutes with local analytic isomorphisms" by
construction [Wlo09, §4]; Kollár passes from the neighbourhoods of compact sets to their union
[Kol07, 44]. That the exceptional families of the pieces glue with the spaces is left to the reader.
This module proves the descent step for a gluing datum `G : GlueOver X R π dom`
(`Hironaka.AnalyticSpace.Glue.Over`):

* **Descent of one closed subspace** (`glueClosedSubspace`): closed subspaces `C i` of the pieces
  whose restrictions to the gluing open subsets correspond under the transitions
  (`CompatClosedSubspaces`) descend to a closed subspace of `G.gluedOver`: the ideal sheaf with the
  stalk ideals `comap ((ιGlued i).stalkMap y) ((C i).stalkIdeal y)` at `ιGlued i y`, well defined
  because two representatives of one glued point are related through a transition
  (`KGlueData.exists_of_ι_base_eq`), the glue condition identifies the two legs' stalk maps, and
  compatibility identifies the two stalk ideals (`pieceStalkIdeal_eq`); its local generators are the
  pieces' carried through the open immersions (`IsOpenImmersion.invApp`). It pulls back to `C i`
  along every `ιGlued i` (`comap_ιGlued_glueClosedSubspace`), its support is the union of the images
  of the pieces' supports (`support_glueClosedSubspace`), and it is the only closed subspace with
  these pull-backs (`ext_of_forall_comap_ιGlued_eq`, `existsUnique_comap_ιGlued_eq`).
* **The labelled family layer**: families `H i : κ i → ClosedSubspace (R i)` with labels
  `lab i : κ i → Λ`, injective on every piece; `memberOfLabel H lab i l` is the member of the `i`-th
  family carrying the label `l`, the empty subspace `⊤` when the piece has no such member.
  `LabelledCompat` asks, label by label, for the compatibility of these members: the partner of a
  member across an overlap is fixed by its label, and a member absent from a neighbouring piece does
  not meet the overlap (the `⊤` convention on empty members). Then
  `glueFamily : Λ → ClosedSubspace G.gluedOver` glues label by label; it pulls back to the given
  members (`comap_ιGlued_glueFamily_lab`), has total support the union of the pieces' total supports
  (`iUnion_support_glueFamily`), is locally finite when the pieces' families are
  (`locallyFinite_glueFamily`), and is a simple-normal-crossings family
  (`ClosedSubspace.IsSncFamily`, `Hironaka.AnalyticSpace.SncFamily`) when the pieces' are
  (`isSncFamily_glueFamily`): the stalk clause at a glued point is the piece's, carried through the
  ring isomorphism of the open immersion's stalk map, the members through the point matched by the
  labels.

The label type is arbitrary here. In the resolution of an analytic space the pieces' exceptional
families are the traces of one family indexed by the stages of a single run of the resolution
functor on the disjoint union of the pieces, so the labelling is the identity
(`Hironaka.Resolution.Analytic.Kol07Thm45.CoproductGluedFamily`), and `LabelledCompat` comes from
the agreement of the stages across the overlaps (`CoproductGluedFamilyCompat`,
`ExhaustionChainFamilies`, `ResolutionOnMembers`); the gluing along an exhaustion uses the chain
form of `Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverFamilyChain`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry Set Opposite
open Manifold AnalyticSpace KLocallyRingedSpace

namespace AnalyticSpace.GlueOver

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K} {ι : Type u}
  {R : ι → AnalyticSpace.{u} K} {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace}
  {dom : ι → Opens X} (G : GlueOver X R π dom) [Countable ι]

variable (π dom) in
/-- The restriction of a closed subspace `Z` of the `i`-th piece to the gluing open subset
`glueOpens i j`, as an ideal sheaf of the restricted piece: the pull-back along the open inclusion
(the trace on a part). -/
noncomputable def restrictGlue (i j : ι) (Z : ClosedSubspace (R i)) :
    IdealSheaf
      ((R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j)).toLocallyRingedSpace.𝒪 :=
  QuotientSpace.comap (ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j)).1 Z

/-- **Compatibility of closed subspaces of the pieces**: on every gluing open subset the transition
`t i j` pulls the `j`-th subspace back to the `i`-th. -/
def CompatClosedSubspaces (C : ∀ i, ClosedSubspace (R i)) : Prop :=
  ∀ i j, QuotientSpace.comap (G.t i j).1 (restrictGlue π dom j i (C j)) =
    restrictGlue π dom i j (C i)

/-- Two representatives of one glued point are related through the transition
(`KGlueData.exists_of_ι_base_eq`, Mathlib's `ι_eq_iff_rel` underneath). -/
theorem exists_t_eq_of_toFun_ιGlued_eq {i j : ι} {y : R i} {y' : R j}
    (h : KLocallyRingedSpace.Hom.toFun (G.ιGlued i) y = KLocallyRingedSpace.Hom.toFun
        (G.ιGlued j) y') :
    ∃ x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j),
      x.1 = y ∧ (KLocallyRingedSpace.Hom.toFun (G.t i j) x).1 = y' := by
  obtain ⟨v, hv₁, hv₂⟩ := G.toKGlueData.exists_of_ι_base_eq h
  exact ⟨v, hv₁, hv₂⟩

/-- The glue condition of the gluing over `X`, on the pieces: `ofRestrict ≫ ιGlued i` and
`t i j ≫ ofRestrict ≫ ιGlued j` agree on the gluing open subset. -/
theorem ofRestrict_comp_ιGlued (i j : ι) :
    (ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j)).1 ≫ (G.ιGlued i).1 =
      (G.t i j).1 ≫ (ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)).1 ≫
        (G.ιGlued j).1 :=
  (G.toKGlueData.toLRSGlueData.toGlueData.glue_condition i j).symm

/-- Two stalk-specialization maps along an equality of points compose to the identity. -/
theorem stalkSpecializes_comp_eq_id {C : Type*} [Category C] [Limits.HasColimits C]
    {Y : TopCat} (F : Y.Presheaf C) {x y : Y} (hxy : x = y) (h₁ : x ⤳ y) (h₂ : y ⤳ x) :
    F.stalkSpecializes h₁ ≫ F.stalkSpecializes h₂ = 𝟙 (F.stalk y) := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]

/-- The ideal algebra of representative independence: in a commutative square `α ≫ a = σ' ≫ β ≫ b`
with `a`, `b` bijective and `σ ≫ σ' = 𝟙`, ideals `I`, `J` with the same image under `a`, `b` pull
back along `α`, `β` to ideals identified by `σ`. -/
theorem comap_eq_of_stalk_square {A B A' B' S : CommRingCat} (α : A ⟶ A') (β : B ⟶ B')
    (a : A' ⟶ S) (b : B' ⟶ S) (σ : B ⟶ A) (σ' : A ⟶ B) (hσ : σ ≫ σ' = 𝟙 B)
    (ha : Function.Bijective a.hom) (hb : Function.Bijective b.hom)
    (hsq : α ≫ a = σ' ≫ β ≫ b) (I : Ideal A') (J : Ideal B')
    (hIJ : Ideal.map a.hom I = Ideal.map b.hom J) :
    Ideal.comap σ.hom (Ideal.comap α.hom I) = Ideal.comap β.hom J := by
  have h1 : Ideal.comap α.hom I = Ideal.comap σ'.hom (Ideal.comap β.hom J) := by
    calc Ideal.comap α.hom I
        = Ideal.comap α.hom (Ideal.comap a.hom (Ideal.map a.hom I)) := by
          rw [Ideal.comap_map_of_bijective _ ha]
      _ = Ideal.comap (α ≫ a).hom (Ideal.map a.hom I) := by
          rw [Ideal.comap_comap, CommRingCat.hom_comp]
      _ = Ideal.comap (σ' ≫ β ≫ b).hom (Ideal.map b.hom J) := by rw [hsq, hIJ]
      _ = Ideal.comap σ'.hom (Ideal.comap β.hom (Ideal.comap b.hom (Ideal.map b.hom J))) := by
          simp only [CommRingCat.hom_comp, Ideal.comap_comap]
      _ = Ideal.comap σ'.hom (Ideal.comap β.hom J) := by
          rw [Ideal.comap_map_of_bijective _ hb]
  rw [h1, Ideal.comap_comap σ.hom σ'.hom, ← CommRingCat.hom_comp, hσ, CommRingCat.hom_id,
    Ideal.comap_id]

/-- The stalk ideal of the `i`-th subspace, read on the glued space at the image point. -/
noncomputable def pieceStalkIdeal (C : ∀ i, ClosedSubspace (R i)) (i : ι) (y : R i) :
    Ideal (G.gluedOver.toLocallyRingedSpace.presheaf.stalk (KLocallyRingedSpace.Hom.toFun
        (G.ιGlued i) y)) :=
  Ideal.comap ((G.ιGlued i).1.stalkMap y).hom ((C i).stalkIdeal y)

/-- **Representative independence**: the piece stalk ideals of two representatives of one glued
point agree under the canonical identification of the stalks. -/
theorem pieceStalkIdeal_eq (C : ∀ i, ClosedSubspace (R i)) (hc : G.CompatClosedSubspaces C)
    {i j : ι} {y : R i} {y' : R j} (h : KLocallyRingedSpace.Hom.toFun
        (G.ιGlued i) y = KLocallyRingedSpace.Hom.toFun (G.ιGlued j) y') :
    Ideal.comap (G.gluedOver.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq h)).hom (G.pieceStalkIdeal C i y) =
      G.pieceStalkIdeal C j y' := by
  obtain ⟨v, hv₁, hv₂⟩ := G.exists_t_eq_of_toFun_ιGlued_eq h
  subst hv₁
  subst hv₂
  -- the two legs from the gluing open
  set f₁ := (ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j)).1 with hf₁
  set f₂ := (G.t i j).1 ≫ (ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)).1
    with hf₂
  have hglue : f₁ ≫ (G.ιGlued i).1 = f₂ ≫ (G.ιGlued j).1 := by
    rw [hf₂, Category.assoc]; exact G.ofRestrict_comp_ιGlued i j
  -- the stalk maps of the two legs are isomorphisms
  have hiso : IsIso (G.t i j).1 := G.toKGlueData.toLRSGlueData.toGlueData.t_isIso i j
  have hoi : LocallyRingedSpace.IsOpenImmersion (G.t i j).1 :=
    LocallyRingedSpace.IsOpenImmersion.of_isIso _
  have hoi₂ : LocallyRingedSpace.IsOpenImmersion f₂ :=
    LocallyRingedSpace.IsOpenImmersion.comp (H := hoi) (G.t i j).1
      (ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)).1
  have hb₂ : Function.Bijective (f₂.stalkMap v).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      (@LocallyRingedSpace.IsOpenImmersion.stalk_iso _ _ f₂ hoi₂ v)
  have hb₁ : Function.Bijective (f₁.stalkMap v).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  -- compatibility at the stalk of `v`
  have hcomp : Ideal.map (f₁.stalkMap v).hom ((C i).stalkIdeal v.1) =
      Ideal.map (f₂.stalkMap v).hom ((C j).stalkIdeal (f₂.base v)) := by
    have h1 := congrArg (fun J : IdealSheaf _ => J.stalkIdeal v) (hc i j)
    simp only [restrictGlue, ← QuotientSpace.comap_comp] at h1
    rw [QuotientSpace.stalkIdeal_comap, QuotientSpace.stalkIdeal_comap] at h1
    exact h1.symm
  -- the stalk maps of the composites agree up to the canonical identification
  have hstalk := LocallyRingedSpace.stalkMap_congr_hom _ _ hglue v
  rw [LocallyRingedSpace.stalkMap_comp, LocallyRingedSpace.stalkMap_comp] at hstalk
  unfold pieceStalkIdeal
  exact comap_eq_of_stalk_square _ _ _ _ _ _ (stalkSpecializes_comp_eq_id _ h _ _) hb₁ hb₂ hstalk
    _ _ hcomp

/-- A representative `(i, y)` of a point of the glued space. -/
noncomputable def gluedRep (z : G.gluedOver) : Σ i : ι, R i :=
  ⟨(G.exists_ιGlued_eq z).choose, (G.exists_ιGlued_eq z).choose_spec.choose⟩

/-- The chosen representative represents: `ιGlued (gluedRep z).1` sends `(gluedRep z).2` to `z`. -/
theorem toFun_ιGlued_gluedRep (z : G.gluedOver) :
    KLocallyRingedSpace.Hom.toFun (G.ιGlued (G.gluedRep z).1) (G.gluedRep z).2 = z :=
  (G.exists_ιGlued_eq z).choose_spec.choose_spec

/-- The glued stalk ideal at `z`: the piece stalk ideal of a representative, carried to `z`. -/
noncomputable def gluedStalkIdeal (C : ∀ i, ClosedSubspace (R i)) (z : G.gluedOver) :
    Ideal (G.gluedOver.toLocallyRingedSpace.presheaf.stalk z) :=
  Ideal.comap (G.gluedOver.toLocallyRingedSpace.presheaf.stalkSpecializes
      (specializes_of_eq (G.toFun_ιGlued_gluedRep z))).hom
    (G.pieceStalkIdeal C (G.gluedRep z).1 (G.gluedRep z).2)

/-- The glued stalk ideal at the image of `y` is the `i`-th piece stalk ideal. -/
theorem gluedStalkIdeal_toFun_ιGlued (C : ∀ i, ClosedSubspace (R i))
    (hc : G.CompatClosedSubspaces C) (i : ι) (y : R i) :
    G.gluedStalkIdeal C (KLocallyRingedSpace.Hom.toFun (G.ιGlued i) y) = G.pieceStalkIdeal C i y :=
        by
  unfold gluedStalkIdeal
  exact G.pieceStalkIdeal_eq C hc (G.toFun_ιGlued_gluedRep _)

/-- A germ of a section transported along an identity of open subsets is the germ of the section. -/
theorem germ_map_eqToHom {Y : TopCat} (F : Y.Presheaf CommRingCat) {U V : Opens Y}
    (e : op U = op V) (x : Y) (hx : x ∈ V) (s : F.obj (op U)) :
    F.germ V x hx (F.map (eqToHom e) s) = F.germ U x (op_injective e ▸ hx) s := by
  obtain rfl : U = V := op_injective e
  simp

/-- Along an open immersion, the stalk map carries the germ of the transported section (`invApp`) to
the germ of the section. -/
theorem stalkMap_germ_invApp {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] (V : Opens X) (b : X) (hb : b ∈ V)
    (hb' : f.base b ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj V)
    (s : X.presheaf.obj (op V)) :
    f.stalkMap b (Y.presheaf.germ _ (f.base b) hb'
        (LocallyRingedSpace.IsOpenImmersion.invApp f V s)) =
      X.presheaf.germ V b hb s := by
  rw [LocallyRingedSpace.stalkMap_germ_apply, LocallyRingedSpace.IsOpenImmersion.invApp_app_apply]
  exact germ_map_eqToHom _ _ _ _ _

/-- The glued stalk ideals have local generators: a piece's generators near the representative,
carried to the glued space through the open immersion's `invApp`, generate at every point of the
image neighbourhood (`stalkMap_germ_invApp`; the stalk map is bijective). -/
theorem hasLocalGenerators_gluedStalkIdeal (C : ∀ i, ClosedSubspace (R i))
    (hc : G.CompatClosedSubspaces C) :
    IdealSheaf.HasLocalGenerators (𝒪 := G.gluedOver.toLocallyRingedSpace.𝒪)
      (G.gluedStalkIdeal C) := by
  intro z
  obtain ⟨i, y, rfl⟩ := G.exists_ιGlued_eq z
  obtain ⟨V, hyV, κ, _, s, hs⟩ := IdealSheaf.hasLocalGenerators_stalkIdeal (C i) y
  refine ⟨(LocallyRingedSpace.IsOpenImmersion.opensFunctor (G.ιGlued i).1).obj V,
    Set.mem_image_of_mem (G.ιGlued i).1.base hyV, κ, inferInstance,
    fun k => LocallyRingedSpace.IsOpenImmersion.invApp (G.ιGlued i).1 V (s k), ?_⟩
  intro b' hb'
  obtain ⟨b, hb, hb_eq⟩ := hb'
  subst hb_eq
  have hbij : Function.Bijective ((G.ιGlued i).1.stalkMap b).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  -- everything below is spelled with `presheaf` (the stalk maps' form), not `𝒪.presheaf`
  have hmap : Ideal.map ((G.ιGlued i).1.stalkMap b).hom (Ideal.span (Set.range fun k =>
      G.gluedOver.toLocallyRingedSpace.presheaf.germ _ ((G.ιGlued i).1.base b)
        (Set.mem_image_of_mem (G.ιGlued i).1.base hb)
        (LocallyRingedSpace.IsOpenImmersion.invApp (G.ιGlued i).1 V (s k)))) =
      Ideal.span (Set.range fun k => (R i).toLocallyRingedSpace.presheaf.germ V b hb (s k)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext k
    exact stalkMap_germ_invApp (G.ιGlued i).1 V b hb _ (s k)
  refine (G.gluedStalkIdeal_toFun_ιGlued C hc i b).trans ?_
  unfold pieceStalkIdeal
  rw [hs b hb]
  change Ideal.comap ((G.ιGlued i).1.stalkMap b).hom
      (Ideal.span (Set.range fun k => (R i).toLocallyRingedSpace.presheaf.germ V b hb (s k))) =
    Ideal.span (Set.range fun k =>
      G.gluedOver.toLocallyRingedSpace.presheaf.germ _ ((G.ιGlued i).1.base b)
        (Set.mem_image_of_mem (G.ιGlued i).1.base hb)
        (LocallyRingedSpace.IsOpenImmersion.invApp (G.ιGlued i).1 V (s k)))
  rw [← hmap, Ideal.comap_map_of_bijective _ hbij]

/-- **The glued closed subspace** of compatible closed subspaces of the pieces. -/
noncomputable def glueClosedSubspace (C : ∀ i, ClosedSubspace (R i))
    (hc : G.CompatClosedSubspaces C) : ClosedSubspace G.gluedOver :=
  IdealSheaf.ofStalks _ (G.gluedStalkIdeal C) (G.hasLocalGenerators_gluedStalkIdeal C hc)

/-- The glued closed subspace pulls back along the open immersion of every piece to the given one.
-/
theorem comap_ιGlued_glueClosedSubspace (C : ∀ i, ClosedSubspace (R i))
    (hc : G.CompatClosedSubspaces C) (i : ι) :
    QuotientSpace.comap (G.ιGlued i).1 (G.glueClosedSubspace C hc) = C i := by
  apply IdealSheaf.ext
  intro y
  have h2 : QuotientSpace.stalkIdeal G.gluedOver.toLocallyRingedSpace (G.glueClosedSubspace C hc)
      ((G.ιGlued i).1.base y) = G.pieceStalkIdeal C i y :=
    (IdealSheaf.stalkIdeal_ofStalks _ _ _).trans (G.gluedStalkIdeal_toFun_ιGlued C hc i y)
  refine (QuotientSpace.stalkIdeal_comap (G.ιGlued i).1 (G.glueClosedSubspace C hc) y).trans ?_
  refine (congrArg (Ideal.map ((G.ιGlued i).1.stalkMap y).hom) h2).trans ?_
  exact Ideal.map_comap_of_surjective _
    ((ConcreteCategory.isIso_iff_bijective ((G.ιGlued i).1.stalkMap y)).mp inferInstance).2 _

/-- The preimage of the glued support under the `i`-th immersion is the `i`-th support. -/
theorem preimage_support_glueClosedSubspace (C : ∀ i, ClosedSubspace (R i))
    (hc : G.CompatClosedSubspaces C) (i : ι) :
    (G.ιGlued i).1.base ⁻¹' (G.glueClosedSubspace C hc).support = (C i).support := by
  have h := congrArg IdealSheaf.support (G.comap_ιGlued_glueClosedSubspace C hc i)
  rwa [QuotientSpace.cosupport_comap] at h

/-- **Uniqueness of descent**: two closed subspaces of the glued space with the same pull-backs to
every piece are equal (the pieces cover, and the stalk maps of the open immersions are
isomorphisms). -/
theorem ext_of_forall_comap_ιGlued_eq {E E' : ClosedSubspace G.gluedOver}
    (h : ∀ i, QuotientSpace.comap (G.ιGlued i).1 E = QuotientSpace.comap (G.ιGlued i).1 E') :
    E = E' := by
  apply IdealSheaf.ext
  intro z
  obtain ⟨i, y, rfl⟩ := G.exists_ιGlued_eq z
  have hbij : Function.Bijective ((G.ιGlued i).1.stalkMap y).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have h1 := congrArg (fun J : IdealSheaf _ => J.stalkIdeal y) (h i)
  rw [QuotientSpace.stalkIdeal_comap, QuotientSpace.stalkIdeal_comap] at h1
  have h2 := congrArg (Ideal.comap ((G.ιGlued i).1.stalkMap y).hom) h1
  simp only [Ideal.comap_map_of_bijective _ hbij] at h2
  exact h2

/-- **Existence and uniqueness of descent**: compatible closed subspaces of the pieces are the
pull-backs of exactly one closed subspace of the glued space. -/
theorem existsUnique_comap_ιGlued_eq (C : ∀ i, ClosedSubspace (R i))
    (hc : G.CompatClosedSubspaces C) :
    ∃! E : ClosedSubspace G.gluedOver, ∀ i, QuotientSpace.comap (G.ιGlued i).1 E = C i :=
  ⟨G.glueClosedSubspace C hc, G.comap_ιGlued_glueClosedSubspace C hc, fun _ hE =>
    G.ext_of_forall_comap_ιGlued_eq fun i =>
      (hE i).trans (G.comap_ιGlued_glueClosedSubspace C hc i).symm⟩

/-- The support of the glued closed subspace is the union of the images of the pieces' supports. -/
theorem support_glueClosedSubspace (C : ∀ i, ClosedSubspace (R i))
    (hc : G.CompatClosedSubspaces C) :
    IdealSheaf.support (G.glueClosedSubspace C hc) =
      ⋃ i, KLocallyRingedSpace.Hom.toFun (G.ιGlued i) '' IdealSheaf.support (C i) := by
  apply Set.eq_of_subset_of_subset
  · intro z hz
    obtain ⟨i, y, rfl⟩ := G.exists_ιGlued_eq z
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ ?_⟩
    have h := G.preimage_support_glueClosedSubspace C hc i
    exact (Set.ext_iff.mp h y).mp hz
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨y, hy, rfl⟩ := hi
    have h := G.preimage_support_glueClosedSubspace C hc i
    exact (Set.ext_iff.mp h y).mpr hy

/-! ### The family layer: labelled families of closed subspaces glue

The hypothesis is the labelled form: a label type `Λ`, per-piece labels `lab i : κ i → Λ`
injective on each piece, and for every label the members carrying it compatible across the
transitions, with the empty subspace `⊤` standing in where a piece has no member with that label
(so a member absent from a neighbouring piece must not meet the overlap: the totality clause, and
the convention on empty members). -/

section Family

variable {Λ : Type u} {κ : ι → Type u}

/-- The unit ideal sheaf (the empty closed subspace) has empty support. -/
theorem support_unitIdeal {Y : AnalyticSpace.{u} K} :
    IdealSheaf.support (⊤ : ClosedSubspace Y) = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x (hx : (⊤ : ClosedSubspace Y).stalkIdeal x ≠ ⊤) =>
    hx (IdealSheaf.stalkIdeal_top x)

open Classical in
/-- The member of the `i`-th family carrying the label `l`; the empty subspace `⊤` when no member of
the piece carries `l`. -/
noncomputable def memberOfLabel (H : ∀ i, κ i → ClosedSubspace (R i)) (lab : ∀ i, κ i → Λ)
    (i : ι) (l : Λ) : ClosedSubspace (R i) :=
  if h : ∃ k, lab i k = l then H i h.choose else ⊤

omit [Countable ι] in
/-- With injective labels, the member of the label `lab i k` is the member `k`. -/
theorem memberOfLabel_lab {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    (hlab : ∀ i, Function.Injective (lab i)) (i : ι) (k : κ i) :
    memberOfLabel H lab i (lab i k) = H i k := by
  have h : ∃ k', lab i k' = lab i k := ⟨k, rfl⟩
  rw [memberOfLabel, dite_eq_left h, hlab i h.choose_spec]

omit [Countable ι] in
/-- A label carried by no member of the piece gives the empty subspace `⊤`. -/
theorem memberOfLabel_of_not_exists {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    {i : ι} {l : Λ} (h : ¬ ∃ k, lab i k = l) : memberOfLabel H lab i l = ⊤ := by
  rw [memberOfLabel, dite_eq_right h]

omit [Countable ι] in
/-- The support of a label's member lies in the piece's total support. -/
theorem support_memberOfLabel_subset (H : ∀ i, κ i → ClosedSubspace (R i)) (lab : ∀ i, κ i → Λ)
    (i : ι) (l : Λ) : (memberOfLabel H lab i l).support ⊆ ⋃ k, (H i k).support := by
  unfold memberOfLabel
  split_ifs with h
  · exact Set.subset_iUnion (fun k => (H i k).support) h.choose
  · rw [support_unitIdeal]
    exact Set.empty_subset _

omit [Countable ι] in
/-- The labels' members have the piece's total support: every member appears at its own label, and
absent labels contribute the empty set. -/
theorem iUnion_support_memberOfLabel {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    (hlab : ∀ i, Function.Injective (lab i)) (i : ι) :
    ⋃ l, (memberOfLabel H lab i l).support = ⋃ k, (H i k).support := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun l => support_memberOfLabel_subset H lab i l
  · refine Set.iUnion_subset fun k => ?_
    have := Set.subset_iUnion (fun l => (memberOfLabel H lab i l).support) (lab i k)
    rwa [memberOfLabel_lab hlab i k] at this

omit [Countable ι] in
/-- A point in the support of a label's member lies in the support of a member carrying that label.
-/
theorem exists_of_mem_support_memberOfLabel {H : ∀ i, κ i → ClosedSubspace (R i)}
    {lab : ∀ i, κ i → Λ} (hlab : ∀ i, Function.Injective (lab i)) {i : ι} {l : Λ} {y : R i}
    (h : y ∈ (memberOfLabel H lab i l).support) : ∃ k, lab i k = l ∧ y ∈ (H i k).support := by
  by_cases hex : ∃ k, lab i k = l
  · obtain ⟨k, rfl⟩ := hex
    exact ⟨k, rfl, by rwa [memberOfLabel_lab hlab i k] at h⟩
  · rw [memberOfLabel_of_not_exists hex, support_unitIdeal] at h
    exact h.elim

/-- **Labelled compatibility of families**: for every label, the members carrying it are compatible
closed subspaces of the pieces (`⊤` where a piece has no member with that label). -/
def LabelledCompat (H : ∀ i, κ i → ClosedSubspace (R i)) (lab : ∀ i, κ i → Λ) : Prop :=
  ∀ l : Λ, G.CompatClosedSubspaces fun i => memberOfLabel H lab i l

/-- **The glued family**, indexed by the labels: the label `l` glues the members carrying it. -/
noncomputable def glueFamily (H : ∀ i, κ i → ClosedSubspace (R i)) (lab : ∀ i, κ i → Λ)
    (hc : G.LabelledCompat H lab) : Λ → ClosedSubspace G.gluedOver :=
  fun l => G.glueClosedSubspace (fun i => memberOfLabel H lab i l) (hc l)

/-- The glued member with label `l` pulls back along `ιGlued i` to the `i`-th piece's member of that
label (`⊤` when the piece has none). -/
theorem comap_ιGlued_glueFamily {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    (hc : G.LabelledCompat H lab) (l : Λ) (i : ι) :
    QuotientSpace.comap (G.ιGlued i).1 (G.glueFamily H lab hc l) = memberOfLabel H lab i l :=
  G.comap_ιGlued_glueClosedSubspace _ (hc l) i

/-- Pulled back to the `i`-th piece, the glued member with label `lab i k` is the member `k`. -/
theorem comap_ιGlued_glueFamily_lab {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    (hlab : ∀ i, Function.Injective (lab i)) (hc : G.LabelledCompat H lab) (i : ι) (k : κ i) :
    QuotientSpace.comap (G.ιGlued i).1 (G.glueFamily H lab hc (lab i k)) = H i k := by
  rw [G.comap_ιGlued_glueFamily hc, memberOfLabel_lab hlab]

/-- The preimage under `ιGlued i` of a glued member's support is the support of the piece's member
of that label. -/
theorem preimage_support_glueFamily {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    (hc : G.LabelledCompat H lab) (l : Λ) (i : ι) :
    (G.ιGlued i).1.base ⁻¹' (G.glueFamily H lab hc l).support =
      (memberOfLabel H lab i l).support :=
  G.preimage_support_glueClosedSubspace _ (hc l) i

/-- The support of a glued member is the union of the images of the pieces' members of that label.
-/
theorem support_glueFamily {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    (hc : G.LabelledCompat H lab) (l : Λ) :
    (G.glueFamily H lab hc l).support =
      ⋃ i, KLocallyRingedSpace.Hom.toFun (G.ιGlued i) '' (memberOfLabel H lab i l).support :=
  G.support_glueClosedSubspace _ (hc l)

/-- The total support of the glued family is the union of the images of the pieces' total supports.
-/
theorem iUnion_support_glueFamily {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    (hlab : ∀ i, Function.Injective (lab i)) (hc : G.LabelledCompat H lab) :
    ⋃ l, (G.glueFamily H lab hc l).support =
      ⋃ i, KLocallyRingedSpace.Hom.toFun (G.ιGlued i) '' ⋃ k, (H i k).support := by
  simp only [G.support_glueFamily hc]
  rw [Set.iUnion_comm]
  refine Set.iUnion_congr fun i => ?_
  rw [← Set.image_iUnion, iUnion_support_memberOfLabel hlab i]

/-- Local finiteness of the glued family, from local finiteness on every piece. -/
theorem locallyFinite_glueFamily {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    (hlab : ∀ i, Function.Injective (lab i)) (hc : G.LabelledCompat H lab)
    (hfin : ∀ i, LocallyFinite fun k => (H i k).support) :
    LocallyFinite fun l => (G.glueFamily H lab hc l).support := by
  intro z
  obtain ⟨i, y, rfl⟩ := G.exists_ιGlued_eq z
  obtain ⟨t, ht, hfin_t⟩ := hfin i y
  have hopen : IsOpenMap (G.ιGlued i).1.base :=
    (inferInstance : LocallyRingedSpace.IsOpenImmersion (G.ιGlued i).1).base_open.isOpenMap
  refine ⟨(G.ιGlued i).1.base '' t, hopen.image_mem_nhds ht, ?_⟩
  refine (hfin_t.image (lab i)).subset ?_
  rintro l ⟨z', hz', y', hy't, rfl⟩
  have hy' : y' ∈ (memberOfLabel H lab i l).support := by
    rw [← G.preimage_support_glueFamily hc l i]
    exact hz'
  obtain ⟨k, rfl, hk⟩ := exists_of_mem_support_memberOfLabel hlab hy'
  exact ⟨k, ⟨y', hk, hy't⟩, rfl⟩

/-- **Simple normal crossings glue** ([Kol07, Definition 24], the local form of the divisor with
simple normal crossings; `ClosedSubspace.IsSncFamily`): the glued family of labelled
simple-normal-crossings families is one: the stalk data at a glued point are the piece's, carried
through the stalk isomorphism of the open immersion; the glued members through the point are the
piece's members through its representative, matched by the labels. -/
theorem isSncFamily_glueFamily {H : ∀ i, κ i → ClosedSubspace (R i)} {lab : ∀ i, κ i → Λ}
    (hlab : ∀ i, Function.Injective (lab i)) (hc : G.LabelledCompat H lab)
    (hsnc : ∀ i, ClosedSubspace.IsSncFamily (H i)) :
    ClosedSubspace.IsSncFamily (G.glueFamily H lab hc) := by
  refine ⟨G.locallyFinite_glueFamily hlab hc fun i => (hsnc i).1, fun z => ?_⟩
  obtain ⟨i, y, rfl⟩ := G.exists_ιGlued_eq z
  obtain ⟨n, w, ⟨hspan, hdim⟩, c, hcinj, hcz⟩ := (hsnc i).2 y
  -- the stalk ring isomorphism along the open immersion
  have hbij : Function.Bijective ((G.ιGlued i).1.stalkMap y).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  -- spelled at the point `Hom.toFun (ιGlued i) y` (the goal's), not `(ιGlued i).1.base y`
  let e : G.gluedOver.presheaf.stalk (KLocallyRingedSpace.Hom.toFun (G.ιGlued i) y) ≃+*
      (R i).presheaf.stalk y :=
    RingEquiv.ofBijective ((G.ιGlued i).1.stalkMap y).hom hbij
  have hce : ∀ I : Ideal ((R i).presheaf.stalk y),
      Ideal.comap ((G.ιGlued i).1.stalkMap y).hom I = Ideal.comap e I :=
    fun _ => Ideal.ext fun _ => Iff.rfl
  -- the members through the glued point are the members through `y`, matched by the labels
  let φ : {l // KLocallyRingedSpace.Hom.toFun (G.ιGlued i) y ∈ (G.glueFamily H lab hc l).support} →
      {k // y ∈ (H i k).support} := fun l =>
    ⟨(exists_of_mem_support_memberOfLabel hlab
        ((Set.ext_iff.mp (G.preimage_support_glueFamily hc l.1 i) y).mp l.2)).choose,
      (exists_of_mem_support_memberOfLabel hlab
        ((Set.ext_iff.mp (G.preimage_support_glueFamily hc l.1 i) y).mp l.2)).choose_spec.2⟩
  have hφ : ∀ l, lab i (φ l).1 = l.1 := fun l =>
    (exists_of_mem_support_memberOfLabel hlab
        ((Set.ext_iff.mp (G.preimage_support_glueFamily hc l.1 i) y).mp l.2)).choose_spec.1
  have hφinj : Function.Injective φ := fun l l' h => by
    apply Subtype.ext
    rw [← hφ l, ← hφ l', h]
  refine ⟨n, fun m => e.symm (w m), ⟨?_, ?_⟩, fun l => c (φ l), hcinj.comp hφinj, fun l => ?_⟩
  · -- the parameters span the maximal ideal
    have hr : Set.range (fun m => e.symm (w m)) = e.symm '' Set.range w := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← Ideal.map_span, hspan, IsLocalRing.map_ringEquiv_maximalIdeal]
  · -- the Krull dimension is the piece's
    exact hdim.trans (ringKrullDim_eq_of_ringEquiv e).symm
  · -- the stalk ideal of the glued member through the point
    have hm : memberOfLabel H lab i l.1 = H i (φ l).1 := by
      rw [← hφ l, memberOfLabel_lab hlab]
    -- the descent pattern: `ofStalks` read at the point, then the representative
    have h1 : QuotientSpace.stalkIdeal G.gluedOver.toLocallyRingedSpace
        (G.glueClosedSubspace (fun i => memberOfLabel H lab i l.1) (hc l.1))
        (KLocallyRingedSpace.Hom.toFun (G.ιGlued i) y) =
        G.pieceStalkIdeal (fun i => memberOfLabel H lab i l.1) i y :=
      (IdealSheaf.stalkIdeal_ofStalks _ _ _).trans (G.gluedStalkIdeal_toFun_ιGlued _ (hc l.1) i y)
    have e2 : G.pieceStalkIdeal (fun i => memberOfLabel H lab i l.1) i y =
        Ideal.comap ((G.ιGlued i).1.stalkMap y).hom ((H i (φ l).1).stalkIdeal y) := by
      unfold pieceStalkIdeal
      dsimp only
      exact congrArg (Ideal.comap _) (congrArg (fun J : ClosedSubspace (R i) => J.stalkIdeal y) hm)
    have h2 : Ideal.comap ((G.ιGlued i).1.stalkMap y).hom ((H i (φ l).1).stalkIdeal y) =
        Ideal.span {e.symm (w (c (φ l)))} := by
      rw [hcz (φ l)]
      refine (hce _).trans ?_
      rw [← Ideal.map_symm e, Ideal.map_span, Set.image_singleton]
    exact h1.trans (e2.trans h2)

end Family

end AnalyticSpace.GlueOver
