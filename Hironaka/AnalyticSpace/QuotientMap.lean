/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace
public import Hironaka.AnalyticSpace.Quotient.Defs
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Functoriality of the quotient by an ideal sheaf

The closed subspace `(S(𝒥), (𝒪_X/𝒥)|_{S(𝒥)})` (`QuotientSpace.quotientSpace`) is a
construction on a locally ringed space `X` and an ideal sheaf `𝒥`. This file makes it functorial
and draws two consequences: restriction to an open subset commutes with the quotient (Hironaka's
`(S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})` restricted to an open `G' ⊆ G` is the local model of `G'`
[Hir64, Ch. 0, §1]), and the quotient is transported along a `K`-isomorphism of the ambient
spaces. Both are what one expects, and both are theorems about the germ-family construction
rather than definitions, which is why they live here.

**The morphism.** Let `φ : X' ⟶ X` be a morphism of locally ringed spaces and `𝒥'`, `𝒥` ideal
sheaves on `X'`, `X` such that every stalk map `φ_{z'}^♯ : 𝒪_{X,φ z'} → 𝒪_{X',z'}` carries
`𝒥_{φ z'}` into `𝒥'_{z'}` (`Compat`). Then `φ` restricts to the supports (`mapBase`; a point where
`𝒥_{φ z'}` is the unit ideal has `𝒥'_{z'}` the unit ideal), induces ring homomorphisms of the
fibres `𝒪_{X,φ z'}/𝒥_{φ z'} → 𝒪_{X',z'}/𝒥'_{z'}` (`fiberMap`, Mathlib's `Ideal.quotientMap`), and
carries a compatible germ family over an open `V` of `S(𝒥)` to a compatible germ family over the
preimage of `V` (`mapFamily`): if the family is locally the classes of one ambient section `a`
over `W ⊆ X`, the image is locally the classes of `φ^♯ a` over `φ⁻¹ W`, because stalk maps carry
the germ of `a` to the germ of `φ^♯ a` (Mathlib's `stalkMap_germ_apply`). This is a morphism of
presheafed spaces (`mapHom`) whose stalk maps are the fibre maps up to the identification
`𝒪_{Z,z} ≅ 𝒪_{X,z}/𝒥_z` (`evalHom_mapHom_stalkMap`); the fibre maps are local, so `map` is a
morphism of locally ringed spaces, and it commutes with the canonical morphisms to `X'` and `X`
(`map_comp_ι`). For `K`-morphisms the same square gives a `K`-morphism of the `K`-quotients
(`KLocallyRingedSpace.quotientMap`).

**Pull-back of an ideal sheaf.** For any `φ`, the family `z' ↦ φ_{z'}^♯(𝒥_{φ z'})` has local
generators (the pull-backs of local generators of `𝒥`), so it is an ideal sheaf `comap φ 𝒥` on
`X'`, compatible with `𝒥` by construction; its support is the preimage of the support (a local
homomorphism carries the unit ideal only to the unit ideal). When the stalk maps of `φ` are
isomorphisms the fibre maps are bijective, hence the stalk maps of `map` are isomorphisms; when
moreover `φ` is an open embedding on points, so is the map of supports, and Mathlib's
`IsOpenImmersion.of_stalk_iso` makes `map` an open immersion (`isOpenImmersion_map_comap`).

**The consequences.** For an open `U ⊆ X` the open immersion `X|U ⟶ X` has isomorphic stalks, so
`(X|U)/(𝒥|U) ⟶ X/𝒥` is an open immersion with image the part of `S(𝒥)` over `U`; two open
immersions with the same image are isomorphic (`isoOfRangeEq`), which is
`restrictOpen_quotient_iso`. A `K`-isomorphism `e : X' ≅ X` is an open immersion with isomorphic
stalks and every point of `S(𝒥)` is hit, so `X'/e⁻¹𝒥 ≅ X/𝒥` (`quotient_kIso`). The last section
prepares a third consequence, that the quotient of `X/𝒥` by an ideal sheaf `𝒥'` is the quotient
of `X` by the lifted ideal sheaf (the preimage of `𝒥'` under the canonical stalk maps): the
lifted stalk family and the kernel of the canonical stalk map are defined here, and the
isomorphism is proved in `Hironaka/AnalyticSpace/QuotientLift.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold Topology

universe u

namespace AnalyticSpace.QuotientSpace

variable {X' X : LocallyRingedSpace.{u}} (φ : X' ⟶ X) (J' : IdealSheaf X'.𝒪) (J : IdealSheaf X.𝒪)

/-- Compatibility of the ideal sheaves with the morphism: the stalk map carries `𝒥_{φ z'}` into
`𝒥'_{z'}`. -/
def Compat : Prop :=
  ∀ z' : X', (stalkIdeal X J (φ.base z')).map (φ.stalkMap z').hom ≤ stalkIdeal X' J' z'

variable (h : Compat φ J' J)
include h

theorem mapBase_mem (z' : support X' J') : φ.base z'.1 ∈ J.support := by
  rw [IdealSheaf.mem_support]
  intro htop
  have h2 := h z'.1
  have h3 : stalkIdeal X J (φ.base z'.1) = ⊤ := htop
  rw [h3, Ideal.map_top] at h2
  exact J'.mem_support.mp z'.2 (top_le_iff.mp h2)

/-- The base map of the induced morphism: `φ` restricted to the supports. -/
def mapBase : support X' J' ⟶ support X J :=
  TopCat.ofHom ⟨fun z' => ⟨φ.base z'.1, mapBase_mem φ J' J h z'⟩,
    (φ.base.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem mapBase_apply (z' : support X' J') : (mapBase φ J' J h z').1 = φ.base z'.1 := rfl

/-- The induced map of fibres `𝒪_{X,φ z'}/𝒥_{φ z'} → 𝒪_{X',z'}/𝒥'_{z'}`. -/
def fiberMap (z' : support X' J') : fiber X J (mapBase φ J' J h z') →+* fiber X' J' z' :=
  Ideal.quotientMap (stalkIdeal X' J' z'.1) (φ.stalkMap z'.1).hom
    (Ideal.map_le_iff_le_comap.mp (h z'.1))

theorem fiberMap_mk (z' : support X' J') (σ : X.presheaf.stalk (mapBase φ J' J h z').1) :
    fiberMap φ J' J h z' (Ideal.Quotient.mk (stalkIdeal X J (mapBase φ J' J h z').1) σ) =
      Ideal.Quotient.mk (stalkIdeal X' J' z'.1) ((φ.stalkMap z'.1).hom σ) :=
  Ideal.quotientMap_mk

instance isLocalHom_fiberMap (z' : support X' J') : IsLocalHom (fiberMap φ J' J h z') where
  map_nonunit a ha := by
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
    rw [← hr] at ha ⊢
    rw [fiberMap_mk] at ha
    have h1 : IsUnit ((φ.stalkMap z'.1).hom r) :=
      (IsLocalHom.of_surjective (Ideal.Quotient.mk (stalkIdeal X' J' z'.1))
        Ideal.Quotient.mk_surjective).map_nonunit _ ha
    have h2 : IsUnit r := (φ.prop z'.1).map_nonunit _ h1
    exact h2.map _

/-- The preimage of an open of the support of `(X, 𝒥)`. -/
abbrev preimageOpens (V : Opens (support X J)) : Opens (support X' J') :=
  (Opens.map (mapBase φ J' J h)).obj V

omit h in
theorem stalkMap_germ_apply'' (W : Opens X) (z' : X') (hz : φ.base z' ∈ W)
    (a : X.presheaf.obj (op W)) :
    (φ.stalkMap z').hom (X.presheaf.germ W (φ.base z') hz a) =
      X'.presheaf.germ ((Opens.map φ.base).obj W) z' hz (φ.c.app (op W) a) :=
  PresheafedSpace.stalkMap_germ_apply φ.toShHom.hom W z' hz a

/-- The induced family is a compatible germ family: locally it is the class family of the
pulled-back section. -/
theorem mapFamily_pred (V : Opens (support X J)) (s : (presheafCommRing X J).obj (op V)) :
    (localPred X' J').pred fun z' : preimageOpens φ J' J h V =>
      fiberMap φ J' J h z'.1 (s.1 ⟨mapBase φ J' J h z'.1, z'.2⟩) := by
  intro z'
  obtain ⟨U₁, hz₁, i₁, W, a, hWa⟩ := s.2 ⟨mapBase φ J' J h z'.1, z'.2⟩
  refine ⟨(Opens.map (mapBase φ J' J h)).obj U₁, hz₁, (Opens.map (mapBase φ J' J h)).map i₁,
    (Opens.map φ.base).obj W, φ.c.app (op W) a, fun w => ?_⟩
  obtain ⟨hw, e⟩ := hWa ⟨mapBase φ J' J h w.1, w.2⟩
  refine ⟨hw, ?_⟩
  have e1 : fiberMap φ J' J h w.1 (s.1 (i₁ ⟨mapBase φ J' J h w.1, w.2⟩)) =
      fiberMap φ J' J h w.1
        (Ideal.Quotient.mk _ (X.presheaf.germ W (φ.base w.1.1) hw a)) := congrArg _ e
  exact e1.trans (congrArg (Ideal.Quotient.mk _) (stalkMap_germ_apply'' φ W w.1.1 hw a))

/-- The family of classes induced by a compatible germ family. -/
def mapFamily (V : Opens (support X J)) (s : (presheafCommRing X J).obj (op V)) :
    (presheafCommRing X' J').obj (op (preimageOpens φ J' J h V)) :=
  ⟨fun z' => fiberMap φ J' J h z'.1 (s.1 ⟨mapBase φ J' J h z'.1, z'.2⟩),
    mapFamily_pred φ J' J h V s⟩

theorem mapFamily_apply (V : Opens (support X J)) (s : (presheafCommRing X J).obj (op V))
    (z' : preimageOpens φ J' J h V) :
    (mapFamily φ J' J h V s).1 z' =
      fiberMap φ J' J h z'.1 (s.1 ⟨mapBase φ J' J h z'.1, z'.2⟩) := rfl

/-- The induced ring homomorphism on sections. -/
def mapSections (V : Opens (support X J)) :
    (presheafCommRing X J).obj (op V) ⟶
      (presheafCommRing X' J').obj (op (preimageOpens φ J' J h V)) :=
  CommRingCat.ofHom
    { toFun := mapFamily φ J' J h V
      map_one' := Subtype.ext (funext fun _ => map_one _)
      map_mul' := fun _ _ => Subtype.ext (funext fun _ => map_mul _ _ _)
      map_zero' := Subtype.ext (funext fun _ => map_zero _)
      map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add _ _ _) }

/-- The induced morphism of presheafed spaces. -/
def mapHom : (quotientSpace X' J').toPresheafedSpace ⟶ (quotientSpace X J).toPresheafedSpace where
  base := mapBase φ J' J h
  c :=
    { app := fun V => mapSections φ J' J h (unop V)
      naturality := fun _ _ _ => rfl }

theorem mapHom_stalkMap_comp_evalHom (z' : support X' J') :
    (mapHom φ J' J h).stalkMap z' ≫ evalHom X' J' z' =
      evalHom X J (mapBase φ J' J h z') ≫ CommRingCat.ofHom (fiberMap φ J' J h z') := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hzU => ?_
  rw [PresheafedSpace.stalkMap_germ_assoc]
  ext s
  have hz : mapBase φ J' J h z' ∈ U := hzU
  have hz' : z' ∈ preimageOpens φ J' J h U := hzU
  change evalHom X' J' z' ((presheafCommRing X' J').germ (preimageOpens φ J' J h U) z' hz'
      (mapSections φ J' J h U s)) =
    fiberMap φ J' J h z' (evalHom X J (mapBase φ J' J h z')
      ((presheafCommRing X J).germ U (mapBase φ J' J h z') hz s))
  rw [evalHom_germ, evalHom_germ]
  rfl

theorem evalHom_mapHom_stalkMap (z' : support X' J')
    (ξ : (quotientSpace X J).presheaf.stalk ((mapHom φ J' J h).base z')) :
    evalHom X' J' z' ((mapHom φ J' J h).stalkMap z' ξ) =
      fiberMap φ J' J h z' (evalHom X J ((mapHom φ J' J h).base z') ξ) :=
  congr_arg (fun f => f ξ) (mapHom_stalkMap_comp_evalHom φ J' J h z')

instance isLocalHom_mapHom_stalkMap (z' : support X' J') :
    IsLocalHom ((mapHom φ J' J h).stalkMap z').hom where
  map_nonunit ξ hξ := by
    have h1 : IsUnit (fiberMap φ J' J h z' (evalHom X J ((mapHom φ J' J h).base z') ξ)) := by
      rw [← evalHom_mapHom_stalkMap]
      exact hξ.map (evalHom X' J' z').hom
    have h2 : IsUnit (evalHom X J ((mapHom φ J' J h).base z') ξ) :=
      (isLocalHom_fiberMap φ J' J h z').map_nonunit _ h1
    have h3 := h2.map (stalkEquiv X J ((mapHom φ J' J h).base z')).symm.toRingHom
    change IsUnit ((stalkEquiv X J _).symm ((stalkEquiv X J _) ξ)) at h3
    rwa [RingEquiv.symm_apply_apply] at h3

/-- Functoriality of the germ-family quotient: the induced morphism of locally ringed spaces. -/
def map : quotientSpace X' J' ⟶ quotientSpace X J :=
  ⟨mapHom φ J' J h, fun z' => isLocalHom_mapHom_stalkMap φ J' J h z'⟩

theorem map_base_apply (z' : support X' J') : ((map φ J' J h).base z').1 = φ.base z'.1 := rfl

end AnalyticSpace.QuotientSpace

namespace AnalyticSpace.QuotientSpace

variable {X' X : LocallyRingedSpace.{u}} (φ : X' ⟶ X) (J' : IdealSheaf X'.𝒪) (J : IdealSheaf X.𝒪)
  (h : Compat φ J' J)
include h

/-- The induced morphism commutes with the canonical morphisms: `map ≫ ι = ι' ≫ φ`. -/
theorem map_comp_ι : map φ J' J h ≫ ι X J = ι X' J' ≫ φ := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.ext _ _ rfl ?_
  refine NatTrans.ext (funext fun U => ?_)
  refine CommRingCat.hom_ext (RingHom.ext fun a => Subtype.ext (funext fun z' => ?_))
  change fiberMap φ J' J h z'.1 (Ideal.Quotient.mk _ (X.presheaf.germ (unop U) _ _ a)) =
    Ideal.Quotient.mk _ (X'.presheaf.germ ((Opens.map φ.base).obj (unop U)) z'.1.1 _ (φ.c.app U a))
  exact congrArg (Ideal.Quotient.mk _) (stalkMap_germ_apply'' φ (unop U) z'.1.1 _ a)

end AnalyticSpace.QuotientSpace

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {X' X : KLocallyRingedSpace.{u} K} (ψ : X' ⟶ X)
  (J' : IdealSheaf X'.toLocallyRingedSpace.𝒪) (J : IdealSheaf X.toLocallyRingedSpace.𝒪)
  (h : QuotientSpace.Compat ψ.1 J' J)

/-- The induced `K`-morphism of quotients. -/
def quotientMap : X'.quotient J' ⟶ X.quotient J :=
  Hom.ofFac (quotientι X' J' ≫ ψ) (quotientι X J) (QuotientSpace.map ψ.1 J' J h)
    (QuotientSpace.map_comp_ι ψ.1 J' J h)

theorem quotientMap_val : (quotientMap ψ J' J h).1 = QuotientSpace.map ψ.1 J' J h := rfl

end AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.QuotientSpace

section Comap

variable {X' X : LocallyRingedSpace.{u}} (φ : X' ⟶ X) (J : IdealSheaf X.𝒪)

/-- The stalks of the pulled-back ideal sheaf have local generators: the pullbacks of local
generators of `J`. -/
theorem hasLocalGenerators_comap :
    IdealSheaf.HasLocalGenerators (𝒪 := X'.𝒪)
      fun z' => (stalkIdeal X J (φ.base z')).map (φ.stalkMap z').hom := by
  intro a
  obtain ⟨U, haU, k, f, -, hgen⟩ := J.exists_generators (φ.base a)
  refine ⟨(Opens.map φ.base).obj U, haU, Fin k, inferInstance, fun i => φ.c.app (op U) (f i),
    fun b hb => ?_⟩
  have hg : stalkIdeal X J (φ.base b) =
      Ideal.span (Set.range fun i => X.presheaf.germ U (φ.base b) hb (f i)) := hgen (φ.base b) hb
  change (stalkIdeal X J (φ.base b)).map (φ.stalkMap b).hom =
    Ideal.span (Set.range fun i =>
      X'.presheaf.germ ((Opens.map φ.base).obj U) b hb (φ.c.app (op U) (f i)))
  rw [hg, Ideal.map_span, ← Set.range_comp]
  exact congrArg Ideal.span
    (congrArg Set.range (funext fun i => stalkMap_germ_apply'' φ U b hb (f i)))

/-- The pulled-back ideal sheaf `φ⁻¹(J)·𝒪_{X'}` along a morphism of locally ringed spaces: the stalk
at `z'` is the ideal generated by the image of `J_{φ z'}` under the stalk map. -/
def comap : IdealSheaf X'.𝒪 :=
  IdealSheaf.ofStalks X'.𝒪 _ (hasLocalGenerators_comap φ J)

theorem stalkIdeal_comap (z' : X') :
    (comap φ J).stalkIdeal z' = (stalkIdeal X J (φ.base z')).map (φ.stalkMap z').hom :=
  IdealSheaf.stalkIdeal_ofStalks _ _ z'

theorem compat_comap : Compat φ (comap φ J) J := fun z' => (stalkIdeal_comap φ J z').ge

/-- The support of the pulled-back ideal sheaf is the preimage of the support. -/
theorem cosupport_comap : (comap φ J).support = φ.base ⁻¹' J.support := by
  ext z'
  rw [IdealSheaf.mem_support, Set.mem_preimage, IdealSheaf.mem_support, stalkIdeal_comap]
  exact not_congr (Ideal.map_eq_top_iff_of_isLocalHom _ _)

/-- Along a stalk isomorphism the induced map of fibres is bijective. -/
theorem fiberMap_comap_bijective (z' : support X' (comap φ J)) [IsIso (φ.stalkMap z'.1)] :
    Function.Bijective (fiberMap φ (comap φ J) J (compat_comap φ J) z') := by
  have hb : Function.Bijective (φ.stalkMap z'.1).hom :=
    (ConcreteCategory.isIso_iff_bijective (φ.stalkMap z'.1)).mp inferInstance
  refine ⟨Ideal.quotientMap_injective' ?_, Ideal.quotientMap_surjective hb.2⟩
  change (stalkIdeal X' (comap φ J) z'.1).comap (φ.stalkMap z'.1).hom ≤ _
  rw [show stalkIdeal X' (comap φ J) z'.1 = (stalkIdeal X J (φ.base z'.1)).map (φ.stalkMap z'.1).hom
    from stalkIdeal_comap φ J z'.1]
  exact (Ideal.comap_map_of_bijective _ hb).le

/-- The stalk maps of the induced morphism are isomorphisms wherever the fibre map is bijective. -/
theorem isIso_map_stalkMap_of_bijective {X' X : LocallyRingedSpace.{u}} (φ : X' ⟶ X)
    (J' : IdealSheaf X'.𝒪) (J : IdealSheaf X.𝒪) (h : Compat φ J' J) (z' : support X' J')
    (hf : Function.Bijective (fiberMap φ J' J h z')) : IsIso ((map φ J' J h).stalkMap z') := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hsq := evalHom_mapHom_stalkMap φ J' J h z'
  have h1 : Function.Bijective (evalHom X' J' z').hom :=
    ⟨evalHom_injective _ _ _, evalHom_surjective _ _ _⟩
  have h2 : Function.Bijective (evalHom X J ((mapHom φ J' J h).base z')).hom :=
    ⟨evalHom_injective _ _ _, evalHom_surjective _ _ _⟩
  constructor
  · intro ξ₁ ξ₂ e
    have e1 : fiberMap φ J' J h z' (evalHom X J _ ξ₁) = fiberMap φ J' J h z' (evalHom X J _ ξ₂) :=
      (hsq ξ₁).symm.trans ((congrArg (evalHom X' J' z') e).trans (hsq ξ₂))
    exact h2.1 (hf.1 e1)
  · intro η
    obtain ⟨x, hx⟩ := hf.2 (evalHom X' J' z' η)
    obtain ⟨ξ, rfl⟩ := h2.2 x
    exact ⟨ξ, h1.1 ((hsq ξ).trans hx)⟩

/-- The stalk maps of the induced morphism are isomorphisms when those of `φ` are. -/
theorem isIso_map_stalkMap (z' : support X' (comap φ J)) [IsIso (φ.stalkMap z'.1)] :
    IsIso ((map φ (comap φ J) J (compat_comap φ J)).stalkMap z') :=
  isIso_map_stalkMap_of_bijective φ _ _ _ z' (fiberMap_comap_bijective φ J z')

/-- The base map of the induced morphism along `φ` is an open embedding when `φ.base` is. -/
theorem isOpenEmbedding_mapBase_comap (hφ : IsOpenEmbedding φ.base) :
    IsOpenEmbedding (mapBase φ (comap φ J) J (compat_comap φ J)) := by
  have e : (mapBase φ (comap φ J) J (compat_comap φ J) : support X' (comap φ J) → support X J) =
      J.support.restrictPreimage φ.base ∘ Homeomorph.setCongr (cosupport_comap φ J) := by
    funext z'
    rfl
  rw [e]
  exact (Set.restrictPreimage_isOpenEmbedding _ hφ).comp (Homeomorph.setCongr _).isOpenEmbedding

/-- Functoriality along an open immersion with isomorphic stalks gives an open immersion of the
quotients. -/
theorem isOpenImmersion_map_comap (hφ : IsOpenEmbedding φ.base) [∀ z', IsIso (φ.stalkMap z')] :
    LocallyRingedSpace.IsOpenImmersion (map φ (comap φ J) J (compat_comap φ J)) :=
  have : ∀ z' : support X' (comap φ J),
      IsIso ((map φ (comap φ J) J (compat_comap φ J)).stalkMap z') :=
    fun z' => isIso_map_stalkMap φ J z'
  LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ (isOpenEmbedding_mapBase_comap φ J hφ)

/-- Pull-back of ideal sheaves is functorial. -/
theorem comap_comp {X'' : LocallyRingedSpace.{u}} (φ' : X'' ⟶ X') :
    comap (φ' ≫ φ) J = comap φ' (comap φ J) := by
  apply IdealSheaf.ext
  intro z
  rw [stalkIdeal_comap, stalkIdeal_comap]
  change _ = ((stalkIdeal X' (comap φ J) (φ'.base z)).map (φ'.stalkMap z).hom)
  rw [show stalkIdeal X' (comap φ J) (φ'.base z) =
      (stalkIdeal X J (φ.base (φ'.base z))).map (φ.stalkMap (φ'.base z)).hom from
    stalkIdeal_comap φ J (φ'.base z)]
  rw [Ideal.map_map, LocallyRingedSpace.stalkMap_comp]
  rfl

end Comap

end AnalyticSpace.QuotientSpace

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] (X : KLocallyRingedSpace.{u} K)
  (J : IdealSheaf X.toLocallyRingedSpace.𝒪) (U : Opens X)

/-- The restriction `𝒥|_U` of an ideal sheaf to the open subspace `X | U`: the pull-back along the
open immersion. -/
def restrictIdeal : IdealSheaf (X.restrictOpen U).toLocallyRingedSpace.𝒪 :=
  QuotientSpace.comap (X.ofRestrict U).1 J

/-- The open subset of the quotient `(S(𝒥), 𝒪_X/𝒥)` lying over the open `U` of `X`. -/
def quotientOpens : Opens (X.quotient J) := (Opens.map (quotientι X J).1.base).obj U

instance isIso_ofRestrict_stalkMap (z' : X.restrictOpen U) :
    IsIso ((X.ofRestrict U).1.stalkMap z') :=
  inferInstance

instance isOpenImmersion_quotientMap_ofRestrict :
    LocallyRingedSpace.IsOpenImmersion
      (quotientMap (X.ofRestrict U) (restrictIdeal X J U) J (QuotientSpace.compat_comap _ _)).1 :=
  QuotientSpace.isOpenImmersion_map_comap _ _ (Opens.isOpenEmbedding U)

theorem range_quotientMap_ofRestrict :
    Set.range (Hom.toFun (quotientMap (X.ofRestrict U) (restrictIdeal X J U) J
        (QuotientSpace.compat_comap _ _))) =
      Set.range (Hom.toFun (ofRestrict (X.quotient J) (quotientOpens X J U))) := by
  rw [range_toFun_ofRestrict]
  ext z
  constructor
  · rintro ⟨z', rfl⟩
    exact z'.1.2
  · intro hz
    refine ⟨⟨⟨z.1, hz⟩, ?_⟩, Subtype.ext rfl⟩
    change (⟨z.1, hz⟩ : X.restrictOpen U) ∈ (QuotientSpace.comap (X.ofRestrict U).1 J).support
    rw [QuotientSpace.cosupport_comap]
    exact z.2

/-- Restriction to an open commutes with the quotient: `(X|U) / (𝒥|U) ≅ (X/𝒥) | U'`, `U'` the part
of the support over `U`. -/
def restrictOpen_quotient_iso :
    (X.restrictOpen U).quotient (restrictIdeal X J U) ≅
      (X.quotient J).restrictOpen (quotientOpens X J U) :=
  isoOfRangeEq
    (quotientMap (X.ofRestrict U) (restrictIdeal X J U) J (QuotientSpace.compat_comap _ _))
    (ofRestrict (X.quotient J) (quotientOpens X J U)) (range_quotientMap_ofRestrict X J U)

end AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {X' X : KLocallyRingedSpace.{u} K} (e : KIso X' X)
  (J : IdealSheaf X.toLocallyRingedSpace.𝒪)

/-- The ideal sheaf transported along a `K`-isomorphism of the ambient spaces. -/
def transportIdeal : IdealSheaf X'.toLocallyRingedSpace.𝒪 := QuotientSpace.comap e.hom.1 J

instance isOpenImmersion_quotientMap_kIso :
    LocallyRingedSpace.IsOpenImmersion
      (quotientMap e.hom (transportIdeal e J) J (QuotientSpace.compat_comap _ _)).1 :=
  have : ∀ z', IsIso (e.hom.1.stalkMap z') := fun z' =>
    LocallyRingedSpace.IsOpenImmersion.stalk_iso e.hom.1 z'
  QuotientSpace.isOpenImmersion_map_comap _ _ (KIso.homeomorph e).isOpenEmbedding

theorem range_quotientMap_kIso :
    Set.range (Hom.toFun
        (quotientMap e.hom (transportIdeal e J) J (QuotientSpace.compat_comap _ _))) =
      Set.range (Hom.toFun (𝟙 (X.quotient J))) := by
  rw [Hom.toFun_id, Set.range_id]
  apply Set.eq_univ_of_forall
  intro z
  refine ⟨⟨(KIso.homeomorph e).symm z.1, ?_⟩, Subtype.ext ?_⟩
  · change (KIso.homeomorph e).symm z.1 ∈ (QuotientSpace.comap e.hom.1 J).support
    rw [QuotientSpace.cosupport_comap]
    change e.hom.1.base ((KIso.homeomorph e).symm z.1) ∈ J.support
    have : e.hom.1.base ((KIso.homeomorph e).symm z.1) = z.1 :=
      (KIso.homeomorph e).apply_symm_apply z.1
    rw [this]
    exact z.2
  · exact (KIso.homeomorph e).apply_symm_apply z.1

/-- Transport of the quotient along a `K`-isomorphism of the ambient spaces:
`X' / e⁻¹𝒥 ≅ X / 𝒥`. -/
def quotient_kIso : X'.quotient (transportIdeal e J) ≅ X.quotient J :=
  haveI : LocallyRingedSpace.IsOpenImmersion
      (𝟙 (X.quotient J) : Hom (X.quotient J) (X.quotient J)).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 (X.quotient J).toLocallyRingedSpace))
  isoOfRangeEq (quotientMap e.hom (transportIdeal e J) J (QuotientSpace.compat_comap _ _))
    (𝟙 (X.quotient J)) (range_quotientMap_kIso e J)

end AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.QuotientSpace

section Lift

variable (X : LocallyRingedSpace.{u}) (J : IdealSheaf X.𝒪)

/-- The kernel of the canonical stalk map `𝒪_{X,z} → 𝒪_{Z,z}` is `𝒥_z`. -/
theorem ker_stalkMap_ι (z : support X J) :
    RingHom.ker ((ι X J).stalkMap z).hom = stalkIdeal X J z.1 := by
  ext σ
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← evalHom_stalkMap X J z σ]
  constructor
  · intro h0
    have h1 : (ιHom X J).stalkMap z σ = 0 := h0
    rw [h1, map_zero]
  · intro h0
    exact evalHom_injective X J z (h0.trans (map_zero _).symm)

/-- Every open of the support is the trace of an open of `X`. -/
theorem exists_opens_eq_preimage (V : Opens (support X J)) : ∃ O : Opens X, V = preimage X J O := by
  obtain ⟨t, ht, hV⟩ := isOpen_induced_iff.mp V.2
  exact ⟨⟨t, ht⟩, Opens.ext hV.symm⟩

variable (J' : IdealSheaf (quotientSpace X J).𝒪)

open Classical in
/-- The stalk family of the lifted ideal sheaf: the preimage of `𝒥'_z` under the canonical stalk
map at the points of the support, the unit ideal elsewhere. -/
noncomputable def liftStalk (x : X) : Ideal (X.presheaf.stalk x) :=
  if h : x ∈ J.support then
    (stalkIdeal (quotientSpace X J) J' ⟨x, h⟩).comap ((ι X J).stalkMap ⟨x, h⟩).hom
  else ⊤

theorem liftStalk_of_mem {x : X} (h : x ∈ J.support) :
    liftStalk X J J' x =
      (stalkIdeal (quotientSpace X J) J' ⟨x, h⟩).comap ((ι X J).stalkMap ⟨x, h⟩).hom :=
  dite_eq_left h

theorem liftStalk_of_notMem {x : X} (h : x ∉ J.support) : liftStalk X J J' x = ⊤ := dite_eq_right h

/-- The stalk map of `ι` carries the germ of an ambient section to the germ of its class family. -/
theorem stalkMap_ι_germ (W : Opens X) (z : support X J) (hz : z.1 ∈ W) (a : X.presheaf.obj (op W)) :
    ((ι X J).stalkMap z).hom (X.presheaf.germ W z.1 hz a) =
      (presheafCommRing X J).germ (preimage X J W) z hz (classFamily X J W a) :=
  PresheafedSpace.stalkMap_germ_apply (ι X J).toShHom.hom W z hz a

end Lift

end AnalyticSpace.QuotientSpace
