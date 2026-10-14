/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.QuotientMap
public import Hironaka.AnalyticSpace.Model
import Hironaka.AnalyticSpace.ModelSupport
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Open subspaces of local models are local models

Hironaka defines an analytic `K`-space by asking that every point have a neighbourhood
`K`-isomorphic to a local analytic `K`-space `(S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})` [Hir64, Ch. 0, §1].
`Hironaka/AnalyticSpace/Defs.lean` states that clause **up to an open of the model** —
`X|U ≅ (S(𝓘), …)|W` for an open `W` of the model — because that form makes open subspaces
analytic by a formal argument. The two forms define the same class of spaces provided an open
subspace of a local model is again a local model: for an open `W ⊆ S(𝓘)` there is an open
`G' ⊆ G` with `W = S(𝓘) ∩ G'` and `(S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})|W ≅ (S(𝓘'), (𝒜_{G'}/𝓘')|_{S(𝓘')})`,
`𝓘' = (f₁|_{G'}, …, f_k|_{G'})`. Hironaka uses this implicitly; it is proved here as
`localModel_restrictOpen_iso`.

**The argument.** An open `W` of the support `S(𝓘)` is the trace of an open `O` of `G`
(`exists_opens_eq_preimage`), and an open `O` of `G` is the trace of an open `G' ≤ G` of `Kⁿ`
(`exists_opens_le_eq_trace`). Restriction to `O` commutes with the quotient
(`restrictOpen_quotient_iso` of `Hironaka/AnalyticSpace/QuotientMap.lean`), so
`(S(𝓘), …)|W ≅ ((G, 𝒜_G)|O) / (𝓘|O)`. The open subspace `(G, 𝒜_G)|O` and `(G', 𝒜_{G'})` are two
open immersions into `(Kⁿ, 𝒜)` with the same image `G'`, hence `K`-isomorphic (`traceIso`,
`isoOfRangeEq`), and the quotient is transported along that isomorphism (`quotient_kIso`). What
remains is to identify the transported ideal sheaf with `𝓘' = (f₁|_{G'}, …)`
(`transportIdeal_restrictIdeal_modelIdeal`). Every stalk of a model ideal is the image, under the
stalk map of the open immersion into `(Kⁿ, 𝒜)`, of the ideal `(germ f₁, …, germ f_k)` of the
**ambient** stalk `𝒜_{Kⁿ,p}` (`ambientIdeal`, `stalkIdeal_modelIdeal_eq_map`; the germ of `f` as a
global section of `𝒜_G` is the image of its ambient germ, `stalkMap_ofRestrict_germ`, by
`restrictStalkIso_germ_toGlobal`), and pulling back along a `K`-morphism `φ` into `(G, 𝒜_G)`
composes those stalk maps (`stalkIdeal_comap_modelIdeal`). Since the inclusion
`(G', 𝒜_{G'}) ⟶ (G, 𝒜_G)` through the trace, followed by the open immersion of `G`, *is* the open
immersion of `G'` (`traceIncl_comp_ofRestrict`), the pulled-back stalk is the image of the
ambient ideal under the stalk map of `(G', 𝒜_{G'}) ⟶ (Kⁿ, 𝒜)`, and the ambient ideals of `f` and
of `f|_{G'}` agree because germs are insensitive to restriction (`germ_res_apply`). The point-set
clause `W = S(𝓘) ∩ G'` reads both sides as `{p ∈ G' | f₁(p) = ⋯ = f_k(p) = 0}` through
`mem_range_localModel_ι_iff` and `mem_cosupport_modelIdeal_iff` (`range_restrict_localModel_ι`).

The route through the ambient stalk avoids comparing stalk isomorphisms at two spellings of the
same point of `Kⁿ`: the morphism identity `traceIncl ≫ ofRestrict G = ofRestrict G'` is rewritten
in a statement about the composite morphism as a whole.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold Topology

universe u

namespace AnalyticSpace

variable (K : Type) [RCLike K] (n : ℕ)

open KLocallyRingedSpace

/-- An open of `(G, 𝒜_G)` is the trace of an open `G₁ ≤ G` of `Kⁿ`. -/
theorem exists_opens_le_eq_trace (G : Opens (Kn.{u} K n)) (O : Opens (analyticSpaceOfOpen K n G)) :
    ∃ G' : Opens (Kn.{u} K n), G' ≤ G ∧ ∀ p : analyticSpaceOfOpen K n G, p ∈ O ↔ p.1 ∈ G' := by
  obtain ⟨t, ht, hO⟩ := isOpen_induced_iff.mp O.2
  refine ⟨⟨t, ht⟩ ⊓ G, inf_le_right, fun p => ?_⟩
  have hO' : (O : Set (analyticSpaceOfOpen K n G)) = Subtype.val ⁻¹' t := hO.symm
  constructor
  · intro hp
    have hp' : p ∈ (O : Set (analyticSpaceOfOpen K n G)) := hp
    rw [hO'] at hp'
    exact ⟨hp', p.2⟩
  · intro hp
    change p ∈ (O : Set (analyticSpaceOfOpen K n G))
    rw [hO']
    exact hp.1

end AnalyticSpace

namespace AnalyticSpace

variable (K : Type) [RCLike K] (n : ℕ)

open KLocallyRingedSpace QuotientSpace

section W

variable (G : Opens (Kn.{u} K n)) {G' : Opens (Kn.{u} K n)} (hG : G' ≤ G)
  (O : Opens (analyticSpaceOfOpen K n G)) (hO : ∀ p : analyticSpaceOfOpen K n G, p ∈ O ↔ p.1 ∈ G')
include hG hO

/-- The open immersion `(G, 𝒜_G)|O ⟶ (Kⁿ, 𝒜)` and the open immersion of `(G', 𝒜_{G'})` have the same
image `G'`. -/
theorem range_ofRestrict_ofRestrict_eq :
    Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict (analyticSpaceOfOpen K n G) O ≫ ofRestrict
        (affine K n) G)) =
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict (affine K n) G')) := by
  rw [Hom.range_toFun_comp, range_toFun_ofRestrict, range_toFun_ofRestrict]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (hO q).mp hq
  · intro hp
    exact ⟨⟨p, hG hp⟩, (hO ⟨p, hG hp⟩).mpr hp, rfl⟩

/-- The `K`-isomorphism `(G, 𝒜_G)|O ≅ (G', 𝒜_{G'})` for an open `O` of `G` with trace `G'`. -/
def traceIso : (analyticSpaceOfOpen K n G).restrictOpen O ≅ analyticSpaceOfOpen K n G' :=
  have : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (analyticSpaceOfOpen K n G) O ≫ ofRestrict (affine K n) G).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      ((ofRestrict (analyticSpaceOfOpen K n G) O).1 ≫ (ofRestrict (affine K n) G).1))
  isoOfRangeEq (ofRestrict (analyticSpaceOfOpen K n G) O ≫ ofRestrict (affine K n) G)
    (ofRestrict (affine K n) G') (range_ofRestrict_ofRestrict_eq K n G hG O hO)

/-- The inclusion `(G', 𝒜_{G'}) ⟶ (G, 𝒜_G)` through the trace. -/
def traceIncl : analyticSpaceOfOpen K n G' ⟶ analyticSpaceOfOpen K n G :=
  (traceIso K n G hG O hO).inv ≫ ofRestrict (analyticSpaceOfOpen K n G) O

theorem traceIncl_comp_ofRestrict :
    traceIncl K n G hG O hO ≫ ofRestrict (affine K n) G = ofRestrict (affine K n) G' := by
  apply Hom.ext
  change ((traceIso K n G hG O hO).inv ≫ ofRestrict (analyticSpaceOfOpen K n G) O ≫
    ofRestrict (affine K n) G).1 = _
  rw [Hom.comp_val]
  have : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (analyticSpaceOfOpen K n G) O ≫ ofRestrict (affine K n) G).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      ((ofRestrict (analyticSpaceOfOpen K n G) O).1 ≫ (ofRestrict (affine K n) G).1))
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _
    (le_of_eq (range_ofRestrict_ofRestrict_eq K n G hG O hO).symm)

theorem traceIncl_base_apply (p : analyticSpaceOfOpen K n G') :
    ((traceIncl K n G hG O hO).1.base p).1 = p.1 := by
  have h := congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ p)
      (traceIncl_comp_ofRestrict K n G hG O hO)
  exact h

end W

section Ambient

variable (G : Opens (Kn.{u} K n)) {k : ℕ} (f : Fin k → AnalyticFun K n G)

open Classical in
/-- The ideal generated by the germs of the `f_i` at a point of `Kⁿ`, read in the stalk of `𝒜_{Kⁿ}`
(the unit ideal off `G`). -/
noncomputable def ambientIdeal (x : Kn.{u} K n) :
    Ideal ((affine K n).toLocallyRingedSpace.presheaf.stalk x) :=
  if h : x ∈ G then
    Ideal.span (Set.range fun i => (affine K n).toLocallyRingedSpace.presheaf.germ G x h (f i))
  else ⊤

theorem ambientIdeal_of_mem {x : Kn.{u} K n} (h : x ∈ G) :
    ambientIdeal K n G f x =
      Ideal.span (Set.range fun i => (affine K n).toLocallyRingedSpace.presheaf.germ G x h (f i)) :=
  dite_eq_left h

/-- The stalk map of `(G, 𝒜_G) ⟶ (Kⁿ, 𝒜)` carries the ambient germ of `g` to the germ of `g` as a
global section of `𝒜_G`. -/
theorem stalkMap_ofRestrict_germ (q : analyticSpaceOfOpen K n G) (g : AnalyticFun K n G) :
    ((ofRestrict (affine K n) G).1.stalkMap q).hom
        ((affine K n).toLocallyRingedSpace.presheaf.germ G q.1 q.2 g) =
      (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ ⊤ q (Opens.mem_top q)
        (toGlobal K n G g) := by
  have h1 : (ofRestrict (affine K n) G).1.stalkMap q =
      ((affine K n).toLocallyRingedSpace.restrictStalkIso
        (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G) q).inv :=
    (LocallyRingedSpace.restrictStalkIso_inv_eq_ofRestrict _ _ _).symm
  rw [h1, ← restrictStalkIso_germ_toGlobal K n G q g]
  exact Iso.hom_inv_id_apply _ _

/-- The stalk ideal of a local model is the image of the ambient ideal. -/
theorem stalkIdeal_modelIdeal_eq_map (q : analyticSpaceOfOpen K n G) :
    stalkIdeal (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f) q =
      Ideal.map ((ofRestrict (affine K n) G).1.stalkMap q).hom (ambientIdeal K n G f q.1) := by
  have h1 : stalkIdeal (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f) q =
      Ideal.span (Set.range fun i =>
        (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ ⊤ q (Opens.mem_top _)
          (toGlobal K n G (f i))) :=
    IdealSheaf.stalkIdeal_ofGlobal _ _ _
  have h2 : ambientIdeal K n G f q.1 = Ideal.span (Set.range fun i =>
      (affine K n).toLocallyRingedSpace.presheaf.germ G q.1 q.2 (f i)) :=
    ambientIdeal_of_mem K n G f q.2
  have h3 : Ideal.map ((ofRestrict (affine K n) G).1.stalkMap q).hom
      (Ideal.span (Set.range fun i =>
        (affine K n).toLocallyRingedSpace.presheaf.germ G q.1 q.2 (f i))) =
      Ideal.span (Set.range fun i =>
        (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ ⊤ q (Opens.mem_top _)
          (toGlobal K n G (f i))) := by
    erw [Ideal.map_span, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext fun i =>
      stalkMap_ofRestrict_germ K n G q (f i)))
  exact h1.trans (h3.symm.trans (congrArg _ h2.symm))

/-- The pull-back of the model ideal along a `K`-morphism into `(G, 𝒜_G)`, through the composite
with the open immersion into `(Kⁿ, 𝒜)`. -/
theorem stalkIdeal_comap_modelIdeal {Y : KLocallyRingedSpace.{u} K}
    (φ : Y ⟶ analyticSpaceOfOpen K n G) (p : Y) :
    (comap φ.1 (modelIdeal K n G f)).stalkIdeal p =
      Ideal.map ((φ ≫ ofRestrict (affine K n) G).1.stalkMap p).hom
        (ambientIdeal K n G f ((φ ≫ ofRestrict (affine K n) G).1.base p)) := by
  rw [stalkIdeal_comap, stalkIdeal_modelIdeal_eq_map]
  erw [Ideal.map_map]
  change _ = Ideal.map ((φ.1 ≫ (ofRestrict (affine K n) G).1).stalkMap p).hom
    (ambientIdeal K n G f ((φ.1 ≫ (ofRestrict (affine K n) G).1).base p))
  rw [LocallyRingedSpace.stalkMap_comp]
  rfl

end Ambient

section W

variable (G : Opens (Kn.{u} K n)) {G' : Opens (Kn.{u} K n)} (hG : G' ≤ G)
  (O : Opens (analyticSpaceOfOpen K n G)) (hO : ∀ p : analyticSpaceOfOpen K n G, p ∈ O ↔ p.1 ∈ G')
include hG hO

/-- The ideal sheaf of a local model, restricted to `O` and transported along the trace isomorphism,
is the ideal sheaf of the restricted equations: `𝓘|_{G'} = (f₁|_{G'}, …, f_k|_{G'})`. -/
theorem transportIdeal_restrictIdeal_modelIdeal {k : ℕ} (f : Fin k → AnalyticFun K n G) :
    transportIdeal (traceIso K n G hG O hO).symm
        (restrictIdeal (analyticSpaceOfOpen K n G) (modelIdeal K n G f) O) =
      modelIdeal K n G' fun i =>
        (affine K n).toLocallyRingedSpace.presheaf.map (homOfLE hG).op (f i) := by
  change comap (traceIso K n G hG O hO).inv.1
    (comap (ofRestrict (analyticSpaceOfOpen K n G) O).1 (modelIdeal K n G f)) = _
  rw [← comap_comp]
  change comap (traceIncl K n G hG O hO).1 (modelIdeal K n G f) = _
  apply IdealSheaf.ext
  intro p
  rw [stalkIdeal_comap_modelIdeal, traceIncl_comp_ofRestrict]
  have h2 : stalkIdeal (analyticSpaceOfOpen K n G').toLocallyRingedSpace
      (modelIdeal K n G' fun i =>
        (affine K n).toLocallyRingedSpace.presheaf.map (homOfLE hG).op (f i)) p =
      Ideal.map ((ofRestrict (affine K n) G').1.stalkMap p).hom
        (ambientIdeal K n G' (fun i =>
          (affine K n).toLocallyRingedSpace.presheaf.map (homOfLE hG).op (f i)) p.1) :=
    stalkIdeal_modelIdeal_eq_map K n G' _ p
  change _ = stalkIdeal (analyticSpaceOfOpen K n G').toLocallyRingedSpace
    (modelIdeal K n G' fun i =>
      (affine K n).toLocallyRingedSpace.presheaf.map (homOfLE hG).op (f i)) p
  rw [h2]
  congr 1
  change ambientIdeal K n G f p.1 = _
  rw [ambientIdeal_of_mem K n G f (hG p.2), ambientIdeal_of_mem K n G' _ p.2]
  exact congrArg Ideal.span (congrArg Set.range (funext fun i =>
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm))

end W

end AnalyticSpace

namespace AnalyticSpace

variable (K : Type) [RCLike K] (n : ℕ)

open KLocallyRingedSpace QuotientSpace

section WRange

variable (G : Opens (Kn.{u} K n)) {G' : Opens (Kn.{u} K n)} (hG : G' ≤ G)
  (O : Opens (analyticSpaceOfOpen K n G)) (hO : ∀ p : analyticSpaceOfOpen K n G, p ∈ O ↔ p.1 ∈ G')
include hG hO

/-- The point set of the open subspace of the model over `O`, and that of the restricted model,
agree in `Kⁿ`: both are `{p ∈ G' | f₁(p) = ⋯ = f_k(p) = 0}`. -/
theorem range_restrict_localModel_ι {k : ℕ} (f : Fin k → AnalyticFun K n G) :
    Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict (localModel K n G f)
        (quotientOpens (analyticSpaceOfOpen K n G) (modelIdeal K n G f) O) ≫
          localModel.ι K n G f)) =
      Set.range (KLocallyRingedSpace.Hom.toFun (localModel.ι K n G' fun i =>
        (affine K n).toLocallyRingedSpace.presheaf.map (homOfLE hG).op (f i))) := by
  ext p
  rw [mem_range_localModel_ι_iff]
  constructor
  · rintro ⟨z, rfl⟩
    have hzO : z.1.1 ∈ O := z.2
    refine ⟨(hO z.1.1).mp hzO, fun i => ?_⟩
    exact (mem_cosupport_modelIdeal_iff K n G f z.1.1).mp z.1.2 i
  · rintro ⟨hp, hf⟩
    have hq : (⟨p, hG hp⟩ : analyticSpaceOfOpen K n G) ∈ (modelIdeal K n G f).support :=
      (mem_cosupport_modelIdeal_iff K n G f ⟨p, hG hp⟩).mpr fun i => hf i
    exact ⟨⟨⟨⟨p, hG hp⟩, hq⟩, (hO _).mpr hp⟩, rfl⟩

end WRange

end AnalyticSpace

namespace AnalyticSpace

variable (K : Type) [RCLike K] (n : ℕ)

open KLocallyRingedSpace QuotientSpace

/-- An open subspace `W` of the local analytic `K`-space `(S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})` is
`K`-isomorphic to the local analytic `K`-space of the restricted equations on an open `G' ≤ G`,
with the same point set in `Kⁿ` [Hir64, Ch. 0, §1]. -/
theorem localModel_restrictOpen_iso (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) (W : Opens (localModel K n G f)) :
    ∃ (G' : Opens (Kn.{u} K n)) (h : G' ≤ G),
      Nonempty (KIso ((localModel K n G f).restrictOpen W)
        (localModel K n G' fun i =>
          (affine K n).toLocallyRingedSpace.presheaf.map (homOfLE h).op (f i))) ∧
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict (localModel K n G f) W ≫ localModel.ι K
          n G f)) =
        Set.range (KLocallyRingedSpace.Hom.toFun (localModel.ι K n G' fun i =>
          (affine K n).toLocallyRingedSpace.presheaf.map (homOfLE h).op (f i))) := by
  obtain ⟨O, hW⟩ := exists_opens_eq_preimage (analyticSpaceOfOpen K n G).toLocallyRingedSpace
    (modelIdeal K n G f) W
  obtain ⟨G', hG, hO⟩ := exists_opens_le_eq_trace K n G O
  have hWO : W = quotientOpens (analyticSpaceOfOpen K n G) (modelIdeal K n G f) O := hW
  subst hWO
  refine ⟨G', hG, ⟨?_⟩, range_restrict_localModel_ι K n G hG O hO f⟩
  have e1 := restrictOpen_quotient_iso (analyticSpaceOfOpen K n G) (modelIdeal K n G f) O
  have e2 := quotient_kIso (traceIso K n G hG O hO).symm
    (restrictIdeal (analyticSpaceOfOpen K n G) (modelIdeal K n G f) O)
  rw [transportIdeal_restrictIdeal_modelIdeal K n G hG O hO f] at e2
  exact (e2 ≪≫ e1).symm

end AnalyticSpace
