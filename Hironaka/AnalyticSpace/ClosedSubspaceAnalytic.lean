/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.LocalModelRestrict
import Hironaka.AnalyticSpace.OpenSubspaceLemmas
import Hironaka.AnalyticSpace.QuotientLift
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The local-model clause for a closed subspace of an analytic `K`-space

A closed analytic subspace of an analytic `K`-space is given by a coherent ideal sheaf
[Hir64, Ch. 0, §1]; it is the quotient `(S(𝓘), (𝒪_X/𝓘)|_{S(𝓘)})` [BM97, §3], and its local models
are `V(f₁, …, f_k, g₁, …, g_l)`: the ambient model of `X` cut out further by ambient lifts of local
generators of `𝓘`. This file proves that clause (`quotient_locallyModel`), the local-model field of
the closed subspace as an analytic `K`-space (`closedSubspace`).

**The general identification.** The first section extends the identification of
`Hironaka/AnalyticSpace/LocalModelRestrict.lean` from the model ideal to any finite-type ideal sheaf
`𝒥` on `(G, 𝒜_G)`: if `𝒥` has local generators `g` over an open `O` of `G` whose image in `Kⁿ` is
`G'`, then the restriction of `𝒥` to `O`, transported along the trace isomorphism
`(G, 𝒜_G)|O ≅ (G', 𝒜_{G'})`, is the model ideal of the `g` read as analytic functions on `G'`
(`transportIdeal_restrictIdeal_eq_modelIdeal`; the `g` live on the image of `O`, which is `G'` —
`functor_obj_eq`, `generatorsOn`). The proof is the same ambient-stalk comparison: stalks of `𝒥`
over `O` are images of the ambient ideals of the `g` (`stalkIdeal_eq_map_ambientIdealOf`, by
Mathlib's `restrictStalkIso_inv_eq_germ_apply`), pulling back composes stalk maps
(`stalkIdeal_comap_of_generators`), and the inclusion through the trace followed by the open
immersion of `G` is the open immersion of `G'`.

**The local-model clause** (`quotient_locallyModel`). At a point `y` of `Z = X/𝒥` with image
`x ∈ X`: a chart of `X` at `x`, `X|U ≅ (S(𝓘), …)|W`, is (an open of a local model being a local
model) a chart `X|U ≅ (S(𝓘₁), …) = (G₁, 𝒜_{G₁})/𝓘₁`; restriction commutes with the quotient, so
the open `Z|U'` over `U` is `(X|U)/(𝒥|U)`; transporting along the chart makes it a quotient of
`(G₁, 𝒜_{G₁})/𝓘₁`, hence (a quotient of a quotient) the quotient of `(G₁, 𝒜_{G₁})` by the lifted
ideal sheaf `𝒥̃`, whose local generators near the image point are the `f_i` and the ambient lifts
`g_j`; on the trace open `G₂` of those generators, the general identification makes `Z` over it
the local model `(S(𝓘₂), …)`, `𝓘₂ = (g₁, …, g_l)` on `G₂`. The remaining bookkeeping — an open of
an open is an open (`restrictOpen_restrictOpen_iso`), an isomorphism restricts over an open
(`restrictOpenIso`), `M|⊤ ≅ M` (`restrictOpenTopIso`) — is in
`Hironaka/AnalyticSpace/OpenSubspaceLemmas.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold Topology

universe u

namespace AnalyticSpace

variable (K : Type) [RCLike K] (n : ℕ)

open KLocallyRingedSpace QuotientSpace

section General

variable (G : Opens (Kn.{u} K n)) {G' : Opens (Kn.{u} K n)} (hG : G' ≤ G)
  (O : Opens (analyticSpaceOfOpen K n G)) (hO : ∀ p : analyticSpaceOfOpen K n G, p ∈ O ↔ p.1 ∈ G')
include hG hO

omit hG hO in
/-- The image in `Kⁿ` of an open `O` of `(G, 𝒜_G)`. -/
abbrev imageIn (O : Opens (analyticSpaceOfOpen K n G)) : Opens (Kn.{u} K n) :=
  (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat)
    G).isOpenMap.functor.obj O

/-- The image in `Kⁿ` of the trace open `O` is `G'`. -/
theorem functor_obj_eq :
    imageIn K n G O = G' := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (hO q).mp hq
  · intro hp
    exact ⟨⟨p, hG hp⟩, (hO _).mpr hp, rfl⟩

variable (J : IdealSheaf (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪) {l : ℕ}
  (g : Fin l → (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.obj (op O))
  (hg : ∀ b (hb : b ∈ O), stalkIdeal (analyticSpaceOfOpen K n G).toLocallyRingedSpace J b =
    Ideal.span (Set.range fun i =>
      (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ O b hb (g i)))
include hg

/-- The generators `g`, read as analytic functions on `G'`. -/
def generatorsOn (i : Fin l) : AnalyticFun K n G' :=
  (affine K n).toLocallyRingedSpace.presheaf.map (eqToHom (functor_obj_eq K n G hG O hO).symm).op
    (g i)

omit hG hO hg in
theorem stalkMap_ofRestrict_germ' (q : analyticSpaceOfOpen K n G) (hq : q ∈ O) (i : Fin l) :
    ((ofRestrict (affine K n) G).1.stalkMap q).hom
        ((affine K n).toLocallyRingedSpace.presheaf.germ
          (imageIn K n G O)
          q.1 ⟨q, hq, rfl⟩ (g i)) =
      (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ O q hq (g i) := by
  have h1 : (ofRestrict (affine K n) G).1.stalkMap q =
      ((affine K n).toLocallyRingedSpace.restrictStalkIso
        (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G) q).inv :=
    (LocallyRingedSpace.restrictStalkIso_inv_eq_ofRestrict _ _ _).symm
  rw [h1]
  exact LocallyRingedSpace.restrictStalkIso_inv_eq_germ_apply _ _ _ _ _ _

open Classical in
/-- The ideal generated by the ambient germs of the `g_i` at a point of `Kⁿ` (the unit ideal off the
image of `O`). -/
noncomputable def ambientIdealOf (x : Kn.{u} K n) :
    Ideal ((affine K n).toLocallyRingedSpace.presheaf.stalk x) :=
  if h : x ∈ imageIn K n G O then
    Ideal.span (Set.range fun i => (affine K n).toLocallyRingedSpace.presheaf.germ _ x h (g i))
  else ⊤

omit hG hO hg in
theorem ambientIdealOf_of_mem {x : Kn.{u} K n}
    (h : x ∈ imageIn K n G O) :
    ambientIdealOf K n G O g x =
      Ideal.span (Set.range fun i => (affine K n).toLocallyRingedSpace.presheaf.germ _ x h (g i)) :=
  dite_eq_left h

omit hG hO in
/-- On `O`, the stalks of `J` are the images of the ambient ideals. -/
theorem stalkIdeal_eq_map_ambientIdealOf (q : analyticSpaceOfOpen K n G) (hq : q ∈ O) :
    stalkIdeal (analyticSpaceOfOpen K n G).toLocallyRingedSpace J q =
      Ideal.map ((ofRestrict (affine K n) G).1.stalkMap q).hom
        (ambientIdealOf K n G O g q.1) := by
  have hqi : q.1 ∈ imageIn K n G O := ⟨q, hq, rfl⟩
  have h2 : ambientIdealOf K n G O g q.1 = Ideal.span (Set.range fun i =>
      (affine K n).toLocallyRingedSpace.presheaf.germ _ q.1 hqi (g i)) :=
    ambientIdealOf_of_mem K n G O g hqi
  have h3 : Ideal.map ((ofRestrict (affine K n) G).1.stalkMap q).hom
      (Ideal.span (Set.range fun i =>
        (affine K n).toLocallyRingedSpace.presheaf.germ _ q.1 hqi (g i))) =
      Ideal.span (Set.range fun i =>
        (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ O q hq (g i)) := by
    erw [Ideal.map_span, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext fun i =>
      stalkMap_ofRestrict_germ' K n G O g q hq i))
  exact (hg q hq).trans (h3.symm.trans (congrArg _ h2.symm))

omit hG hO in
/-- The pull-back of `J` along a `K`-morphism into `(G, 𝒜_G)` landing in `O`. -/
theorem stalkIdeal_comap_of_generators {Y : KLocallyRingedSpace.{u} K}
    (φ : Y ⟶ analyticSpaceOfOpen K n G) (hφ : ∀ p : Y, φ.1.base p ∈ O) (p : Y) :
    (comap φ.1 J).stalkIdeal p =
      Ideal.map ((φ ≫ ofRestrict (affine K n) G).1.stalkMap p).hom
        (ambientIdealOf K n G O g ((φ ≫ ofRestrict (affine K n) G).1.base p)) := by
  rw [stalkIdeal_comap, stalkIdeal_eq_map_ambientIdealOf K n G O J g hg _ (hφ p)]
  erw [Ideal.map_map]
  change _ = Ideal.map ((φ.1 ≫ (ofRestrict (affine K n) G).1).stalkMap p).hom
    (ambientIdealOf K n G O g ((φ.1 ≫ (ofRestrict (affine K n) G).1).base p))
  rw [LocallyRingedSpace.stalkMap_comp]
  rfl

omit hg in
theorem traceIncl_base_mem (p : analyticSpaceOfOpen K n G') :
    (traceIncl K n G hG O hO).1.base p ∈ O := by
  change ((traceIso K n G hG O hO).inv ≫ ofRestrict (analyticSpaceOfOpen K n G) O).1.base p ∈ O
  exact ((traceIso K n G hG O hO).inv.1.base p).2

/-- A finite-type ideal sheaf on `(G, 𝒜_G)`, restricted to the trace open `O` of `G'` and
transported along the trace isomorphism, is the model ideal of its local generators read on `G'`. -/
theorem transportIdeal_restrictIdeal_eq_modelIdeal :
    transportIdeal (traceIso K n G hG O hO).symm (restrictIdeal (analyticSpaceOfOpen K n G) J O) =
      modelIdeal K n G' (generatorsOn K n G hG O hO g) := by
  change comap (traceIso K n G hG O hO).inv.1
    (comap (ofRestrict (analyticSpaceOfOpen K n G) O).1 J) = _
  rw [← comap_comp]
  change comap (traceIncl K n G hG O hO).1 J = _
  apply IdealSheaf.ext
  intro p
  rw [stalkIdeal_comap_of_generators K n G O J g hg (traceIncl K n G hG O hO)
    (traceIncl_base_mem K n G hG O hO), traceIncl_comp_ofRestrict]
  have h2 : stalkIdeal (analyticSpaceOfOpen K n G').toLocallyRingedSpace
      (modelIdeal K n G' (generatorsOn K n G hG O hO g)) p =
      Ideal.map ((ofRestrict (affine K n) G').1.stalkMap p).hom
        (ambientIdeal K n G' (generatorsOn K n G hG O hO g) p.1) :=
    stalkIdeal_modelIdeal_eq_map K n G' _ p
  change _ = stalkIdeal (analyticSpaceOfOpen K n G').toLocallyRingedSpace
    (modelIdeal K n G' (generatorsOn K n G hG O hO g)) p
  rw [h2]
  congr 1
  have hpi : p.1 ∈ imageIn K n G O := by
    rw [functor_obj_eq K n G hG O hO]
    exact p.2
  change ambientIdealOf K n G O g p.1 = _
  rw [ambientIdealOf_of_mem K n G O g hpi, ambientIdeal_of_mem K n G' _ p.2]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

end General

end AnalyticSpace


open AnalyticSpace.KLocallyRingedSpace AnalyticSpace.QuotientSpace

namespace AnalyticSpace

variable {K : Type} [RCLike K] (X : AnalyticSpace.{u} K)

/-- The local-model clause for a closed subspace: every point of the quotient of `X` by a
finite-type ideal sheaf has a neighbourhood `K`-isomorphic to (an open of) a local analytic
`K`-space — the model of `X` at the point, cut out further by the ambient lifts of local
generators of the ideal sheaf. -/
theorem quotient_locallyModel (J : IdealSheaf X.toLocallyRingedSpace.𝒪)
    (y : X.toKLocallyRingedSpace.quotient J) :
    ∃ (U : Opens (X.toKLocallyRingedSpace.quotient J)) (_ : y ∈ U) (n k : ℕ)
      (G : Opens (Kn.{u} K n)) (f : Fin k → AnalyticFun K n G) (W : Opens (localModel K n G f)),
      Nonempty (KIso ((X.toKLocallyRingedSpace.quotient J).restrictOpen U)
        ((localModel K n G f).restrictOpen W)) := by
  obtain ⟨U₀, hxU, n, k, G, f, W₀, ⟨e₀⟩⟩ := X.locallyModel y.1
  obtain ⟨G₁, hG₁, ⟨e₁⟩, -⟩ := localModel_restrictOpen_iso K n G f W₀
  let f₁ : Fin k → AnalyticFun K n G₁ := fun i =>
    (affine K n).toLocallyRingedSpace.presheaf.map (homOfLE hG₁).op (f i)
  let e : X.toKLocallyRingedSpace.restrictOpen U₀ ≅ localModel K n G₁ f₁ := e₀ ≪≫ e₁
  have hyU₀' : y ∈ quotientOpens X.toKLocallyRingedSpace J U₀ := hxU
  let J₁ := restrictIdeal X.toKLocallyRingedSpace J U₀
  let J₂ := transportIdeal e.symm J₁
  let Jt := KLocallyRingedSpace.liftIdeal (analyticSpaceOfOpen K n G₁) (modelIdeal K n G₁ f₁) J₂
  let e3 := restrictOpen_quotient_iso X.toKLocallyRingedSpace J U₀
  let e4 := quotient_kIso e.symm J₁
  let e5 := quotient_quotient_iso (analyticSpaceOfOpen K n G₁) (modelIdeal K n G₁ f₁) J₂
  let E : (X.toKLocallyRingedSpace.quotient J).restrictOpen
      (quotientOpens X.toKLocallyRingedSpace J U₀) ≅ (analyticSpaceOfOpen K n G₁).quotient Jt :=
    e3.symm ≪≫ e4.symm ≪≫ e5
  let q : (analyticSpaceOfOpen K n G₁).quotient Jt := E.hom.1.base ⟨y, hyU₀'⟩
  obtain ⟨V, hqV, l, g, -, hg⟩ := Jt.exists_generators q.1
  obtain ⟨G₂, hG₂, hV⟩ := exists_opens_le_eq_trace K n G₁ V
  have hid := transportIdeal_restrictIdeal_eq_modelIdeal K n G₁ hG₂ V hV Jt g hg
  let e7 := restrictOpen_quotient_iso (analyticSpaceOfOpen K n G₁) Jt V
  let e8 := quotient_kIso (traceIso K n G₁ hG₂ V hV).symm
    (restrictIdeal (analyticSpaceOfOpen K n G₁) Jt V)
  rw [hid] at e8
  have hqV' : q ∈ quotientOpens (analyticSpaceOfOpen K n G₁) Jt V := hqV
  let e9 := restrictOpenIso E (quotientOpens (analyticSpaceOfOpen K n G₁) Jt V)
  let e10 := restrictOpen_restrictOpen_iso (quotientOpens X.toKLocallyRingedSpace J U₀)
    ((Opens.map E.hom.1.base).obj (quotientOpens (analyticSpaceOfOpen K n G₁) Jt V))
  refine ⟨imageOpens (quotientOpens X.toKLocallyRingedSpace J U₀)
    ((Opens.map E.hom.1.base).obj (quotientOpens (analyticSpaceOfOpen K n G₁) Jt V)),
    ⟨⟨⟨y, hyU₀'⟩, hqV'⟩, rfl⟩, n, l, G₂, generatorsOn K n G₁ hG₂ V hV g, ⊤, ⟨?_⟩⟩
  exact e10.symm ≪≫ e9 ≪≫ e7.symm ≪≫ e8.symm ≪≫ (restrictOpenTopIso _).symm

end AnalyticSpace
