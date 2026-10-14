/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.ModelTransport.IdealSheaf
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.LocalDiffeomorph
import Hironaka.Manifold.Snc.Bundled
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Transforms along a square of analytic isomorphisms across the models

The notions attached to an analytic map `f : M' → M` in the vocabulary of the main theorems —
Hironaka's weak transform [Hir64, p. 142], the reduced transform `red(f⁻¹(E) ∪ f⁻¹(D))`
[Hir64, Main Theorem II'(N) (iii), p. 156], the isomorphism-over-a-set clause `IsAnalyticIsoOver`
and properness — transport along a square `f ∘ g' = g ∘ f'` of analytic isomorphisms `g : N ≃ M`,
`g' : N' ≃ M'` across the models (`IsModelSquare`,
`Hironaka/Resolution/Analytic/ModelTransport/IdealSheaf.lean`): `f'` is `g⁻¹ ∘ f ∘ g'`, the same map
read on the re-modelled manifolds. For the main theorems the squares are the identities of
`Hironaka/Resolution/Analytic/ModelTransport/Manifold.lean` at the stages of a transported
succession (`Succession.lean`) and at the space of a transported family (`Family.lean`).

* The weak transform: both sides are the unique ideal sheaf with the colon stalks
  `(f⁻¹(J)_{a'} : f⁻¹(D)_{a'}^{ν})` (`IsDivExceptional.unique`); the colon data correspond under the
  stalk isomorphism of `g'` (`Ideal.map_colon_pow_of_bijective`), the exponent — the generic order
  of `J` along the centre through `f a'` — transports because the order along a centre is read on
  stalks (`ordAlongIdeal_pullbackDiffeomorph`) and the connected component of the centre is carried
  by the homeomorphism `g` (`genericOrdAlong_pullbackDiffeomorph`); when no ideal sheaf with the
  colon stalks exists on one side, none exists on the other, and both sides are the unit ideal. The
  same argument as `weakTransform_comap_liftStep` of `Hironaka/Manifold/Sequence/Functor/`,
  across the models.
* The reduced transform: the closed sets `f⁻¹(E) ∪ f⁻¹(D)` correspond under `g'`; the vanishing
  stalks are carried by the stalk isomorphism (`vanishingStalk_preimage_pullbackDiffeomorph`, the
  two-model form of `vanishingStalk_preimage_of_isLocalDiffeomorphAt'` of
  `Hironaka/Resolution/Analytic/IdealSheaf/VanishingPreimage.lean`); the local-generator condition
  transports both ways — forward by `hasLocalGenerators_pullback`, back by the forward direction
  along `g⁻¹` (`g` is a bijection). The same argument as `reducedTransform_comap_of_surjective`.
* `IsAnalyticIsoOver`: the local inverses are conjugated by `g`, `g'` (`PartialDiffeomorph.trans`);
  the bijection onto the set is read through the square.
* `IsProperMap`: `f' = g⁻¹ ∘ f ∘ g'` with homeomorphisms.

The Jacobian ideal and the monoidal transformations along a square, which need charts, are in
`Hironaka/Resolution/Analytic/ModelTransport/SquareChart.lean`.
-/

public section

noncomputable section

open AnalyticManifold TopologicalSpace Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section Germs

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace E' N]

/-- A germ at `h b` vanishes on `Z` iff its pull-back along the local analytic isomorphism `h`
vanishes on `h⁻¹(Z)` at `b`: the two-model form of
`Germ.vanishesOn_compTendsto_of_isLocalDiffeomorphAt'`
(`Hironaka/Resolution/Analytic/IdealSheaf/VanishingPreimage.lean`), the same proof with the models
free. -/
theorem Germ.vanishesOn_compTendsto_of_isLocalDiffeomorphAt_models {h : N → M}
    (hh : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω h) {b : N}
    (hb : IsLocalDiffeomorphAt 𝓘(𝕜, E') 𝓘(𝕜, E) ω h b) (Z : Set M) (k : (𝓝 (h b)).Germ 𝕜) :
    Germ.VanishesOn (h ⁻¹' Z) b (k.compTendsto h (hh.continuous.tendsto b)) ↔
      Germ.VanishesOn Z (h b) k := by
  obtain ⟨Φ, hbΦ, heq⟩ := hb.exists_partialDiffeomorph
  induction k using Germ.inductionOn with
  | h f =>
    rw [Germ.coe_compTendsto, Germ.vanishesOn_coe, Germ.vanishesOn_coe]
    have hev : ∀ᶠ y in 𝓝 b, y ∈ Φ.source := Φ.open_source.mem_nhds hbΦ
    have hmap : Filter.map h (𝓝[h ⁻¹' Z] b) = 𝓝[Z] (h b) := by
      have e1 : Filter.map h (𝓝[h ⁻¹' Z] b) = Filter.map ⇑Φ (𝓝[h ⁻¹' Z] b) :=
        Filter.map_congr ((hev.mono fun y hy => heq hy).filter_mono nhdsWithin_le_nhds)
      have hset : (h ⁻¹' Z : Set N) =ᶠ[𝓝 b] (⇑Φ ⁻¹' Z) :=
        Filter.eventuallyEqSet_iff.mpr (hev.mono fun y hy => by
          rw [Set.mem_preimage, Set.mem_preimage, heq hy])
      rw [e1, nhdsWithin_eq_iff_eventuallyEqSet.mpr hset, heq hbΦ]
      exact Φ.toOpenPartialHomeomorph.map_nhdsWithin_preimage_eq hbΦ Z
    rw [← hmap, Filter.eventually_map]
    exact Iff.rfl

/-- The vanishing stalk of `h⁻¹(Z)` at `b` is the image of the vanishing stalk of `Z` at `h b`
under the germ map: the two-model form of `vanishingStalk_preimage_of_isLocalDiffeomorphAt'`. -/
theorem vanishingStalk_preimage_of_isLocalDiffeomorphAt_models {h : N → M}
    (hh : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω h) {b : N}
    (hb : IsLocalDiffeomorphAt 𝓘(𝕜, E') 𝓘(𝕜, E) ω h b) (Z : Set M) :
    vanishingStalk (𝕜 := 𝕜) (E := E') (h ⁻¹' Z) b =
      Ideal.map (germMap h hh b) (vanishingStalk (𝕜 := 𝕜) (E := E) Z (h b)) := by
  have hcomap : (vanishingStalk (𝕜 := 𝕜) (E := E') (h ⁻¹' Z) b).comap (germMap h hh b) =
      vanishingStalk (𝕜 := 𝕜) (E := E) Z (h b) := by
    ext s
    rw [Ideal.mem_comap, mem_vanishingStalk_iff, mem_vanishingStalk_iff, stalkToGerm_germMap]
    exact Germ.vanishesOn_compTendsto_of_isLocalDiffeomorphAt_models hh hb Z _
  rw [← hcomap]
  exact (Ideal.map_comap_of_surjective _
    (germMap_bijective_of_isLocalDiffeomorphAt' h hh hb).2 _).symm

end Germs

section Square

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
  {N : AnalyticManifold.{u} 𝕜 E'} (g : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N M ω)

/-- The vanishing stalk along an analytic isomorphism across the models. -/
theorem vanishingStalk_preimage_pullbackDiffeomorph (Z : Set M) (b : N) :
    vanishingStalk (𝕜 := 𝕜) (E := E') (⇑g ⁻¹' Z) b =
      Ideal.map (g.stalkRingEquiv b) (vanishingStalk (𝕜 := 𝕜) (E := E) Z (g b)) :=
  vanishingStalk_preimage_of_isLocalDiffeomorphAt_models g.contMDiff (g.isLocalDiffeomorph b) Z

/-- Local generators of the vanishing stalks of a set are carried along `g`
(`hasLocalGenerators_pullback`). -/
theorem hasLocalGenerators_vanishingStalk_preimage_diffeomorph (W : Set M)
    (hW : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M) fun y : M =>
      vanishingStalk (𝕜 := 𝕜) (E := E) W y) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E' N) fun x : N =>
      vanishingStalk (𝕜 := 𝕜) (E := E') (⇑g ⁻¹' W) x := by
  have := hasLocalGenerators_pullback ⇑g g.contMDiff (IdealSheaf.ofStalks _ _ hW)
  refine (congrArg IdealSheaf.HasLocalGenerators (funext fun x => ?_)).mp this
  rw [IdealSheaf.stalkIdeal_ofStalks]
  exact (vanishingStalk_preimage_pullbackDiffeomorph g W x).symm

/-- Local generators of the vanishing stalks, both ways (`g` is a bijection: the other way is the
forward direction along `g⁻¹`). -/
theorem hasLocalGenerators_vanishingStalk_preimage_diffeomorph_iff (W : Set M) :
    (IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E' N) fun x : N =>
      vanishingStalk (𝕜 := 𝕜) (E := E') (⇑g ⁻¹' W) x) ↔
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M) fun y : M =>
      vanishingStalk (𝕜 := 𝕜) (E := E) W y := by
  refine ⟨fun h => ?_, hasLocalGenerators_vanishingStalk_preimage_diffeomorph g W⟩
  have := hasLocalGenerators_vanishingStalk_preimage_diffeomorph g.symm _ h
  have hset : ⇑g.symm ⁻¹' (⇑g ⁻¹' W) = W := by
    ext y; simp [g.apply_symm_apply]
  rwa [hset] at this

/-- The order along a centre along `g`: the stalk isomorphism preserves inclusions and powers. -/
theorem _root_.Manifold.IdealSheaf.ordAlongIdeal_pullbackDiffeomorph
    (D J : AnalyticManifold.IdealSheaf M)
    (b : N) :
    IdealSheaf.ordAlongIdeal (D.pullbackDiffeomorph g) (J.pullbackDiffeomorph g) b =
      IdealSheaf.ordAlongIdeal D J (g b) := by
  have hiff : ∀ A C : Ideal (IdealSheaf.stalkRing M (g b)),
      Ideal.map (g.stalkRingEquiv b) A ≤ Ideal.map (g.stalkRingEquiv b) C ↔ A ≤ C := fun A C => by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ (g.stalkRingEquiv b).bijective]
  simp only [IdealSheaf.ordAlongIdeal, IdealSheaf.stalkIdeal_pullbackDiffeomorph]
  refine iSup_congr fun p => ?_
  rw [← Ideal.map_pow]
  exact iSup_congr_Prop (hiff _ _) fun _ => rfl

/-- The generic order along a centre along `g`: the connected component of the centre through the
point is carried by the homeomorphism `g` (`Homeomorph.image_connectedComponentIn`), the order
pointwise. -/
theorem _root_.Manifold.IdealSheaf.genericOrdAlong_pullbackDiffeomorph
    (D J : AnalyticManifold.IdealSheaf M)
    (b : N) :
    IdealSheaf.genericOrdAlong (D.pullbackDiffeomorph g) (J.pullbackDiffeomorph g) b =
      IdealSheaf.genericOrdAlong D J (g b) := by
  simp only [IdealSheaf.genericOrdAlong_def]
  have hcos : (D.pullbackDiffeomorph g).support = ⇑g ⁻¹' D.support :=
    IdealSheaf.support_pullback _ _ D
  by_cases hb : g b ∈ D.support
  · have hcc : connectedComponentIn (⇑g ⁻¹' D.support) b =
        ⇑g ⁻¹' connectedComponentIn D.support (g b) := by
      have h1 := g.toHomeomorph.symm.image_connectedComponentIn (s := D.support)
        (x := g.toHomeomorph b) hb
      rw [Homeomorph.image_symm, Homeomorph.symm_apply_apply] at h1
      exact h1.symm
    rw [hcos, hcc]
    apply le_antisymm
    · refine le_iInf₂ fun z hz => ?_
      have := iInf₂_le (f := fun y (_ : y ∈ ⇑g ⁻¹' connectedComponentIn D.support (g b)) =>
        IdealSheaf.ordAlongIdeal (D.pullbackDiffeomorph g) (J.pullbackDiffeomorph g) y) (g.symm z)
        (by rw [Set.mem_preimage, g.apply_symm_apply]; exact hz)
      rwa [IdealSheaf.ordAlongIdeal_pullbackDiffeomorph, g.apply_symm_apply] at this
    · refine le_iInf₂ fun y hy => ?_
      rw [IdealSheaf.ordAlongIdeal_pullbackDiffeomorph]
      exact iInf₂_le (g y) hy
  · have hb' : b ∉ (D.pullbackDiffeomorph g).support := by rw [hcos]; exact hb
    rw [connectedComponentIn_eq_empty hb', connectedComponentIn_eq_empty hb]
    simp

variable {M' : AnalyticManifold.{u} 𝕜 E} {N' : AnalyticManifold.{u} 𝕜 E'}
  (g' : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N' M' ω) (f : AnalyticMap M' M)
  (f' : AnalyticMap N' N) (hsq : IsModelSquare g g' f f')

include hsq in
/-- The pointwise form of the square `f ∘ g' = g ∘ f'`: `f' = g⁻¹ ∘ f ∘ g'`. -/
theorem IsModelSquare.apply_eq (x : N') : f' x = g.symm (f (g' x)) := by
  rw [hsq x, g.symm_apply_apply]

include hsq in
/-- The reversed square, for `g⁻¹`, `g'⁻¹`. -/
theorem IsModelSquare.symm : IsModelSquare g.symm g'.symm f' f := fun y => by
  rw [hsq.apply_eq g g' f f' (g'.symm y), g'.apply_symm_apply]

include hsq in
/-- The colon stalks (`IsDivExceptional`) along a square: the stalk isomorphism carries colon ideals
and powers (`Ideal.map_colon_pow_of_bijective`), the exponent (the generic order along the centre)
transports by `genericOrdAlong_pullbackDiffeomorph`. -/
theorem _root_.Manifold.IdealSheaf.IsDivExceptional.pullbackDiffeomorph_of_square
    (J D : AnalyticManifold.IdealSheaf M)
    {J' : AnalyticManifold.IdealSheaf M'}
    (h : IdealSheaf.IsDivExceptional (IdealSheaf.pullback ⇑f f.contMDiff J)
      (IdealSheaf.pullback ⇑f f.contMDiff D)
      (fun a => (IdealSheaf.genericOrdAlong D J (f a)).toNat) J') :
    IdealSheaf.IsDivExceptional (IdealSheaf.pullback ⇑f' f'.contMDiff (J.pullbackDiffeomorph g))
      (IdealSheaf.pullback ⇑f' f'.contMDiff (D.pullbackDiffeomorph g))
      (fun x => (IdealSheaf.genericOrdAlong (D.pullbackDiffeomorph g) (J.pullbackDiffeomorph g)
        (f' x)).toNat)
      (J'.pullbackDiffeomorph g') := by
  intro x
  have h1 : IdealSheaf.pullback ⇑f' f'.contMDiff (J.pullbackDiffeomorph g) =
      IdealSheaf.pullbackDiffeomorph g'
          (IdealSheaf.pullback ⇑f f.contMDiff J) :=
    (IdealSheaf.pullbackDiffeomorph_comap g g' f f' hsq J).symm
  have h2 : IdealSheaf.pullback ⇑f' f'.contMDiff (D.pullbackDiffeomorph g) =
      IdealSheaf.pullbackDiffeomorph g'
          (IdealSheaf.pullback ⇑f f.contMDiff D) :=
    (IdealSheaf.pullbackDiffeomorph_comap g g' f f' hsq D).symm
  rw [h1, h2, IdealSheaf.stalkIdeal_pullbackDiffeomorph, IdealSheaf.stalkIdeal_pullbackDiffeomorph,
    IdealSheaf.stalkIdeal_pullbackDiffeomorph, h (g' x)]
  beta_reduce
  rw [IdealSheaf.genericOrdAlong_pullbackDiffeomorph, ← hsq x]
  exact Ideal.map_colon_pow_of_bijective _ (g'.stalkRingEquiv x).bijective _ _ _

include hsq in
/-- **Hironaka's weak transform [Hir64, p. 142] along a square of analytic isomorphisms across the
models**: both sides are the unique ideal sheaf with the colon stalks (`IsDivExceptional.unique`),
the colon data corresponding under `g'`; when no such sheaf exists on one side none exists on the
other (pull back along `g'⁻¹`), and both are the unit ideal. -/
theorem _root_.AnalyticManifold.IdealSheaf.weakTransform_of_square
    (D J : AnalyticManifold.IdealSheaf M) :
    IdealSheaf.weakTransform f' (J.pullbackDiffeomorph g) (D.pullbackDiffeomorph g) =
      (IdealSheaf.weakTransform f J D).pullbackDiffeomorph g' := by
  unfold IdealSheaf.weakTransform
  split_ifs with h1 h2 h2
  · exact IsDivExceptional.unique (Classical.choose_spec h1)
      (IdealSheaf.IsDivExceptional.pullbackDiffeomorph_of_square g g' f f' hsq J D
        (Classical.choose_spec h2))
  · exfalso
    obtain ⟨J'', hJ''⟩ := h1
    refine h2 ⟨J''.pullbackDiffeomorph g'.symm, ?_⟩
    have := IdealSheaf.IsDivExceptional.pullbackDiffeomorph_of_square g.symm g'.symm f' f
      (hsq.symm g g' f f') (J.pullbackDiffeomorph g) (D.pullbackDiffeomorph g) hJ''
    simpa only [IdealSheaf.pullbackDiffeomorph_symm_pullbackDiffeomorph] using this
  · exfalso
    exact h1 ⟨_, IdealSheaf.IsDivExceptional.pullbackDiffeomorph_of_square g g' f f' hsq J D
      (Classical.choose_spec h2)⟩
  · exact (IdealSheaf.pullbackDiffeomorph_top g').symm

include hsq in
/-- **Hironaka's `red(f⁻¹(E) ∪ f⁻¹(D))` [Hir64, Main Theorem II'(N) (iii), p. 156] along a
square**: the closed sets correspond, the vanishing stalks along the stalk isomorphisms, the
local-generator condition both ways. -/
theorem _root_.AnalyticManifold.IdealSheaf.reducedTransform_of_square
    (D E₀ : AnalyticManifold.IdealSheaf M) :
    IdealSheaf.reducedTransform f' (E₀.pullbackDiffeomorph g) (D.pullbackDiffeomorph g) =
      (IdealSheaf.reducedTransform f E₀ D).pullbackDiffeomorph g' := by
  have hW : ⇑f' ⁻¹' IdealSheaf.support (E₀.pullbackDiffeomorph g) ∪
      ⇑f' ⁻¹' IdealSheaf.support (D.pullbackDiffeomorph g) =
      ⇑g' ⁻¹' (⇑f ⁻¹' E₀.support ∪ ⇑f ⁻¹' D.support) := by
    rw [IdealSheaf.support_pullbackDiffeomorph,
      IdealSheaf.support_pullbackDiffeomorph]
    ext x
    simp only [Set.mem_union, Set.mem_preimage, hsq x]
  by_cases h₂ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') fun x : M' =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑f ⁻¹' E₀.support ∪ ⇑f ⁻¹' D.support) x
  · have h₁ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E' N') fun x : N' =>
        vanishingStalk (𝕜 := 𝕜) (E := E')
          (⇑f' ⁻¹' IdealSheaf.support (E₀.pullbackDiffeomorph g) ∪
            ⇑f' ⁻¹' IdealSheaf.support (D.pullbackDiffeomorph g)) x := by
      rw [hW]
      exact hasLocalGenerators_vanishingStalk_preimage_diffeomorph g' _ h₂
    rw [reducedTransform_eq_of_hasLocalGenerators f D E₀ h₂,
      reducedTransform_eq_of_hasLocalGenerators f' _ _ h₁]
    refine IdealSheaf.ext fun x => ?_
    rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph, IdealSheaf.stalkIdeal_ofStalks,
      IdealSheaf.stalkIdeal_ofStalks, hW, vanishingStalk_preimage_pullbackDiffeomorph]
  · have h₁ : ¬ IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E' N') fun x : N' =>
        vanishingStalk (𝕜 := 𝕜) (E := E')
          (⇑f' ⁻¹' IdealSheaf.support (E₀.pullbackDiffeomorph g) ∪
            ⇑f' ⁻¹' IdealSheaf.support (D.pullbackDiffeomorph g)) x := by
      rw [hW]
      exact fun hg => h₂ ((hasLocalGenerators_vanishingStalk_preimage_diffeomorph_iff g' _).mp hg)
    rw [reducedTransform_eq_mul_of_not f D E₀ h₂, reducedTransform_eq_mul_of_not f' _ _ h₁,
      IdealSheaf.pullbackDiffeomorph_mul,
      IdealSheaf.pullbackDiffeomorph_comap g g' f f' hsq,
      IdealSheaf.pullbackDiffeomorph_comap g g' f f' hsq]

include hsq in
/-- A local analytic isomorphism on a set transports along a square: the local inverse is
conjugated by the two isomorphisms (`PartialDiffeomorph.trans`). -/
theorem isLocalDiffeomorphOn_of_square {U : Set M}
    (h : IsLocalDiffeomorphOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω f (⇑f ⁻¹' U)) :
    IsLocalDiffeomorphOn 𝓘(𝕜, E') 𝓘(𝕜, E') ω f' (⇑f' ⁻¹' (⇑g ⁻¹' U)) := by
  rintro ⟨x, hx⟩
  have hx' : g' x ∈ ⇑f ⁻¹' U := by
    change f (g' x) ∈ U
    rw [hsq x]; exact hx
  obtain ⟨Φ, hxΦ, hΦ⟩ := (h ⟨g' x, hx'⟩).exists_partialDiffeomorph
  refine IsLocalDiffeomorphAt.of_eqOn
    ((g'.toPartialDiffeomorphUniv.trans Φ).trans g.symm.toPartialDiffeomorphUniv)
    ⟨⟨Set.mem_univ _, hxΦ⟩, Set.mem_univ _⟩ fun y hy => ?_
  have hmem : g' y ∈ Φ.source := hy.1.2
  change f' y = g.symm (Φ (g' y))
  rw [hsq.apply_eq g g' f f' y, hΦ hmem]

include hsq in
/-- A bijection onto a set transports along a square. -/
theorem bijOn_of_square {U : Set M} (h : Set.BijOn f (⇑f ⁻¹' U) U) :
    Set.BijOn f' (⇑f' ⁻¹' (⇑g ⁻¹' U)) (⇑g ⁻¹' U) := by
  refine ⟨fun x hx => hx, fun a ha b hb hab => ?_, fun v hv => ?_⟩
  · have ha' : g' a ∈ ⇑f ⁻¹' U := by change f (g' a) ∈ U; rw [hsq a]; exact ha
    have hb' : g' b ∈ ⇑f ⁻¹' U := by change f (g' b) ∈ U; rw [hsq b]; exact hb
    have : f (g' a) = f (g' b) := by
      rw [hsq a, hsq b]
      exact congrArg g hab
    exact g'.injective (h.injOn ha' hb' this)
  · obtain ⟨y, hy, hyv⟩ := h.surjOn (show g v ∈ U from hv)
    refine ⟨g'.symm y, ?_, ?_⟩
    · change f' (g'.symm y) ∈ ⇑g ⁻¹' U
      rw [hsq.apply_eq g g' f f', g'.apply_symm_apply, hyv, Set.mem_preimage,
        g.apply_symm_apply]
      exact hv
    · rw [hsq.apply_eq g g' f f', g'.apply_symm_apply, hyv, g.symm_apply_apply]

include hsq in
/-- **`IsAnalyticIsoOver` along a square**: both directions by the forward lemmas at the square and
at the reversed square. -/
theorem _root_.AnalyticMap.isAnalyticIsoOver_of_square_iff (U : Set M) :
    f'.IsIsoOver (⇑g ⁻¹' U) ↔ f.IsIsoOver U := by
  constructor
  · rintro ⟨h1, h2⟩
    have hU : ⇑g.symm ⁻¹' (⇑g ⁻¹' U) = U := by ext y; simp [g.apply_symm_apply]
    have e1 := isLocalDiffeomorphOn_of_square g.symm g'.symm f' f (hsq.symm g g' f f') h1
    have e2 := bijOn_of_square g.symm g'.symm f' f (hsq.symm g g' f f') h2
    rw [hU] at e1 e2
    exact ⟨e1, e2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalDiffeomorphOn_of_square g g' f f' hsq h1, bijOn_of_square g g' f f' hsq h2⟩

include hsq in
/-- **Properness along a square**: `f' = g⁻¹ ∘ f ∘ g'` with `g`, `g'` homeomorphisms
(`Homeomorph.isProperMap`, `IsProperMap.comp`). -/
theorem isProperMap_of_square_iff : IsProperMap ⇑f' ↔ IsProperMap ⇑f := by
  have e : ⇑f' = ⇑g.symm ∘ ⇑f ∘ ⇑g' := funext (hsq.apply_eq g g' f f')
  have e' : ⇑f = ⇑g ∘ ⇑f' ∘ ⇑g'.symm := funext fun y => by
    rw [Function.comp_apply, Function.comp_apply, hsq.apply_eq g g' f f', g'.apply_symm_apply,
      g.apply_symm_apply]
  constructor
  · intro h
    rw [e']
    exact (g.toHomeomorph.isProperMap.comp h).comp g'.symm.toHomeomorph.isProperMap
  · intro h
    rw [e]
    exact (g.symm.toHomeomorph.isProperMap.comp h).comp g'.toHomeomorph.isProperMap

end Square

end Hironaka.Manifold

end
