/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CenterList
public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
public import Hironaka.Manifold.Snc.Basic
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.BlowUp.Transform.Bundled
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.Weak
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.Bundled
import Hironaka.Resolution.Analytic.GoingUp.NormalCrossingsTransport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The stalk-level clauses of [Kol07, Definition 66] along a local analytic isomorphism

In the global case of the proof of [Kol07, Theorem 103] the functor `BO_{n,m}` is descended
along the surjective cover `g : X^* → X`, and the clauses of [Kol07, Definition 66] are carried
back along it (the proof remarks, at the end of its local case, that the functoriality package
is local): the order of the marked transform along the centre and
the normal-crossings condition of the boundary with the centre are conditions on the stalks at
the points of the centre, carried both ways by the bijective germ map of a local analytic
isomorphism at a point (`germMap_bijective_of_isLocalDiffeomorphAt`). This file states them
pointwise, for an analytic map `h : N → M` that is a local analytic isomorphism at the point:

* `IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt`: the order of `J` along the centre `D`
  transports (`ordAlongIdeal_pullback_diffeomorph`, at a point);
* `IdealSheaf.genericOrdAlong_comap_of_isLocalDiffeomorph`: the generic order along the centre
  `Y` transports (both sides `⊤` off the centre, `genericOrdAlong_eq_ordAlong` on it);
* `NormalCrossingsData`, the stalk-level content of `HasOnlyNormalCrossingsWith` at a point, and
  its transport along a bijective ring map (`NormalCrossingsData.map`);
  `HasOnlyNormalCrossingsWith.comap_of_isLocalDiffeomorph` (pull-back) and
  `HasOnlyNormalCrossingsWith.of_comap_of_surjective` (descent along a surjective local
  isomorphism: every point of the centre has a preimage, and the inverse germ map carries the
  data back);
* the vanishing ideals and local generators along a local isomorphism, the naturality of
  Hironaka's reduced transform `red(f⁻¹(E) ∪ f⁻¹(D))` along a square with a surjective local
  isomorphism (`reducedTransform_comap_of_surjective`), and the transforms of one blowing-up
  along the lift of a local isomorphism (`totalTransform_comap_liftStep`,
  `exceptionalIdealSheaf_comap_liftStep`, `birationalTransform_comap_liftStep`,
  `reducedTransform_comap_liftStep`, `weakTransform_comap_liftStep`).

These are the stalkwise inputs of the stage-by-stage description of the pull-back of a list of
centres in `Hironaka.Resolution.Analytic.Functor.PullbackSequence`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Topology Filter IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### The order along a centre -/

section OrdAlong

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- The order of `J` along the centre `D` transports along a local analytic isomorphism
at a point: the stalk ideals are carried by the bijective germ map, which preserves inclusions and
powers (`ordAlongIdeal_pullback_diffeomorph`, pointwise). -/
theorem _root_.Manifold.IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt (h : AnalyticMap N M)
    (D J : AnalyticManifold.IdealSheaf M) {b : N}
        (hb : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω h b) :
    IdealSheaf.ordAlongIdeal (D.pullback h h.contMDiff)
        (J.pullback h h.contMDiff) b =
      IdealSheaf.ordAlongIdeal D J (h b) := by
  have hbij : Function.Bijective (germMap ⇑h h.contMDiff b) :=
    germMap_bijective_of_isLocalDiffeomorphAt ⇑h h.contMDiff hb
  have hiff : ∀ (A C : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk (h b))),
      Ideal.map (germMap ⇑h h.contMDiff b) A ≤ Ideal.map (germMap ⇑h h.contMDiff b) C ↔ A ≤ C :=
    fun A C => by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ hbij]
  simp only
      [IdealSheaf.ordAlongIdeal,
          IdealSheaf.stalkIdeal_pullback]
  refine iSup_congr fun p => ?_
  rw [← Ideal.map_pow]
  exact iSup_congr_Prop (hiff _ _) fun _ => rfl

/-- The generic order along a centre is `⊤` off the centre (the component is empty). -/
theorem _root_.Manifold.IdealSheaf.genericOrdAlong_eq_top_of_notMem
    (D J : AnalyticManifold.IdealSheaf M)
    {a : M}
    (ha : a ∉ D.support) : IdealSheaf.genericOrdAlong D J a = ⊤ := by
  rw [IdealSheaf.genericOrdAlong_def, connectedComponentIn_eq_empty ha]
  simp

variable {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The generic order of `J` along the centre `Y` transports along a local analytic
isomorphism: on the centre it is the order along the centre (`genericOrdAlong_eq_ordAlong`), which
transports pointwise; off the centre both sides are `⊤`. -/
theorem _root_.Manifold.IdealSheaf.genericOrdAlong_comap_of_isLocalDiffeomorph
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (J : AnalyticManifold.IdealSheaf M) (b : N) :
    IdealSheaf.genericOrdAlong (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf
        (J.pullback h h.contMDiff) b =
      IdealSheaf.genericOrdAlong hY.idealSheaf J (h b) := by
  by_cases hb : h b ∈ Y
  · rw [genericOrdAlong_eq_ordAlong hY J hb,
      genericOrdAlong_eq_ordAlong (hY.preimage_of_isLocalDiffeomorph hh) _
        (show b ∈ ⇑h ⁻¹' Y from hb),
      ← comap_idealSheaf_of_isLocalDiffeomorph ψ h hh hY,
      IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt h _ _ (hh b)]
  · rw [IdealSheaf.genericOrdAlong_eq_top_of_notMem _ _
        (by rw [(hY.preimage_of_isLocalDiffeomorph hh).cosupport_idealSheaf]; exact hb),
      IdealSheaf.genericOrdAlong_eq_top_of_notMem _ _ (by rwa [hY.cosupport_idealSheaf])]

end OrdAlong

/-! ### Normal crossings at a point -/

section NormalCrossings

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- The stalk-level content of `HasOnlyNormalCrossingsWith E D` at a point (Hironaka's Definition
2, [Hir64, Ch. 0, §5, p. 141], as in the vocabulary of the main theorems): a regular system of
parameters `z` containing an equation of each minimal prime of `I` and generating `D`. -/
def NormalCrossingsData (I D : Ideal R) : Prop :=
  ∃ (n : ℕ) (z : Fin n → R),
    (Ideal.span (Set.range z) = maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R) ∧
    (∀ P ∈ I.minimalPrimes, ∃ i, P = Ideal.span {z i}) ∧
    ∃ s : Finset (Fin n), D = Ideal.span (z '' ↑s)

/-- The normal-crossings data transport along a bijective ring map (argument for the germ
map of a diffeomorphism, made algebraic): the regular system of parameters, the minimal primes and
the generators of `D` are carried by `e`. -/
theorem NormalCrossingsData.map (e : R →+* S) (he : Function.Bijective e) {I D : Ideal R}
    (h : NormalCrossingsData I D) : NormalCrossingsData (I.map e) (D.map e) := by
  obtain ⟨n, z, ⟨hspan, hdim⟩, hmin, s, hD⟩ := h
  refine ⟨n, fun i => e (z i), ⟨?_, ?_⟩, ?_, s, ?_⟩
  · rw [show (fun i => e (z i)) = e ∘ z from rfl, Set.range_comp, ← Ideal.map_span, hspan]
    exact map_maximalIdeal_of_surjective _ he.2
  · exact hdim.trans (ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective e he))
  · intro P hP
    obtain ⟨i, hi⟩ := hmin (P.comap e) (Ideal.comap_mem_minimalPrimes_of_bijective _ he hP)
    refine ⟨i, ?_⟩
    rw [← Ideal.map_comap_of_surjective _ he.2 P, hi, Ideal.map_span, Set.image_singleton]
  · rw [hD, Ideal.map_span, ← Set.image_comp]
    rfl

/-- The inverse transport: data for the images along a bijective ring map come from data for the
ideals themselves. -/
theorem NormalCrossingsData.of_map (e : R →+* S) (he : Function.Bijective e) {I D : Ideal R}
    (h : NormalCrossingsData (I.map e) (D.map e)) : NormalCrossingsData I D := by
  set e' := RingEquiv.ofBijective e he
  have hcomp : e'.symm.toRingHom.comp e = RingHom.id R :=
    RingHom.ext fun r => e'.symm_apply_apply r
  have hinv : ∀ K : Ideal R, Ideal.map e'.symm.toRingHom (Ideal.map e K) = K := fun K => by
    rw [Ideal.map_map, hcomp, Ideal.map_id]
  have := h.map e'.symm.toRingHom e'.symm.bijective
  rwa [hinv, hinv] at this

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- `HasOnlyNormalCrossingsWith` is the pointwise normal-crossings data at the points of the
support of `D`. -/
theorem hasOnlyNormalCrossingsWith_iff_normalCrossingsData
    (E' D : AnalyticManifold.IdealSheaf M) :
    E'.HasOnlyNormalCrossingsWith D ↔
      ∀ x ∈ D.support, NormalCrossingsData (E'.stalkIdeal x) (D.stalkIdeal x) :=
  Iff.rfl

/-- Hironaka's Definition 2 pulls back along a local analytic isomorphism
(`HasOnlyNormalCrossingsWith.pullback_diffeomorph`, for a local isomorphism): the data at `h b` are
carried to `b` by the bijective germ map. -/
theorem HasOnlyNormalCrossingsWith.comap_of_isLocalDiffeomorph (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {E' D : AnalyticManifold.IdealSheaf M}
    (hE : E'.HasOnlyNormalCrossingsWith D) :
    AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith (E'.pullback h h.contMDiff)
      (D.pullback h h.contMDiff) := by
  rw [hasOnlyNormalCrossingsWith_iff_normalCrossingsData] at hE ⊢
  intro b hb
  have hgb : h b ∈ D.support := by
    have hb' : b ∈ (D.pullback h h.contMDiff).support := hb
    rwa [IdealSheaf.support_pullback] at hb'
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt ⇑h h.contMDiff (hh b)
  rw
      [IdealSheaf.stalkIdeal_pullback,
    IdealSheaf.stalkIdeal_pullback]
  exact (hE (h b) hgb).map _ hbij

/-- Hironaka's Definition 2 descends along a surjective local analytic isomorphism: every point of
the centre has a preimage, at which the data of the pull-backs are the images of the data at the
point under the bijective germ map. -/
theorem HasOnlyNormalCrossingsWith.of_comap_of_surjective (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hs : Function.Surjective h)
    {E' D : AnalyticManifold.IdealSheaf M}
    (hE : AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith (E'.pullback h h.contMDiff)
      (D.pullback h h.contMDiff)) :
    E'.HasOnlyNormalCrossingsWith D := by
  rw [hasOnlyNormalCrossingsWith_iff_normalCrossingsData] at hE ⊢
  intro x hx
  obtain ⟨b, rfl⟩ := hs x
  have hb : b ∈ (D.pullback h h.contMDiff).support := by
    rw [IdealSheaf.support_pullback]
    exact hx
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt ⇑h h.contMDiff (hh b)
  have hd := hE b hb
  rw
      [IdealSheaf.stalkIdeal_pullback,
    IdealSheaf.stalkIdeal_pullback] at hd
  exact hd.of_map _ hbij

end NormalCrossings

/-! ### Vanishing ideals and local generators along a local isomorphism -/

section Vanishing

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- A function germ at `h b` vanishes on `Z` iff its composite with `h` vanishes on `h⁻¹(Z)` at
`b`, for `h` a local analytic isomorphism at `b` (embedding lemma at a point: on the
source of a local inverse `h` is a homeomorphism onto an open set, so it maps the trace of the
neighbourhood filter on `h⁻¹(Z)` onto the trace on `Z`). -/
theorem Germ.vanishesOn_compTendsto_of_isLocalDiffeomorphAt (h : AnalyticMap N M) {b : N}
    (hb : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω h b) (Z : Set M) (k : (𝓝 (h b)).Germ 𝕜) :
    Germ.VanishesOn (⇑h ⁻¹' Z) b (k.compTendsto ⇑h (h.contMDiff.continuous.tendsto b)) ↔
      Germ.VanishesOn Z (h b) k := by
  obtain ⟨Φ, hbΦ, heq⟩ := hb.exists_partialDiffeomorph
  induction k using Germ.inductionOn with
  | h f =>
    rw [Germ.coe_compTendsto, Germ.vanishesOn_coe, Germ.vanishesOn_coe]
    have hev : ∀ᶠ y in 𝓝 b, y ∈ Φ.source := Φ.open_source.mem_nhds hbΦ
    have hmap : Filter.map ⇑h (𝓝[⇑h ⁻¹' Z] b) = 𝓝[Z] (h b) := by
      have e1 : Filter.map ⇑h (𝓝[⇑h ⁻¹' Z] b) = Filter.map ⇑Φ (𝓝[⇑h ⁻¹' Z] b) :=
        Filter.map_congr ((hev.mono fun y hy => heq hy).filter_mono nhdsWithin_le_nhds)
      have hset : (⇑h ⁻¹' Z : Set N) =ᶠ[𝓝 b] (⇑Φ ⁻¹' Z) :=
        Filter.eventuallyEqSet_iff.mpr (hev.mono fun y hy => by
          rw [Set.mem_preimage, Set.mem_preimage, heq hy])
      rw [e1, nhdsWithin_eq_iff_eventuallyEqSet.mpr hset, heq hbΦ]
      exact Φ.toOpenPartialHomeomorph.map_nhdsWithin_preimage_eq hbΦ Z
    rw [← hmap, Filter.eventually_map]
    exact Iff.rfl

/-- The vanishing ideal of `h⁻¹(Z)` at `b` is the image of the vanishing ideal of `Z` at `h b`
under the bijective germ map of the local analytic isomorphism `h` at `b`
(`vanishingStalk_preimage_diffeomorph`, pointwise). -/
theorem vanishingStalk_preimage_of_isLocalDiffeomorphAt (h : AnalyticMap N M) {b : N}
    (hb : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω h b) (Z : Set M) :
    vanishingStalk (𝕜 := 𝕜) (E := E) (⇑h ⁻¹' Z) b =
      Ideal.map (germMap ⇑h h.contMDiff b) (vanishingStalk (𝕜 := 𝕜) (E := E) Z (h b)) := by
  have hcomap : (vanishingStalk (𝕜 := 𝕜) (E := E) (⇑h ⁻¹' Z) b).comap (germMap ⇑h h.contMDiff b) =
      vanishingStalk (𝕜 := 𝕜) (E := E) Z (h b) := by
    ext s
    rw [Ideal.mem_comap, mem_vanishingStalk_iff, mem_vanishingStalk_iff, stalkToGerm_germMap]
    exact Germ.vanishesOn_compTendsto_of_isLocalDiffeomorphAt h hb Z _
  rw [← hcomap]
  exact (Ideal.map_comap_of_surjective _
    (germMap_bijective_of_isLocalDiffeomorphAt ⇑h h.contMDiff hb).2 _).symm

/-- Local generators of the vanishing ideals pull back along a local analytic isomorphism. -/
theorem hasLocalGenerators_vanishingStalk_preimage_of_isLocalDiffeomorph (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (W : Set M)
    (hW : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M) fun y : M =>
      vanishingStalk (𝕜 := 𝕜) (E := E) W y) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N) fun x : N =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑h ⁻¹' W) x := by
  have := hasLocalGenerators_pullback ⇑h h.contMDiff (IdealSheaf.ofStalks _ _ hW)
  refine (congrArg IdealSheaf.HasLocalGenerators (funext fun x => ?_)).mp this
  rw [IdealSheaf.stalkIdeal_ofStalks, vanishingStalk_preimage_of_isLocalDiffeomorphAt h (hh x)]

/-- **Local generators descend along a surjective local analytic isomorphism**: for a family of
stalk ideals `I` on `M`, if the pulled-back family `b ↦ (germMap h b)(I (h b))` on `N` has local
generators, so has `I` — at `x = h q` the generators near `q` are pushed forward along a local
inverse of `h` (their germs at the points of the image open set are carried by the stalk map of the
inverse, the two-sided inverse of the germ map of `h`). -/
theorem _root_.Manifold.IdealSheaf.HasLocalGenerators.of_map_germMap_of_surjective
    (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hs : Function.Surjective h)
    (I : ∀ x : M, Ideal ((structureSheaf 𝕜 E M).presheaf.stalk x))
    (hI : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N) fun b : N =>
      Ideal.map (germMap ⇑h h.contMDiff b) (I (h b))) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M) I := by
  intro x
  obtain ⟨q, rfl⟩ := hs x
  obtain ⟨Φ, hqΦ, heq⟩ := (hh q).exists_partialDiffeomorph
  obtain ⟨U', hqU', k, f, hf⟩ := hI.exists_fin q
  let W : Opens N := U' ⊓ ⟨Φ.source, Φ.open_source⟩
  have hqW : q ∈ W := ⟨hqU', hqΦ⟩
  have hVopen : IsOpen (Φ.target ∩ Φ.invFun ⁻¹' (W : Set N)) :=
    Φ.toOpenPartialHomeomorph.isOpen_inter_preimage_symm W.2
  let V : Opens M := ⟨Φ.target ∩ Φ.invFun ⁻¹' (W : Set N), hVopen⟩
  have hinvq : Φ.invFun (h q) = q := by rw [heq hqΦ]; exact Φ.left_inv hqΦ
  have hxV : h q ∈ V := by
    refine ⟨heq hqΦ ▸ Φ.map_source hqΦ, ?_⟩
    change Φ.invFun (h q) ∈ W
    rw [hinvq]
    exact hqW
  have hinv : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω Φ.invFun (V : Set M) :=
    Φ.contMDiffOn_invFun.mono inter_subset_left
  have hmaps : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (extendSection 𝕜 E (f i) ∘ Φ.invFun) (V : Set M) :=
    fun i => (contMDiffOn_extendSection (f i)).comp hinv fun v hv =>
      (show Φ.invFun v ∈ (U' : Set N) ∩ Φ.source from hv.2).1
  refine ⟨V, hxV, Fin k, inferInstance, fun i => sectionOfContMDiffOn _ V (hmaps i),
    fun v hv => ?_⟩
  have hv2 : Φ.invFun v ∈ (U' : Set N) ∩ Φ.source := hv.2
  obtain ⟨y, hyW, rfl⟩ : ∃ y ∈ (U' : Set N) ∩ Φ.source, h y = v :=
    ⟨Φ.invFun v, hv2, by rw [heq hv2.2]; exact Φ.right_inv hv.1⟩
  have hyS : y ∈ Φ.source := hyW.2
  have hyU : y ∈ U' := hyW.1
  have hyinv : Φ.invFun (h y) = y := by rw [heq hyS]; exact Φ.left_inv hyS
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt ⇑h h.contMDiff (hh y)
  -- the stalk map of the inverse at `h y`, the two-sided inverse of the germ map of `h` at `y`
  set g := germMapOn Φ.invFun (V := V) hinv hv hyinv with hg
  have hcomp : g.comp (germMap ⇑h h.contMDiff y) = RingHom.id _ := by
    refine RingHom.ext fun t => stalkToGerm_injective 𝓘(𝕜, E) ω M (h y) ?_
    rw [RingHom.comp_apply, hg, stalkToGerm_germMapOn, stalkToGerm_germMap, RingHom.id_apply]
    induction stalkToGerm 𝓘(𝕜, E) ω M (h y) t using Germ.inductionOn with
    | h k =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
      refine Germ.coe_eq.mpr ?_
      filter_upwards [V.2.mem_nhds hv] with z hz
      simp only [Function.comp_apply]
      have hmem : Φ.invFun z ∈ Φ.source :=
        (show Φ.invFun z ∈ (U' : Set N) ∩ Φ.source from hz.2).2
      have hri : Φ.toPartialEquiv (Φ.invFun z) = z := Φ.right_inv hz.1
      rw [heq hmem, hri]
  have hmapg : ∀ K : Ideal ((structureSheaf 𝕜 E N).presheaf.stalk y),
      Ideal.map g K = Ideal.comap (germMap ⇑h h.contMDiff y) K := fun K => by
    conv_lhs => rw [← Ideal.map_comap_of_surjective _ hbij.2 K]
    rw [Ideal.map_map, hcomp, Ideal.map_id]
  have hfy := hf y hyU
  rw [← Ideal.comap_map_of_bijective (I := I (h y)) _ hbij, hfy, ← hmapg, Ideal.map_span,
    ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  change g ((structureSheaf 𝕜 E N).presheaf.germ U' y hyU (f i)) = _
  rw [hg, germMapOn_germ Φ.invFun hinv hv hyinv hyU (f i) hv (hmaps i)]

end Vanishing

/-! ### The reduced transform along a surjective local isomorphism -/

section Reduced

variable {M₁ M₂ N₁ N₂ : AnalyticManifold.{u} 𝕜 E}

/-- Hironaka's `red(f⁻¹(E) ∪ f⁻¹(D))` (`reducedTransform`) is natural along a square
`f₂ ∘ ℓ = h ∘ f₁` of analytic maps with `ℓ` a surjective local analytic isomorphism
(`reducedTransform_pullback_of_comp_eq` with the diffeomorphism replaced by a surjective local
isomorphism): the closed sets correspond, the vanishing ideals along the bijective germ maps, and
the local-generator condition pulls back and — this is where surjectivity enters — descends. -/
theorem reducedTransform_comap_of_surjective (h : AnalyticMap M₁ M₂) (f₁ : AnalyticMap N₁ M₁)
    (f₂ : AnalyticMap N₂ M₂) (ℓ : AnalyticMap N₁ N₂) (hℓ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ℓ)
    (hs : Function.Surjective ℓ) (hsq : ∀ x, f₂ (ℓ x) = h (f₁ x))
        (D B : AnalyticManifold.IdealSheaf M₂) :
    (AnalyticManifold.IdealSheaf.reducedTransform f₂ B D).pullback ℓ ℓ.contMDiff =
      AnalyticManifold.IdealSheaf.reducedTransform f₁ (B.pullback h h.contMDiff)
        (D.pullback h h.contMDiff) := by
  have hW :
      ⇑f₁ ⁻¹' IdealSheaf.support (B.pullback h h.contMDiff) ∪
      ⇑f₁ ⁻¹' IdealSheaf.support (D.pullback h h.contMDiff) =
      ⇑ℓ ⁻¹' (⇑f₂ ⁻¹' B.support ∪ ⇑f₂ ⁻¹' D.support) := by
    rw
        [show IdealSheaf.support (B.pullback h h.contMDiff) =
            ⇑h ⁻¹' B.support from
        IdealSheaf.support_pullback ⇑h h.contMDiff B,
      show IdealSheaf.support (D.pullback h h.contMDiff) =
          ⇑h ⁻¹' D.support from
        IdealSheaf.support_pullback ⇑h h.contMDiff D]
    ext x
    simp only [Set.mem_union, Set.mem_preimage, hsq]
  by_cases h₂ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N₂) fun x : N₂ =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑f₂ ⁻¹' B.support ∪ ⇑f₂ ⁻¹' D.support) x
  · have h₁ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N₁) fun x : N₁ =>
        vanishingStalk (𝕜 := 𝕜) (E := E)
          (⇑f₁ ⁻¹' IdealSheaf.support
              (B.pullback h h.contMDiff) ∪
            ⇑f₁ ⁻¹' IdealSheaf.support
                (D.pullback h h.contMDiff)) x := by
      rw [hW]
      exact hasLocalGenerators_vanishingStalk_preimage_of_isLocalDiffeomorph ℓ hℓ _ h₂
    rw [reducedTransform_eq_of_hasLocalGenerators f₂ D B h₂,
      reducedTransform_eq_of_hasLocalGenerators f₁ _ _ h₁]
    refine IdealSheaf.ext fun x => ?_
    rw
        [IdealSheaf.stalkIdeal_pullback,
            IdealSheaf.stalkIdeal_ofStalks,
      IdealSheaf.stalkIdeal_ofStalks, hW, vanishingStalk_preimage_of_isLocalDiffeomorphAt ℓ (hℓ x)]
  · have h₁ : ¬ IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N₁) fun x : N₁ =>
        vanishingStalk (𝕜 := 𝕜) (E := E)
          (⇑f₁ ⁻¹' IdealSheaf.support
              (B.pullback h h.contMDiff) ∪
            ⇑f₁ ⁻¹' IdealSheaf.support
                (D.pullback h h.contMDiff)) x := by
      rw [hW]
      intro hg
      refine h₂ (IdealSheaf.HasLocalGenerators.of_map_germMap_of_surjective ℓ hℓ hs _ ?_)
      refine (congrArg IdealSheaf.HasLocalGenerators (funext fun x => ?_)).mp hg
      rw [vanishingStalk_preimage_of_isLocalDiffeomorphAt ℓ (hℓ x)]
    rw [reducedTransform_eq_mul_of_not f₂ D B h₂, reducedTransform_eq_mul_of_not f₁ _ _ h₁]
    change (B.pullback ⇑f₂ f₂.contMDiff * D.pullback ⇑f₂ f₂.contMDiff).pullback ⇑ℓ ℓ.contMDiff =
      (B.pullback ⇑h h.contMDiff).pullback ⇑f₁ f₁.contMDiff *
        (D.pullback ⇑h h.contMDiff).pullback ⇑f₁ f₁.contMDiff
    rw [IdealSheaf.pullback_mul, IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback,
      IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback,
      IdealSheaf.pullback_congr B (f₂.contMDiff.comp ℓ.contMDiff) (h.contMDiff.comp f₁.contMDiff)
        (show ⇑f₂ ∘ ⇑ℓ = ⇑h ∘ ⇑f₁ from funext hsq),
      IdealSheaf.pullback_congr D (f₂.contMDiff.comp ℓ.contMDiff) (h.contMDiff.comp f₁.contMDiff)
        (show ⇑f₂ ∘ ⇑ℓ = ⇑h ∘ ⇑f₁ from funext hsq)]

end Reduced

/-! ### One step of the pull-back: the transforms along the lift of the blowing-up -/

section OneStep

variable {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}
  (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
  (hY : IsClosedSubmanifold ψ Y c)

/-- The total transform along the lift `Bl_{h⁻¹Y} N → Bl_Y M` of a local analytic isomorphism
(`liftStep`): `ℓ^* π^* J = π'^* h^* J` (`π ∘ ℓ = h ∘ π'`). -/
theorem totalTransform_comap_liftStep (J : AnalyticManifold.IdealSheaf M) :
    (J.pullback _ (isBlowUp_blowUpπ ψ hY).contMDiff).pullback
        ⇑(AnalyticManifold.BlowUpSequence.liftStep h hh hY)
        (AnalyticManifold.BlowUpSequence.liftStep h hh hY).contMDiff =
      (J.pullback ⇑h h.contMDiff).pullback _ (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph
          hh)).contMDiff := by
  rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr _ _ _ (funext fun q =>
      AnalyticManifold.BlowUpSequence.blowUpπ_liftStep h hh hY q)

/-- The exceptional ideal sheaf along the lift: `ℓ^* I_F = I_{F'}`
(`comap_idealSheaf_of_isLocalDiffeomorph` for the centre). -/
theorem exceptionalIdealSheaf_comap_liftStep :
    (hY.idealSheaf.pullback _ (isBlowUp_blowUpπ ψ hY).contMDiff).pullback
        ⇑(AnalyticManifold.BlowUpSequence.liftStep h hh hY)
            (AnalyticManifold.BlowUpSequence.liftStep h hh hY).contMDiff =
      (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf.pullback _ (isBlowUp_blowUpπ ψ
          (hY.preimage_of_isLocalDiffeomorph hh)).contMDiff := by
  rw [← comap_idealSheaf_of_isLocalDiffeomorph ψ h hh hY]
  rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr _ _ _ (funext fun q =>
      AnalyticManifold.BlowUpSequence.blowUpπ_liftStep h hh hY q)

/-- Kollár's marked transform ([Kol07, Definition 60, (60.1)]) along the lift of a local analytic
isomorphism: for a marking `m ≤ ν_Y(J)` along the centre,
`ℓ^* (π)^{-1}_*(J, m) = (π')^{-1}_*(h^* J, m)`
— both are the unique ideal sheaves with the colon stalks, and the colon stalks
correspond along the bijective germ map of `ℓ` (`birationalTransform_pullback_of_comp_eq`
with the diffeomorphism replaced by the lift; the marking is legitimate for `(h^* J, m)` by the
transport of the order along the centre). -/
theorem birationalTransform_comap_liftStep
    (J : MarkedIdealSheaf (structureSheaf 𝕜 E M))
    (hm : ∀ a ∈ Y, (J.m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J.I a) :
    (MarkedIdealSheaf.birationalTransform hY (isBlowUp_blowUpπ ψ hY) J).I.pullback _
        (AnalyticManifold.BlowUpSequence.liftStep h hh hY).contMDiff =
      (MarkedIdealSheaf.birationalTransform (hY.preimage_of_isLocalDiffeomorph hh)
        (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
        ⟨J.I.pullback h h.contMDiff, J.m⟩).I := by
  have hm' : ∀ a ∈ ⇑h ⁻¹' Y, (J.m : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf
        (J.I.pullback h h.contMDiff) a := by
    intro a ha
    rw [← comap_idealSheaf_of_isLocalDiffeomorph ψ h hh hY,
      IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt h _ _ (hh a)]
    exact hm (h a) ha
  have h2 := isDivExceptional_birationalTransform hY (isBlowUp_blowUpπ ψ hY) J hm
  refine IsDivExceptional.unique ?_
    (isDivExceptional_birationalTransform (hY.preimage_of_isLocalDiffeomorph hh)
      (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
      ⟨J.I.pullback h h.contMDiff, J.m⟩ hm')
  intro q
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt ⇑(AnalyticManifold.BlowUpSequence.liftStep
      h hh hY)
    (AnalyticManifold.BlowUpSequence.liftStep h hh hY).contMDiff
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY q)
  rw [IdealSheaf.stalkIdeal_pullback,
    h2 (AnalyticManifold.BlowUpSequence.liftStep h hh hY q), Ideal.map_colon_pow_of_bijective _
        hbij,
    ← IdealSheaf.stalkIdeal_pullback, ← IdealSheaf.stalkIdeal_pullback,
    totalTransform_comap_liftStep h hh hY J.I, exceptionalIdealSheaf_comap_liftStep h hh hY]

/-- The reduced transform of the boundary along the lift of a SURJECTIVE local
analytic isomorphism: `ℓ^* red(π⁻¹E ∪ π⁻¹Y) = red(π'⁻¹ h^*E ∪ π'⁻¹ h⁻¹Y)`
(`reducedTransform_comap_of_surjective` on the square `π ∘ ℓ = h ∘ π'`). -/
theorem reducedTransform_comap_liftStep (hs : Function.Surjective h)
    (E₀ : AnalyticManifold.IdealSheaf M) :
    (AnalyticManifold.IdealSheaf.reducedTransform (Manifold.blowUpπ ψ hY) E₀
        hY.idealSheaf).pullback _ (AnalyticManifold.BlowUpSequence.liftStep h hh hY).contMDiff =
      AnalyticManifold.IdealSheaf.reducedTransform
        (Manifold.blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
        (E₀.pullback h h.contMDiff)
        (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf := by
  rw [reducedTransform_comap_of_surjective h (Manifold.blowUpπ ψ
      (hY.preimage_of_isLocalDiffeomorph hh))
    (Manifold.blowUpπ ψ hY) (AnalyticManifold.BlowUpSequence.liftStep h hh hY)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY)
    (AnalyticManifold.BlowUpSequence.surjective_liftStep h hh hY hs)
        (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep h hh hY) hY.idealSheaf
    E₀, comap_idealSheaf_of_isLocalDiffeomorph ψ h hh hY]

/-- Hironaka's weak transform (`IdealSheaf.weakTransform`) along the lift
of a local analytic isomorphism: `ℓ^* (π)_*^{-1} J = (π')_*^{-1} h^* J` — both are the unique
ideal sheaves with the colon stalks `(π⁻¹J : I_F^ν)`, the exponent the generic order along the
centre, which transports (`genericOrdAlong_comap_of_isLocalDiffeomorph`). -/
theorem weakTransform_comap_liftStep
    (J : AnalyticManifold.IdealSheaf M) :
    (AnalyticManifold.IdealSheaf.weakTransform (Manifold.blowUpπ ψ hY) J
        hY.idealSheaf).pullback _ (AnalyticManifold.BlowUpSequence.liftStep h hh hY).contMDiff =
      AnalyticManifold.IdealSheaf.weakTransform
        (Manifold.blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
        (J.pullback h h.contMDiff)
        (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf := by
  rw [weakTransform_eq (Manifold.blowUpπ ψ hY) hY hY.isIdealSheafOf_idealSheaf
      (isBlowUp_blowUpπ ψ hY) J,
    weakTransform_eq (Manifold.blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
      (hY.preimage_of_isLocalDiffeomorph hh)
      (hY.preimage_of_isLocalDiffeomorph hh).isIdealSheafOf_idealSheaf
      (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh)) _]
  refine IsDivExceptional.unique ?_
    (isDivExceptional_weakTransformOf (hY.preimage_of_isLocalDiffeomorph hh)
      (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh)) _)
  intro q
  have h2 := isDivExceptional_weakTransformOf hY (isBlowUp_blowUpπ ψ hY) J
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt ⇑(AnalyticManifold.BlowUpSequence.liftStep
      h hh hY)
    (AnalyticManifold.BlowUpSequence.liftStep h hh hY).contMDiff
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY q)
  have hexp : (IdealSheaf.genericOrdAlong hY.idealSheaf J
        (Manifold.blowUpπ ψ hY (AnalyticManifold.BlowUpSequence.liftStep h hh hY q))).toNat =
      (IdealSheaf.genericOrdAlong (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf
        (J.pullback h h.contMDiff)
        (Manifold.blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh) q)).toNat := by
    rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep h hh hY q,
      IdealSheaf.genericOrdAlong_comap_of_isLocalDiffeomorph h hh hY J]
  rw [IdealSheaf.stalkIdeal_pullback,
    h2 (AnalyticManifold.BlowUpSequence.liftStep h hh hY q), Ideal.map_colon_pow_of_bijective _
        hbij,
    ← IdealSheaf.stalkIdeal_pullback, ← IdealSheaf.stalkIdeal_pullback,
    totalTransform_comap_liftStep h hh hY J, exceptionalIdealSheaf_comap_liftStep h hh hY]
  beta_reduce
  rw [hexp]

end OneStep

/-! ### The reduced ideal sheaf of a pulled-back family -/

/-- Along a
surjective local analytic isomorphism `h`, the reduced ideal sheaf of `h⁻¹(E)` is the pull-back of
the reduced ideal sheaf of `E` — the vanishing stalks of the preimage are the images of the
vanishing stalks under the bijective germ maps, and local generators descend along surjective
local isomorphisms, so both branches of the `if` agree. -/
theorem _root_.Manifold.HypersurfaceFamily.idealSheaf_comap_of_surjective
    {M N : AnalyticManifold.{u} 𝕜 E}
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) (F : HypersurfaceFamily M) :
    (F.comap h).idealSheaf = F.idealSheaf.pullback h h.contMDiff := by
  unfold HypersurfaceFamily.idealSheaf
  rw [HypersurfaceFamily.support_comap]
  by_cases h₂ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M) fun x : M =>
      vanishingStalk (𝕜 := 𝕜) (E := E) F.support x
  · have h₁ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N) fun x : N =>
        vanishingStalk (𝕜 := 𝕜) (E := E) (⇑h ⁻¹' F.support) x :=
      hasLocalGenerators_vanishingStalk_preimage_of_isLocalDiffeomorph h hh _ h₂
    rw [dite_eq_left h₂, dite_eq_left h₁]
    refine IdealSheaf.ext fun x => ?_
    rw
        [IdealSheaf.stalkIdeal_pullback,
            IdealSheaf.stalkIdeal_ofStalks,
      IdealSheaf.stalkIdeal_ofStalks, vanishingStalk_preimage_of_isLocalDiffeomorphAt h (hh x)]
  · have h₁ : ¬ IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N) fun x : N =>
        vanishingStalk (𝕜 := 𝕜) (E := E) (⇑h ⁻¹' F.support) x := by
      intro hg
      refine h₂ (IdealSheaf.HasLocalGenerators.of_map_germMap_of_surjective h hh hs _ ?_)
      refine (congrArg IdealSheaf.HasLocalGenerators (funext fun x => ?_)).mp hg
      rw [vanishingStalk_preimage_of_isLocalDiffeomorphAt h (hh x)]
    rw [dite_eq_right h₂, dite_eq_right h₁]
    exact (IdealSheaf.pullback_top _ _).symm

end Hironaka.Manifold

end
