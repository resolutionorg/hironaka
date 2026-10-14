/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.PullbackFibre
public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.ExceptionalDense
public import Hironaka.Resolution.Analytic.Wlo09.FamilyCoherence
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
import Hironaka.Manifold.IdealSheaf.Pullback

/-!
# The global lift of a local analytic isomorphism to the principalizations

Włodarczyk's principalization commutes with local analytic isomorphisms
[Wlo09, Theorem 2.0.3, last sentence; Theorem 3.5.1 (2)]: for a local analytic isomorphism
`g : N → M` and an ideal sheaf `I` on `M`, the succession of the principalization of `g^*I` over a
neighbourhood `U_{K'}` of a compact of `N` is the pull-back of the succession of the
principalization of `I` over a neighbourhood `U_K ⊇ g(U_{K'})`, up to blow-ups with empty centre
(the clause `isPullbackAlong` of
`IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms`). Over the whole manifolds this gives a map
`g̃ : Ñ → M̃` over `g`, the "natural lifting" of [Wlo09, Theorem 2.0.1 (3)] for the
principalization, which identifies `Ñ` with the fibre product `N ×_M M̃`. This module constructs
it for two extension-compatible families `F'` over `N` and `F` over `M` from exactly the data the
theorem asserts: every `U_{K'}` has compact closure (`hcl`) and the per-compact pull-back relation
(`hrel`).

* The pieces (`liftCompact`, `lastLift`, `pieceMap`): for a compact `K'` of `N` the compact
  `K := closure g(U_{K'})` of `M` satisfies `g(U_{K'}) ⊆ U_K`, so the relation supplies a lift
  `R_{r'} → S_r` of the last stages over `g` (`exists_lift_bijOn_fiber`), a local analytic
  isomorphism bijective on the fibres; after `toSpace K` it is a map `R_{r'} → M̃` over `g`.
* Uniqueness (`eqOn_of_map_eq`): two maps from an open subset of `Ñ` to `M̃`, continuous there and
  over `g`, agree. Off the images `Z` of the centres of `S` the composite blow-down of `S` is
  injective, so over a point of `U_K ∖ Z` the fibre of `F.map` is a single point; the points of
  the piece whose image in `M` avoids `Z` are dense in the piece
  (`dense_preimage_compl_centerImages` pulled back along the open map `lastLift`), and `M̃` is
  Hausdorff (`Set.EqOn.of_subset_closure`).
  This is `eq_of_map_comp_eq` of `FamilyCoherence.lean` with `g` in place of an inclusion.
* The gluing (`pieceFun`, `liftFun`, `lift`): on the open piece `O_{K'} = F'.map⁻¹(U_{K'})` the
  piece map read through the inverse of `toSpace K'`; the value of the lift at `q` is the piece
  map of the singleton compact `{F'.map q}`. Every piece map agrees with the lift on its piece
  (uniqueness on the overlap), so the lift is analytic, a local analytic isomorphism
  (`isLocalDiffeomorph_lift`), over `g` (`map_lift`), bijective on the fibres (`bijOn_fiber_lift`),
  and the only continuous map over `g` (`eq_lift_of_map_eq`).
* `IdealSheafPair.commutesWithLocalAnalyticIsomorphisms_of_isPullbackUpToEmptyAlong`: the clause
  `IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms` for an assignment on the pairs whose
  successions pull back along local analytic isomorphisms over every pair of compacts and
  whose neighbourhoods have compact closures; and its consequences `bijOn_preimage_of_bijOn_fiber`
  (over an open on which `g` is injective, the lift is a bijection between the preimages: the
  identification `Ñ = N ×_M M̃`), `surjective_of_bijOn_fiber` (the global content of
  [Wlo09, Theorem 3.5.1 (1)]), and the naturality
  `IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms.comp_eq`, `id_eq` from uniqueness, through
  the lift clause at a pair given by its ideal sheaf (`exists_lift_of_eq`).
-/

@[expose] public section

noncomputable section

open Set Topology Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u v

namespace AnalyticManifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ExtensionCompatibleFamily

open FiniteSuccession

variable {M N : AnalyticManifold.{u} 𝕜 E} (F : ExtensionCompatibleFamily M)
  (F' : ExtensionCompatibleFamily N) (g : AnalyticMap N M)

/-! ### The identification of the end result and the fibres -/

/-- `toSpace K` is a local analytic isomorphism at every point: the preimage of `map⁻¹(U_K)` is
everything, since `map ∘ toSpace K = σ_K` lands in `U_K`. -/
theorem isLocalDiffeomorph_toSpace (K : Compacts M) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (F.toSpace K) := fun a =>
  (F.toSpace_isIso K).1 ⟨a, by
    change F.map (F.toSpace K a) ∈ (F.nhd K : Set M)
    rw [F.map_toSpace_apply]
    exact ((F.seq K).composite a).2⟩

/-- `toSpace K` is injective. -/
theorem toSpace_injective (K : Compacts M) : Function.Injective (F.toSpace K) := by
  intro a b hab
  refine (F.toSpace_isIso K).2.injOn ?_ ?_ hab <;>
  · change F.map (F.toSpace K _) ∈ (F.nhd K : Set M)
    rw [F.map_toSpace_apply]
    exact ((F.seq K).composite _).2

/-- `toSpace K` maps the fibre of the composite blow-down over a point `x ∈ U_K` bijectively onto
the fibre of `map` over `x`. -/
theorem bijOn_fiber_toSpace (K : Compacts M) (x : M.restrict (F.nhd K)) :
    BijOn (F.toSpace K) {a | (F.seq K).composite a = x} (F.map ⁻¹' {x.1}) := by
  refine ⟨fun a ha => ?_, (F.toSpace_injective K).injOn, fun q hq => ?_⟩
  · rw [mem_preimage, mem_singleton_iff, F.map_toSpace_apply,
      show (F.seq K).composite a = x from ha]
  · have hq' : F.map q ∈ F.nhd K := by
      rw [mem_singleton_iff.mp hq]
      exact x.2
    obtain ⟨a, ha⟩ := F.exists_toSpace_eq K hq'
    refine ⟨a, ?_, ha⟩
    apply Subtype.ext
    rw [← F.map_toSpace_apply, ha]
    exact mem_singleton_iff.mp hq

/-- Two points of `M̃` over a point of `U_K` off the images `Z` of the centres of `seq K` coincide:
the composite blow-down of `seq K` is injective off `Z` (`isIsoOver_composite_compl_centerImages`),
and `toSpace K` is a bijection onto `map⁻¹(U_K)`. -/
theorem eq_of_map_eq_of_notMem_centerImages (K : Compacts M) {b : (F.seq K).last}
    (hb : (F.seq K).composite b ∉ (F.seq K).centerImages) {p₁ p₂ : F.space}
    (h₁ : F.map p₁ = ((F.seq K).composite b).1) (h₂ : F.map p₂ = ((F.seq K).composite b).1) :
    p₁ = p₂ := by
  have hinj := (F.seq K).isIsoOver_composite_compl_centerImages.2.injOn
  have key : ∀ p : F.space, F.map p = ((F.seq K).composite b).1 → p = F.toSpace K b := by
    intro p hp
    have hmem : F.map p ∈ F.nhd K := by
      rw [hp]
      exact ((F.seq K).composite b).2
    obtain ⟨a, ha⟩ := F.exists_toSpace_eq K hmem
    have hab : (F.seq K).composite a = (F.seq K).composite b := by
      apply Subtype.ext
      rw [← F.map_toSpace_apply, ha, hp]
    rw [← ha]
    congr 1
    exact hinj (by rw [mem_preimage, hab]; exact hb) hb hab
  rw [key p₁ h₁, key p₂ h₂]

/-! ### The pieces -/

/-- The singleton compact of a point. -/
def singletonCompact (y : N) : Compacts N := ⟨{y}, isCompact_singleton⟩

/-- The image of a point of `Ñ` lies in the neighbourhood of its singleton compact. -/
theorem map_mem_nhd_singletonCompact (q : F'.space) :
    F'.map q ∈ F'.nhd (singletonCompact (F'.map q)) :=
  F'.subset_nhd _ (mem_singleton _)

section Compacts

variable {F'}
variable (hcl : ∀ K' : Compacts N, IsCompact (closure (F'.nhd K' : Set N)))
include hcl

/-- The closure of `g(U_{K'})` is compact: it lies in the compact `g(closure U_{K'})`. -/
theorem isCompact_closure_image_nhd (K' : Compacts N) :
    IsCompact (closure (⇑g '' (F'.nhd K' : Set N))) :=
  ((hcl K').image g.contMDiff.continuous).of_isClosed_subset isClosed_closure
    (closure_minimal (image_mono subset_closure) ((hcl K').image g.contMDiff.continuous).isClosed)

/-- The compact `K := closure g(U_{K'})` of `M` attached to a compact `K'` of `N`. -/
def liftCompact (K' : Compacts N) : Compacts M :=
  ⟨closure (⇑g '' (F'.nhd K' : Set N)), isCompact_closure_image_nhd g hcl K'⟩

variable {g} in
/-- `g(U_{K'}) ⊆ U_K` for the attached compact `K`. -/
theorem image_nhd_subset_nhd_liftCompact (K' : Compacts N) :
    ⇑g '' (F'.nhd K' : Set N) ⊆ F.nhd (liftCompact g hcl K') := fun x hx =>
  F.subset_nhd (liftCompact g hcl K') (show x ∈ closure (⇑g '' (F'.nhd K' : Set N)) from
    subset_closure hx)

end Compacts

section Pieces

variable {F F' g}
variable (hcl : ∀ K' : Compacts N, IsCompact (closure (F'.nhd K' : Set N)))
  (hrel : F'.IsPullbackAlong F g)
include hcl hrel

/-- The pull-back relation between the successions over `U_{K'}` and over `U_K`. -/
theorem isPullbackUpToEmptyAlong_liftCompact (K' : Compacts N) :
    (F'.seq K').IsPullbackUpToEmptyAlong (F.seq (liftCompact g hcl K')) g :=
  hrel K' _ (image_nhd_subset_nhd_liftCompact F hcl K')

/-- The lift of the last stages `R_{r'} → S_r` over `g` supplied by the relation
(`exists_lift_bijOn_fiber`), a local analytic isomorphism bijective on the fibres. -/
def lastLift (K' : Compacts N) :
    AnalyticMap (F'.seq K').last (F.seq (liftCompact g hcl K')).last :=
  (isPullbackUpToEmptyAlong_liftCompact hcl hrel K').exists_lift_bijOn_fiber.choose

theorem isLocalDiffeomorph_lastLift (K' : Compacts N) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (lastLift hcl hrel K') :=
  (isPullbackUpToEmptyAlong_liftCompact hcl hrel K').exists_lift_bijOn_fiber.choose_spec.1

/-- The last lift is over `g`. -/
theorem composite_lastLift (K' : Compacts N) (p : (F'.seq K').last) :
    ((F.seq (liftCompact g hcl K')).composite (lastLift hcl hrel K' p)).1 =
      g ((F'.seq K').composite p).1 :=
  (isPullbackUpToEmptyAlong_liftCompact hcl hrel K').exists_lift_bijOn_fiber.choose_spec.2.1 p

/-- The last lift is bijective on the fibres. -/
theorem bijOn_fiber_lastLift (K' : Compacts N) (y : N.restrict (F'.nhd K')) :
    BijOn (lastLift hcl hrel K') (fiberR (F'.seq K') (Fin.last _) y)
      (fiberS (F.seq (liftCompact g hcl K')) g (Fin.last _) y) :=
  (isPullbackUpToEmptyAlong_liftCompact hcl hrel K').exists_lift_bijOn_fiber.choose_spec.2.2 y

/-- The piece map `R_{r'} → M̃`: the last lift followed by the identification `toSpace K`. -/
def pieceMap (K' : Compacts N) : AnalyticMap (F'.seq K').last F.space :=
  (F.toSpace (liftCompact g hcl K')).comp (lastLift hcl hrel K')

/-- The piece map is over `g`. -/
theorem map_pieceMap (K' : Compacts N) (p : (F'.seq K').last) :
    F.map (pieceMap hcl hrel K' p) = g (F'.map (F'.toSpace K' p)) := by
  change F.map (F.toSpace _ (lastLift hcl hrel K' p)) = _
  rw [F.map_toSpace_apply, composite_lastLift, F'.map_toSpace_apply]

theorem isLocalDiffeomorph_pieceMap (K' : Compacts N) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (pieceMap hcl hrel K') := fun p =>
  IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorph_lastLift hcl hrel K' p)
    (hg := F.isLocalDiffeomorph_toSpace _ _)

/-- The piece map maps the fibre of the composite blow-down of `R` over `y ∈ U_{K'}` bijectively
onto the fibre of `F.map` over `g y`. -/
theorem bijOn_fiber_pieceMap (K' : Compacts N) (y : N.restrict (F'.nhd K')) :
    BijOn (pieceMap hcl hrel K') (fiberR (F'.seq K') (Fin.last _) y) (F.map ⁻¹' {g y.1}) := by
  have hb := bijOn_fiber_lastLift hcl hrel K' y
  -- the fibre of `S` over `g y`, as the fibre of the composite over the point of `U_K`
  have hgy : g y.1 ∈ F.nhd (liftCompact g hcl K') :=
    image_nhd_subset_nhd_liftCompact F hcl K' ⟨y.1, y.2, rfl⟩
  have hfib : fiberS (F.seq (liftCompact g hcl K')) g (Fin.last _) y =
      {a | (F.seq (liftCompact g hcl K')).composite a = ⟨g y.1, hgy⟩} := by
    ext a
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hfib] at hb
  exact (F.bijOn_fiber_toSpace _ ⟨g y.1, hgy⟩).comp hb

/-- **Density of the good points of a piece**: every nonempty open subset of the end result
`R_{r'}` of the piece of `K'` contains a point whose image under the last lift lies over a point
off the images of the centres of `seq K` (the dense set `dense_preimage_compl_centerImages` of
`S_r`, pulled back along the open map `lastLift`). -/
theorem exists_mem_notMem_centerImages (K' : Compacts N) {W : Set (F'.seq K').last}
    (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ a ∈ W, (F.seq (liftCompact g hcl K')).composite (lastLift hcl hrel K' a) ∉
      (F.seq (liftCompact g hcl K')).centerImages := by
  have hdense : Dense (⇑(lastLift hcl hrel K') ⁻¹'
      ((F.seq (liftCompact g hcl K')).composite ⁻¹'
        ((F.seq (liftCompact g hcl K')).centerImages)ᶜ)) :=
    (F.seq (liftCompact g hcl K')).dense_preimage_compl_centerImages.preimage
      (isLocalDiffeomorph_lastLift hcl hrel K').isOpenMap
  obtain ⟨a, haW, haZ⟩ := hdense.inter_open_nonempty W hW hne
  exact ⟨a, haW, haZ⟩

/-! ### Uniqueness of maps over `g` -/

/-- **Uniqueness.** Two maps from an open subset `O` of `Ñ` to `M̃`, continuous on `O` and over `g`
there, agree on `O`: they agree at every point of a piece whose image in `M` avoids the images of
the centres (`eq_of_map_eq_of_notMem_centerImages`), such points are dense in the piece
(`exists_mem_notMem_centerImages`), and `M̃` is Hausdorff. -/
theorem eqOn_of_map_eq {O : Set F'.space} (hO : IsOpen O) {φ₁ φ₂ : F'.space → F.space}
    (h₁ : ContinuousOn φ₁ O) (h₂ : ContinuousOn φ₂ O)
    (hφ₁ : ∀ q ∈ O, F.map (φ₁ q) = g (F'.map q)) (hφ₂ : ∀ q ∈ O, F.map (φ₂ q) = g (F'.map q)) :
    EqOn φ₁ φ₂ O := by
  refine EqOn.of_subset_closure (s := {q | φ₁ q = φ₂ q} ∩ O) (fun q hq => hq.1) h₁ h₂
    inter_subset_right fun q₀ hq₀ => ?_
  rw [mem_closure_iff]
  intro V hV hq₀V
  -- the piece of the singleton compact `{F'.map q₀}` contains `q₀`
  obtain ⟨a₀, ha₀⟩ := F'.exists_toSpace_eq _ (F'.map_mem_nhd_singletonCompact q₀)
  obtain ⟨a, haV, haZ⟩ := exists_mem_notMem_centerImages hcl hrel (singletonCompact (F'.map q₀))
    ((hV.inter hO).preimage (F'.toSpace _).contMDiff.continuous)
    ⟨a₀, by rw [mem_preimage, ha₀]; exact ⟨hq₀V, hq₀⟩⟩
  refine ⟨F'.toSpace _ a, haV.1, ?_, haV.2⟩
  refine F.eq_of_map_eq_of_notMem_centerImages _ haZ ?_ ?_
  · rw [hφ₁ _ haV.2, composite_lastLift, F'.map_toSpace_apply]
  · rw [hφ₂ _ haV.2, composite_lastLift, F'.map_toSpace_apply]

/-! ### The gluing -/

/-- **The lift at a point**: the piece map of the singleton compact of its image, at the point of
the end result identified with it by `toSpace`. -/
def liftFun (q : F'.space) : F.space :=
  pieceMap hcl hrel (singletonCompact (F'.map q))
    (F'.exists_toSpace_eq _ (F'.map_mem_nhd_singletonCompact q)).choose

open scoped Classical in
/-- The piece map of `K'` read on the piece `O_{K'} = F'.map⁻¹(U_{K'})` through the inverse of
`toSpace K'`; off the piece, the lift. -/
def pieceFun (K' : Compacts N) (q : F'.space) : F.space :=
  if hq : F'.map q ∈ F'.nhd K' then pieceMap hcl hrel K' (F'.exists_toSpace_eq K' hq).choose
  else liftFun hcl hrel q

theorem pieceFun_of_mem {K' : Compacts N} {q : F'.space} (hq : F'.map q ∈ F'.nhd K') :
    pieceFun hcl hrel K' q = pieceMap hcl hrel K' (F'.exists_toSpace_eq K' hq).choose :=
  dite_eq_left hq

/-- On its piece the piece function is over `g`. -/
theorem map_pieceFun {K' : Compacts N} {q : F'.space} (hq : F'.map q ∈ F'.nhd K') :
    F.map (pieceFun hcl hrel K' q) = g (F'.map q) := by
  rw [pieceFun_of_mem hcl hrel hq, map_pieceMap, (F'.exists_toSpace_eq K' hq).choose_spec]

/-- The piece function at a point of the end result is the piece map. -/
theorem pieceFun_toSpace (K' : Compacts N) (a : (F'.seq K').last) :
    pieceFun hcl hrel K' (F'.toSpace K' a) = pieceMap hcl hrel K' a := by
  have hq : F'.map (F'.toSpace K' a) ∈ F'.nhd K' := by
    rw [F'.map_toSpace_apply]
    exact ((F'.seq K').composite a).2
  rw [pieceFun_of_mem hcl hrel hq]
  congr 1
  exact F'.toSpace_injective K' (F'.exists_toSpace_eq K' hq).choose_spec

/-- Near a point of its piece the piece function is the piece map after a local inverse of
`toSpace K'`. -/
theorem pieceFun_eqOn_target {K' : Compacts N} {q : F'.space} (hq : F'.map q ∈ F'.nhd K') :
    ∃ Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (F'.seq K').last F'.space ω,
      q ∈ Φ.target ∧ EqOn (pieceFun hcl hrel K') (pieceMap hcl hrel K' ∘ Φ.symm) Φ.target := by
  have ha : F'.toSpace K' (F'.exists_toSpace_eq K' hq).choose = q :=
    (F'.exists_toSpace_eq K' hq).choose_spec
  obtain ⟨Φ, haΦ, hΦ⟩ :=
    (F'.isLocalDiffeomorph_toSpace K' (F'.exists_toSpace_eq K' hq).choose).exists_partialDiffeomorph
  refine ⟨Φ, by rw [← ha, hΦ haΦ]; exact Φ.map_source haΦ, fun z hz => ?_⟩
  have hz' : Φ.symm z ∈ Φ.source := Φ.map_target hz
  have hzs : F'.toSpace K' (Φ.symm z) = z := by
    rw [hΦ hz']
    exact Φ.right_inv hz
  change pieceFun hcl hrel K' z = pieceMap hcl hrel K' (Φ.symm z)
  conv_lhs => rw [← hzs]
  exact pieceFun_toSpace hcl hrel K' _

/-- The piece function is a local analytic isomorphism at every point of its piece. -/
theorem isLocalDiffeomorphAt_pieceFun {K' : Compacts N} {q : F'.space}
    (hq : F'.map q ∈ F'.nhd K') :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (pieceFun hcl hrel K') q := by
  obtain ⟨Φ, hqΦ, hΦ⟩ := pieceFun_eqOn_target hcl hrel hq
  have h1 : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (pieceMap hcl hrel K' ∘ Φ.symm) q :=
    IsLocalDiffeomorphAt.comp (hf := Φ.symm.isLocalDiffeomorphAt _ _ _ hqΦ)
      (hg := isLocalDiffeomorph_pieceMap hcl hrel K' _)
  exact h1.congr_of_eventuallyEq (hΦ.eventuallyEq_of_mem (Φ.open_target.mem_nhds hqΦ))

/-- The piece function is continuous on its piece. -/
theorem continuousOn_pieceFun (K' : Compacts N) :
    ContinuousOn (pieceFun hcl hrel K') (⇑F'.map ⁻¹' (F'.nhd K' : Set N)) := fun _ hq =>
  (isLocalDiffeomorphAt_pieceFun hcl hrel hq).contMDiffAt.continuousAt.continuousWithinAt

/-- The piece function maps the fibre of `F'.map` over `y ∈ U_{K'}` bijectively onto the fibre of
`F.map` over `g y`. -/
theorem bijOn_fiber_pieceFun (K' : Compacts N) (y : N.restrict (F'.nhd K')) :
    BijOn (pieceFun hcl hrel K') (⇑F'.map ⁻¹' {y.1}) (⇑F.map ⁻¹' {g y.1}) := by
  have hb := bijOn_fiber_pieceMap hcl hrel K' y
  have ht := F'.bijOn_fiber_toSpace K' y
  -- the composite `pieceFun ∘ toSpace K'` is the piece map
  have hcomp : BijOn (pieceFun hcl hrel K' ∘ F'.toSpace K') (fiberR (F'.seq K') (Fin.last _) y)
      (⇑F.map ⁻¹' {g y.1}) :=
    hb.congr fun a _ => (pieceFun_toSpace hcl hrel K' a).symm
  refine ⟨fun q hq => ?_, fun q₁ hq₁ q₂ hq₂ h => ?_, fun p hp => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := ht.surjOn hq
    exact hcomp.mapsTo ha
  · obtain ⟨a₁, ha₁, rfl⟩ := ht.surjOn hq₁
    obtain ⟨a₂, ha₂, rfl⟩ := ht.surjOn hq₂
    rw [hcomp.injOn ha₁ ha₂ h]
  · obtain ⟨a, ha, hfa⟩ := hcomp.surjOn hp
    exact ⟨F'.toSpace K' a, ht.mapsTo ha, hfa⟩

/-- The lift agrees with every piece function on its piece: uniqueness on the overlap of the
piece with the piece of the singleton compact. -/
theorem liftFun_eq_pieceFun {K' : Compacts N} {q : F'.space} (hq : F'.map q ∈ F'.nhd K') :
    liftFun hcl hrel q = pieceFun hcl hrel K' q := by
  have hq₀ : F'.map q ∈ F'.nhd (singletonCompact (F'.map q)) :=
    F'.map_mem_nhd_singletonCompact q
  have hOo : IsOpen (⇑F'.map ⁻¹' (F'.nhd K' : Set N) ∩
      ⇑F'.map ⁻¹' (F'.nhd (singletonCompact (F'.map q)) : Set N)) :=
    ((F'.nhd K').isOpen.preimage F'.map.contMDiff.continuous).inter
      ((F'.nhd _).isOpen.preimage F'.map.contMDiff.continuous)
  have h := eqOn_of_map_eq hcl hrel hOo
    ((continuousOn_pieceFun hcl hrel (singletonCompact (F'.map q))).mono inter_subset_right)
    ((continuousOn_pieceFun hcl hrel K').mono inter_subset_left)
    (fun z hz => map_pieceFun hcl hrel hz.2) (fun z hz => map_pieceFun hcl hrel hz.1) ⟨hq, hq₀⟩
  rw [← h]
  exact (pieceFun_of_mem hcl hrel hq₀).symm

/-- Near every point the lift is the piece function of any piece containing the point. -/
theorem liftFun_eventuallyEq (K' : Compacts N) {q : F'.space} (hq : F'.map q ∈ F'.nhd K') :
    liftFun hcl hrel =ᶠ[𝓝 q] pieceFun hcl hrel K' :=
  eventuallyEq_of_mem
    (((F'.nhd K').isOpen.preimage F'.map.contMDiff.continuous).mem_nhds hq)
    fun _ hz => liftFun_eq_pieceFun hcl hrel hz

/-- **The lift is a local analytic isomorphism.** -/
theorem isLocalDiffeomorph_liftFun : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (liftFun hcl hrel) :=
  fun q => (isLocalDiffeomorphAt_pieceFun hcl hrel (F'.map_mem_nhd_singletonCompact q))
    |>.congr_of_eventuallyEq (liftFun_eventuallyEq hcl hrel _ (F'.map_mem_nhd_singletonCompact q))

/-- **The lift `g̃ : Ñ → M̃`** as an analytic map. -/
def lift : AnalyticMap F'.space F.space :=
  ⟨liftFun hcl hrel, (isLocalDiffeomorph_liftFun hcl hrel).contMDiff⟩

theorem coe_lift : ⇑(lift hcl hrel) = liftFun hcl hrel := rfl

/-- The lift is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_lift : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (lift hcl hrel) :=
  isLocalDiffeomorph_liftFun hcl hrel

/-- **The lift is over `g`**: `F.map ∘ g̃ = g ∘ F'.map`. -/
theorem map_lift (q : F'.space) : F.map (lift hcl hrel q) = g (F'.map q) := by
  change F.map (liftFun hcl hrel q) = _
  rw [liftFun_eq_pieceFun hcl hrel (F'.map_mem_nhd_singletonCompact q),
    map_pieceFun hcl hrel (F'.map_mem_nhd_singletonCompact q)]

/-- **The lift is bijective on the fibres**: it maps the fibre of `F'.map` over `y` bijectively
onto the fibre of `F.map` over `g y`. -/
theorem bijOn_fiber_lift (y : N) :
    BijOn (lift hcl hrel) (⇑F'.map ⁻¹' {y}) (⇑F.map ⁻¹' {g y}) := by
  have hy : y ∈ F'.nhd (singletonCompact y) := F'.subset_nhd _ (mem_singleton y)
  exact (bijOn_fiber_pieceFun hcl hrel (singletonCompact y) ⟨y, hy⟩).congr fun q hq =>
    (liftFun_eq_pieceFun hcl hrel (by rw [mem_singleton_iff.mp hq]; exact hy)).symm

/-- **The lift is the only continuous map over `g`.** -/
theorem eq_lift_of_map_eq {φ : F'.space → F.space} (hφ : Continuous φ)
    (hmap : ∀ q, F.map (φ q) = g (F'.map q)) : φ = lift hcl hrel :=
  funext fun q =>
    eqOn_of_map_eq hcl hrel isOpen_univ hφ.continuousOn
      (lift hcl hrel).contMDiff.continuous.continuousOn (fun q _ => hmap q)
      (fun q _ => map_lift hcl hrel q) (mem_univ q)

end Pieces

end ExtensionCompatibleFamily

/-! ### The lift clause for an assignment on pairs, and its consequences -/

section Assignment

/-- A map `g'` over `g` which is bijective on the fibres is, over a set `W` on which `g` is
injective, a bijection from the preimage of `W` onto the preimage of `g(W)`: the identification of
`Ñ` with the fibre product `N ×_M M̃` over `W`. -/
theorem bijOn_preimage_of_bijOn_fiber {X X' Y Y' : Type*} {π : X' → X} {π' : Y' → Y} {g : Y → X}
    {g' : Y' → X'} (hmap : ∀ q, π (g' q) = g (π' q))
    (hbij : ∀ y, BijOn g' (π' ⁻¹' {y}) (π ⁻¹' {g y})) {W : Set Y} (hW : InjOn g W) :
    BijOn g' (π' ⁻¹' W) (π ⁻¹' (g '' W)) := by
  refine ⟨fun q hq => ⟨π' q, hq, (hmap q).symm⟩, fun q₁ hq₁ q₂ hq₂ h => ?_, fun p hp => ?_⟩
  · have hy : π' q₁ = π' q₂ := hW hq₁ hq₂ (by rw [← hmap, ← hmap, h])
    exact (hbij (π' q₁)).injOn rfl hy.symm h
  · obtain ⟨y, hyW, hy⟩ := hp
    obtain ⟨q, hq, hgq⟩ := (hbij y).surjOn (show p ∈ π ⁻¹' {g y} by rw [mem_preimage, hy]; rfl)
    exact ⟨q, by rw [mem_preimage, mem_singleton_iff.mp hq]; exact hyW, hgq⟩

/-- A map over a surjective `g` which is bijective on the fibres is surjective. -/
theorem surjective_of_bijOn_fiber {X X' Y Y' : Type*} {π : X' → X} {π' : Y' → Y} {g : Y → X}
    {g' : Y' → X'} (hbij : ∀ y, BijOn g' (π' ⁻¹' {y}) (π ⁻¹' {g y})) (hg : Function.Surjective g) :
    Function.Surjective g' := fun p => by
  obtain ⟨y, hy⟩ := hg (π p)
  obtain ⟨q, -, hq⟩ := (hbij y).surjOn (show p ∈ π ⁻¹' {g y} by rw [mem_preimage, hy]; rfl)
  exact ⟨q, hq⟩

namespace IdealSheafPair

/-- **An assignment on the pairs whose successions pull back along local analytic isomorphisms
lifts them**, provided the neighbourhoods of its values have compact closures:
`IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms` from its first clause, the lift
`ExtensionCompatibleFamily.lift` of the two families `P(N, g^*I)` and `P(M, I)` with its
properties supplying the second. -/
theorem commutesWithLocalAnalyticIsomorphisms_of_isPullbackUpToEmptyAlong
    (P : CompatibleFamilyAssignment (IdealSheafPair.{u, v} 𝕜))
    (hP : ∀ (T : IdealSheafPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E} (g : AnalyticMap N T.M)
      (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g),
      (P (T.pullback g hg)).IsPullbackAlong (P T) g)
    (hcl : ∀ (T : IdealSheafPair.{u, v} 𝕜) (K : Compacts T.M),
      IsCompact (closure ((P T).nhd K : Set T.M))) :
    CommutesWithLocalAnalyticIsomorphisms P where
  isPullbackAlong := hP
  exists_lift T _ g hg :=
    have hcl' := hcl (T.pullback g hg)
    have hrel := hP T g hg
    ⟨ExtensionCompatibleFamily.lift hcl' hrel, ExtensionCompatibleFamily.map_lift hcl' hrel,
      ExtensionCompatibleFamily.isLocalDiffeomorph_lift hcl' hrel,
      ExtensionCompatibleFamily.bijOn_fiber_lift hcl' hrel,
      fun _ hφ hm => ExtensionCompatibleFamily.eq_lift_of_map_eq hcl' hrel hφ hm⟩

namespace CommutesWithLocalAnalyticIsomorphisms

variable {P : CompatibleFamilyAssignment (IdealSheafPair.{u, v} 𝕜)}
  (hP : CommutesWithLocalAnalyticIsomorphisms P)
include hP

/-- **The lift clause at a pair given by its ideal sheaf**: for a local analytic isomorphism
`g : N → M` and an ideal sheaf `J` on `N` with `J = g^*I`, the lift exists from the space of the
pair `(N, J)`. The form in which the lift of a composite `g ∘ h` is applied to the pair of
`h^*(g^*I)` without rewriting `(g ∘ h)^*I`. -/
theorem exists_lift_of_eq (T : IdealSheafPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E}
    (g : AnalyticMap N T.M) (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g)
    (J : IdealSheaf N) (hJ : J = T.I.pullback g g.contMDiff) (hJ₀ : J.IsNonzeroEverywhere) :
    ∃ g' : AnalyticMap (P ⟨T.E, N, J, hJ₀⟩).space (P T).space,
      (∀ q, (P T).map (g' q) = g ((P ⟨T.E, N, J, hJ₀⟩).map q)) ∧
      IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g' ∧
      (∀ y : N, Set.BijOn g' ((P ⟨T.E, N, J, hJ₀⟩).map ⁻¹' {y}) ((P T).map ⁻¹' {g y})) ∧
      ∀ φ : (P ⟨T.E, N, J, hJ₀⟩).space → (P T).space, Continuous φ →
        (∀ q, (P T).map (φ q) = g ((P ⟨T.E, N, J, hJ₀⟩).map q)) → φ = g' := by
  subst hJ
  exact hP.exists_lift T g hg

/-- **Naturality under composition**: for local analytic isomorphisms `g : N → M` and `h : L → N`,
every continuous map `k` from the space of `P(L, h^*(g^*I))` to the space of `P(M, I)` over
`g ∘ h` is the composite `g' ∘ h'` of maps `g'`, `h'` over `g` and `h`; in particular the lift of
`g ∘ h` is the composite of the lifts. From the uniqueness clause at `g ∘ h`, whose pulled-back
ideal sheaf is `h^*(g^*I)` (`exists_lift_of_eq`). -/
theorem comp_eq (T : IdealSheafPair.{u, v} 𝕜) {N L : AnalyticManifold.{u} 𝕜 T.E}
    (g : AnalyticMap N T.M) (h : AnalyticMap L N)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω h)
    {g' : (P (T.pullback g hg)).space → (P T).space} (hg'c : Continuous g')
    (hg' : ∀ q, (P T).map (g' q) = g ((P (T.pullback g hg)).map q))
    {h' : (P ((T.pullback g hg).pullback h hh)).space → (P (T.pullback g hg)).space}
    (hh'c : Continuous h')
    (hh' : ∀ q, (P (T.pullback g hg)).map (h' q) = h ((P ((T.pullback g hg).pullback h hh)).map q))
    {k : (P ((T.pullback g hg).pullback h hh)).space → (P T).space} (hk : Continuous k)
    (hkmap : ∀ q, (P T).map (k q) = g (h ((P ((T.pullback g hg).pullback h hh)).map q))) :
    k = g' ∘ h' := by
  have hgh : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω (g.comp h) := fun x =>
    IsLocalDiffeomorphAt.comp (hf := hh x) (hg := hg (h x))
  obtain ⟨k₀, -, -, -, huniq⟩ := hP.exists_lift_of_eq T (g.comp h) hgh
    ((T.I.pullback g g.contMDiff).pullback h h.contMDiff)
    (Manifold.IdealSheaf.pullback_pullback T.I g g.contMDiff h h.contMDiff)
    ((T.pullback g hg).pullback h hh).isNonzeroEverywhere
  rw [huniq k hk hkmap, huniq (g' ∘ h') (hg'c.comp hh'c) fun q => by
    rw [Function.comp_apply, hg', hh']
    rfl]

/-- **The lift of the identity is the identity**: every continuous map from the space of `P(M, I)`
to itself over the identity of `M` is the identity. -/
theorem id_eq (T : IdealSheafPair.{u, v} 𝕜) {k : (P T).space → (P T).space} (hk : Continuous k)
    (hkmap : ∀ q, (P T).map (k q) = (P T).map q) : k = id := by
  have hid : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω (ContMDiffMap.id : AnalyticMap T.M T.M) :=
    (Diffeomorph.refl 𝓘(𝕜, T.E) T.M ω).isLocalDiffeomorph
  obtain ⟨k₀, -, -, -, huniq⟩ := hP.exists_lift_of_eq T ContMDiffMap.id hid T.I
    (Manifold.IdealSheaf.pullback_id_eq_self T.I).symm T.isNonzeroEverywhere
  rw [huniq k hk hkmap, huniq id continuous_id fun _ => rfl]

end CommutesWithLocalAnalyticIsomorphisms

end IdealSheafPair

end Assignment

end AnalyticManifold

end

end
