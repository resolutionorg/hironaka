/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Manifold.FiniteSuccession.Functor.Pushforward
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.Fields
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The push-forward of a list of centres commutes with pull-back along a local analytic isomorphism

In the proof of [Kol07, Lemma 102] one pulls back by `h`, restricts to `h⁻¹(Eʲ) = Eʲ`, and pulls
back by `h|_{h⁻¹Eʲ}`: the push-forward of a blow-up sequence of a closed submanifold `S ⊆ M`
(`BlowUpSequence.pushforward`, [Kol07, Definition 30, 30.3]) pulled back along a local analytic
isomorphism `g : N → M` is the push-forward, from `g⁻¹(S) ⊆ N`, of the sequence pulled back along
the restricted local isomorphism `g|_{g⁻¹S} : g⁻¹S → S`:

* `IsClosedSubmanifold.restrictInvFunOfPreimage`, `restrictPartialDiffeomorphOfPreimage`,
  **`IsClosedSubmanifold.isLocalDiffeomorph_restrictMap`**, `surjective_restrictMap`: the
  restricted map is a local analytic isomorphism between the bundled submanifolds, surjective
  when `g` is (the codimension-one lemmas of
  `Hironaka.Resolution.Analytic.OrderReduction.Functoriality`, at any codimension `s`);
* `PushforwardStage.IsPullbackStage P P' G gᵢ`, the invariant of the induction: a local
  isomorphism `G : P'.space → P.space` of ambient stages with `P'.sub = G⁻¹(P.sub)` and the square
  `P.incl ∘ gᵢ = G ∘ P'.incl`; `IsPullbackStage.preimage_imageVal` (the pulled-back pushed centre
  is the pushed pulled-back centre), and the step `isPullbackStage_blowUpStep`: the invariant
  propagates through `blowUpStep` along the lift `stepMap` of `G` (`liftStep` composed with the
  identification of the two blow-ups of the same centre), the next square by uniqueness of lifts
  on the dense complement of the exceptional divisor, the next `sub`-identity by
  `strictTransformSet` being the closure of a preimage under the open map `stepMap`;
* **`BlowUpSequence.pushforward_pullback`**: the statement above, by induction on the list through
  `pushforwardAux_pullback` (any pair of stages with the invariant; `cons_congr_heq` and
  `heq_pullback_of_heq` identify the two `cons` whose centres are propositionally equal).

This is used to show that the functors built by descent commute with local isomorphisms.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The restricted map at any codimension -/

section RestrictMap

variable {M N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold ψ S s)

open scoped Classical in
/-- `BD.restrictInvFunOfPreimage` at any codimension (as in the proof of
[Kol07, Lemma 102]): the local inverse `Ψ` of `h` read on the bundled submanifolds. -/
def IsClosedSubmanifold.restrictInvFunOfPreimage (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω)
    (hΨ : Set.EqOn h Ψ Ψ.source) (p₀ : (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold)
    (y : hS.toAnalyticManifold) : (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold :=
  if hy : (y : S).1 ∈ Ψ.target then
    ⟨Ψ.invFun (y : S).1, by
      change h (Ψ.invFun (y : S).1) ∈ S
      have hm : Ψ.invFun (y : S).1 ∈ Ψ.source := Ψ.map_target hy
      rw [(hΨ hm).trans (Ψ.right_inv hy)]
      exact (y : S).2⟩
  else p₀

/-- The value of `restrictInvFunOfPreimage` on the target of `Ψ`. -/
theorem IsClosedSubmanifold.restrictInvFunOfPreimage_of_mem
    (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω) (hΨ : Set.EqOn h Ψ Ψ.source)
    (p₀ : (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold) {y : hS.toAnalyticManifold}
    (hy : (y : S).1 ∈ Ψ.target) :
    IsClosedSubmanifold.restrictInvFunOfPreimage h hh hS Ψ hΨ p₀ y =
      ⟨Ψ.invFun (y : S).1, by
        change h (Ψ.invFun (y : S).1) ∈ S
        have hm : Ψ.invFun (y : S).1 ∈ Ψ.source := Ψ.map_target hy
        rw [(hΨ hm).trans (Ψ.right_inv hy)]
        exact (y : S).2⟩ := by
  unfold IsClosedSubmanifold.restrictInvFunOfPreimage
  exact dite_eq_left hy

/-- `BD.restrictPartialDiffeomorphOfPreimage` at any codimension: a local
inverse of `h` restricted to the bundled submanifolds `h⁻¹(S)` and `S` is a partial diffeomorphism
agreeing with the restricted map on `h⁻¹(S) ∩ Ψ.source`. -/
def IsClosedSubmanifold.restrictPartialDiffeomorphOfPreimage
    (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω) (hΨ : Set.EqOn h Ψ Ψ.source)
    (p₀ : (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold) :
    PartialDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜)
      (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold hS.toAnalyticManifold ω where
  toFun := (hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff fun _ hx => hx
  invFun := IsClosedSubmanifold.restrictInvFunOfPreimage h hh hS Ψ hΨ p₀
  source := {p | (p : ⇑h ⁻¹' S).1 ∈ Ψ.source}
  target := {y | (y : S).1 ∈ Ψ.target}
  map_source' p hp := by
    change h (p : ⇑h ⁻¹' S).1 ∈ Ψ.target
    rw [hΨ hp]
    exact Ψ.map_source hp
  map_target' y hy := by
    change (IsClosedSubmanifold.restrictInvFunOfPreimage h hh hS Ψ hΨ p₀ y : ⇑h ⁻¹' S).1 ∈
      Ψ.source
    rw [IsClosedSubmanifold.restrictInvFunOfPreimage_of_mem h hh hS Ψ hΨ p₀ hy]
    exact Ψ.map_target hy
  left_inv' p hp := by
    have hc : h (p : ⇑h ⁻¹' S).1 ∈ Ψ.target := by
      rw [hΨ hp]
      exact Ψ.map_source hp
    apply Subtype.ext
    change (IsClosedSubmanifold.restrictInvFunOfPreimage h hh hS Ψ hΨ p₀
      (((hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff fun _ hx => hx) p) :
        ⇑h ⁻¹' S).1 = (p : ⇑h ⁻¹' S).1
    rw [IsClosedSubmanifold.restrictInvFunOfPreimage_of_mem h hh hS Ψ hΨ p₀ hc]
    change Ψ.invFun (h (p : ⇑h ⁻¹' S).1) = (p : ⇑h ⁻¹' S).1
    rw [hΨ hp]
    exact Ψ.left_inv hp
  right_inv' y hy := by
    apply Subtype.ext
    change (((hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff fun _ hx => hx)
      (IsClosedSubmanifold.restrictInvFunOfPreimage h hh hS Ψ hΨ p₀ y) : S).1 = (y : S).1
    rw [IsClosedSubmanifold.restrictInvFunOfPreimage_of_mem h hh hS Ψ hΨ p₀ hy]
    change h (Ψ.invFun (y : S).1) = (y : S).1
    have hm : Ψ.invFun (y : S).1 ∈ Ψ.source := Ψ.map_target hy
    exact (hΨ hm).trans (Ψ.right_inv hy)
  open_source := Ψ.open_source.preimage continuous_subtype_val
  open_target := Ψ.open_target.preimage continuous_subtype_val
  contMDiffOn_toFun :=
    ((hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff
      fun _ hx => hx).contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    intro y hy
    have hT : IsOpen {y : hS.toAnalyticManifold | (y : S).1 ∈ Ψ.target} :=
      Ψ.open_target.preimage continuous_subtype_val
    refine ContMDiffAt.contMDiffWithinAt ?_
    refine (hS.preimage_of_isLocalDiffeomorph hh).contMDiffAt_of_val ?_
    have hev : (Subtype.val ∘ IsClosedSubmanifold.restrictInvFunOfPreimage h hh hS Ψ hΨ p₀) =ᶠ[𝓝 y]
        fun z : hS.toAnalyticManifold => Ψ.invFun (z : S).1 := by
      filter_upwards [hT.mem_nhds hy] with z hz
      change (IsClosedSubmanifold.restrictInvFunOfPreimage h hh hS Ψ hΨ p₀ z : ⇑h ⁻¹' S).1 =
        Ψ.invFun (z : S).1
      rw [IsClosedSubmanifold.restrictInvFunOfPreimage_of_mem h hh hS Ψ hΨ p₀ hz]
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
    exact (Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds hy)).comp y
      (hS.contMDiff_val y)

/-- `BD.isLocalDiffeomorph_restrictMap` at any codimension (the proof of [Kol07, Lemma 102]
"`h|_{E^j_Y}` is also a smooth surjection"): the restriction of a local analytic
isomorphism to the preimage of a closed submanifold is a local analytic isomorphism between the
bundled submanifolds. -/
theorem IsClosedSubmanifold.isLocalDiffeomorph_restrictMap :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω
      ((hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff fun _ hx => hx) := by
  intro p
  obtain ⟨Ψ, hpΨ, hΨ⟩ := (hh (p : ⇑h ⁻¹' S).1).exists_partialDiffeomorph
  exact IsLocalDiffeomorphAt.of_eqOn
    (IsClosedSubmanifold.restrictPartialDiffeomorphOfPreimage h hh hS Ψ hΨ p) hpΨ fun _ _ => rfl

/-- `BD.surjective_restrictMap` at any codimension: the restriction of a surjection to
the preimage of a submanifold is a surjection onto the submanifold. -/
theorem IsClosedSubmanifold.surjective_restrictMap (hS' : IsClosedSubmanifold ψ (⇑h ⁻¹' S) s)
    (hs : Function.Surjective h) :
    Function.Surjective (hS'.restrictMap hS h h.contMDiff fun _ hx => hx) := by
  intro q
  obtain ⟨x, hx⟩ := hs (q : S).1
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change h x ∈ S
  rw [hx]
  exact (q : S).2

end RestrictMap

/-- A chosen blowing-up along a set propositionally equal to `Y` is a blowing-up with centre
`Y`. -/
theorem isBlowUp_blowUpπ_of_eq {M : AnalyticManifold.{u} 𝕜 E} {Y Y' : Set M} {c : ℕ} (e : Y' = Y)
    (hY' : IsClosedSubmanifold ψ Y' c) : IsBlowUp ψ Y c (blowUpπ ψ hY') := by
  subst e
  exact isBlowUp_blowUpπ ψ hY'

/-- The lift of `h` from a blowing-up of a centre propositionally equal to `h⁻¹(Y)`, through the
identification of the two blowings-up, is heterogeneously the lift `liftStep`. -/
theorem heq_liftStep_comp_diffeomorph {M N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) {Y' : Set N} (hY' : IsClosedSubmanifold ψ Y' c)
    (e : Y' = ⇑h ⁻¹' Y) :
    HEq (AnalyticManifold.BlowUpSequence.liftStep h hh hY)
      ((AnalyticManifold.BlowUpSequence.liftStep h hh hY).comp (Diffeomorph.toAnalyticMap
        (IsBlowUp.diffeomorph (hY.preimage_of_isLocalDiffeomorph hh) (isBlowUp_blowUpπ_of_eq e hY')
          (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))))) := by
  subst e
  refine heq_of_eq (ContMDiffMap.ext fun p => ?_)
  change AnalyticManifold.BlowUpSequence.liftStep h hh hY p =
    AnalyticManifold.BlowUpSequence.liftStep h hh hY (IsBlowUp.diffeomorph
        (hY.preimage_of_isLocalDiffeomorph hh) _ _ p)
  congr 1
  exact ((isBlowUp_blowUpπ ψ hY').eqOn_of_comp_eq (hY.preimage_of_isLocalDiffeomorph hh)
    (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh)) isOpen_univ
    (IsBlowUp.diffeomorph _ _ _).continuous.continuousOn continuous_id.continuousOn
    (fun q _ => blowDown_liftPoint _ _ _ q) (fun _ _ => rfl) (Set.mem_univ p)).symm

namespace PushforwardStage

variable {s : ℕ} {Tᵢ Tᵢ' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}

/-! ### The invariant -/

/-- The invariant of the induction in the proof of [Kol07, Lemma 102], at one stage: `G : P'.space
→ P.space` is a local analytic isomorphism of the ambient stages under which the strict transform
`P'.sub` is the preimage of `P.sub` and the inclusions of the bundled stages commute with `gᵢ : Tᵢ'
→ Tᵢ`. -/
structure IsPullbackStage (P : PushforwardStage ψ s Tᵢ) (P' : PushforwardStage ψ s Tᵢ')
    (G : AnalyticMap P'.space P.space) (gᵢ : AnalyticMap Tᵢ' Tᵢ) : Prop where
  isLocalDiffeomorph : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω G
  sub_eq : P'.sub = ⇑G ⁻¹' P.sub
  square : ∀ q, P.incl (gᵢ q) = G (P'.incl q)

variable {P : PushforwardStage ψ s Tᵢ} {P' : PushforwardStage ψ s Tᵢ'}
  {G : AnalyticMap P'.space P.space} {gᵢ : AnalyticMap Tᵢ' Tᵢ}

/-- The pull-back along `G` of the pushed-forward centre `(j_i)_* Z` is the pushed-forward
pulled-back centre `(j_i')_* (gᵢ⁻¹ Z)`. -/
theorem IsPullbackStage.preimage_imageVal (h : IsPullbackStage P P' G gᵢ) (Z : Set Tᵢ) :
    ⇑G ⁻¹' (P.isClosedSubmanifold.imageVal (P.iso '' Z)) =
      P'.isClosedSubmanifold.imageVal (P'.iso '' (⇑gᵢ ⁻¹' Z)) := by
  rw [P.imageVal_image_eq, P'.imageVal_image_eq]
  ext x
  constructor
  · rintro ⟨z, hz, hGx⟩
    have hx : x ∈ P'.sub := by
      rw [h.sub_eq]
      change G x ∈ P.sub
      rw [← P.range_incl]
      exact ⟨z, hGx⟩
    rw [← P'.range_incl] at hx
    obtain ⟨q, rfl⟩ := hx
    refine ⟨q, ?_, rfl⟩
    change gᵢ q ∈ Z
    have : P.incl (gᵢ q) = P.incl z := by rw [h.square, hGx]
    rwa [P.isClosedEmbedding_incl.injective this]
  · rintro ⟨q, hq, rfl⟩
    exact ⟨gᵢ q, hq, h.square q⟩

/-! ### The step -/

section Step

variable (h : IsPullbackStage P P' G gᵢ)
  (hgᵢ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω gᵢ) {Z : Set Tᵢ} {c : ℕ}
  (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)

/-- The identification of the blowing-up of `P'.space` along the pushed pulled-back centre with the
blowing-up along the pulled-back pushed centre (the same set, `preimage_imageVal`). -/
def stepIso :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E)
      (blowUp ψ (P'.isClosedSubmanifold_imageVal_image (hZ.preimage_of_isLocalDiffeomorph hgᵢ)))
      (blowUp ψ ((P.isClosedSubmanifold_imageVal_image hZ).preimage_of_isLocalDiffeomorph
        h.isLocalDiffeomorph)) ω :=
  IsBlowUp.diffeomorph
    ((P.isClosedSubmanifold_imageVal_image hZ).preimage_of_isLocalDiffeomorph h.isLocalDiffeomorph)
    (isBlowUp_blowUpπ_of_eq (h.preimage_imageVal Z).symm _) (isBlowUp_blowUpπ ψ _)

theorem blowUpπ_stepIso (p) :
    blowUpπ ψ ((P.isClosedSubmanifold_imageVal_image hZ).preimage_of_isLocalDiffeomorph
        h.isLocalDiffeomorph) (stepIso h hgᵢ hZ p) =
      blowUpπ ψ (P'.isClosedSubmanifold_imageVal_image (hZ.preimage_of_isLocalDiffeomorph hgᵢ)) p :=
  blowDown_liftPoint _ _ _ p

/-- The lift of `G` to the next stages: `liftStep` after the identification `stepIso`. -/
def stepMap :
    AnalyticMap
      (blowUp ψ (P'.isClosedSubmanifold_imageVal_image (hZ.preimage_of_isLocalDiffeomorph hgᵢ)))
      (blowUp ψ (P.isClosedSubmanifold_imageVal_image hZ)) :=
  (AnalyticManifold.BlowUpSequence.liftStep G h.isLocalDiffeomorph
      (P.isClosedSubmanifold_imageVal_image hZ)).comp
    (Diffeomorph.toAnalyticMap (stepIso h hgᵢ hZ))

theorem isLocalDiffeomorph_stepMap :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (stepMap h hgᵢ hZ) :=
  AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep G h.isLocalDiffeomorph _)
    (stepIso h hgᵢ hZ).isLocalDiffeomorph

/-- The lift lies over `G`. -/
theorem blowUpπ_stepMap (p) :
    blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ) (stepMap h hgᵢ hZ p) =
      G (blowUpπ ψ (P'.isClosedSubmanifold_imageVal_image (hZ.preimage_of_isLocalDiffeomorph hgᵢ))
        p) := by
  change blowUpπ ψ _ (AnalyticManifold.BlowUpSequence.liftStep G h.isLocalDiffeomorph _
      (stepIso h hgᵢ hZ p)) = _
  rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep, blowUpπ_stepIso]

/-- The blow-down of a pushed-forward point is the push-forward of its blow-down
(`restrictMap_blowUpStep_iso` read through the inclusions). -/
theorem blowUpπ_incl_blowUpStep (P : PushforwardStage ψ s Tᵢ)
    (hZ : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z c)
    (p : blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) hZ) :
    blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ)
        ((P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)).incl p) =
      P.incl (blowUpπ (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) hZ p) :=
  congrArg Subtype.val (P.restrictMap_blowUpStep_iso hZ (isBlowUp_blowUpπ _ hZ) p)

/-- The next square: the two lifts of the inclusions agree, by uniqueness of lifts on the dense
complement of the exceptional divisor. -/
theorem incl_blowUpStep_liftStep (q) :
    (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)).incl (AnalyticManifold.BlowUpSequence.liftStep gᵢ hgᵢ
        hZ q) =
      stepMap h hgᵢ hZ ((P'.blowUpStep (hZ.preimage_of_isLocalDiffeomorph hgᵢ)
        (isBlowUp_blowUpπ _ _)).incl q) := by
  -- both maps blow down to `P.incl ∘ gᵢ ∘ π'`
  have hπ₁ : ∀ q, blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ)
      ((P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)).incl (AnalyticManifold.BlowUpSequence.liftStep gᵢ
          hgᵢ hZ q)) =
      P.incl (gᵢ (blowUpπ _ (hZ.preimage_of_isLocalDiffeomorph hgᵢ) q)) := by
    intro q
    rw [blowUpπ_incl_blowUpStep, AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]
  have hπ₂ : ∀ q, blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ)
      (stepMap h hgᵢ hZ ((P'.blowUpStep (hZ.preimage_of_isLocalDiffeomorph hgᵢ)
          (isBlowUp_blowUpπ _ _)).incl q)) =
      P.incl (gᵢ (blowUpπ _ (hZ.preimage_of_isLocalDiffeomorph hgᵢ) q)) := by
    intro q
    exact (blowUpπ_stepMap h hgᵢ hZ _).trans
      ((congrArg G (blowUpπ_incl_blowUpStep P' (hZ.preimage_of_isLocalDiffeomorph hgᵢ)
          q)).trans (h.square _).symm)
  have hdense : Dense (⇑(blowUpπ _ (hZ.preimage_of_isLocalDiffeomorph hgᵢ)) ⁻¹' (⇑gᵢ ⁻¹' Z)ᶜ) :=
    (isBlowUp_blowUpπ _ (hZ.preimage_of_isLocalDiffeomorph hgᵢ)).dense_preimage_compl
        (hZ.preimage_of_isLocalDiffeomorph hgᵢ)
  have hcont₁ : Continuous fun q : blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (hZ.preimage_of_isLocalDiffeomorph hgᵢ) =>
      (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)).incl (AnalyticManifold.BlowUpSequence.liftStep gᵢ
          hgᵢ hZ q) :=
    (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ)).incl.contMDiff.continuous.comp
      (AnalyticManifold.BlowUpSequence.liftStep gᵢ hgᵢ hZ).contMDiff.continuous
  have hcont₂ : Continuous fun q : blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (hZ.preimage_of_isLocalDiffeomorph hgᵢ) =>
      stepMap h hgᵢ hZ ((P'.blowUpStep (hZ.preimage_of_isLocalDiffeomorph hgᵢ)
          (isBlowUp_blowUpπ _ _)).incl q) :=
    (stepMap h hgᵢ hZ).contMDiff.continuous.comp
      (P'.blowUpStep (hZ.preimage_of_isLocalDiffeomorph hgᵢ) (isBlowUp_blowUpπ _
          _)).incl.contMDiff.continuous
  refine congrFun (Continuous.ext_on hdense hcont₁ hcont₂ fun q hq => ?_) q
  have hnot : P.incl (gᵢ (blowUpπ _ (hZ.preimage_of_isLocalDiffeomorph hgᵢ) q)) ∉
      P.isClosedSubmanifold.imageVal (P.iso '' Z) := by
    rw [P.imageVal_image_eq]
    rintro ⟨z, hz, hzq⟩
    exact hq (by
      change gᵢ (blowUpπ _ (hZ.preimage_of_isLocalDiffeomorph hgᵢ) q) ∈ Z
      rw [← P.isClosedEmbedding_incl.injective hzq]
      exact hz)
  refine (isBlowUp_blowUpπ ψ (P.isClosedSubmanifold_imageVal_image hZ)).bijOn_compl.injOn ?_ ?_
    ((hπ₁ q).trans (hπ₂ q).symm)
  · change blowUpπ ψ _ _ ∉ _
    rw [hπ₁ q]
    exact hnot
  · change blowUpπ ψ _ _ ∉ _
    rw [hπ₂ q]
    exact hnot

/-- The invariant propagates through one blow-up step. -/
theorem isPullbackStage_blowUpStep :
    IsPullbackStage (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
      (P'.blowUpStep (hZ.preimage_of_isLocalDiffeomorph hgᵢ) (isBlowUp_blowUpπ _ _))
      (stepMap h hgᵢ hZ) (AnalyticManifold.BlowUpSequence.liftStep gᵢ hgᵢ hZ) where
  isLocalDiffeomorph := isLocalDiffeomorph_stepMap h hgᵢ hZ
  sub_eq := by
    change strictTransformSet _ _ P'.sub = ⇑(stepMap h hgᵢ hZ) ⁻¹' strictTransformSet _ _ P.sub
    unfold strictTransformSet
    rw [(isLocalDiffeomorph_stepMap h hgᵢ hZ).isOpenMap.preimage_closure_eq_closure_preimage
      (stepMap h hgᵢ hZ).contMDiff.continuous]
    congr 1
    ext p
    simp only [Set.mem_preimage, Set.mem_sdiff, blowUpπ_stepMap, h.sub_eq,
      ← h.preimage_imageVal Z]
  square := incl_blowUpStep_liftStep h hgᵢ hZ

end Step

/-! ### The induction -/

/-- The induction of the proof of [Kol07, Lemma 102] on lists, from any pair of stages with the
invariant:
the pull-back along `G` of the push-forward of `L` is the push-forward of the pull-back of `L`
along `gᵢ`. -/
theorem pushforwardAux_pullback :
    ∀ {Tᵢ Tᵢ' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} (P : PushforwardStage ψ s Tᵢ)
      (P' : PushforwardStage ψ s Tᵢ') (G : AnalyticMap P'.space P.space) (gᵢ : AnalyticMap Tᵢ' Tᵢ)
      (hgᵢ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω gᵢ)
      (h : IsPullbackStage P P' G gᵢ)
      (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Tᵢ),
      (AnalyticManifold.BlowUpSequence.pushforwardAux P L).pullback G h.isLocalDiffeomorph =
        AnalyticManifold.BlowUpSequence.pushforwardAux P' (L.pullback gᵢ hgᵢ)
  | _, _, _, _, _, _, _, _, AnalyticManifold.BlowUpSequence.nil _ => rfl
  | _, _, P, P', G, gᵢ, hgᵢ, h, @AnalyticManifold.BlowUpSequence.cons _ _ _ _ _ _ _ _ Z c hZ rest
      => by
    change AnalyticManifold.BlowUpSequence.cons
        ((P.isClosedSubmanifold_imageVal_image hZ).preimage_of_isLocalDiffeomorph
          h.isLocalDiffeomorph)
        ((AnalyticManifold.BlowUpSequence.pushforwardAux (P.blowUpStep hZ
            (isBlowUp_blowUpπ _ hZ)) rest).pullback
          (AnalyticManifold.BlowUpSequence.liftStep G h.isLocalDiffeomorph _) _) =
      AnalyticManifold.BlowUpSequence.cons
        (P'.isClosedSubmanifold_imageVal_image (hZ.preimage_of_isLocalDiffeomorph hgᵢ))
        (AnalyticManifold.BlowUpSequence.pushforwardAux
          (P'.blowUpStep (hZ.preimage_of_isLocalDiffeomorph hgᵢ) (isBlowUp_blowUpπ _ _))
          (rest.pullback (AnalyticManifold.BlowUpSequence.liftStep gᵢ hgᵢ hZ) _))
    refine AnalyticManifold.BlowUpSequence.cons_congr_heq (h.preimage_imageVal Z) _ _ _ _ ?_
    refine HEq.trans ?_ (heq_of_eq (pushforwardAux_pullback
      (P.blowUpStep hZ (isBlowUp_blowUpπ _ hZ))
      (P'.blowUpStep (hZ.preimage_of_isLocalDiffeomorph hgᵢ) (isBlowUp_blowUpπ _ _))
      (stepMap h hgᵢ hZ) (AnalyticManifold.BlowUpSequence.liftStep gᵢ hgᵢ hZ)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep gᵢ hgᵢ hZ)
          (isPullbackStage_blowUpStep h hgᵢ hZ)
      rest))
    exact AnalyticManifold.BlowUpSequence.heq_pullback_of_heq (h.preimage_imageVal Z) _ _ _ _ _ _ _
      (heq_liftStep_comp_diffeomorph G h.isLocalDiffeomorph
        (P.isClosedSubmanifold_imageVal_image hZ)
        (P'.isClosedSubmanifold_imageVal_image (hZ.preimage_of_isLocalDiffeomorph hgᵢ))
        (h.preimage_imageVal Z).symm)

end PushforwardStage

/-! ### The statement -/

/-- **The push-forward along a closed submanifold ([Kol07, Definition 30, 30.3]) commutes with
pull-back along a local analytic isomorphism** (the proof of [Kol07, Lemma 102]): for a closed
submanifold `hS : IsClosedSubmanifold ψ S s`, a local analytic isomorphism `g : N → M` and a list
of centres `L` on the bundled `S`, the pull-back along `g` of the push-forward of `L` is the
push-forward, from `g⁻¹(S)`, of the pull-back of `L` along the restricted local isomorphism
`g|_{g⁻¹S}`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforward_pullback
    {M N : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}
    (hS : IsClosedSubmanifold ψ S s) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
        (n - s) → 𝕜)) hS.toAnalyticManifold) :
    (L.pushforward hS).pullback g hg =
      (L.pullback
        ((hS.preimage_of_isLocalDiffeomorph hg).restrictMap hS g g.contMDiff fun _ hx => hx)
        (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap g hg hS)).pushforward
        (hS.preimage_of_isLocalDiffeomorph hg) :=
  PushforwardStage.pushforwardAux_pullback
    (⟨M, S, hS, Diffeomorph.refl _ _ _⟩ : PushforwardStage ψ s hS.toAnalyticManifold)
    (⟨N, ⇑g ⁻¹' S, hS.preimage_of_isLocalDiffeomorph hg, Diffeomorph.refl _ _ _⟩ :
      PushforwardStage ψ s (hS.preimage_of_isLocalDiffeomorph hg).toAnalyticManifold)
    g _ _ ⟨hg, rfl, fun _ => rfl⟩ L

end Manifold

end
