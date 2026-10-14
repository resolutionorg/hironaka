/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeq
public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
public import Hironaka.Manifold.BlowUp.Transform.SaturationFiniteType
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.StrictSubspace
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The ideal-theoretic strict transforms along pull-backs and along the deletion of empty blow-ups

The independence of the local resolution of a piece from the chosen embedding
[Kol07, Theorem 36, proof] compares the final ideal-theoretic strict transforms
(`FiniteSuccession.strictTransformSubspaceSeq`) along the values of the embedded
desingularization functor for two embeddings. The comparison transports them along the sequences
that the functoriality clause of `IsEmbeddedDesing` (`CommutesWithLocalIsos`, the commutation with
smooth morphisms of [Kol07, 34.1]) produces: the pull-back along a local analytic isomorphism `g`
restricted onto its image, with the empty blow-ups deleted. This module proves the ideal-level
counterparts of the corresponding transports of the set-level strict transforms and of the weak
transforms:

* **(A)** `saturationStalk_congr`, `strictTransformSubspace_congr`: the strict transform
  `strictTransformSubspace` depends on the witnesses `hY : IsClosedSubmanifold ψ Y c`,
  `h : IsBlowUp ψ Y c π` only through the SET `Y` and the blow-down `π` (the ideal sheaf of a
  closed submanifold depends only on the set, `IsClosedSubmanifold.idealSheaf_congr`). A
  succession's witnesses `isClosedSubmanifold_center i` carry the chosen chart and codimension of
  its monoidality witness, so the constructor form of the recursion
  (`cons_strictTransformSubspaceSeqAux_succ`) is not `rfl` as it is for the weak transform (whose
  centre argument is the ideal sheaf itself); (A) bridges the two.
* **(B)** The pull-back of a blow-up sequence along a smooth morphism [Kol07, Definition 30.1] at
  the ideal level: along the lift `liftStep` of a SURJECTIVE local analytic isomorphism `h : N → M`
  to the blowings-up, the strict transform pulls back to the strict transform of the pull-back
  (`strictTransformSubspace_comap_liftStep`), then along a whole list (`BlowUpSequence.pullback`) in
  the ℕ-indexed, `Fin`-indexed and last-stage forms (`strictTransformSubspaceSeqAux_pullback`,
  `strictTransformSubspaceSeq_pullback`, `strictTransformSubspaceSeq_last_pullbackLiftLast`). The
  saturation stalks correspond under the bijective germ maps of the lift
  (`saturationStalk_comap_liftStep`: `Ideal.map_colon_pow_of_bijective`,
  `totalTransform_comap_liftStep`, `exceptionalIdealSheaf_comap_liftStep`); the two saturations
  take the same branch of the case distinction in `strictTransformSubspace`
  (`hasLocalGenerators_saturationStalk_comap_liftStep_iff`: local generators pull back,
  `hasLocalGenerators_pullback`, and descend along a surjective local isomorphism,
  `HasLocalGenerators.of_map_germMap_of_surjective`). The surjectivity of `h` is a hypothesis of
  the formalization forced by that sheaf-wide case distinction — a non-surjective `h` sees the
  branch on `N` while `M` may take the other branch off the image; the sources' statement is
  pointwise, and the map produced by the functoriality clause
  (`restrictMap g U' (imageOpens g hg U')`) is surjective.
* **(C)** Deleting the empty blow-ups [Kol07, 34.1]: the final strict transform along the cleaned
  list `L.eraseEmpty` is the pull-back along the isomorphism `eraseEmptyLast⁻¹` of the last stages
  of the one along `L` (`strictTransformSubspaceSeq_last_eraseEmpty`, the counterpart of
  `weakTransformSeq_last_eraseEmpty`): an empty blowing-up is an isomorphism whose exceptional
  ideal sheaf is the unit ideal, so its strict transform is the pull-back
  (`strictTransformSubspace_blowUpπ_of_eq_empty`); the two saturations are then isomorphic
  sheaves and take one branch.
* **(D)** `strictTransformSubspaceSeq_last_pullback_eraseEmpty`: (B) at the last stage composed
  with (C), the exact right-hand side that the functoriality clause produces.
* **(B′)** The surjectivity of `h` in (B) and (D) was needed only for the coincidence of the
  branches; since every saturation has local generators (`saturationStalk_hasLocalGenerators`,
  `SaturationFiniteType.lean`), the condition of the case distinction is a theorem for every
  centre, blow-up and ideal sheaf (`strictTransformSubspace_eq_ofStalks`), so the identities hold
  along ANY local analytic isomorphism, the open inclusions of Kollár's proof included. The
  unconditional forms `strictTransformSubspace_comap_liftStep'`,
  `strictTransformSubspaceSeqAux_pullback'`, `strictTransformSubspaceSeq_pullback'`,
  `strictTransformSubspaceSeq_last_pullbackLiftLast'`,
  `strictTransformSubspaceSeq_last_pullback_eraseEmpty'` stand beside the surjective ones.

The strict transform of a closed subspace is the saturation of its total transform by the
exceptional divisor [BM97, §3, Proposition 3.13]. Not in the sources; bookkeeping on the pull-back
and deletion transports of the `Functor` modules and on the saturation stalks.
-/

public section

noncomputable section

open TopologicalSpace Set AnalyticManifold
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### (A) The strict transform depends on its witnesses only through the set -/

section Congr

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- (A) The saturation stalks depend on the witnesses only through the centre set and the
blow-down: the total transform depends only on `π`, the exceptional ideal sheaf only on the set
(`IsClosedSubmanifold.idealSheaf_congr`). -/
theorem saturationStalk_congr {n n' c c' : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
    {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)} {Y Y' : Set M} (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hY' : IsClosedSubmanifold ψ' Y' c') (h' : IsBlowUp ψ' Y' c' π)
    (e : Y = Y') (I : Manifold.IdealSheaf (structureSheaf 𝕜 E M)) :
    saturationStalk hY h I = saturationStalk hY' h' I := by
  subst e
  have hE : hY.idealSheaf.pullback π h.contMDiff = hY'.idealSheaf.pullback π h'.contMDiff := by
    rw [hY.idealSheaf_congr hY' rfl]
  funext a'
  unfold saturationStalk
  rw [hE]

/-- (A) The strict transform `strictTransformSubspace` depends on the witnesses only through the
centre set and the blow-down. -/
theorem strictTransformSubspace_congr {n n' c c' : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
    {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)} {Y Y' : Set M} (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hY' : IsClosedSubmanifold ψ' Y' c') (h' : IsBlowUp ψ' Y' c' π)
    (e : Y = Y') (I : Manifold.IdealSheaf (structureSheaf 𝕜 E M)) :
    strictTransformSubspace hY h I = strictTransformSubspace hY' h' I := by
  unfold strictTransformSubspace
  rw [saturationStalk_congr hY h hY' h' e I]

end Congr

/-! ### (B′) The strict transform always takes its `ofStalks` branch -/

section EqOfStalks

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- (B′) The strict transform `strictTransformSubspace` ALWAYS takes its `ofStalks` branch: the
condition of its case distinction, that the saturation stalks have local generators, is a theorem
for every centre, blow-up and ideal sheaf (`saturationStalk_hasLocalGenerators`). -/
theorem strictTransformSubspace_eq_ofStalks (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (I : Manifold.IdealSheaf (structureSheaf 𝕜 E M)) :
    strictTransformSubspace hY h I =
      IdealSheaf.ofStalks _ _ (saturationStalk_hasLocalGenerators hY h I) := by
  rw [strictTransformSubspace, dite_eq_left (saturationStalk_hasLocalGenerators hY h I)]

end EqOfStalks

/-! ### (B) One step: the strict transform along the lift of a local isomorphism -/

section PullbackStep

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}
  (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
  (hY : IsClosedSubmanifold ψ Y c)

/-- (B) at the stalks: the saturation stalks of the pulled-back ideal sheaf along the pulled-back
blowing-up [Kol07, Definition 30.1] are the images of the saturation stalks under the bijective
germ maps of the lift `liftStep` — colons by powers transport along a ring isomorphism
(`Ideal.map_colon_pow_of_bijective`), the total transform and the exceptional ideal sheaf pull back
(`totalTransform_comap_liftStep`, `exceptionalIdealSheaf_comap_liftStep`). No surjectivity is
needed here. -/
theorem saturationStalk_comap_liftStep
    (J : AnalyticManifold.IdealSheaf M)
    (q : blowUp ψ (hY.preimage_of_isLocalDiffeomorph hh)) :
    saturationStalk (hY.preimage_of_isLocalDiffeomorph hh)
        (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
        (J.pullback h h.contMDiff) q =
      Ideal.map (germMap ⇑(BlowUpSequence.liftStep h hh hY) (BlowUpSequence.liftStep h hh
          hY).contMDiff q)
        (saturationStalk hY (isBlowUp_blowUpπ ψ hY) J (BlowUpSequence.liftStep h hh hY q)) := by
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt ⇑(BlowUpSequence.liftStep h hh hY)
    (BlowUpSequence.liftStep h hh hY).contMDiff (BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY
        q)
  unfold saturationStalk
  rw [Ideal.map_iSup]
  refine iSup_congr fun k => ?_
  rw [Ideal.map_colon_pow_of_bijective _ hbij, ← IdealSheaf.stalkIdeal_pullback,
    ← IdealSheaf.stalkIdeal_pullback, totalTransform_comap_liftStep h hh hY J,
    exceptionalIdealSheaf_comap_liftStep h hh hY]

/-- (B) For a SURJECTIVE `h` the two saturations take the same branch of the case distinction in
`strictTransformSubspace`: local generators pull back along the lift
(`hasLocalGenerators_pullback`) and descend along the surjective local isomorphism `liftStep`
(`HasLocalGenerators.of_map_germMap_of_surjective`). -/
theorem hasLocalGenerators_saturationStalk_comap_liftStep_iff
    (hs : Function.Surjective h) (J : AnalyticManifold.IdealSheaf M) :
    IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 E (blowUp ψ (hY.preimage_of_isLocalDiffeomorph hh)))
        (saturationStalk (hY.preimage_of_isLocalDiffeomorph hh)
          (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
          (J.pullback h h.contMDiff)) ↔
      IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E (blowUp ψ hY))
        (saturationStalk hY (isBlowUp_blowUpπ ψ hY) J) := by
  have hfun : saturationStalk (hY.preimage_of_isLocalDiffeomorph hh)
      (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
      (J.pullback h h.contMDiff) = fun q =>
        Ideal.map (germMap ⇑(BlowUpSequence.liftStep h hh hY)
            (BlowUpSequence.liftStep h hh hY).contMDiff q)
          (saturationStalk hY (isBlowUp_blowUpπ ψ hY) J (BlowUpSequence.liftStep h hh hY q)) :=
    funext (saturationStalk_comap_liftStep h hh hY J)
  rw [hfun]
  constructor
  · intro hN
    exact IdealSheaf.HasLocalGenerators.of_map_germMap_of_surjective
        (BlowUpSequence.liftStep h hh hY)
      (BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY) (BlowUpSequence.surjective_liftStep h hh
          hY hs)
      _ hN
  · intro hM
    have hpb := hasLocalGenerators_pullback ⇑(BlowUpSequence.liftStep h hh hY)
      (BlowUpSequence.liftStep h hh hY).contMDiff (IdealSheaf.ofStalks _ _ hM)
    simpa only [IdealSheaf.stalkIdeal_ofStalks] using hpb

/-- (B) The pull-back of a blow-up sequence [Kol07, Definition 30.1] at the ideal level, one
step: along the lift of a SURJECTIVE local analytic isomorphism the strict transform pulls back to
the strict transform of the pull-back — in the `then` branches by the stalk identity
`saturationStalk_comap_liftStep`, in the `else` branches by `⊤` pulling back to `⊤`, the branches
coinciding by `hasLocalGenerators_saturationStalk_comap_liftStep_iff`. -/
theorem strictTransformSubspace_comap_liftStep
    (hs : Function.Surjective h) (J : AnalyticManifold.IdealSheaf M) :
    (strictTransformSubspace hY (isBlowUp_blowUpπ ψ hY) J).pullback _ (BlowUpSequence.liftStep h hh
        hY).contMDiff =
      strictTransformSubspace (hY.preimage_of_isLocalDiffeomorph hh)
        (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
        (J.pullback h h.contMDiff) := by
  by_cases hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E (blowUp ψ hY))
    (saturationStalk hY (isBlowUp_blowUpπ ψ hY) J)
  · have hex' := (hasLocalGenerators_saturationStalk_comap_liftStep_iff h hh hY hs J).mpr hex
    refine IdealSheaf.ext fun q => ?_
    rw [IdealSheaf.stalkIdeal_pullback,
      stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _ hex,
      stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _ hex',
      saturationStalk_comap_liftStep h hh hY J q]
  · have hex' : ¬ IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 E (blowUp ψ (hY.preimage_of_isLocalDiffeomorph hh)))
        (saturationStalk (hY.preimage_of_isLocalDiffeomorph hh)
          (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
          (J.pullback h h.contMDiff)) :=
      fun h' => hex ((hasLocalGenerators_saturationStalk_comap_liftStep_iff h hh hY hs J).mp h')
    rw [strictTransformSubspace_of_not_hasLocalGenerators _ _ _ hex,
      strictTransformSubspace_of_not_hasLocalGenerators _ _ _ hex']
    exact IdealSheaf.pullback_top _ _

/-- (B′) `strictTransformSubspace_comap_liftStep` WITHOUT surjectivity: both sides take the
`ofStalks` branch (`strictTransformSubspace_eq_ofStalks`), and the stalk identity
`saturationStalk_comap_liftStep` never needed surjectivity. -/
theorem strictTransformSubspace_comap_liftStep'
    (J : AnalyticManifold.IdealSheaf M) :
    (strictTransformSubspace hY (isBlowUp_blowUpπ ψ hY) J).pullback _ (BlowUpSequence.liftStep h hh
        hY).contMDiff =
      strictTransformSubspace (hY.preimage_of_isLocalDiffeomorph hh)
        (isBlowUp_blowUpπ ψ (hY.preimage_of_isLocalDiffeomorph hh))
        (J.pullback h h.contMDiff) := by
  refine IdealSheaf.ext fun q => ?_
  rw [IdealSheaf.stalkIdeal_pullback,
    stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _
      (saturationStalk_hasLocalGenerators _ _ _),
    stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _
      (saturationStalk_hasLocalGenerators _ _ _),
    saturationStalk_comap_liftStep h hh hY J q]

include hh in
/-- (B) for any analytic `G` between the blowings-up lying over `h` with `S = h⁻¹(Y)`: such a
`G` is the lift (`heq_liftStep_of_forall`); the counterpart of `weakTransform_comap_of_square`. -/
theorem strictTransformSubspace_comap_of_square
    (hs : Function.Surjective h) {S : Set N} (hS : IsClosedSubmanifold ψ S c) (e : S = ⇑h ⁻¹' Y)
    (G : AnalyticMap (blowUp ψ hS) (blowUp ψ hY))
    (hcomm : ∀ q, blowUpπ ψ hY (G q) = h (blowUpπ ψ hS q)) (J : AnalyticManifold.IdealSheaf M) :
    (strictTransformSubspace hY (isBlowUp_blowUpπ ψ hY) J).pullback G G.contMDiff =
      strictTransformSubspace hS (isBlowUp_blowUpπ ψ hS)
          (J.pullback h h.contMDiff) := by
  subst e
  obtain rfl := eq_of_heq (BlowUpSequence.heq_liftStep_of_forall h hh hY hS rfl G hcomm)
  exact strictTransformSubspace_comap_liftStep h hh hY hs J

end PullbackStep

end Hironaka.Manifold

/-! ### The constructor form of the recursion of the ideal-theoretic strict transforms -/

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}

/-- The recursion of the ideal-theoretic strict transforms on the constructor form, at the level
of the ℕ-indexed auxiliary recursion (the counterpart of `cons_weakTransformSeqAux_succ`); the
witnesses of the `cons` — the chosen chart and codimension of the monoidality witness of the first
step, on the cosupport of `hY.idealSheaf` — are bridged to `hY` itself by
`strictTransformSubspace_congr`. -/
theorem cons_strictTransformSubspaceSeqAux_succ (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (J : IdealSheaf M) :
    ∀ (k : ℕ) (h : k + 1 < (cons ψ hY rest).length + 1),
      (cons ψ hY rest).strictTransformSubspaceSeqAux J (k + 1) h =
        rest.strictTransformSubspaceSeqAux
          (strictTransformSubspace hY (isBlowUp_blowUpπ ψ hY) J) k (Nat.lt_of_succ_lt_succ h)
  | 0, h => by
    change strictTransformSubspace ((cons ψ hY rest).isClosedSubmanifold_center
        ⟨0, Nat.lt_of_succ_lt_succ h⟩) ((cons ψ hY rest).isBlowUp_map ⟨0, Nat.lt_of_succ_lt_succ h⟩)
        J = strictTransformSubspace hY (isBlowUp_blowUpπ ψ hY) J
    exact strictTransformSubspace_congr _ _ hY (isBlowUp_blowUpπ ψ hY) hY.cosupport_idealSheaf J
  | k + 1, h => by
    change strictTransformSubspace ((cons ψ hY rest).isClosedSubmanifold_center
        ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
      ((cons ψ hY rest).isBlowUp_map ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
      ((cons ψ hY rest).strictTransformSubspaceSeqAux J (k + 1) (Nat.lt_of_succ_lt h)) = _
    rw [cons_strictTransformSubspaceSeqAux_succ hY rest J k (Nat.lt_of_succ_lt h)]
    rfl

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

open Manifold Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### (B) Along a list: the strict transforms of the pull-back by a surjective local
isomorphism -/

/-- (B) along a list [Kol07, Definition 30.1]: the ideal-theoretic strict transforms along
`h^* L`, for a SURJECTIVE `h`, are the pull-backs along the lifts of the strict transforms along `L`
(`strictTransformSubspace_comap_liftStep` at each step; the counterpart of
`boundarySeqAux_pullback`). -/
theorem strictTransformSubspaceSeqAux_pullback [FiniteDimensional 𝕜 E] :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h), Function.Surjective h →
    ∀ (J : IdealSheaf M) (i : ℕ) (hi : i < L.length + 1)
    (hi' : i < (L.pullback h hh).length + 1),
    (L.pullback h hh).toSuccession.strictTransformSubspaceSeqAux
        (J.pullback h h.contMDiff)
        i hi' =
      (L.toSuccession.strictTransformSubspaceSeqAux J i hi).pullback _ (L.pullbackLiftAux h hh i hi
          hi').contMDiff
  | _, _, nil _, _, _, _, _, 0, _, _ => rfl
  | _, _, cons _ _, _, _, _, _, 0, _, _ => rfl
  | _, _, cons hY rest, h, hh, hs, J, i + 1, hi, hi' => by
    revert hi hi'
    change ∀ (hi : i + 1 < (FiniteSuccession.cons ψ₀ hY rest.toSuccession).length + 1)
      (hi' : i + 1 < (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).length + 1),
      (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).strictTransformSubspaceSeqAux
        (J.pullback h h.contMDiff) (i + 1) hi' =
      Manifold.IdealSheaf.pullback _ (rest.pullbackLiftAux (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY) i (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hi')).contMDiff
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).strictTransformSubspaceSeqAux J (i + 1) hi)
    intro hi hi'
    rw [FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ,
      FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ,
      ← strictTransformSubspace_comap_liftStep h hh hY hs J]
    exact strictTransformSubspaceSeqAux_pullback rest _ _ (surjective_liftStep h hh hY hs) _ i _ _
  | _, _, nil _, _, _, _, _, i + 1, hi, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- (B), `Fin`-indexed (the counterpart of `boundarySeq_pullback`). -/
theorem strictTransformSubspaceSeq_pullback [FiniteDimensional 𝕜 E] (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) (J : IdealSheaf M) (i : Fin (L.length + 1)) :
    (L.pullback h hh).toSuccession.strictTransformSubspaceSeq
        (J.pullback h h.contMDiff)
        ⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ =
      (L.toSuccession.strictTransformSubspaceSeq J i).pullback _ (L.pullbackLift h hh i).contMDiff
          :=
  strictTransformSubspaceSeqAux_pullback L h hh hs J i.1 i.2 _

/-- (B′) `strictTransformSubspaceSeqAux_pullback` WITHOUT surjectivity. -/
theorem strictTransformSubspaceSeqAux_pullback' [FiniteDimensional 𝕜 E] :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (J : IdealSheaf M) (i : ℕ)
    (hi : i < L.length + 1) (hi' : i < (L.pullback h hh).length + 1),
    (L.pullback h hh).toSuccession.strictTransformSubspaceSeqAux
        (J.pullback h h.contMDiff)
        i hi' =
      (L.toSuccession.strictTransformSubspaceSeqAux J i hi).pullback _ (L.pullbackLiftAux h hh i hi
          hi').contMDiff
  | _, _, nil _, _, _, _, 0, _, _ => rfl
  | _, _, cons _ _, _, _, _, 0, _, _ => rfl
  | _, _, cons hY rest, h, hh, J, i + 1, hi, hi' => by
    revert hi hi'
    change ∀ (hi : i + 1 < (FiniteSuccession.cons ψ₀ hY rest.toSuccession).length + 1)
      (hi' : i + 1 < (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).length + 1),
      (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).strictTransformSubspaceSeqAux
        (J.pullback h h.contMDiff) (i + 1) hi' =
      Manifold.IdealSheaf.pullback _ (rest.pullbackLiftAux (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY) i (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hi')).contMDiff
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).strictTransformSubspaceSeqAux J (i + 1) hi)
    intro hi hi'
    rw [FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ,
      FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ,
      ← strictTransformSubspace_comap_liftStep' h hh hY J]
    exact strictTransformSubspaceSeqAux_pullback' rest _ _ _ i _ _
  | _, _, nil _, _, _, _, i + 1, hi, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

/-- (B′) `strictTransformSubspaceSeq_pullback` WITHOUT surjectivity. -/
theorem strictTransformSubspaceSeq_pullback' [FiniteDimensional 𝕜 E] (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (J : IdealSheaf M) (i : Fin (L.length + 1)) :
    (L.pullback h hh).toSuccession.strictTransformSubspaceSeq
        (J.pullback h h.contMDiff)
        ⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ =
      (L.toSuccession.strictTransformSubspaceSeq J i).pullback _ (L.pullbackLift h hh i).contMDiff
          :=
  strictTransformSubspaceSeqAux_pullback' L h hh J i.1 i.2 _

/-- (B′) `strictTransformSubspaceSeq_last_pullbackLiftLast` WITHOUT surjectivity: (B) at the last
stage along ANY local analytic isomorphism — the open inclusions of [Kol07, Theorem 36, proof]
included. -/
theorem strictTransformSubspaceSeq_last_pullbackLiftLast' [FiniteDimensional 𝕜 E] :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (J : IdealSheaf M),
    (L.pullback h hh).toSuccession.strictTransformSubspaceSeq
        (J.pullback h h.contMDiff)
        (Fin.last _) =
      (L.toSuccession.strictTransformSubspaceSeq J (Fin.last _)).pullback _ (L.pullbackLiftLast h
          hh).contMDiff
  | _, _, nil _, _, _, _ => rfl
  | _, _, cons hY rest, h, hh, J => by
    have e1 : ((cons hY rest).pullback h hh).toSuccession.strictTransformSubspaceSeq
          (J.pullback h h.contMDiff) (Fin.last _) =
        (rest.pullback (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.strictTransformSubspaceSeq
          (strictTransformSubspace (hY.preimage_of_isLocalDiffeomorph hh)
            (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))
            (J.pullback h h.contMDiff)) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ ψ₀
        (hY.preimage_of_isLocalDiffeomorph hh)
        (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)).toSuccession
        (J.pullback h h.contMDiff) _ (Fin.last _).2
    have e2 : (cons hY rest).toSuccession.strictTransformSubspaceSeq J (Fin.last _) =
        rest.toSuccession.strictTransformSubspaceSeq
          (strictTransformSubspace hY (isBlowUp_blowUpπ ψ₀ hY) J) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ ψ₀ hY rest.toSuccession J _
        (Fin.last _).2
    rw [e1, e2, ← strictTransformSubspace_comap_liftStep' h hh hY J]
    exact strictTransformSubspaceSeq_last_pullbackLiftLast' rest (liftStep h hh hY) _ _

/-- (B) at the last stage, along the bundled last-stage lift `pullbackLiftLast` (the counterpart
of `strictTransformSeq_last_pullbackLiftLast`). -/
theorem strictTransformSubspaceSeq_last_pullbackLiftLast [FiniteDimensional 𝕜 E] :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h), Function.Surjective h →
    ∀ (J : IdealSheaf M),
    (L.pullback h hh).toSuccession.strictTransformSubspaceSeq
        (J.pullback h h.contMDiff)
        (Fin.last _) =
      (L.toSuccession.strictTransformSubspaceSeq J (Fin.last _)).pullback _ (L.pullbackLiftLast h
          hh).contMDiff
  | _, _, nil _, _, _, _, _ => rfl
  | _, _, cons hY rest, h, hh, hs, J => by
    have e1 : ((cons hY rest).pullback h hh).toSuccession.strictTransformSubspaceSeq
          (J.pullback h h.contMDiff) (Fin.last _) =
        (rest.pullback (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.strictTransformSubspaceSeq
          (strictTransformSubspace (hY.preimage_of_isLocalDiffeomorph hh)
            (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))
            (J.pullback h h.contMDiff)) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ ψ₀
        (hY.preimage_of_isLocalDiffeomorph hh)
        (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)).toSuccession
        (J.pullback h h.contMDiff) _ (Fin.last _).2
    have e2 : (cons hY rest).toSuccession.strictTransformSubspaceSeq J (Fin.last _) =
        rest.toSuccession.strictTransformSubspaceSeq
          (strictTransformSubspace hY (isBlowUp_blowUpπ ψ₀ hY) J) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ ψ₀ hY rest.toSuccession J _
        (Fin.last _).2
    rw [e1, e2, ← strictTransformSubspace_comap_liftStep h hh hY hs J]
    exact strictTransformSubspaceSeq_last_pullbackLiftLast rest (liftStep h hh hY) _
      (surjective_liftStep h hh hY hs) _

/-! ### (C) Along the deletion of the empty blow-ups -/

variable {Y : Set M} {c : ℕ}

/-- (C), one step: the strict transform along the blowing-up of an EMPTY centre is the
pull-back — the exceptional ideal sheaf is the unit ideal (`idealSheaf_eq_top_of_eq_empty`), so
every colon is the total transform's stalk, which has local generators; the counterpart of
`weakTransform_blowUpπ_of_eq_empty`. -/
theorem strictTransformSubspace_blowUpπ_of_eq_empty (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅)
    (J : IdealSheaf M) :
    strictTransformSubspace hY (isBlowUp_blowUpπ ψ₀ hY) J =
      J.pullback _ (blowUpπ ψ₀ hY).contMDiff := by
  have hE : hY.idealSheaf.pullback _ (isBlowUp_blowUpπ ψ₀ hY).contMDiff = ⊤ := by
    rw [hY.idealSheaf_eq_top_of_eq_empty hY₀, IdealSheaf.pullback_top]
  have hsat : saturationStalk hY (isBlowUp_blowUpπ ψ₀ hY) J =
      fun a => (J.pullback _ (blowUpπ ψ₀ hY).contMDiff).stalkIdeal a := by
    funext a
    unfold saturationStalk
    rw [hE, IdealSheaf.stalkIdeal_top]
    simp only [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ, iSup_const]
  have hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E (blowUp ψ₀ hY))
      (saturationStalk hY (isBlowUp_blowUpπ ψ₀ hY) J) := by
    rw [hsat]
    intro a
    obtain ⟨U, ha, k, f, -, hf⟩ :=
        (J.pullback _ (blowUpπ ψ₀ hY).contMDiff).locallyFG a
    exact ⟨U, ha, Fin k, inferInstance, f, hf⟩
  refine IdealSheaf.ext fun a => ?_
  rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _ hex, hsat]

/-- (C) transport along an equality of lists (the counterpart of
`weakTransformSeq_last_stageOfEq`). -/
theorem strictTransformSubspaceSeq_last_stageOfEq {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (I : IdealSheaf M) :
    L₂.toSuccession.strictTransformSubspaceSeq I (Fin.last _) =
      (L₁.toSuccession.strictTransformSubspaceSeq I (Fin.last _)).pullback _
          (Diffeomorph.toAnalyticMap (stageOfEq e).symm).contMDiff := by
  subst e
  exact (comap_refl_symm _).symm

/-- (C) transport along a diffeomorphism and its lift to the last stages: the strict transform at
the last stage of the transported list `Z.map φ` is the pull-back along `(mapLast φ)⁻¹` of the
strict transform of `φ^* J` at the last stage of `Z` (`strictTransformSubspace_comap_of_square` at
each step; the counterpart of `weakTransformSeq_last_map`). -/
theorem strictTransformSubspaceSeq_last_map [FiniteDimensional 𝕜 E] :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (Z : BlowUpSequence ψ₀ M) (J : IdealSheaf N),
    (Z.map φ).toSuccession.strictTransformSubspaceSeq J (Fin.last _) =
      (Z.toSuccession.strictTransformSubspaceSeq
          (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) (Fin.last _)).pullback _
              (Diffeomorph.toAnalyticMap (Z.mapLast φ).symm).contMDiff
  | _, _, φ, nil _, J => (comap_symm_comap φ J).symm
  | _, _, φ, @cons _ _ _ _ _ _ _ _ Y _ hY rest, J => by
    have e1 : ((cons hY rest).map φ).toSuccession.strictTransformSubspaceSeq J (Fin.last _) =
        (rest.map (liftDiffeomorph φ hY)).toSuccession.strictTransformSubspaceSeq
          (strictTransformSubspace (hY.image_diffeomorph φ)
            (isBlowUp_blowUpπ ψ₀ (hY.image_diffeomorph φ)) J) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ ψ₀ (hY.image_diffeomorph φ)
        (rest.map (liftDiffeomorph φ hY)).toSuccession J _ (Fin.last _).2
    have e2 : (cons hY rest).toSuccession.strictTransformSubspaceSeq
          (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) (Fin.last _) =
        rest.toSuccession.strictTransformSubspaceSeq (strictTransformSubspace hY
          (isBlowUp_blowUpπ ψ₀ hY)
              (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff))
          (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ ψ₀ hY rest.toSuccession _ _
        (Fin.last _).2
    have hsq := strictTransformSubspace_comap_of_square (Diffeomorph.toAnalyticMap φ)
      φ.isLocalDiffeomorph (hY.image_diffeomorph φ) φ.toEquiv.surjective hY
      (preimage_image_diffeomorph φ Y).symm (Diffeomorph.toAnalyticMap (liftDiffeomorph φ hY))
      (blowUpπ_liftDiffeomorph φ hY) J
    change _ = Manifold.IdealSheaf.pullback (J := _) _ (Diffeomorph.toAnalyticMap (rest.mapLast
        (liftDiffeomorph φ
        hY)).symm).contMDiff
    rw [e1, e2, strictTransformSubspaceSeq_last_map (liftDiffeomorph φ hY) rest, hsq]

/-- (C) Deleting the empty blow-ups [Kol07, 34.1], the ideal-level counterpart of
`strictTransformSeq_last_eraseEmpty` and `weakTransformSeq_last_eraseEmpty`: **the strict transform
of `I` at the last stage of the cleaned list is the pull-back along `eraseEmptyLast⁻¹` of the one
at the last stage of the list** — a kept step contributes the same strict transform on both sides,
a deleted step the pull-back along the empty blowing-up
(`strictTransformSubspace_blowUpπ_of_eq_empty`), which the transport of the cleaned tail along
`Bl_∅ M ≃ M` absorbs (`strictTransformSubspaceSeq_last_map`). -/
theorem strictTransformSubspaceSeq_last_eraseEmpty [FiniteDimensional 𝕜 E] :
    ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (I : IdealSheaf M),
    L.eraseEmpty.toSuccession.strictTransformSubspaceSeq I (Fin.last _) =
      (L.toSuccession.strictTransformSubspaceSeq I (Fin.last _)).pullback _
          (Diffeomorph.toAnalyticMap L.eraseEmptyLast.symm).contMDiff
  | _, nil _, I => (comap_refl_symm I).symm
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, I => by
    have e2 : (cons hY rest).toSuccession.strictTransformSubspaceSeq I (Fin.last _) =
        rest.toSuccession.strictTransformSubspaceSeq
          (strictTransformSubspace hY (isBlowUp_blowUpπ ψ₀ hY) I) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ ψ₀ hY rest.toSuccession I _
        (Nat.lt_succ_self _)
    by_cases hY₀ : Y = ∅
    · rw [eraseEmptyLast_cons_of_eq_empty hY rest hY₀, e2]
      change _ = Manifold.IdealSheaf.pullback (J := _) _ (Diffeomorph.toAnalyticMap
        ((rest.eraseEmptyLast.trans (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀))).trans
          (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm)).symm).contMDiff
      rw [comap_trans_symm, comap_trans_symm,
        strictTransformSubspaceSeq_last_stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm I,
        strictTransformSubspaceSeq_last_map, toAnalyticMap_emptyBlowUpDiffeomorph hY hY₀,
        ← strictTransformSubspace_blowUpπ_of_eq_empty hY hY₀ I,
        strictTransformSubspaceSeq_last_eraseEmpty rest]
    · have e3 : (cons hY rest.eraseEmpty).toSuccession.strictTransformSubspaceSeq I (Fin.last _) =
          rest.eraseEmpty.toSuccession.strictTransformSubspaceSeq
            (strictTransformSubspace hY (isBlowUp_blowUpπ ψ₀ hY) I) (Fin.last _) :=
        FiniteSuccession.cons_strictTransformSubspaceSeqAux_succ ψ₀ hY rest.eraseEmpty.toSuccession
          I _ (Nat.lt_succ_self _)
      rw [eraseEmptyLast_cons_of_ne_empty hY rest hY₀, e2]
      exact (strictTransformSubspaceSeq_last_stageOfEq (L₁ := cons hY rest.eraseEmpty)
        (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm I).trans
        ((congrArg (Manifold.IdealSheaf.pullback _ (Diffeomorph.toAnalyticMap
          (stageOfEq (L₁ := cons hY rest.eraseEmpty)
            (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm).symm).contMDiff)
          (e3.trans (strictTransformSubspaceSeq_last_eraseEmpty rest _))).trans
          (comap_trans_symm rest.eraseEmptyLast _ _).symm)

/-! ### (D) = (B) + (C): the shape the functoriality clause `CommutesWithLocalIsos` produces -/

/-- (D) The final strict transform along `(h^* L).eraseEmpty` — the right-hand side of the
functoriality clause of `IsEmbeddedDesing` — is the pull-back of the final strict transform along
`L`, through the last-stage lift and `eraseEmptyLast⁻¹`; `h` SURJECTIVE (the clause's
`restrictMap g U' (imageOpens g hg U')` is). -/
theorem strictTransformSubspaceSeq_last_pullback_eraseEmpty [FiniteDimensional 𝕜 E]
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) (J : IdealSheaf M) :
    (L.pullback h hh).eraseEmpty.toSuccession.strictTransformSubspaceSeq
        (J.pullback h h.contMDiff) (Fin.last _) =
      Manifold.IdealSheaf.pullback _ (Diffeomorph.toAnalyticMap (L.pullback h
          hh).eraseEmptyLast.symm).contMDiff
        ((L.toSuccession.strictTransformSubspaceSeq J (Fin.last _)).pullback _ (L.pullbackLiftLast
            h hh).contMDiff) := by
  rw [strictTransformSubspaceSeq_last_eraseEmpty,
    strictTransformSubspaceSeq_last_pullbackLiftLast L h hh hs J]

/-- (D′) `strictTransformSubspaceSeq_last_pullback_eraseEmpty` WITHOUT surjectivity: the value of
the functoriality clause at ANY local analytic isomorphism — an OPEN INCLUSION `W' ↪ W` in
particular — has its final strict transform pulled back from the one over the source, through the
last-stage lift and `eraseEmptyLast⁻¹`. -/
theorem strictTransformSubspaceSeq_last_pullback_eraseEmpty' [FiniteDimensional 𝕜 E]
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (J : IdealSheaf M) :
    (L.pullback h hh).eraseEmpty.toSuccession.strictTransformSubspaceSeq
        (J.pullback h h.contMDiff) (Fin.last _) =
      Manifold.IdealSheaf.pullback _ (Diffeomorph.toAnalyticMap (L.pullback h
          hh).eraseEmptyLast.symm).contMDiff
        ((L.toSuccession.strictTransformSubspaceSeq J (Fin.last _)).pullback _ (L.pullbackLiftLast
            h hh).contMDiff) := by
  rw [strictTransformSubspaceSeq_last_eraseEmpty,
    strictTransformSubspaceSeq_last_pullbackLiftLast' L h hh J]

end AnalyticManifold.BlowUpSequence

end
