/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
public import Hironaka.Resolution.Analytic.Functor.Family
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The order clause along the pull-back by a local analytic isomorphism

The compatible-family form of Step 2.1 (`Step21Fam.lean`) restricts sequences of centres along the
open inclusions `M.restrict V → M.restrict W` of a shrinking chain, local analytic isomorphisms
that are not surjective. The transport of the clauses of [Kol07, Definition 66] along a pull-back
proved in `Functor/PullbackSequence.lean` (`isOfOrderGe_of_pullback`) goes the other way and needs
surjectivity, because the reduced boundary `red(π⁻¹E ∪ π⁻¹Z)` of the successions
(`IdealSheaf.reducedTransform`; clause (iii) of [Hir64, Main Theorem II′(N)]) is defined by a
global case split on the existence of local generators, which descends only along surjections.
Forward, under the normal-crossings clause (3′) itself, no case split is needed: the boundary at
every stage is the reduced ideal sheaf of a family with simple normal crossings
(`reducedTransform_eq_idealSheaf_totalTransform`), such families pull back along local
isomorphisms (`isSnc_comap`), their reduced ideal sheaves are the pull-backs
(`idealSheaf_comap_of_isSnc`), and the total transform of a family pulls back along the lift
(`totalTransform_comap_liftStep`). This is the local nature of the functoriality package noted in
[Kol07, 104, Step 2.3] ("the functoriality package is local").

* `BlowUpSequence.isOfOrderGe_pullback` — a sequence of order `≥ m` for `(𝓘, m, red E)` pulls back
  along any local analytic isomorphism `h` to a sequence of order `≥ m` for
  `(h^* 𝓘, m, red h⁻¹E)`; `AnalyticTriple.isOfOrderGe_pullback` is its form for triples;
* `BlowUpSequence.isOfOrderGe_shrinkAppend` — the shrink-and-append step of the chain
  (`FamilyChain.lean`) keeps the order clause for the restricted triple;
* `AnalyticTriple.pullback_inclusion_restrictLE`, `pullback_eq_of_eq` — restricting a restricted
  triple, and pull-backs along equal maps.

These are the order clauses carried by the chain of `Step21Fam.lean` and by Step 2.2 in the
compatible-family form (`Step22Fam.lean`).
-/

public section

universe u

open Set TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The reduced ideal sheaf of `h⁻¹(E)` is the pull-back of the reduced ideal sheaf of `E`, for a
family `E` with simple normal crossings and a local analytic isomorphism `h` (no surjectivity is
needed): both sides fall under the first branch of the definition (the vanishing stalks of such a
family have local generators, `IsSnc.hasLocalGenerators_vanishingStalk_support`), and the
vanishing stalks correspond along the bijective germ maps. Not in the sources. -/
theorem HypersurfaceFamily.idealSheaf_comap_of_isSnc {M N : AnalyticManifold.{u} 𝕜 E}
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ₀) :
    (F.comap h).idealSheaf = F.idealSheaf.pullback h h.contMDiff := by
  have h₂ := hF.hasLocalGenerators_vanishingStalk_support
  have h₁ := (HypersurfaceFamily.isSnc_comap hF h hh).hasLocalGenerators_vanishingStalk_support
  unfold HypersurfaceFamily.idealSheaf
  rw [dite_eq_left h₂, dite_eq_left h₁]
  refine IdealSheaf.ext fun x => ?_
  rw
      [IdealSheaf.stalkIdeal_pullback,
          IdealSheaf.stalkIdeal_ofStalks,
    IdealSheaf.stalkIdeal_ofStalks, HypersurfaceFamily.support_comap,
    vanishingStalk_preimage_of_isLocalDiffeomorphAt h (hh x)]

/-- The order clause pulls back along any local analytic isomorphism (the local nature of
[Kol07, 34.1]): a sequence of order `≥ m` for `(𝓘, m, red E)`, `E` with simple normal crossings,
pulls back to a sequence of order `≥ m` for `(h^* 𝓘, m, red h⁻¹E)`. By recursion on the sequence
through `isOfOrderGe_cons_iff`: the normal-crossings clause and the order clause at the first
centre transport along `h` (`comap_of_isLocalDiffeomorph`,
`ordAlongIdeal_comap_of_isLocalDiffeomorphAt`); for the tail, the boundary after the first
blow-up is the reduced ideal sheaf of the total transform of `E`, a family with simple normal
crossings, on both sides (`reducedTransform_eq_idealSheaf_totalTransform`), the controlled
transform pulls back along the lift (`birationalTransform_comap_liftStep`), and the total transform
of `h⁻¹E` is the pull-back of the total transform of `E` (`totalTransform_comap_liftStep`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.isOfOrderGe_pullback :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
      (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (I : AnalyticManifold.IdealSheaf M) (m : ℕ)
      {F : HypersurfaceFamily M}, F.IsSnc ψ₀ → L.toSuccession.IsOfOrderGe I m F.idealSheaf →
      (L.pullback h hh).toSuccession.IsOfOrderGe (I.pullback h h.contMDiff) m
        (F.comap h).idealSheaf
  | _, _, BlowUpSequence.nil _, _, _, _, m, _, _, _ => FiniteSuccession.isOfOrderGe_nil _ _ m
  | _, _, @BlowUpSequence.cons _ _ _ _ _ _ _ _ Y _ hY rest, h, hh, I, m, F, hF, hge => by
    have := finiteDimensional_of_chartIso ψ₀
    obtain ⟨⟨hnc, hm⟩, hrest⟩ := (FiniteSuccession.isOfOrderGe_cons_iff (I := I) (m := m)
      (E₀ := F.idealSheaf) hY rest.toSuccession).mp hge
    have hF' : (F.comap h).IsSnc ψ₀ := HypersurfaceFamily.isSnc_comap hF h hh
    have hsw : F.HasSncWith ψ₀ Y _ := (hasOnlyNormalCrossingsWith_idealSheaf_iff hF hY).mp hnc
    have hnc' : IdealSheaf.HasOnlyNormalCrossingsWith (F.comap h).idealSheaf
        (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf := by
      rw [HypersurfaceFamily.idealSheaf_comap_of_isSnc h hh hF,
        ← comap_idealSheaf_of_isLocalDiffeomorph ψ₀ h hh hY]
      exact HasOnlyNormalCrossingsWith.comap_of_isLocalDiffeomorph h hh hnc
    have hsw' : (F.comap h).HasSncWith ψ₀ (⇑h ⁻¹' Y) _ :=
      (hasOnlyNormalCrossingsWith_idealSheaf_iff hF' (hY.preimage_of_isLocalDiffeomorph hh)).mp
        hnc'
    have hm' : ∀ b ∈ ⇑h ⁻¹' Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf
            (I.pullback h h.contMDiff) b := by
      intro b hb
      rw [← comap_idealSheaf_of_isLocalDiffeomorph ψ₀ h hh hY,
        IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt h _ _ (hh b)]
      exact hm (h b) hb
    -- the boundary after the first blow-up, on both sides
    have e1 :
        IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) F.idealSheaf hY.idealSheaf
            =
        (F.totalTransform (blowUpπ ψ₀ hY) Y).idealSheaf :=
      reducedTransform_eq_idealSheaf_totalTransform hY (isBlowUp_blowUpπ ψ₀ hY) hF hsw
    have hF₁ : (F.totalTransform (blowUpπ ψ₀ hY) Y).IsSnc ψ₀ :=
      HypersurfaceFamily.isSnc_totalTransform hY (isBlowUp_blowUpπ ψ₀ hY) hF hsw
    rw [e1] at hrest
    have ih := AnalyticManifold.BlowUpSequence.isOfOrderGe_pullback rest
        (BlowUpSequence.liftStep h hh hY) (BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY)
      _ m hF₁ hrest
    refine
        (FiniteSuccession.isOfOrderGe_cons_iff (I := I.pullback h h.contMDiff)
            (m := m)
      (E₀ := (F.comap h).idealSheaf) (hY.preimage_of_isLocalDiffeomorph hh)
      (rest.pullback (BlowUpSequence.liftStep h hh hY) (BlowUpSequence.isLocalDiffeomorph_liftStep
          h hh hY)).toSuccession).mpr
      ⟨⟨hnc', hm'⟩, ?_⟩
    have e2 : (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
            (rest.pullback (BlowUpSequence.liftStep h hh hY)
              (BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY)).toSuccession).markedTransformSeq
          (I.pullback h h.contMDiff) m
              (Fin.succ (0 : Fin ((rest.pullback (BlowUpSequence.liftStep h hh hY)
            (BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY)).toSuccession.length + 1))) =
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeq I m
            (Fin.succ (0 : Fin (rest.toSuccession.length + 1)))).pullback _
                (BlowUpSequence.liftStep h hh hY).contMDiff := by
      rw [FiniteSuccession.cons_markedTransformSeq_one,
        FiniteSuccession.cons_markedTransformSeq_one]
      exact (birationalTransform_comap_liftStep h hh hY ⟨I, m⟩ hm).symm
    have e3 : IdealSheaf.reducedTransform (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))
        (F.comap h).idealSheaf (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf =
        ((F.totalTransform (blowUpπ ψ₀ hY) Y).comap (BlowUpSequence.liftStep h hh hY)).idealSheaf
            := by
      rw [← HypersurfaceFamily.totalTransform_comap_liftStep h hh hY F]
      exact reducedTransform_eq_idealSheaf_totalTransform (hY.preimage_of_isLocalDiffeomorph hh)
        (isBlowUp_blowUpπ ψ₀ _) hF' hsw'
    rw [e2, e3]
    exact ih

/-- The order clause pulls back, for triples: a sequence of order `≥ m` starting with `T` pulls
back along any local analytic isomorphism to a sequence of order `≥ m` starting with the
pulled-back triple. -/
theorem AnalyticTriple.isOfOrderGe_pullback {M N : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ M) (m : ℕ) (L : BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    (L.pullback h hh).toSuccession.IsOfOrderGe (T.pullback h hh).I m
      (T.pullback h hh).F.idealSheaf :=
  BlowUpSequence.isOfOrderGe_pullback L h hh T.I m T.isSnc hL

/-- Pulling back along equal maps gives equal triples. -/
theorem AnalyticTriple.pullback_eq_of_eq {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    {f g : AnalyticMap N M} (e : f = g) (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) : T.pullback f hf = T.pullback g hg := by
  subst e
  rfl

/-- Restricting the restriction of a triple to `W` further to `V ≤ W` is its restriction to `V`
(`inclusion W ∘ restrictLE = inclusion V`). -/
theorem AnalyticTriple.pullback_inclusion_restrictLE {M : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ M) {V W : Opens M} (hVW : V ≤ W) :
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).pullback (M.restrictLE hVW)
        (isLocalDiffeomorph_restrictLE hVW) =
      T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V) :=
  AnalyticTriple.pullback_pullback T (M.inclusion W) (isLocalDiffeomorph_inclusion M W)
    (M.restrictLE hVW) (isLocalDiffeomorph_restrictLE hVW)

end Manifold

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold
open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

/-- The inclusion of the lifted range after the corestriction is the lift itself. -/
theorem inclusion_comp_liftCorestrict :
    ((L.stage (Fin.last _)).inclusion (L.liftRange h hh)).comp (L.liftCorestrict h hh) =
      L.pullbackLiftLast h hh := rfl

/-- The shrink-and-append step of the chain keeps the order clause: the sequence so far pulled back
to the smaller open is of order `≥ m` for the restricted triple (`isOfOrderGe_pullback`), and the
appended value, of order `≥ m` for the induced triple restricted to the reading open, pulls back
along the corestricted lift to a sequence of order `≥ m` for the induced triple of the restricted
sequence (`induced_pullback`), so the concatenation is of order `≥ m` (`isOfOrderGe_concat`). -/
theorem isOfOrderGe_shrinkAppend (T : AnalyticTriple ψ₀ M) (m : ℕ)
    (hL : L.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf)
    (L' : BlowUpSequence ψ₀ ((L.stage (Fin.last _)).restrict (L.liftRange h hh)))
    (hL' : L'.toSuccession.IsOfOrderGe
      ((T.induced m L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).I m
      ((T.induced m L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf) :
    (L.shrinkAppend h hh L').toSuccession.IsOfOrderGe (T.pullback h hh).I m
      (T.pullback h hh).F.idealSheaf := by
  have := finiteDimensional_of_chartIso ψ₀
  have hL₁ := T.isOfOrderGe_pullback m L hL h hh
  have hL₂ := AnalyticTriple.isOfOrderGe_pullback _ m L' hL' (L.liftCorestrict h hh)
    (L.isLocalDiffeomorph_liftCorestrict h hh)
  have e : ((T.induced m L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).pullback (L.liftCorestrict h hh)
        (L.isLocalDiffeomorph_liftCorestrict h hh) =
      (T.pullback h hh).induced m (L.pullback h hh) hL₁ := by
    rw [AnalyticTriple.pullback_pullback,
      AnalyticTriple.pullback_eq_of_eq _ (inclusion_comp_liftCorestrict L h hh) _
        (isLocalDiffeomorph_pullbackLiftLast L h hh)]
    exact AnalyticTriple.induced_pullback T m L hL h hh hL₁
  rw [e] at hL₂
  unfold shrinkAppend
  refine isOfOrderGe_concat (L.pullback h hh) _ hL₁ ?_
  rw [AnalyticTriple.boundarySeq_last_eq_idealSheaf (T.pullback h hh) m (L.pullback h hh) hL₁]
  exact hL₂

end AnalyticManifold.BlowUpSequence

