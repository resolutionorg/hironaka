/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedState
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalMonomial
import Hironaka.Resolution.Algebraic.Kol07.MarkedProduct
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedMain
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedOrderGe
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.MarkedTransformMul
import Hironaka.Resolution.Algebraic.Wlo05.StrictTransformReduced
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The clauses from the end data of the loop

Clause (c) of [Wlo05, Theorem 1.0.2] and the fine form of clause (e) for `BED`, derived from the
end data `EmbeddedEnd ⟨TX, 1⟩ (componentIdeals TX) ∅ (BED TX)` taken as a hypothesis `h`; the proof
of the theorem obtains the end data from CP1–CP6 (`embeddedEnd_BED_of_invCE`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge`).

* `BED_strictTransform_last_smooth_of_embeddedEnd`,
  `BED_hasSncWith_strictTransform_last_of_embeddedEnd` — clause (c): the final strict transform of
  the reduced `Y` is smooth and has simple normal crossings with the final boundary. The end data
  give them for the members — the irreducible components of `Y` — whose final strict transforms
  are pairwise disjoint, and the final strict transform of `Y` is their product
  (`strictTransformSeq_eq_prod_of_pairwise_disjoint`: reduced, same support).
* `BED_comap_composite_eq_strictTransform_mul_sncDivisor_of_embeddedEnd` — clause (e) in the fine
  form of [Wlo05, Theorem 4.7.1], `σ^*(I_Y) = M(σ^*(I_Y)) · I_Ỹ`: `σ^*(I_Y) = I_Ỹ · J` with `J` the
  ideal of an snc divisor supported on the final boundary. [Kol07, 72] writes `σ^*(I_Y)` as the
  final marked transform times the product of the pulled-back exceptional divisors; the end data
  identify the final marked transform with `I_Ỹ`, and
  `isIdealOfSncDivisor_prod_comap_exceptionalAt`
  (`Hironaka.Resolution.Algebraic.Kol07.ExceptionalMonomial`) makes the product an snc divisor
  supported on the final boundary.

It also proves the elementary identity `iInf_componentIdeals_eq`: a reduced ideal is the
intersection of the reduced ideals of the irreducible components of its support. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.IdealSheafData
  Scheme.BlowUpSequence Hironaka.Sequence Hironaka.BMO IsLocalRing

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

omit [CharZero k] in
/-- A reduced ideal is the intersection of the reduced ideals of the irreducible components of its
support (the decomposition of `Y` in [Wlo05, Theorem 4.7.1]): the Galois connection between
supports and vanishing ideals (`vanishingIdeal_iSup`), the union
`coe_support_eq_biUnion_componentIdeals` and `vanishingIdeal_support_of_isReduced`. -/
theorem iInf_componentIdeals_eq (TX : Triple k) [IsReduced TX.I.subscheme] :
    (⨅ c ∈ componentIdeals TX, c) = TX.I := by
  classical
  have hle : ∀ c ∈ componentIdeals TX, TX.I ≤ c := fun c hc => by
    obtain ⟨η, hη, rfl⟩ := (mem_componentIdeals_iff TX).mp hc
    rw [← le_support_iff_le_vanishingIdeal, ← SetLike.coe_subset_coe, Closeds.coe_closure]
    exact TX.I.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη.1)
  have hsupp : TX.I.support = ⨆ c ∈ componentIdeals TX, c.support := by
    refine le_antisymm (IsConcreteLE.le_iff.mpr fun x hx => ?_)
      (iSup₂_le fun c hc => support_antitone (hle c hc))
    have hx' : x ∈ ⋃ c ∈ componentIdeals TX, (c.support : Set TX.X.left) := by
      rw [← coe_support_eq_biUnion_componentIdeals]
      exact hx
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx'
    exact le_iSup₂ (f := fun c (_ : c ∈ componentIdeals TX) => c.support) c hc hxc
  calc (⨅ c ∈ componentIdeals TX, c)
      = ⨅ c ∈ componentIdeals TX, vanishingIdeal c.support := by
        refine iInf_congr fun c => iInf_congr fun hc => ?_
        obtain ⟨η, -, rfl⟩ := (mem_componentIdeals_iff TX).mp hc
        rw [support_vanishingIdeal_eq]
    _ = vanishingIdeal (⨆ c ∈ componentIdeals TX, c.support) := by
        simp only [vanishingIdeal_iSup]
    _ = TX.I := by rw [← hsupp, vanishingIdeal_support_of_isReduced]

section OfEnd

variable (TX : Triple k) [IsReduced TX.I.subscheme]
  (h : EmbeddedEnd ⟨TX, 1⟩ (componentIdeals TX) ∅ (BED TX))

omit [IsReduced TX.I.subscheme] in
include h in
/-- The final strict transforms of the irreducible components of `Y` are pairwise disjoint
([Wlo05, Theorem 4.7.1]), from the end data. -/
theorem pairwise_disjoint_strictTransformSeq_BED_last_of_embeddedEnd :
    ((componentIdeals TX : Finset TX.X.left.IdealSheafData) : Set TX.X.left.IdealSheafData).Pairwise
      fun a b => Disjoint ((BED TX).strictTransformSeq a (Fin.last _)).support
        ((BED TX).strictTransformSeq b (Fin.last _)).support := by
  classical
  have h' := h.pairwise
  rwa [Finset.union_empty] at h'

include h in
/-- The final strict transform of `Y` is the product of the final strict transforms of its
irreducible components, from the end data. -/
theorem strictTransformSeq_BED_last_eq_prod_of_embeddedEnd :
    (BED TX).strictTransformSeq TX.I (Fin.last _) =
      ∏ c ∈ componentIdeals TX, (BED TX).strictTransformSeq c (Fin.last _) := by
  have : IsLocallyNoetherian TX.X.left := (TX.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact strictTransformSeq_eq_prod_of_pairwise_disjoint (BED TX) TX.I (componentIdeals TX)
    (fun c => c)
    (fun c hc => by
      obtain ⟨η, -, rfl⟩ := (mem_componentIdeals_iff TX).mp hc
      have := isIntegral_subscheme_vanishingIdeal_closure η
      infer_instance)
    (coe_support_eq_biUnion_componentIdeals TX) (Fin.last _)
    (pairwise_disjoint_strictTransformSeq_BED_last_of_embeddedEnd TX h)

include h in
/-- Clause (c) of [Wlo05, Theorem 1.0.2], second part, from the end data: the final total
transform of the boundary has simple normal crossings with the final strict transform of `Y`. -/
theorem BED_hasSncWith_strictTransform_last_of_embeddedEnd :
    ((BED TX).totalTransformSeq TX.E (Fin.last _)).HasSncWith
      ((BED TX).strictTransformSeq TX.I (Fin.last _)) := by
  classical
  rw [strictTransformSeq_BED_last_eq_prod_of_embeddedEnd TX h]
  refine hasSncWith_prod_of_pairwise_disjoint _ (componentIdeals TX) _
    (pairwise_disjoint_strictTransformSeq_BED_last_of_embeddedEnd TX h) fun c hc => ?_
  exact h.snc c (Finset.mem_union_left _ hc)

include h in
/-- Clause (c) of [Wlo05, Theorem 1.0.2], first part, from the end data: the final strict
transform of `Y` is smooth over `k`. -/
theorem BED_strictTransform_last_smooth_of_embeddedEnd :
    Smooth (((BED TX).strictTransformSeq TX.I (Fin.last _)).subschemeι ≫ (BED TX).composite ≫
      (TX.X.left ↘ Spec (CommRingCat.of k))) := by
  obtain ⟨d, hd⟩ := TX.smoothOfRelativeDimension
  have : Smooth ((BED TX).composite ≫ (TX.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := d) (isOrderGeSeq_BED TX).1 (Fin.last _)
  exact HasSncWith.smooth ((BED TX).composite ≫ (TX.X.left ↘ Spec (.of k)))
    (BED_hasSncWith_strictTransform_last_of_embeddedEnd TX h)

include h in
/-- Clause (e) of [Wlo05, Theorem 1.0.2] in the fine form of [Wlo05, Theorem 4.7.1], from the end
data: the pull-back of `I_Y` to the end result is the final strict transform of `Y` times the
ideal of a simple normal crossing divisor supported on the final boundary. -/
theorem BED_comap_composite_eq_strictTransform_mul_sncDivisor_of_embeddedEnd :
    ∃ J : ((BED TX).stage (Fin.last _)).IdealSheafData, IsIdealOfSncDivisor J ∧
      J.support ≤ ((BED TX).totalTransformSeq TX.E (Fin.last _)).support ∧
      TX.I.comap (BED TX).composite = (BED TX).strictTransformSeq TX.I (Fin.last _) * J := by
  obtain ⟨d, hd⟩ := TX.smoothOfRelativeDimension
  have hrun := isOrderGeSeq_BED TX
  refine ⟨∏ j : Fin (BED TX).length,
    ((BED TX).exceptionalAt j).comap ((BED TX).stageMapBetween (Fin.last _) j.succ (Fin.le_last _)),
    isIdealOfSncDivisor_prod_comap_exceptionalAt ⟨TX, 1⟩ (BED TX) hrun, ?_, ?_⟩
  · rw [support_finset_prod]
    refine iSup₂_le fun j _ => IsConcreteLE.le_iff.mpr fun b hb => ?_
    rw [mem_support_comap_iff_apply] at hb
    exact preimage_stageMapBetween_support_subset (BED TX) TX.E (Fin.le_last _)
      (support_exceptionalAt_le_support_totalTransformSeq (BED TX) TX.E j hb)
  · rw [comap_composite_eq_markedTransformSeq_last_mul_prod (BED TX) TX.I 1
      (exceptionalAt_pow_dvd_comap_step_of_isOrderGeSeq (TX.X.left ↘ Spec (.of k)) d (BED TX) TX.I 1
        TX.E hrun),
      strictTransformSeq_BED_last_eq_prod_of_embeddedEnd TX h]
    congr 1
    · exact h.marked_eq
    · exact Finset.prod_congr rfl fun j _ => by rw [pow_one]

end OfEnd

end Hironaka.Resolution
