/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctor
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEndBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEraseEmpty
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorSplit
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedOrderGe
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullback
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Scheme.FiniteType
public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.Resolution.Defs
import Hironaka.Scheme.Resolution.Basic

/-!
# The clauses of Włodarczyk's Theorem 1.0.2 for the functor `EDFunctor`

The clauses of [Wlo05, Theorem 1.0.2] for the embedded desingularization functor
`Hironaka.Resolution.EDFunctor` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctor`), in the form
used by `AlgebraicGeometry.exists_functorial_embeddedDesingularization`, stated and proved at the
end of this file: for a smooth, quasi-compact, separated `X` of finite type over
`k`, equidimensional (`hX`), and a REDUCED closed subscheme `Y`. Nothing is proved twice: the proofs
live here and the main theorem applies them.

**Why the statements hold.** The functor runs `BED` (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`)
on the CORE of `Y` — the reduced ideal of `V(Y) ∩ X₁`, `X₁` the union of the irreducible components
of `X` not inside `V(Y)` (`coreIdeal`, `componentsOutside`) — which is nonzero everywhere, as the
triples of `BED` require (`EDFunctor_seq_of_pos`). On the smooth `X` the components are pairwise
disjoint, so `X = X₀ ⊔ X₁` is a clopen split with `Y|_{X₀} = 0` and `core|_{X₁} = Y|_{X₁}`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorSplit`). Hence:

* the clauses about the run alone — smooth centres, and clause (a) — are those of `BED` at the core
  triple (`BED_center_smooth`, `BED_isSnc_totalTransformSeq`, `BED_hasSncWith_center`,
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedOrderGe`);
* clause (b): a point of a centre lies over `X₁` (no centre lies over `X₀`: the run has order `≥ 1`
  for the core, whose cosupport misses `X₀`), where the strict transforms and the smooth points of
  `Y` and of its core agree; then `BED_center_disjoint_reg` at the core
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow`);
* clause (c) and the fine form of clause (e): the end data of the CP loop at the core
  (`BED_strictTransform_last_smooth_of_embeddedEnd`,
  `BED_hasSncWith_strictTransform_last_of_embeddedEnd`,
  `BED_comap_composite_eq_strictTransform_mul_sncDivisor_of_embeddedEnd` at
  `embeddedEnd_BED_of_invCE`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEndBridge` and
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge`), transported to `Y`: over `X₁` the last
  strict transforms agree, over `X₀` that of `Y` is zero on a smooth stage
  (`smooth_strictTransformSeq_last_of_coreIdeal`, `hasSncWith_strictTransformSeq_last_of_coreIdeal`,
  `comap_composite_eq_strictTransform_mul_of_coreIdeal`);
* clause (d), in its two forms: the core commutes with a smooth `h` (`coreIdeal_comap`, the
  exchange of components for flat `h`), the empty boundary pulls back to itself, and the hypothesis
  that the image of `h` meets every component transfers to the core (`hmeets_coreIdeal`); then
  `bed_pullback_of_surjective` and `bed_pullback_eraseEmpty` at the two core triples
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullback`,
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEraseEmpty`; the commutation with smooth morphisms of
  [Kol07, 34.1]).

The triples are those of [Kol07, Notation 64]. The reduction to the core is not in the
literature.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme Hironaka IdealSheafData BlowUpSequence

namespace Hironaka.Resolution.EDFunctor

variable {k : Type u} [Field k] [CharZero k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k))] [Smooth (X ↘ Spec (CommRingCat.of k))]
  (hX : ∃ n : ℕ, SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k)))
  (Y : X.IdealSheafData) [IsReduced Y.subscheme]

include hX in
/-- Smooth centres for the functor: `BED_center_smooth` at the core triple
(`EDFunctor_seq_of_pos`). -/
theorem center_smooth :
    ∀ i : Fin ((Hironaka.Resolution.EDFunctor k).seq X Y).length,
      Smooth ((((Hironaka.Resolution.EDFunctor k).seq X Y).center i).subschemeι ≫
        ((Hironaka.Resolution.EDFunctor k).seq X Y).stageMap i.castSucc ≫
          (X ↘ Spec (CommRingCat.of k))) := by
  have _ : IsReduced Y.subscheme := inferInstance
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  have := isReduced_subscheme_coreIdeal Y
  rw [EDFunctor_seq_of_pos X Y hX]
  exact BED_center_smooth _ (inferInstanceAs (IsEmpty PEmpty))

include hX in
/-- Clause (a) of [Wlo05, Theorem 1.0.2], first part, for the functor:
`BED_isSnc_totalTransformSeq` at the core triple. -/
theorem isSnc_totalTransformSeq :
    ∀ i : Fin (((Hironaka.Resolution.EDFunctor k).seq X Y).length + 1),
      (((Hironaka.Resolution.EDFunctor k).seq X Y).totalTransformSeq
        (DivisorFamily.empty X) i).IsSnc := by
  have _ : IsReduced Y.subscheme := inferInstance
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  have := isReduced_subscheme_coreIdeal Y
  rw [EDFunctor_seq_of_pos X Y hX]
  exact BED_isSnc_totalTransformSeq _ (inferInstanceAs (IsEmpty PEmpty))

include hX in
/-- Clause (a) of [Wlo05, Theorem 1.0.2], second part, for the functor: `BED_hasSncWith_center` at
the core triple. -/
theorem hasSncWith_center :
    ∀ i : Fin ((Hironaka.Resolution.EDFunctor k).seq X Y).length,
      (((Hironaka.Resolution.EDFunctor k).seq X Y).totalTransformSeq (DivisorFamily.empty X)
        i.castSucc).HasSncWith (((Hironaka.Resolution.EDFunctor k).seq X Y).center i) := by
  have _ : IsReduced Y.subscheme := inferInstance
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  have := isReduced_subscheme_coreIdeal Y
  rw [EDFunctor_seq_of_pos X Y hX]
  exact BED_hasSncWith_center _ (inferInstanceAs (IsEmpty PEmpty))

include hX in
/-- Clause (b) of [Wlo05, Theorem 1.0.2] for the functor: a point of a centre lies over `X₁`,
where the strict transforms and the smooth points of `Y` and of its core agree
(`stageMap_notMem_image_smoothLocus_of_coreIdeal`); then `BED_center_disjoint_reg` at the core
triple. -/
theorem center_disjoint_reg :
    ∀ (i : Fin ((Hironaka.Resolution.EDFunctor k).seq X Y).length)
      (x : ((Hironaka.Resolution.EDFunctor k).seq X Y).stage i.castSucc),
      x ∈ (((Hironaka.Resolution.EDFunctor k).seq X Y).center i).support →
        x ∈ (((Hironaka.Resolution.EDFunctor k).seq X Y).strictTransformSeq Y i.castSucc).support →
          ((Hironaka.Resolution.EDFunctor k).seq X Y).stageMap i.castSucc x ∉
            Y.subschemeι ''
              ((Y.subschemeι ≫ (X ↘ Spec (CommRingCat.of k))).smoothLocus : Set _) := by
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  have := isReduced_subscheme_coreIdeal Y
  refine stageMap_notMem_image_smoothLocus_of_coreIdeal X Y ?_
  rw [EDFunctor_seq_of_pos X Y hX]
  exact BED_center_disjoint_reg _ (inferInstanceAs (IsEmpty PEmpty))

include hX in
/-- Clause (c) of [Wlo05, Theorem 1.0.2], first part, for the functor: the clause for `BED` at the
core triple (`BED_strictTransform_last_smooth_of_embeddedEnd` at `embeddedEnd_BED_of_invCE`),
transported to `Y` (`smooth_strictTransformSeq_last_of_coreIdeal`: over `X₁` the last strict
transforms agree, over `X₀` that of `Y` is zero on the smooth last stage). -/
theorem strictTransform_last_smooth :
    Smooth ((((Hironaka.Resolution.EDFunctor k).seq X Y).strictTransformSeq Y
        (Fin.last ((Hironaka.Resolution.EDFunctor k).seq X Y).length)).subschemeι ≫
      ((Hironaka.Resolution.EDFunctor k).seq X Y).composite ≫ (X ↘ Spec (CommRingCat.of k))) := by
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  have := isReduced_subscheme_coreIdeal Y
  rcases id hX with ⟨n, hn⟩
  have : Smooth (((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) ≫
      (X ↘ Spec (CommRingCat.of k))) := by
    rw [EDFunctor_seq_of_pos X Y hX]
    exact IsSmooth.smooth_stageMap (f := X ↘ Spec (CommRingCat.of k)) (n := n)
        (isOrderGeSeq_BED _).1 _
  refine smooth_strictTransformSeq_last_of_coreIdeal X Y ?_
  rw [EDFunctor_seq_of_pos X Y hX]
  exact BED_strictTransform_last_smooth_of_embeddedEnd _
    (embeddedEnd_BED_of_invCE _ (inferInstanceAs (IsEmpty PEmpty)))

include hX in
/-- Clause (c) of [Wlo05, Theorem 1.0.2], second part, for the functor: the clause for `BED` at
the core triple (`BED_hasSncWith_strictTransform_last_of_embeddedEnd` at
`embeddedEnd_BED_of_invCE`), transported to `Y`
(`hasSncWith_strictTransformSeq_last_of_coreIdeal`). -/
theorem hasSncWith_strictTransform_last :
    (((Hironaka.Resolution.EDFunctor k).seq X Y).totalTransformSeq (DivisorFamily.empty X)
        (Fin.last ((Hironaka.Resolution.EDFunctor k).seq X Y).length)).HasSncWith
      (((Hironaka.Resolution.EDFunctor k).seq X Y).strictTransformSeq Y
        (Fin.last ((Hironaka.Resolution.EDFunctor k).seq X Y).length)) := by
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  have := isReduced_subscheme_coreIdeal Y
  rcases id hX with ⟨n, hn⟩
  have : Smooth (((EDFunctor k).seq X Y).stageMap (Fin.last ((EDFunctor k).seq X Y).length) ≫
      (X ↘ Spec (CommRingCat.of k))) := by
    rw [EDFunctor_seq_of_pos X Y hX]
    exact IsSmooth.smooth_stageMap (f := X ↘ Spec (CommRingCat.of k)) (n := n)
        (isOrderGeSeq_BED _).1 _
  refine hasSncWith_strictTransformSeq_last_of_coreIdeal X Y ?_
  rw [EDFunctor_seq_of_pos X Y hX]
  exact BED_hasSncWith_strictTransform_last_of_embeddedEnd _
    (embeddedEnd_BED_of_invCE _ (inferInstanceAs (IsEmpty PEmpty)))

include hX in
/-- Clause (e) of [Wlo05, Theorem 1.0.2] in the fine form for the functor: the clause for `BED` at
the core triple (`BED_comap_composite_eq_strictTransform_mul_sncDivisor_of_embeddedEnd` at
`embeddedEnd_BED_of_invCE`), with the same snc divisor `J`; the factorisation transfers stalkwise
(`comap_composite_eq_strictTransform_mul_of_coreIdeal`). -/
theorem comap_composite_eq_strictTransform_mul_sncDivisor :
    ∃ J : (((Hironaka.Resolution.EDFunctor k).seq X Y).stage
        (Fin.last ((Hironaka.Resolution.EDFunctor k).seq X Y).length)).IdealSheafData,
      IsIdealOfSncDivisor J ∧
        J.support ≤ (((Hironaka.Resolution.EDFunctor k).seq X Y).totalTransformSeq
          (DivisorFamily.empty X)
          (Fin.last ((Hironaka.Resolution.EDFunctor k).seq X Y).length)).support ∧
        Y.comap ((Hironaka.Resolution.EDFunctor k).seq X Y).composite =
          ((Hironaka.Resolution.EDFunctor k).seq X Y).strictTransformSeq Y
            (Fin.last ((Hironaka.Resolution.EDFunctor k).seq X Y).length) * J := by
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  have := isReduced_subscheme_coreIdeal Y
  have hcore : ∃ J : (((EDFunctor k).seq X Y).stage
      (Fin.last ((EDFunctor k).seq X Y).length)).IdealSheafData,
      IsIdealOfSncDivisor J ∧
        J.support ≤ (((EDFunctor k).seq X Y).totalTransformSeq (DivisorFamily.empty X)
          (Fin.last ((EDFunctor k).seq X Y).length)).support ∧
        (coreIdeal Y).comap ((EDFunctor k).seq X Y).composite =
          ((EDFunctor k).seq X Y).strictTransformSeq (coreIdeal Y)
            (Fin.last ((EDFunctor k).seq X Y).length) * J := by
    rw [EDFunctor_seq_of_pos X Y hX]
    exact BED_comap_composite_eq_strictTransform_mul_sncDivisor_of_embeddedEnd _
      (embeddedEnd_BED_of_invCE _ (inferInstanceAs (IsEmpty PEmpty)))
  obtain ⟨J, hJ₁, hJ₂, hJ₃⟩ := hcore
  exact ⟨J, hJ₁, hJ₂, comap_composite_eq_strictTransform_mul_of_coreIdeal X Y J hJ₃⟩

include hX in
/-- Clause (d) of [Wlo05, Theorem 1.0.2], for a smooth surjection: the core commutes with the
smooth `h` (`coreIdeal_comap`), so the two values are `BED` at the two core triples, one the
pull-back data of the other; then `bed_pullback_of_surjective`. -/
theorem pullback_of_surjective (X' : Scheme.{u}) [X'.Over (Spec (CommRingCat.of k))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X' ↘ Spec (CommRingCat.of k))] [Smooth (X' ↘ Spec (CommRingCat.of k))]
    (hX' : ∃ n : ℕ, SmoothOfRelativeDimension n (X' ↘ Spec (CommRingCat.of k)))
    (h : X' ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] [Smooth h] (hs : Function.Surjective h) :
    (Hironaka.Resolution.EDFunctor k).seq X' (Y.comap h) =
      ((Hironaka.Resolution.EDFunctor k).seq X Y).pullback h := by
  have _ : IsReduced Y.subscheme := inferInstance
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  have := noetherianSpace_of_field (X' ↘ Spec (CommRingCat.of k))
  have := isReduced_subscheme_coreIdeal Y
  rw [EDFunctor_seq_of_pos X Y hX, EDFunctor_seq_of_pos X' (Y.comap h) hX']
  refine bed_pullback_of_surjective
    (⟨.of X, hX, coreIdeal Y, isNonzeroEverywhere_coreIdeal Y, DivisorFamily.empty X,
      isSnc_empty_of_smooth (X ↘ Spec (CommRingCat.of k))⟩ : Triple k)
    (⟨.of X', hX', coreIdeal (Y.comap h), isNonzeroEverywhere_coreIdeal (Y.comap h),
      DivisorFamily.empty X',
      isSnc_empty_of_smooth (X' ↘ Spec (CommRingCat.of k))⟩ : Triple k)
    ?_ h hs ?_
  · exact inferInstanceAs (IsEmpty PEmpty)
  exact ⟨(HomIsOver.comp_over :
      h ≫ (X ↘ Spec (CommRingCat.of k)) = X' ↘ Spec (CommRingCat.of k)),
    coreIdeal_comap h Y, (empty_comap h).symm⟩

include hX in
/-- Clause (d) of [Wlo05, Theorem 1.0.2], for a smooth morphism whose image meets every irreducible
component of `Y`: as for a surjection, with the image hypothesis transferred to the core
(`hmeets_coreIdeal`); then `bed_pullback_eraseEmpty`. -/
theorem pullback_eraseEmpty (X' : Scheme.{u}) [X'.Over (Spec (CommRingCat.of k))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X' ↘ Spec (CommRingCat.of k))] [Smooth (X' ↘ Spec (CommRingCat.of k))]
    (hX' : ∃ n : ℕ, SmoothOfRelativeDimension n (X' ↘ Spec (CommRingCat.of k)))
    (h : X' ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] [Smooth h]
    (hmeets : ∀ η ∈ (Y.support : Set X), (∀ η' ∈ (Y.support : Set X), η' ⤳ η → η' = η) →
      (Set.range h ∩ closure {η}).Nonempty) :
    (Hironaka.Resolution.EDFunctor k).seq X' (Y.comap h) =
      (((Hironaka.Resolution.EDFunctor k).seq X Y).pullback h).eraseEmpty := by
  have _ : IsReduced Y.subscheme := inferInstance
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  have := noetherianSpace_of_field (X' ↘ Spec (CommRingCat.of k))
  have := isReduced_subscheme_coreIdeal Y
  rw [EDFunctor_seq_of_pos X Y hX, EDFunctor_seq_of_pos X' (Y.comap h) hX']
  refine bed_pullback_eraseEmpty
    (⟨.of X, hX, coreIdeal Y, isNonzeroEverywhere_coreIdeal Y, DivisorFamily.empty X,
      isSnc_empty_of_smooth (X ↘ Spec (CommRingCat.of k))⟩ : Triple k)
    (⟨.of X', hX', coreIdeal (Y.comap h), isNonzeroEverywhere_coreIdeal (Y.comap h),
      DivisorFamily.empty X',
      isSnc_empty_of_smooth (X' ↘ Spec (CommRingCat.of k))⟩ : Triple k)
    ?_ h ?_ (hmeets_coreIdeal (X ↘ Spec (CommRingCat.of k)) Y h hmeets)
  · exact inferInstanceAs (IsEmpty PEmpty)
  exact ⟨(HomIsOver.comp_over :
      h ≫ (X ↘ Spec (CommRingCat.of k)) = X' ↘ Spec (CommRingCat.of k)),
    coreIdeal_comap h Y, (empty_comap h).symm⟩

end Hironaka.Resolution.EDFunctor

namespace Hironaka.Resolution

/-- The side condition of the deletion form of clause (d) of [Wlo05, Theorem 1.0.2] in the form
`EDFunctor.pullback_eraseEmpty` takes it: if the image of `h` meets every irreducible component of
the closed subscheme `Y`, it meets the closure of every point of `V(Y)` maximal for
specialization. Such a point `η = ι y` is the generic point of the component `closure {y}` of `Y`
(a generic point `g` of an irreducible `Z ⊇ closure {y}` specializes to `y`, so `ι g = η` by
maximality and `g = y`), and `ι` carries `closure {y}` into `closure {η}`. -/
theorem range_inter_closure_nonempty_of_forall_irreducibleComponents {X X' : Scheme.{u}}
    (Y : X.IdealSheafData) (h : X' ⟶ X)
    (hZ : ∀ Z ∈ irreducibleComponents Y.subscheme, (Set.range h ∩ Y.subschemeι '' Z).Nonempty) :
    ∀ η ∈ (Y.support : Set X), (∀ η' ∈ (Y.support : Set X), η' ⤳ η → η' = η) →
      (Set.range h ∩ closure {η}).Nonempty := by
  intro η hη hmax
  rw [← Y.range_subschemeι] at hη
  obtain ⟨y, rfl⟩ := hη
  have hinj : Function.Injective Y.subschemeι := Y.subschemeι.isClosedEmbedding.injective
  have hcomp : closure {y} ∈ irreducibleComponents Y.subscheme := by
    refine ⟨isIrreducible_singleton.closure, fun Z hZirr hsub => ?_⟩
    have hg := hZirr.genericPoint_closure_eq
    have hspec : hZirr.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, hg]
      exact subset_closure (hsub (subset_closure rfl))
    have heq : Y.subschemeι hZirr.genericPoint = Y.subschemeι y :=
      hmax _ (by rw [← Y.range_subschemeι]; exact ⟨_, rfl⟩)
        (hspec.map Y.subschemeι.continuous)
    rw [hinj heq] at hg
    rw [hg]
    exact subset_closure
  obtain ⟨p, hp, hpZ⟩ := hZ _ hcomp
  refine ⟨p, hp, ?_⟩
  have := image_closure_subset_closure_image (f := Y.subschemeι) Y.subschemeι.continuous hpZ
  rwa [Set.image_singleton] at this

end Hironaka.Resolution

end

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme

namespace AlgebraicGeometry

/-- **Włodarczyk's embedded desingularization with smooth centres** [Wlo05, Theorem 1.0.2]. There
is a family `ED` of blow-up sequence functors on embedded pairs
(`BlowUpSequenceFunctor (EmbeddedPair k)`), one for each field `k` of characteristic zero, such
that
* every value `S = ED(X, Y)`, with composite `σ : X_r → X`, exceptional divisors `E_i` (the total
  transforms of the empty divisor family) and strict transforms `Y_i` of `Y`, is an embedded
  desingularization of the pair (`EmbeddedPair.IsDesingularizedBy`): every centre `C_i` is smooth
  over `k`; (a) every `E_i`, the last included, is a simple normal crossing family, and `C_i` has
  simple normal crossings with `E_i`; (b) no point of `C_i ∩ Y_i` lies over a point of `Reg(Y)`,
  the image in `X` of the smooth locus of `Y → Spec k` (the points where `Y`, not `Y_i`, is
  smooth); (c) `Ỹ = Y_r` is smooth over `k` and has simple normal crossings with `E_r`; (e)
  `σ^*(I_Y) = I_Ỹ · J` for the ideal sheaf `J` of a simple normal crossing divisor supported in
  `E_r`;
* (d) for a morphism of embedded pairs `h : (X', Y') ⟶ (X, Y)` whose underlying morphism is
  smooth, `ED(X', Y')` is the pull-back `h^* S` if `h` is surjective, and `h^* S` with the empty
  blow-ups deleted if the image of `h` meets every irreducible component of `Y`
  (`CommutesWithSmoothMorphismsMeetingComponents`).

An embedded pair (`EmbeddedPair`) is a reduced closed subscheme `Y` of a smooth, equidimensional
algebraic `k`-scheme `X` (smooth of one relative dimension over `k`); a morphism
`(X', Y') ⟶ (X, Y)` is a `k`-morphism `h : X' → X` along which the ideal sheaf of `Y` pulls back to
that of `Y'`. If `Y = X` (the ideal sheaf `⊥`), (b) forces every centre to be empty. If `Y` is
empty or smooth, the clauses on `S` alone hold for the empty succession.

Relation to the source.
* **Translation.** `S.totalTransformSeq (DivisorFamily.empty _) i` is Włodarczyk's exceptional
  divisor $E_i$, `S.strictTransformSeq P.Y i` his strict transform $Y_i$, and the image in `X` of
  the smooth locus of `Y → Spec k` is his $\operatorname{Reg}(Y)$.
* **Interpretation.** Włodarczyk's "subvariety $Y$ of a smooth variety $X$" is read as a reduced
  closed subscheme `Y` of a smooth, equidimensional algebraic `k`-scheme `X` (`EmbeddedPair`). His
  Bravo–Villamayor strengthening, the source of clause (e), is stated for "a reduced closed
  subscheme" [Wlo05, Theorem 4.7.1].
* **Gap.** In clause (e), $\sigma^*(I_Y) = I_{\tilde Y} I_{\tilde E}$, Włodarczyk's divisor
  $\tilde E$ is "a natural combination of the irreducible components of the divisor $E_r$"; here `J`
  is only asked to be the ideal sheaf of a simple normal crossing divisor supported in $E_r$.
* **Gap.** In clause (d) the deletion form, in which `ED(X', Y')` is the pull-back of `ED(X, Y)`
  with the empty blow-ups deleted, is asserted only when the image of `h` meets every component of
  `Y`, whereas Włodarczyk's (d), read through his Definition 2.1.5 (extensions by isomorphisms) and
  Proposition 2.4.2, asserts it for every smooth `h`. The construction handles the components of `Y`
  in rounds whose boundary data depend on all of them, and over an open subset missing a component
  the runs fall out of step: for `Y` the disjoint union of a smooth surface and the three coordinate
  axes through a point off it, in a smooth threefold, the pull-back of `ED(X, Y)` to the complement
  of the surface has three non-empty centres that the run on that complement lacks.
* **Gap.** The parts of Włodarczyk's (d) on embeddings of ambient varieties and on equivariance
  under group actions have no counterpart; in particular, although the family `ED` has one functor
  for each field, no clause relates the functors of different fields, as Kollár's change of fields
  [Kol07, 34.2] (`CommutesWithChangeOfFields`) does. The functor built here is not Włodarczyk's
  single invariant-driven run, and functoriality for closed embeddings is, in Kollár's words, "quite
  delicate" [Kol07, 34 and Claim 71.2]: he proves it only for an empty boundary, whereas the later
  rounds here run with the exceptional divisors of the earlier ones as boundary.

Source statement: [Wlo05, Theorem 1.0.2] -/
theorem exists_functorial_embeddedDesingularization :
    ∃ ED : ∀ (k : Type u) [Field k] [CharZero k], BlowUpSequenceFunctor (EmbeddedPair k),
      (∀ (k : Type u) [Field k] [CharZero k] (P : EmbeddedPair k),
        P.IsDesingularizedBy (ED k P)) ∧
      ∀ (k : Type u) [Field k] [CharZero k],
        CommutesWithSmoothMorphismsMeetingComponents (ED k) := by
  refine ⟨fun k _ _ P => (Hironaka.Resolution.EDFunctor k).seq P.X.left P.Y,
    fun _ _ _ P => ?_, fun _ _ _ => ⟨?_, ?_⟩⟩
  · have := P.isReduced
    exact ⟨fun i =>
        ⟨Hironaka.Resolution.EDFunctor.center_smooth P.X.left P.smoothOfRelativeDimension P.Y i,
          Hironaka.Resolution.EDFunctor.hasSncWith_center P.X.left P.smoothOfRelativeDimension
            P.Y i⟩,
      Hironaka.Resolution.EDFunctor.isSnc_totalTransformSeq P.X.left P.smoothOfRelativeDimension
        P.Y,
      Hironaka.Resolution.EDFunctor.center_disjoint_reg P.X.left P.smoothOfRelativeDimension P.Y,
      Hironaka.Resolution.EDFunctor.strictTransform_last_smooth P.X.left
        P.smoothOfRelativeDimension P.Y,
      Hironaka.Resolution.EDFunctor.hasSncWith_strictTransform_last P.X.left
        P.smoothOfRelativeDimension P.Y,
      Hironaka.Resolution.EDFunctor.comap_composite_eq_strictTransform_mul_sncDivisor P.X.left
        P.smoothOfRelativeDimension P.Y⟩
  · rintro P Q ⟨h, hY⟩ hs hsurj
    have : Smooth h.left := hs
    have := P.isReduced
    change (Hironaka.Resolution.EDFunctor _).seq Q.X.left Q.Y =
      ((Hironaka.Resolution.EDFunctor _).seq P.X.left P.Y).pullback h.left
    rw [hY]
    exact Hironaka.Resolution.EDFunctor.pullback_of_surjective P.X.left
      P.smoothOfRelativeDimension P.Y Q.X.left Q.smoothOfRelativeDimension h.left hsurj
  · rintro P Q ⟨h, hY⟩ hs hmeets
    have : Smooth h.left := hs
    have := P.isReduced
    change (Hironaka.Resolution.EDFunctor _).seq Q.X.left Q.Y =
      (((Hironaka.Resolution.EDFunctor _).seq P.X.left P.Y).pullback h.left).eraseEmpty
    rw [hY]
    exact Hironaka.Resolution.EDFunctor.pullback_eraseEmpty P.X.left
      P.smoothOfRelativeDimension P.Y Q.X.left Q.smoothOfRelativeDimension h.left
      (Hironaka.Resolution.range_inter_closure_nonempty_of_forall_irreducibleComponents P.Y h.left
        hmeets)

end AlgebraicGeometry
