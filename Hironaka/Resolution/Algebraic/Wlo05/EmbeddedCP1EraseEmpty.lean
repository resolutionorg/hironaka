/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.EraseEmptyIndex
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainExtendsByEmpty
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.TakeLast
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 across the deletion of empty blow-ups

Step 2.2 of the order reduction is the deletion of the empty blow-ups from the blow-up of `Z₋₁`
followed by the pushforward of the run on the hypersurface ([Kol07, 34.1] and [Kol07, 32] for
the deletion; `Hironaka.OrderReduction.Step22*`). CP1
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For`) passes across the deletion: an empty centre
(`⊤`) contains no nonempty strict transform, and the strict transform of the component stays
nonempty before its absorption (the generic lift, `exists_genericLift`), so the first containing
indices correspond (`centerContains_eraseEmpty_iff`, `eraseIdx`, `exists_eraseIdx_eq`); the stage
data agree through `eraseEmpty_take`, the `_eraseEmpty_last` identities along the last-stage
isomorphism `eraseEmptyLastHom` and the bridges of `Hironaka.Scheme.BlowUpSequence.TakeLast`, and
the induced family of the erased sequence differs from the pullback of the original's by unit
members only (`eraseEmbeds_eraseEmpty`), which the chain form ignores
(`chainRelativeAt_of_extendsByEmpty`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainExtendsByEmpty`). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3EraseEmpty`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- A non-empty centre advances the erased index: for `l < m` with `Z_l ≠ ⊤`,
`eraseIdx S l < eraseIdx S m`. -/
theorem eraseIdx_lt_of_ne_top_of_lt : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) {l m : ℕ}
    (hl : l < S.length), S.center ⟨l, hl⟩ ≠ ⊤ → l < m → eraseIdx S l < eraseIdx S m
  | _, nil _, _, _, hl, _, _ => absurd hl (Nat.not_lt_zero _)
  | _, cons _ _ _, _, 0, _, _, hlm => absurd hlm (Nat.not_lt_zero _)
  | _, cons X D rest, 0, m + 1, _, hD, _ => by
    classical
    have hD' : D ≠ ⊤ := hD
    change eraseIdx (cons X D rest) 0 < (if D = ⊤ then 0 else 1) + eraseIdx rest m
    rw [eraseIdx_cons_zero, ite_eq_right hD']
    omega
  | _, cons X D rest, l + 1, m + 1, hl, hD, hlm => by
    classical
    change (if D = ⊤ then 0 else 1) + eraseIdx rest l <
      (if D = ⊤ then 0 else 1) + eraseIdx rest m
    exact Nat.add_lt_add_left
      (eraseIdx_lt_of_ne_top_of_lt rest (Nat.lt_of_succ_lt_succ hl) hD
        (Nat.lt_of_succ_lt_succ hlm)) _

variable {k : Type u} [Field k] [CharZero k]

/-- CP1 across the deletion of empty blow-ups: CP1 along a run of order `≥ 1` for `(I, 1, E)`
passes to the erased run. The member hypotheses (`cp1For_concat`'s) keep the component's strict
transform nonempty before its absorption, so that a deleted centre never counts as containing
it. -/
theorem cp1For_eraseEmpty (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (S : BlowUpSequence X) (I : X.IdealSheafData)
    (E : DivisorFamily X) {η : X} (hη : η ∈ I.support.genericPoints)
    (hηE : ∀ j, η ∉ (E.component j).support)
    (hIc : I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (hS : S.IsOrderGeSeq f I 1 E) (h : CP1For S I E η) : CP1For S.eraseEmpty I E η := by
  have := isLocallyNoetherian_of_smoothOfRelativeDimension f n
  intro i' hi' hmin'
  obtain ⟨m, hm, hne, hem⟩ := exists_eraseIdx_eq S i'.val i'.isLt
  -- the stage `m` of `S` is a containing stage
  have hcont : CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure {η})) m := by
    have hiff := centerContains_eraseEmpty_iff S (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) m hm hne
    rw [hem] at hiff
    exact hiff.mp hi'
  -- and the first one: a deleted centre contains no nonempty strict transform
  have hminS : ∀ l < m, ¬ CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure
      {η})) l := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
    intro hl hcl
    obtain ⟨hl', hle⟩ := hcl
    by_cases hlt : S.center ⟨l, hl'⟩ = ⊤
    · obtain ⟨η', hη'⟩ := exists_genericLift S I E 1 hη hηE hIc ⟨l, Nat.lt_succ_of_lt hl'⟩
        fun l'' hl'' => ih l'' hl'' (lt_trans hl'' hl)
      have htop : S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
          ⟨l, Nat.lt_succ_of_lt hl'⟩ = ⊤ := by
        rw [hlt] at hle
        exact top_le_iff.mp hle
      have hmem := hη'.mem_support
      rw [htop, IdealSheafData.support_top, ← SetLike.mem_coe, Closeds.coe_bot] at hmem
      exact hmem
    · have hlt2 : eraseIdx S l < i'.val := by
        rw [← hem]
        exact eraseIdx_lt_of_ne_top_of_lt S hl' hlt hl
      exact hmin' (eraseIdx S l) hlt2
        ((centerContains_eraseEmpty_iff S (IdealSheafData.vanishingIdeal (Closeds.closure
            {η})) l hl' hlt).mpr
          ⟨hl', hle⟩)
  -- CP1 for `S` at stage `m`
  have hA := h ⟨m, hm⟩ hcont hminS
  -- ... on the last stage of the prefix `S.take m`
  have hmle : m ≤ S.length := hm.le
  have hB := forall_chainRelativeAt_of_heq (stage_take_last S hmle)
    (totalTransformSeq_take_last_heq S E hmle) (markedTransformSeq_take_last_heq S I 1 hmle)
    (strictTransformSeq_take_last_heq S (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) hmle) hA
  -- ... on the last stage of the erased prefix, through the last-stage isomorphism
  have hRord := isOrderGeSeq_take f I 1 E hS m
  have hiso : IsIso (S.take m).eraseEmptyLastHom := isIso_eraseEmptyLastHom (S.take m)
  have hmarked := markedTransformSeq_eraseEmpty_last (S.take m) f n I 1 E hRord
  have hstrict :=
    strictTransformSeq_eraseEmpty_last (S.take m) (IdealSheafData.vanishingIdeal (Closeds.closure
        {η}))
  obtain ⟨e, hcompE, htopE, -⟩ := eraseEmbeds_eraseEmpty (S.take m) E
  have hext : ExtendsByEmpty ((S.take m).eraseEmpty.totalTransformSeq E (Fin.last _))
      (((S.take m).totalTransformSeq E (Fin.last _)).comap (S.take m).eraseEmptyLastHom) :=
    ⟨e, e.injective, fun i => hcompE i, fun b hb => htopE b hb⟩
  have hC : ∀ q ∈ ((S.take m).eraseEmpty.strictTransformSeq (IdealSheafData.vanishingIdeal
      (Closeds.closure {η}))
      (Fin.last _)).support,
      ChainRelativeAt ((S.take m).eraseEmpty.totalTransformSeq E (Fin.last _))
        ((S.take m).eraseEmpty.markedTransformSeq I 1 (Fin.last _))
        ((S.take m).eraseEmpty.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
            {η}))
          (Fin.last _)) q := by
    intro q hq
    have hq' : (S.take m).eraseEmptyLastHom q ∈ ((S.take m).strictTransformSeq
        (IdealSheafData.vanishingIdeal (Closeds.closure {η})) (Fin.last _)).support := by
      rw [hstrict] at hq
      exact (mem_support_comap_iff_apply _ _ _).mp hq
    rw [hmarked, hstrict]
    exact (chainRelativeAt_of_extendsByEmpty hext).mpr
      (@chainRelativeAt_comap_of_isIso_stalkMap _ _ _ hiso _ _ _ q (hB _ hq'))
  -- ... on the last stage of the erased sequence's prefix at `i'`
  have e₁ : S.eraseEmpty.take i'.val = (S.take m).eraseEmpty := by
    rw [← hem]
    exact eraseEmpty_take S m
  have hD : ∀ q ∈ ((S.eraseEmpty.take i'.val).strictTransformSeq
      (IdealSheafData.vanishingIdeal (Closeds.closure {η})) (Fin.last _)).support,
      ChainRelativeAt ((S.eraseEmpty.take i'.val).totalTransformSeq E (Fin.last _))
        ((S.eraseEmpty.take i'.val).markedTransformSeq I 1 (Fin.last _))
        ((S.eraseEmpty.take i'.val).strictTransformSeq (IdealSheafData.vanishingIdeal
            (Closeds.closure {η}))
          (Fin.last _)) q := by
    rw [e₁]
    exact hC
  -- ... and at the stage `i'` of the erased sequence
  have hi'le : i'.val ≤ S.eraseEmpty.length := i'.isLt.le
  exact forall_chainRelativeAt_of_heq (stage_take_last S.eraseEmpty hi'le).symm
    (totalTransformSeq_take_last_heq S.eraseEmpty E hi'le).symm
    (markedTransformSeq_take_last_heq S.eraseEmpty I 1 hi'le).symm
    (strictTransformSeq_take_last_heq S.eraseEmpty (IdealSheafData.vanishingIdeal (Closeds.closure
        {η}))
      hi'le).symm hD

end Hironaka.Resolution
