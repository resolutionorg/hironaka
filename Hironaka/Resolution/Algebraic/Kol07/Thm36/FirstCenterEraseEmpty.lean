/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.EraseEmptyIndex
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The first-centre index across the deletion of empty blow-ups

Kollár's functoriality under smooth morphisms compares a blow-up sequence with a pullback from
which the empty blow-ups have been deleted [Kol07, 34.1; item 32]. The affine resolution
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`) truncates the principalization run at a
first-centre index, so the index has to be read through the deletion. `eraseIdx S m`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.EraseEmptyIndex`) is the position in `S.eraseEmpty` of
the `m`-th stage of `S`; for an integral closed subscheme `V(J)` the absorbing stage, the first
centre containing the strict transform of `V(J)`, has a nonempty centre
(`center_firstCenterIndex_ne_top`: the strict transform of an integral subscheme keeps a generic
point up to that stage), so the predicate `CenterContains` transports through
`centerContains_eraseEmpty_iff`:

* `firstCenterIndex_eraseEmpty`: the equality
  `firstCenterIndex S.eraseEmpty J = eraseIdx S (firstCenterIndex S J)`; no deleted (empty) centre
  before the absorbing stage contains the transform, and the absorbing centre survives the
  deletion; when no centre ever contains the transform both indices are the lengths;
* `take_eraseEmpty_firstCenterIndex`: the truncations at the first containing index correspond
  under the deletion (`eraseEmpty_take`).

Stated for any blow-up sequence on a locally Noetherian scheme; used by
`Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- The index of the length is the length of the erased sequence: every kept stage advances the
index by one. -/
theorem eraseIdx_length : ∀ {X : Scheme.{u}} (S : BlowUpSequence X),
    eraseIdx S S.length = S.eraseEmpty.length
  | _, nil _ => rfl
  | _, cons X D rest => by
    classical
    by_cases hD : D = ⊤
    · have := isIso_blowUpπ_of_eq_top hD
      rw [show (cons X D rest).length = rest.length + 1 from rfl,
        eraseIdx_cons_succ_of_eq_top rest hD, eraseEmpty_cons_of_eq_top rest hD, length_pullback,
        eraseIdx_length rest]
    · rw [show (cons X D rest).length = rest.length + 1 from rfl,
        eraseIdx_cons_succ_of_ne_top rest hD, eraseEmpty_cons_of_ne_top rest hD,
        show (cons X D rest.eraseEmpty).length = rest.eraseEmpty.length + 1 from rfl,
        eraseIdx_length rest]

/-- Up to the first containing index the strict transform of an integral `V(J)` is nonempty: it
keeps a generic point (`exists_isGenericPoint_strictTransformSeq_of_le_firstCenterIndex`). -/
theorem strictTransformSeq_ne_top_of_le_firstCenterIndex [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (J : X.IdealSheafData) [IsIntegral J.subscheme] (i : Fin (S.length + 1))
    (hi : i.val ≤ firstCenterIndex S J) : S.strictTransformSeq J i ≠ ⊤ := by
  obtain ⟨η, hη⟩ := exists_isGenericPoint_support J
  obtain ⟨η', hη', -, -⟩ :=
    exists_isGenericPoint_strictTransformSeq_of_le_firstCenterIndex S J hη i hi
  intro h
  have hmem := hη'.mem
  rw [h] at hmem
  simp at hmem

/-- The first containing centre of an integral `V(J)` is a nonempty centre: an empty centre `⊤`
containing the strict transform would force the strict transform to be `⊤`. -/
theorem center_firstCenterIndex_ne_top [IsLocallyNoetherian X] (S : BlowUpSequence X)
    (J : X.IdealSheafData) [IsIntegral J.subscheme] (h : ∃ n, CenterContains S J n) :
    S.center ⟨firstCenterIndex S J, firstCenterIndex_lt_length h⟩ ≠ ⊤ := by
  intro htop
  obtain ⟨hn, hle⟩ := firstCenterIndex_of_exists h
  have hst : S.strictTransformSeq J ⟨firstCenterIndex S J, Nat.lt_succ_of_lt hn⟩ = ⊤ := by
    apply top_le_iff.mp
    have hle' : S.center ⟨firstCenterIndex S J, hn⟩ ≤
        S.strictTransformSeq J ⟨firstCenterIndex S J, Nat.lt_succ_of_lt hn⟩ := hle
    rwa [htop] at hle'
  exact strictTransformSeq_ne_top_of_le_firstCenterIndex S J _ le_rfl hst

/-- For an integral `V(J)`, the first containing index of the sequence with its empty blow-ups
deleted is the image under `eraseIdx S` of the first containing index of `S` [Kol07, 34.1; item
32]: before the absorbing stage no deleted (empty) centre contains the transform, and the absorbing
centre is nonempty; when no centre ever contains the transform, both indices are the lengths. -/
theorem firstCenterIndex_eraseEmpty [IsLocallyNoetherian X] (S : BlowUpSequence X)
    (J : X.IdealSheafData) [IsIntegral J.subscheme] :
    firstCenterIndex S.eraseEmpty J = eraseIdx S (firstCenterIndex S J) := by
  classical
  by_cases h : ∃ n, CenterContains S J n
  · have hlt : firstCenterIndex S J < S.length := firstCenterIndex_lt_length h
    have hne := center_firstCenterIndex_ne_top S J h
    have hc : CenterContains S.eraseEmpty J (eraseIdx S (firstCenterIndex S J)) :=
      (centerContains_eraseEmpty_iff S J _ hlt hne).2 (firstCenterIndex_of_exists h)
    have h' : ∃ n, CenterContains S.eraseEmpty J n := ⟨_, hc⟩
    apply le_antisymm
    · unfold firstCenterIndex
      rw [dite_eq_left h']
      exact Nat.find_min' h' hc
    · by_contra hlt'
      push Not at hlt'
      have hc' := firstCenterIndex_of_exists h'
      obtain ⟨n, hn, hne', he, hnm⟩ := exists_eraseIdx_eq_of_lt S hc'.1 hlt'
      rw [← he] at hc'
      exact not_centerContains_of_lt_firstCenterIndex h hnm
        ((centerContains_eraseEmpty_iff S J n hn hne').1 hc')
  · have h' : ¬ ∃ n, CenterContains S.eraseEmpty J n := by
      rintro ⟨n', hn'⟩
      obtain ⟨n, hn, hne, he⟩ := exists_eraseIdx_eq S n' hn'.1
      rw [← he] at hn'
      exact h ⟨n, (centerContains_eraseEmpty_iff S J n hn hne).1 hn'⟩
    unfold firstCenterIndex
    rw [dite_eq_right h, dite_eq_right h', eraseIdx_length]

/-- The truncations at the first containing index correspond under the deletion of empty blow-ups
(`eraseEmpty_take`). -/
theorem take_eraseEmpty_firstCenterIndex [IsLocallyNoetherian X] (S : BlowUpSequence X)
    (J : X.IdealSheafData) [IsIntegral J.subscheme] :
    S.eraseEmpty.take (firstCenterIndex S.eraseEmpty J) =
      (S.take (firstCenterIndex S J)).eraseEmpty := by
  rw [firstCenterIndex_eraseEmpty, eraseEmpty_take]

end Hironaka.Resolution
