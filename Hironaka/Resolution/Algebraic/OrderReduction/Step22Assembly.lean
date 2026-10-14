/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step22RestrictToHypersurface
public import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Resolution.Algebraic.BoundaryClearing.Tuned
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Cosupp
import Hironaka.Scheme.BlowUpSequence.ConcatMaxOrd
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2 of order reduction: the assembled sequence and the maximal-contact case

Steps 1 and 2 of the proof of [Kol07, Theorem 103]: on a triple with a smooth hypersurface of
maximal contact, `BO_{n,m}(X, I, E)` is Step 2.1 followed by Step 2.2 on the tuned ideal
`W_{s(m)}(I)`, and the empty sequence when `max-ord I < m`.

* **Step 2** (`step2Seq = S₁.concat step22`) is a smooth blow-up sequence of order `m` for
  `(X, I, E)` (`isOrderSeq_concat`, the second part being an order-`m` sequence for the original
  boundary by `isOrderSeq_step22_totalTransformSeq`), without empty blow-ups
  (`noEmptyCenters_concat`), whose final ideal has `max-ord < m`
  (`maxOrd_weakTransformSeq_concat_last` reduces it to `maxOrd_step22_lt`); the deletion of empty
  blow-ups of [Kol07, 32] is the identity on it.
* **`BO^H_{n,m}`** (`maxContactCase`) is read back through the tuning of Step 1
  (`Hironaka.BD.isOrderSeq_iff_tuned`, `maxOrd_weakTransformSeq_lt_iff_tuned`): a smooth blow-up
  sequence of order `m` for the original `(X, I, E)`, without empty blow-ups, with
  `max-ord I_r < m` (clause (1) of Theorem 103); below the mark the empty sequence, for which
  clause (1) is `max-ord I < m` itself.

These are the fields of the local functor of Step 3
(`Hironaka/Resolution/Algebraic/OrderReduction/Step3Globalization.lean`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData IsLocalRing

namespace Hironaka.BO

section Step2

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m j) (hm : 1 ≤ m)
  {H : T.X.left.IdealSheafData}
  (hH : IsSmoothDivisor H) (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)

/-- Step 2 is Step 2.1 followed by Step 2.2 (definitional). -/
theorem step2Seq_eq :
    step2Seq T hn hmax bd hm hH hle =
      (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.concat (step22 T hn hmax bd hm hH hle) :=
  rfl

/-- Step 2 is a smooth blow-up sequence of order `m` starting with `(X, I, E)` (Step 2 of the
proof of [Kol07, Theorem 103]): `isOrderSeq_concat`, Step 2.2 being an order-`m` sequence for the
original boundary `E_r`. -/
theorem isOrderSeq_step2Seq :
    (step2Seq T hn hmax bd hm hH hle).IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m :=
  isOrderSeq_concat _ _ _ (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι))
    (isOrderSeq_step22_totalTransformSeq T hn hmax bd hm hH hle)

/-- Step 2 has no empty blow-up ([Kol07, 32]). -/
theorem noEmptyCenters_step2Seq : (step2Seq T hn hmax bd hm hH hle).NoEmptyCenters :=
  noEmptyCenters_concat _ _ (noEmptyCenters_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι))
    (noEmptyCenters_step22 T hn hmax bd hm hH hle)

/-- The final ideal of Step 2 has `max-ord < m` (clause (1) of [Kol07, Theorem 103] for Step 2):
it is the final ideal of Step 2.2 up to the identification of the last stages. -/
theorem maxOrd_step2Seq_lt :
    ((step2Seq T hn hmax bd hm hH hle).weakTransformSeq T.I (Fin.last _)).maxOrd < (m : ℕ∞) := by
  exact (maxOrd_weakTransformSeq_concat_last (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1
    (step22 T hn hmax bd hm hH hle) T.I).trans_lt (maxOrd_step22_lt T hn hmax bd hm hH hle)

/-- Deleting the empty blow-ups of Step 2 changes nothing: there are none ([Kol07, 32]). -/
theorem eraseEmpty_step2Seq :
    (step2Seq T hn hmax bd hm hH hle).eraseEmpty = step2Seq T hn hmax bd hm hH hle :=
  (eraseEmpty_eq_self_iff _).mpr (noEmptyCenters_step2Seq T hn hmax bd hm hH hle)

end Step2

section Assembly

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hT : Triple.BOClass n m T)
  {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H) (bd : ∀ m j : ℕ,
      BDData.{u} n m j)

/-- At the mark, `BO^H_{n,m}(X, I, E)` is Step 2 on the tuned triple `(X, W_{s(m)}(I), E)` at the
mark `s(m)`, with `H` kept (`retune_keeps_maxContact`): Step 1 of the proof of
[Kol07, Theorem 103]. -/
theorem maxContactCase_of_maxOrd_eq (h : T.I.maxOrd = m) :
    maxContactCase T hT hH hle bd =
      step2Seq (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1) (le_of_eq (maxOrd_tuned h hT.1)) bd
        (one_le_tuningParam m) hH (retune_keeps_maxContact h hT.1 hle) :=
  dite_eq_left h

/-- Below the mark, `BO^H_{n,m}(X, I, E)` is the empty sequence (the remark after
[Kol07, Theorem 68]). -/
theorem maxContactCase_of_maxOrd_lt (h : T.I.maxOrd < m) :
    maxContactCase T hT hH hle bd = BlowUpSequence.nil T.X.left :=
  dite_eq_right h.ne

/-- `BO^H_{n,m}(X, I, E)` is a smooth blow-up sequence of order `m` starting with `(X, I, E)`:
Step 2 on the tuned triple, read back through `Hironaka.BD.isOrderSeq_iff_tuned`
([Kol07, Corollary 101]), or the empty sequence. -/
theorem isOrderSeq_maxContactCase :
    (maxContactCase T hT hH hle bd).IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m := by
  by_cases h : T.I.maxOrd = m
  · rw [maxContactCase_of_maxOrd_eq T hT hH hle bd h]
    obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
    exact (Hironaka.BD.isOrderSeq_iff_tuned (T.X.left ↘ Spec (.of k)) d _ T.I T.E m h hT.1).mpr
      (isOrderSeq_step2Seq (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1)
        (le_of_eq (maxOrd_tuned h hT.1)) bd (one_le_tuningParam m) hH
        (retune_keeps_maxContact h hT.1 hle))
  · rw [maxContactCase_of_maxOrd_lt T hT hH hle bd (lt_of_le_of_ne hT.2.2 h)]
    exact ⟨isSmooth_nil _, fun i => i.elim0⟩

/-- `BO^H_{n,m}(X, I, E)` has no empty blow-up ([Kol07, 32]). -/
theorem noEmptyCenters_maxContactCase : (maxContactCase T hT hH hle bd).NoEmptyCenters := by
  by_cases h : T.I.maxOrd = m
  · rw [maxContactCase_of_maxOrd_eq T hT hH hle bd h]
    exact noEmptyCenters_step2Seq _ _ _ _ _ _ _
  · rw [maxContactCase_of_maxOrd_lt T hT hH hle bd (lt_of_le_of_ne hT.2.2 h)]
    exact fun i => i.elim0

/-- `max-ord I_r < m` at the end of `BO^H_{n,m}(X, I, E)` (clause (1) of [Kol07, Theorem 103]):
Step 2's `max-ord < s(m)` for the tuned ideal read back through
`maxOrd_weakTransformSeq_lt_iff_tuned`; below the mark, `max-ord I < m` itself. -/
theorem maxOrd_maxContactCase_lt :
    ((maxContactCase T hT hH hle bd).weakTransformSeq T.I (Fin.last _)).maxOrd < (m : ℕ∞) := by
  by_cases h : T.I.maxOrd = m
  · rw [maxOrd_weakTransformSeq_last_congr (maxContactCase_of_maxOrd_eq T hT hH hle bd h) T.I]
    obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
    have hS := isOrderSeq_step2Seq (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1)
      (le_of_eq (maxOrd_tuned h hT.1)) bd (one_le_tuningParam m) hH
      (retune_keeps_maxContact h hT.1 hle)
    exact (maxOrd_weakTransformSeq_lt_iff_tuned (T.X.left ↘ Spec (.of k)) d _ T.I T.E m h hT.1
      ((Hironaka.BD.isOrderSeq_iff_tuned (T.X.left ↘ Spec (.of k)) d _ T.I T.E m h hT.1).mpr hS)).mp
      (maxOrd_step2Seq_lt (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1)
        (le_of_eq (maxOrd_tuned h hT.1)) bd (one_le_tuningParam m) hH
        (retune_keeps_maxContact h hT.1 hle))
  · have hlt : T.I.maxOrd < m := lt_of_le_of_ne hT.2.2 h
    rw [maxOrd_weakTransformSeq_last_congr (maxContactCase_of_maxOrd_lt T hT hH hle bd hlt) T.I]
    exact hlt

/-- Deleting the empty blow-ups of `BO^H_{n,m}(X, I, E)` changes nothing: there are none
([Kol07, 32]). -/
theorem eraseEmpty_maxContactCase :
    (maxContactCase T hT hH hle bd).eraseEmpty = maxContactCase T hT hH hle bd :=
  (eraseEmpty_eq_self_iff _).mpr (noEmptyCenters_maxContactCase T hT hH hle bd)

end Assembly

end Hironaka.BO
