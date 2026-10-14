/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step21BoundaryClearing
import Hironaka.Resolution.Algebraic.Kol07.CosuppTransport
import Hironaka.Resolution.Algebraic.Kol07.TotalTransformPositions
import Hironaka.Scheme.BlowUpSequence.TrivialCenter
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.1 of order reduction: the rounds and the disjointness from the boundary

The `j`-th round of Step 2.1 of the proof of [Kol07, Theorem 103] ([Kol07, 104, Step 2.1])
applies the boundary-clearing functor of [Kol07, Lemma 102] to the induced triple and to the
transform of the `j`-th member, so that afterwards `Π⁻¹_{r(j)*}(E^i) ∩ cosupp(I_{r(j)}, m) = ∅`
for every `i ≤ j`. This module reads off the two branches of the definition of `BO.step21Seq`
(`step21Seq_zero`, `step21Seq_succ_of_lt`, `step21Seq_succ_of_not_lt`) and its two carried facts
(`isOrderSeq_step21Seq`, `noEmptyCenters_step21Seq`), and proves the disjointness by induction on
the number of rounds (`disjoint_cosupp_step21`). At round `j`, the disjointness for the new
member `E^j` is clause (1) of [Kol07, Lemma 102] for `BD_{n,m,j}` on the induced triple
(`BDData.disjoint_cosupp`), read on the original family through the positions of the total
transform (`nth_totalTransformSeq_of_lt`) and transported through the concatenation
(`disjoint_cosupp_concat_iff`); for the old members `E^i`, `i < j`, the disjointness at the end of
the previous round persists along the `j`-th round because every centre of a blow-up of order `m`
lies in the cosupport (`disjoint_cosupp_strictTransformSeq_last_of_disjoint`). After all
`card E.ι` rounds the birational transform of every member misses the cosupport
(`disjoint_cosupp_step21_final`), the first of the two conclusions Kollár records at the end of
Step 2.1.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.BO

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ j : ℕ, BDData.{u} n m j)

/-- Step 2.1 begins with the empty sequence. -/
theorem step21Seq_zero : (step21Seq T hn hmax bd 0).1 = BlowUpSequence.nil T.X.left :=
  rfl

/-- The sequence after `j + 1` rounds is the sequence after `j` rounds followed by `BD_{n,m,j}`
applied to the induced triple, for a position `j` of `E` ([Kol07, 104, Step 2.1]). -/
theorem step21Seq_succ_of_lt (j : ℕ) (hj : j < Fintype.card T.E.ι) :
    (step21Seq T hn hmax bd (j + 1)).1 =
      (step21Seq T hn hmax bd j).1.concat
        (((bd j).functor k).seq
          (T.induced (step21Seq T hn hmax bd j).1 (step21Seq T hn hmax bd j).2.1 (Fin.last _))
          (bdClass_induced_last T hn hmax (step21Seq T hn hmax bd j).2.1
            (step21Seq T hn hmax bd j).2.2 hj)) := by
  rw [step21Seq, dite_eq_left hj]

/-- Beyond the last position the sequence is unchanged. -/
theorem step21Seq_succ_of_not_lt (j : ℕ) (hj : ¬ j < Fintype.card T.E.ι) :
    (step21Seq T hn hmax bd (j + 1)).1 = (step21Seq T hn hmax bd j).1 := by
  rw [step21Seq, dite_eq_right hj]

/-- Every Step 2.1 sequence is a smooth blow-up sequence of order `m` starting with `(X, I, E)`:
the first carried fact. -/
theorem isOrderSeq_step21Seq (j : ℕ) :
    (step21Seq T hn hmax bd j).1.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m :=
  (step21Seq T hn hmax bd j).2.1

/-- No Step 2.1 sequence has an empty blow-up ([Kol07, 32]): the second carried fact. -/
theorem noEmptyCenters_step21Seq (j : ℕ) : (step21Seq T hn hmax bd j).1.NoEmptyCenters :=
  (step21Seq T hn hmax bd j).2.2

/-- After `j` rounds, the birational transforms of the first `j` members of `E` are disjoint from
the cosupport of the final ideal ([Kol07, 104, Step 2.1]). -/
theorem disjoint_cosupp_step21 (j : ℕ) {i : ℕ} (hi : i < Fintype.card T.E.ι) (hij : i < j) :
    Disjoint
      {x | (m : ℕ∞) ≤
        ((step21Seq T hn hmax bd j).1.weakTransformSeq T.I (Fin.last _)).ord x}
      (((step21Seq T hn hmax bd j).1.strictTransformSeq (T.E.nth ⟨i, hi⟩)
        (Fin.last _)).support : Set _) := by
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero _)
  | succ j ih =>
    by_cases hj : j < Fintype.card T.E.ι
    · refine (disjoint_cosupp_congr (step21Seq_succ_of_lt T hn hmax bd j hj) T.I _ m).mpr ?_
      refine (disjoint_cosupp_concat_iff _ _ _ _ _).mpr ?_
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | heq
      · -- an already cleared member: the disjointness persists along the `j`-th round
        obtain ⟨n', hn'⟩ :=
          (T.induced (step21Seq T hn hmax bd j).1 (step21Seq T hn hmax bd j).2.1
            (Fin.last _)).smoothOfRelativeDimension
        exact disjoint_cosupp_strictTransformSeq_last_of_disjoint n' _ _
          (((bd j).functor k).isOrderSeq _ _) _ (ih hlt)
      · -- the member cleared at this round: clause (1) of Lemma 102, read on the original family
        subst heq
        have hd := (bd i).disjoint_cosupp k
          (T.induced (step21Seq T hn hmax bd i).1 (step21Seq T hn hmax bd i).2.1 (Fin.last _))
          (bdClass_induced_last T hn hmax (step21Seq T hn hmax bd i).2.1
            (step21Seq T hn hmax bd i).2.2 hj)
        rw [show (T.induced (step21Seq T hn hmax bd i).1 (step21Seq T hn hmax bd i).2.1
            (Fin.last _)).E.nth ⟨i, (bdClass_induced_last T hn hmax (step21Seq T hn hmax bd i).2.1
              (step21Seq T hn hmax bd i).2.2 hj).2.2⟩ =
            (step21Seq T hn hmax bd i).1.strictTransformSeq (T.E.nth ⟨i, hi⟩) (Fin.last _) from
          nth_totalTransformSeq_of_lt _ _ _ hi] at hd
        exact hd
    · refine (disjoint_cosupp_congr (step21Seq_succ_of_not_lt T hn hmax bd j hj) T.I _ m).mpr ?_
      exact ih (lt_of_lt_of_le hi (Nat.le_of_not_lt hj))

/-- After all `card E.ι` rounds, the birational transform of every member of `E` misses the
cosupport of the final ideal: the first conclusion of [Kol07, 104, Step 2.1],
"`Π^{-1}_{r(s)*} E` is disjoint from `cosupp(I_{r(s)}, m)`". -/
theorem disjoint_cosupp_step21_final {i : ℕ} (hi : i < Fintype.card T.E.ι) :
    Disjoint
      {x | (m : ℕ∞) ≤
        ((step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.weakTransformSeq T.I (Fin.last _)).ord x}
      (((step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.strictTransformSeq (T.E.nth ⟨i, hi⟩)
        (Fin.last _)).support : Set _) :=
  disjoint_cosupp_step21 T hn hmax bd (Fintype.card T.E.ι) hi hi

end Hironaka.BO
