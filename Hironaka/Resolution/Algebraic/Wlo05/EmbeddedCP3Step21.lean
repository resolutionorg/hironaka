/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3EraseEmpty
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Raw
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Transport
import Hironaka.Scheme.BlowUpSequence.Remark67
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP3 along Step 2.1

Step 2.1 of the proof of [Kol07, Theorem 103] (item 104, Step 2.1) passes over the members `Eʲ` of
the boundary in order, each pass being the output `BD_{N,1,j}` of [Kol07, Lemma 102] on the triple
induced at the end of the previous ones (`step21Seq`,
`Hironaka.Resolution.Algebraic.OrderReduction.Step21BoundaryClearing`). For the statement CP3 of the
embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): CP3 along
each pass is `cp3For_rawSeq_member` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Raw`), since
the value of the functor `bdData` at the mark `1` is `rawSeq` on the tuned triple with its empty
blow-ups deleted (`dataFunctor_seq_of_maxOrd_eq`, `functor_seq`, `cp3For_eraseEmpty`; below the mark
the output is empty), and the passes concatenate (`cp3For_concat`). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Tower`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BO Hironaka.BD Hironaka.Local IsLocalRing
  Hironaka.Stage

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Step2

variable {N : ℕ} (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
  (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
  (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
    T'.toTriple.HasDimLE (N - 1) → T'.m = tuningParam m → Dom k T')
  (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
    ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
  (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
  (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
    (B k).CommutesWithBaseChange (B L) σ)

/-- `cp3For_rawSeq_member` with the mark carried as a variable equal to `1`: the form the tuned
triple of `bdData` produces (its mark is `tuningParam 1`). -/
theorem cp3For_rawSeq_member_of_eq_one {Dom' : MarkedTriple k → Prop}
    (B' : OrderGeSeqAssignment k Dom') (T : Triple k) (j : T.E.ι) (m : ℕ) (hm1 : m = 1)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) (hn : T.HasDimLE N)
    (hDom' : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (N - 1) → T'.m = m → Dom' T')
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom' T'), T'.m = 1 → CP3For (B'.seq T' hT') T'.I T'.E) :
    CP3For (rawSeq T m j hI hmax hn B' hDom') T.I T.E := by
  subst hm1
  exact cp3For_rawSeq_member B' T j hI hmax hn hDom' hcp3

/-- CP3 along the output of `BD_{N,1,j}` on a triple of its class ([Kol07, Lemma 102] with the data
`bdData` at the mark `1`; the deletion of empty blow-ups of [Kol07, 32]): below the mark the
output is empty; at the mark the tuning is the identity (`W_tuningParam_one`) and the value is
`rawSeq` on the tuned triple with its empty blow-ups deleted (`cp3For_eraseEmpty`). -/
theorem cp3For_bdData_seq {j : ℕ} (T : Triple k) (hT : Triple.BDClass N 1 j T)
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 →
      CP3For ((B k).seq T' hT') T'.I T'.E) :
    CP3For (((bdData N 1 j Dom B (hDom 1) hB hsm hbc).functor k).seq T hT) T.I T.E := by
  change CP3For ((dataFunctor N 1 j le_rfl (B k) (hDom 1 k)).seq T hT) _ _
  rcases lt_or_eq_of_le hT.2.1 with hlt | heq
  · rw [dataFunctor_seq_of_maxOrd_lt N 1 j le_rfl (B k) (hDom 1 k) T hT hlt]
    intro i
    exact i.elim0
  · rw [dataFunctor_seq_of_maxOrd_eq N 1 j le_rfl (B k) (hDom 1 k) T hT heq, functor_seq]
    obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
    have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
    have hIt : (T.tuned 1 le_rfl).I = T.I := Scheme.IdealSheafData.W_tuningParam_one _ _
    have key : ∀ (m : ℕ), m = 1 →
        ∀ (hI : (T.tuned 1 le_rfl).I.IsDBalanced (T.X.left ↘ Spec (.of k)) m)
          (hmax : (T.tuned 1 le_rfl).I.maxOrd = m)
          (hDom'' : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (N - 1) → T'.m = m → Dom k T'),
          CP3For (rawSeq (T.tuned 1 le_rfl) m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2⟩) hI hmax
            (hasDimLE_tuned hT.1 1 le_rfl) (B k) hDom'').eraseEmpty
            (T.tuned 1 le_rfl).I (T.tuned 1 le_rfl).E := by
      intro m hm1 hI hmax hDom''
      subst hm1
      exact cp3For_eraseEmpty (T.X.left ↘ Spec (.of k)) n' _ _ _
        (IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (.of k)) n'
          (isOrderSeq_rawSeq _ 1 _ hI hmax _ (B k) hDom''))
        (cp3For_rawSeq_member (B k) _ _ hI hmax _ hDom'' hcp3)
    have h := key (tuningParam 1) tuningParam_one (domain_tuned le_rfl hT heq).2.1
      (domain_tuned le_rfl hT heq).2.2.1 (hDom 1 k)
    exact (congrArg (fun J => CP3For _ J T.E) hIt).mp h

variable (T : Triple k) (hn : T.HasDimLE N) (hmax : T.I.maxOrd ≤ 1) {H : T.X.left.IdealSheafData}
  (hH : IsSmoothDivisor H) (hle : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec
      (.of k)) T.I 1 H)

/-- **CP3 along Step 2.1** ([Kol07, 104, Step 2.1]): the passes over the members in order, each the
output of Lemma 102 on the triple induced at the end of the previous passes
(`bdClass_induced_last`), concatenated (`cp3For_concat`; the ideal of the induced triple is the
weak transform, which is the marked transform at the mark `1`, [Kol07, Remark 67]). -/
theorem cp3For_step21Seq
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 →
      CP3For ((B k).seq T' hT') T'.I T'.E) (j : ℕ) :
    CP3For (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).1
      T.I T.E := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  induction j with
  | zero =>
    intro i
    exact i.elim0
  | succ j ih =>
    simp only [step21Seq]
    by_cases hj : j < Fintype.card T.E.ι
    · rw [dite_eq_left hj]
      refine cp3For_concat _ _ T.I T.E ih ?_
      have h := cp3For_bdData_seq Dom B hDom hB hsm hbc
        (T.induced (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).1
          (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).2.1
          (Fin.last _))
        (bdClass_induced_last T hn hmax
          (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).2.1
          (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).2.2 hj) hcp3
      rwa [IsOrderSeq.markedTransformSeq_eq_weakTransformSeq (T.X.left ↘ Spec (.of k)) n'
        (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).2.1]
    · rw [dite_eq_right hj]
      exact ih

end Step2

end Hironaka.Resolution
