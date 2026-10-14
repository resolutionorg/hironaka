/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferentFunctor
public import Hironaka.Resolution.Algebraic.OrderReduction.Step2Functorial
public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferent
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalFamilyErasure
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Bookkeeping
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Assembly
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2 of order reduction is indifferent to empty boundary members

Kollár's convention [Kol07, 32] and the reindexing of [Kol07, 34.1]: deleting unit-ideal members of
the boundary changes nothing. This module proves it for the maximal-contact case of
[Kol07, Theorem 103] (`Hironaka.BO.maxContactCase`, Steps 1–2 of the proof) under two hypotheses
on the boundary-clearing data of [Kol07, Lemma 102] at every mark: `hind`, the rounds at matched
positions agree (`BDFamily.IndifferentToEmptyMembers`), and `hnil`, the round of a unit member is
`nil` (`BDFamily.NilAtUnitMember`,
`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferentFunctor.lean`). Both hold for the
boundary-clearing data of `Hironaka/Resolution/Algebraic/BoundaryClearing/`.

* **Step 2.1** ([Kol07, 104, Step 2.1]; `step21Seq`, one round per member in order): by induction
  on the position `j` of the larger boundary `E`, the sequence after `j` rounds equals the sequence
  of the smaller boundary `E'` after `erasureCount E E' e j` rounds, the number of members of `E'`
  whose partner sits below position `j`. A deleted member's round is `nil` (`hnil`: its transform
  is the unit ideal at every stage, `strictTransformSeq_top`); a surviving member's round is the
  partner's round (`hind` at the matched positions, the deletion carried to the induced boundaries
  by `exists_isTopErasure_totalTransformSeq` and the positions by
  `monoEquivOfFin_totalTransformSeq_of_lt`); at the end the counts are the sizes
  (`erasureCount_card`).
* **Step 2.2** ([Kol07, 104, Step 2.2]; `step22`): the exceptional sub-families of the two
  boundaries at the end of the common Step 2.1 sequence agree up to a surjective order embedding
  (`exists_orderEmbedding_exceptionalFamily`), so the two Step 2.2 input triples
  `(X_r, I_r, F_r + H_r)` differ by a deletion of no members, and `hind` at the mark `s(m)`, at the
  positions `card F_r.ι` and `card F'_r.ι` (`monoEquivOfFin_lex_inr_last`), identifies the values
  through the re-tuning (`step22Functor_seq_of_maxOrd_eq`); below the mark both are `nil`.
* `maxContactCase_indifferentToEmptyMembers` concludes through the case split of `maxContactCase`
  on `max-ord I`.

The abbreviation `Triple.withBoundary` used throughout is defined in
`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferentFunctor.lean`. The globalised functor
is treated in `Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferentGlobal.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence IsLocalRing

namespace Hironaka.BO

/-! ### Counting the surviving positions -/

section Count

variable {X : Scheme.{u}} (E E' : DivisorFamily X) (e : E'.ι ↪o E.ι)

/-- The number of members of `E'` whose partner in `E` along `e` sits at a position below `j`: the
number of Step 2.1 rounds of `(X, I, E')` matched by the first `j` rounds of `(X, I, E)`. Not in
the sources; it makes the reindexing of [Kol07, 34.1] explicit. -/
noncomputable def erasureCount (j : ℕ) : ℕ :=
  Fintype.card {a : E'.ι // ((monoEquivOfFin E.ι rfl).symm (e a) : ℕ) < j}

theorem erasureCount_zero : erasureCount E E' e 0 = 0 :=
  Fintype.card_eq_zero_iff.mpr ⟨fun a => Nat.not_lt_zero _ a.2⟩

theorem erasureCount_succ_of_not_lt {j : ℕ} (hj : ¬ j < Fintype.card E.ι) :
    erasureCount E E' e (j + 1) = erasureCount E E' e j :=
  Fintype.card_congr (Equiv.subtypeEquivRight fun _ =>
    ⟨fun _ => lt_of_lt_of_le (Fin.isLt _) (not_lt.mp hj),
      fun _ => Nat.lt_succ_of_lt (lt_of_lt_of_le (Fin.isLt _) (not_lt.mp hj))⟩)

/-- A position of `E` outside the range of `e` (a deleted member) adds no matched round. -/
theorem erasureCount_succ_of_notMem {j : ℕ} (hj : j < Fintype.card E.ι)
    (h : E.nthIdx ⟨j, hj⟩ ∉ Set.range e) :
    erasureCount E E' e (j + 1) = erasureCount E E' e j :=
  Fintype.card_congr (Equiv.subtypeEquivRight fun a =>
    ⟨fun ha => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp ha with hlt | heq
      · exact hlt
      · exact absurd ⟨a, (monoEquivOfFin E.ι rfl).symm_apply_eq.mp (Fin.ext heq)⟩ h,
      Nat.lt_succ_of_lt⟩)

/-- At a matched position `j = e i'`, the count is the position of `i'` in `E'`. -/
theorem erasureCount_of_mem {j : ℕ} (hj : j < Fintype.card E.ι) {i' : E'.ι}
    (h : e i' = E.nthIdx ⟨j, hj⟩) :
    erasureCount E E' e j = ((monoEquivOfFin E'.ι rfl).symm i' : ℕ) := by
  unfold erasureCount
  rw [← card_subtype_lt_eq_symm_monoEquivOfFin]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  have hi : (monoEquivOfFin E.ι rfl).symm (e i') = ⟨j, hj⟩ :=
    (monoEquivOfFin E.ι rfl).symm_apply_eq.mpr h
  rw [← e.lt_iff_lt, ← (monoEquivOfFin E.ι rfl).symm.lt_iff_lt, hi, Fin.lt_def]

/-- After a matched position `j = e i'`, the count is the position of `i'` in `E'` plus one. -/
theorem erasureCount_succ_of_mem {j : ℕ} (hj : j < Fintype.card E.ι) {i' : E'.ι}
    (h : e i' = E.nthIdx ⟨j, hj⟩) :
    erasureCount E E' e (j + 1) = ((monoEquivOfFin E'.ι rfl).symm i' : ℕ) + 1 := by
  unfold erasureCount
  rw [← card_subtype_le_eq_symm_monoEquivOfFin]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  have hi : (monoEquivOfFin E.ι rfl).symm (e i') = ⟨j, hj⟩ :=
    (monoEquivOfFin E.ι rfl).symm_apply_eq.mpr h
  rw [← e.le_iff_le, ← (monoEquivOfFin E.ι rfl).symm.le_iff_le, hi, Fin.le_def]
  exact Nat.lt_succ_iff

/-- After all positions of `E`, every member of `E'` is matched. -/
theorem erasureCount_card : erasureCount E E' e (Fintype.card E.ι) = Fintype.card E'.ι :=
  Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => Fin.isLt _)

end Count

/-! ### Step 2.1 -/

section Step21

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bdm : ∀ j : ℕ, BDData.{u} n m j) (E' : DivisorFamily T.X.left)
  (hsnc' : E'.IsSnc) (e : E'.ι ↪o T.E.ι)
  (hn₂ : (T.withBoundary E' hsnc').HasDimLE n) (hmax₂ : (T.withBoundary E' hsnc').I.maxOrd ≤ m)

/-- At the end of any smooth blow-up sequence of order `m`, the member at a deleted position of
`E` is the unit ideal, being its birational transform (`component_originalIdx`,
`strictTransformSeq_top`). -/
theorem nth_induced_eq_top (htop : ∀ b, b ∉ Set.range e → T.E.component b = ⊤)
    (S : BlowUpSequence T.X.left) (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) {j : ℕ}
    (hj : j < Fintype.card T.E.ι) (hmem : T.E.nthIdx ⟨j, hj⟩ ∉ Set.range e)
    (hj₁ : j < Fintype.card (T.induced S hS (Fin.last _)).E.ι) :
    (T.induced S hS (Fin.last _)).E.nth ⟨j, hj₁⟩ = ⊤ := by
  have htop' : T.E.component (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩) = ⊤ := htop _ hmem
  have hj₁' : j < Fintype.card (S.totalTransformSeq T.E (Fin.last _)).ι := hj₁
  have h1 : (T.induced S hS (Fin.last _)).E.nth ⟨j, hj₁⟩ =
      (S.totalTransformSeq T.E (Fin.last _)).component
        (S.originalIdx T.E (Fin.last _) (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩)) :=
    congrArg (S.totalTransformSeq T.E (Fin.last _)).component
      (monoEquivOfFin_totalTransformSeq_of_lt S T.E hj hj₁')
  rw [h1, component_originalIdx, htop', strictTransformSeq_top]
  rfl

/-- The rounds of the boundary-clearing data at matched positions of the two induced boundaries
agree: `hind` on the triple induced by the common sequence, with the deletion carried to the
induced boundaries (`exists_isTopErasure_totalTransformSeq`) and the positions by
`monoEquivOfFin_totalTransformSeq_of_lt`. -/
theorem step21Seq_round_indifferent (hind : BDFamily.IndifferentToEmptyMembers bdm)
    (hmem : ∀ i, T.E.component (e i) = E'.component i)
    (htop : ∀ b, b ∉ Set.range e → T.E.component b = ⊤) (S : BlowUpSequence T.X.left)
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) (hne : S.NoEmptyCenters)
    (hS₂ : S.IsOrderSeq ((T.withBoundary E' hsnc').X.left ↘ Spec (.of k))
      (T.withBoundary E' hsnc').I (T.withBoundary E' hsnc').E m) {j j' : ℕ}
    (hj : j < Fintype.card T.E.ι) (hj' : j' < Fintype.card E'.ι)
    (hpos : e (E'.nthIdx ⟨j', hj'⟩) = T.E.nthIdx ⟨j, hj⟩) :
    ((bdm j).functor k).seq (T.induced S hS (Fin.last _))
        (bdClass_induced_last T hn hmax hS hne hj) =
      ((bdm j').functor k).seq ((T.withBoundary E' hsnc').induced S hS₂ (Fin.last _))
        (bdClass_induced_last (T.withBoundary E' hsnc') hn₂ hmax₂ hS₂ hne hj') := by
  obtain ⟨e', he', ho⟩ := exists_isTopErasure_totalTransformSeq S E' T.E e ⟨hmem, htop⟩
  have hT₁ := bdClass_induced_last T hn hmax hS hne hj
  have hT₂ := bdClass_induced_last (T.withBoundary E' hsnc') hn₂ hmax₂ hS₂ hne hj'
  have hc : ∀ i, (T.induced S hS (Fin.last _)).E.component (e' i) =
      ((T.withBoundary E' hsnc').induced S hS₂ (Fin.last _)).E.component i := he'.1
  have ht : ∀ b, b ∉ Set.range e' → (T.induced S hS (Fin.last _)).E.component b = ⊤ := he'.2
  have hj₁ : j < Fintype.card (S.totalTransformSeq T.E (Fin.last _)).ι := hT₁.2.2
  have hj₂ : j' < Fintype.card (S.totalTransformSeq E' (Fin.last _)).ι := hT₂.2.2
  have hpos' : e' (((T.withBoundary E' hsnc').induced S hS₂ (Fin.last _)).E.nthIdx ⟨j', hT₂.2.2⟩) =
      (T.induced S hS (Fin.last _)).E.nthIdx ⟨j, hT₁.2.2⟩ := by
    change e' (monoEquivOfFin (S.totalTransformSeq E' (Fin.last _)).ι rfl ⟨j', hj₂⟩) =
      monoEquivOfFin (S.totalTransformSeq T.E (Fin.last _)).ι rfl ⟨j, hj₁⟩
    rw [monoEquivOfFin_totalTransformSeq_of_lt S E' hj' hj₂,
      monoEquivOfFin_totalTransformSeq_of_lt S T.E hj hj₁, ho]
    exact congrArg _ hpos
  have hT₂' : Triple.BDClass n m j' ({ T.induced S hS (Fin.last _) with
      E := ((T.withBoundary E' hsnc').induced S hS₂ (Fin.last _)).E
      isSnc := ((T.withBoundary E' hsnc').induced S hS₂ (Fin.last _)).isSnc } : Triple k) := hT₂
  exact hind k (T.induced S hS (Fin.last _))
    ((T.withBoundary E' hsnc').induced S hS₂ (Fin.last _)).E
    ((T.withBoundary E' hsnc').induced S hS₂ (Fin.last _)).isSnc e' hc ht j j' hT₁.2.2 hT₂.2.2
    hpos' hT₁ hT₂'

/-- The inductive step at a matched position, on the whole Step 2.1 values: equal sequences after
`j` and `j'` rounds give equal sequences after the next round. -/
theorem step21Seq_succ_indifferent_aux (hind : BDFamily.IndifferentToEmptyMembers bdm)
    (hmem : ∀ i, T.E.component (e i) = E'.component i)
    (htop : ∀ b, b ∉ Set.range e → T.E.component b = ⊤)
    (σ : {S : BlowUpSequence T.X.left // S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m ∧
      S.NoEmptyCenters})
    (σ₂ : {S : BlowUpSequence (T.withBoundary E' hsnc').X.left //
      S.IsOrderSeq ((T.withBoundary E' hsnc').X.left ↘ Spec (.of k)) (T.withBoundary E' hsnc').I
        (T.withBoundary E' hsnc').E m ∧ S.NoEmptyCenters})
    (hσ : σ.1 = σ₂.1) {j j' : ℕ} (hj : j < Fintype.card T.E.ι) (hj' : j' < Fintype.card E'.ι)
    (hpos : e (E'.nthIdx ⟨j', hj'⟩) = T.E.nthIdx ⟨j, hj⟩) :
    σ.1.concat (((bdm j).functor k).seq (T.induced σ.1 σ.2.1 (Fin.last _))
        (bdClass_induced_last T hn hmax σ.2.1 σ.2.2 hj)) =
      σ₂.1.concat (((bdm j').functor k).seq
        ((T.withBoundary E' hsnc').induced σ₂.1 σ₂.2.1 (Fin.last _))
        (bdClass_induced_last (T.withBoundary E' hsnc') hn₂ hmax₂ σ₂.2.1 σ₂.2.2 hj')) := by
  obtain ⟨S, hS⟩ := σ
  obtain ⟨S₂, hS₂⟩ := σ₂
  dsimp only at hσ ⊢
  subst hσ
  exact congrArg S.concat (step21Seq_round_indifferent T hn hmax bdm E' hsnc' e hn₂ hmax₂ hind
    hmem htop S hS.1 hS.2 hS₂.1 hj hj' hpos)

/-- The Step 2.1 sequence of `(X, I, E)` after `j` rounds is the Step 2.1 sequence of `(X, I, E')`
after the matched number of rounds ([Kol07, 104, Step 2.1] with the conventions [Kol07, 32] and
[Kol07, 34.1]): a deleted member's round is `nil` (`hnil`), a surviving member's round is its
partner's (`hind`). -/
theorem step21Seq_indifferent (hind : BDFamily.IndifferentToEmptyMembers bdm)
    (hnil : BDFamily.NilAtUnitMember bdm) (hmem : ∀ i, T.E.component (e i) = E'.component i)
    (htop : ∀ b, b ∉ Set.range e → T.E.component b = ⊤) (j : ℕ) :
    (step21Seq T hn hmax bdm j).1 =
      (step21Seq (T.withBoundary E' hsnc') hn₂ hmax₂ bdm (erasureCount T.E E' e j)).1 := by
  induction j with
  | zero =>
    rw [erasureCount_zero]
    rfl
  | succ j ih =>
    by_cases hj : j < Fintype.card T.E.ι
    · by_cases hin : T.E.nthIdx ⟨j, hj⟩ ∈ Set.range e
      · obtain ⟨i', hi'⟩ := hin
        have hc₀ := erasureCount_of_mem T.E E' e hj hi'
        have hc₁ : erasureCount T.E E' e (j + 1) = erasureCount T.E E' e j + 1 :=
          (erasureCount_succ_of_mem T.E E' e hj hi').trans (congrArg (· + 1) hc₀.symm)
        have hj' : erasureCount T.E E' e j < Fintype.card E'.ι := by
          rw [hc₀]
          exact Fin.isLt _
        have hpos : e (E'.nthIdx ⟨erasureCount T.E E' e j, hj'⟩) = T.E.nthIdx ⟨j, hj⟩ := by
          rw [show E'.nthIdx ⟨erasureCount T.E E' e j, hj'⟩ = i' from
            (congrArg E'.nthIdx (Fin.ext hc₀)).trans
              ((monoEquivOfFin E'.ι rfl).apply_symm_apply i')]
          exact hi'
        rw [hc₁]
        simp only [step21Seq]
        rw [dite_eq_left hj, dite_eq_left hj']
        exact step21Seq_succ_indifferent_aux T hn hmax bdm E' hsnc' e hn₂ hmax₂ hind hmem htop _ _
          ih hj hj' hpos
      · rw [erasureCount_succ_of_notMem T.E E' e hj hin]
        simp only [step21Seq]
        rw [dite_eq_left hj]
        have hrd := hnil k j
          (T.induced (step21Seq T hn hmax bdm j).1 (step21Seq T hn hmax bdm j).2.1 (Fin.last _))
          (bdClass_induced_last T hn hmax (step21Seq T hn hmax bdm j).2.1
            (step21Seq T hn hmax bdm j).2.2 hj)
          (nth_induced_eq_top T E' e htop _ _ hj hin _)
        exact (concat_eq_of_eq_nil (step21Seq T hn hmax bdm j).1 hrd).trans ih
    · rw [erasureCount_succ_of_not_lt T.E E' e hj]
      simp only [step21Seq]
      rw [dite_eq_right hj]
      exact ih

end Step21

/-! ### Step 2.2 and Step 2 -/

section Step22

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (E' : DivisorFamily T.X.left) (hsnc' : E'.IsSnc) (e : E'.ι ↪o T.E.ι)
  (hn₂ : (T.withBoundary E' hsnc').HasDimLE n) (hmax₂ : (T.withBoundary E' hsnc').I.maxOrd ≤ m)
  (bd : ∀ m j : ℕ, BDData.{u} n m j) (hm : 1 ≤ m)

omit hn hmax hn₂ hmax₂ in
/-- Step 2.2 on the two input triples built from the same Step 2.1 sequence agree
([Kol07, 104, Step 2.2] with the reindexing of [Kol07, 34.1]): their boundaries `F_r + H_r` and
`F'_r + H_r` are matched by a surjective order embedding, no member being deleted
(`exists_orderEmbedding_exceptionalFamily`), so `hind` at the mark `s(m)` identifies the re-tuned
values at the positions of `H_r`; below the mark both are `nil`. -/
theorem step22Seq_indifferent_aux (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m))
    (hmem : ∀ i, T.E.component (e i) = E'.component i)
    (htop : ∀ b, b ∉ Set.range e → T.E.component b = ⊤) (S : BlowUpSequence T.X.left)
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hS₂ : S.IsOrderSeq ((T.withBoundary E' hsnc').X.left ↘ Spec (.of k))
      (T.withBoundary E' hsnc').I (T.withBoundary E' hsnc').E m) {H : T.X.left.IdealSheafData}
    (hsnc : ((S.exceptionalFamily T.E).append (S.strictTransformSeq H (Fin.last _))).IsSnc)
    (hsnc₂ : ((S.exceptionalFamily E').append (S.strictTransformSeq H (Fin.last _))).IsSnc)
    {j j' : ℕ} (hj : j = Fintype.card (S.exceptionalFamily T.E).ι)
    (hj' : j' = Fintype.card (S.exceptionalFamily E').ι)
    (hT₂ : Triple.BDClass n m j (step22TripleOfSeq T S hS hsnc))
    (hT₂' : Triple.BDClass n m j' (step22TripleOfSeq (T.withBoundary E' hsnc') S hS₂ hsnc₂)) :
    (step22Functor bd m j hm).seq (step22TripleOfSeq T S hS hsnc) hT₂ =
      (step22Functor bd m j' hm).seq (step22TripleOfSeq (T.withBoundary E' hsnc') S hS₂ hsnc₂)
        hT₂' := by
  subst hj hj'
  by_cases h₂ : (step22TripleOfSeq T S hS hsnc).I.maxOrd = m
  · have h₂' : (step22TripleOfSeq (T.withBoundary E' hsnc') S hS₂ hsnc₂).I.maxOrd = m := h₂
    rw [step22Functor_seq_of_maxOrd_eq bd m _ hm _ hT₂ h₂,
      step22Functor_seq_of_maxOrd_eq bd m _ hm _ hT₂' h₂']
    obtain ⟨g, hgs, hgc⟩ := exists_orderEmbedding_exceptionalFamily S E' T.E e ⟨hmem, htop⟩
    have hTt := bdClass_tuned hT₂ h₂ hm
    have hTt' := bdClass_tuned hT₂' h₂' hm
    have hc : ∀ i, ((step22TripleOfSeq T S hS hsnc).tuned m hm).E.component (sumLexMapEmb g i) =
        ((step22TripleOfSeq (T.withBoundary E' hsnc') S hS₂ hsnc₂).tuned m hm).E.component i := by
      intro i
      obtain ⟨a, rfl⟩ := toLex.surjective i
      rcases a with b | u
      · exact hgc b
      · rfl
    have ht : ∀ b, b ∉ Set.range (sumLexMapEmb g) →
        ((step22TripleOfSeq T S hS hsnc).tuned m hm).E.component b = ⊤ := by
      intro b hb
      exfalso
      obtain ⟨a, rfl⟩ := toLex.surjective b
      rcases a with b₀ | u
      · obtain ⟨c, hc⟩ := hgs b₀
        exact hb ⟨toLex (Sum.inl c), (sumLexMapEmb_apply_inl g c).trans
          (congrArg _ (congrArg _ hc))⟩
      · exact hb ⟨toLex (Sum.inr u), rfl⟩
    have hj₁ : Fintype.card (S.exceptionalFamily T.E).ι <
        Fintype.card ((S.exceptionalFamily T.E).ι ⊕ₗ PUnit.{u + 1}) := hTt.2.2
    have hj₂ : Fintype.card (S.exceptionalFamily E').ι <
        Fintype.card ((S.exceptionalFamily E').ι ⊕ₗ PUnit.{u + 1}) := hTt'.2.2
    have hpos : sumLexMapEmb g (DivisorFamily.nthIdx _ ⟨_, hTt'.2.2⟩) =
        DivisorFamily.nthIdx _ ⟨_, hTt.2.2⟩ := by
      change sumLexMapEmb g
          (monoEquivOfFin ((S.exceptionalFamily E').ι ⊕ₗ PUnit.{u + 1}) rfl ⟨_, hj₂⟩) =
        monoEquivOfFin ((S.exceptionalFamily T.E).ι ⊕ₗ PUnit.{u + 1}) rfl ⟨_, hj₁⟩
      rw [monoEquivOfFin_lex_inr_last hj₂, monoEquivOfFin_lex_inr_last hj₁]
      rfl
    have hTt'' : Triple.BDClass n (tuningParam m) _
        ({ (step22TripleOfSeq T S hS hsnc).tuned m hm with
          E := ((step22TripleOfSeq (T.withBoundary E' hsnc') S hS₂ hsnc₂).tuned m hm).E
          isSnc := ((step22TripleOfSeq (T.withBoundary E' hsnc') S hS₂ hsnc₂).tuned m hm).isSnc } :
          Triple k) := hTt'
    exact hind (tuningParam m) k ((step22TripleOfSeq T S hS hsnc).tuned m hm)
      ((step22TripleOfSeq (T.withBoundary E' hsnc') S hS₂ hsnc₂).tuned m hm).E
      ((step22TripleOfSeq (T.withBoundary E' hsnc') S hS₂ hsnc₂).tuned m hm).isSnc
      (sumLexMapEmb g) hc ht _ _ hTt.2.2 hTt'.2.2 hpos hTt hTt''
  · have hlt : (step22TripleOfSeq T S hS hsnc).I.maxOrd < m := lt_of_le_of_ne hT₂.2.1 h₂
    have hlt' : (step22TripleOfSeq (T.withBoundary E' hsnc') S hS₂ hsnc₂).I.maxOrd < m := hlt
    rw [step22Functor_seq_of_maxOrd_lt bd m _ hm _ hT₂ hlt,
      step22Functor_seq_of_maxOrd_lt bd m _ hm _ hT₂' hlt']
    rfl

variable {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)

/-- Step 2 on `(X, I, E')`, generalised over its Step 2.1 sequence `S₂` with `S₂` equal to the
Step 2.1 sequence of `(X, I, E)`: it is Step 2 on `(X, I, E)`. -/
theorem step2Seq_indifferent_aux (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m))
    (hmem : ∀ i, T.E.component (e i) = E'.component i)
    (htop : ∀ b, b ∉ Set.range e → T.E.component b = ⊤)
    (S₂ : BlowUpSequence (T.withBoundary E' hsnc').X.left)
    (hS₂ : S₂.IsOrderSeq ((T.withBoundary E' hsnc').X.left ↘ Spec (.of k))
      (T.withBoundary E' hsnc').I (T.withBoundary E' hsnc').E m)
    (e₁ : S₂ = (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1)
    (hsnc₂ : ((S₂.exceptionalFamily E').append (S₂.strictTransformSeq H (Fin.last _))).IsSnc)
    (j' : ℕ) (hj' : j' = Fintype.card (S₂.exceptionalFamily E').ι)
    (hT₂' : Triple.BDClass n m j' (step22TripleOfSeq (T.withBoundary E' hsnc') S₂ hS₂ hsnc₂)) :
    S₂.concat ((step22Functor bd m j' hm).seq
        (step22TripleOfSeq (T.withBoundary E' hsnc') S₂ hS₂ hsnc₂) hT₂') =
      step2Seq T hn hmax bd hm hH hle := by
  subst e₁
  exact (congrArg _ (step22Seq_indifferent_aux T E' hsnc' e bd hm hind hmem htop _
    (isOrderSeq_step21Seq T hn hmax (bd m) _) hS₂ (step22Triple T hn hmax bd hm hH hle).isSnc
    hsnc₂ rfl hj' (bdClass_step22Triple T hn hmax bd hm hH hle) hT₂')).symm

/-- Step 2 of the proof of [Kol07, Theorem 103] on `(X, I, E)` and on `(X, I, E')` agree, for `E'`
obtained from `E` by deleting unit members ([Kol07, 104, Steps 2.1–2.2] with the conventions
[Kol07, 32] and [Kol07, 34.1]). -/
theorem step2Seq_indifferent (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m))
    (hnil : ∀ m, BDFamily.NilAtUnitMember (bd m))
    (hmem : ∀ i, T.E.component (e i) = E'.component i)
    (htop : ∀ b, b ∉ Set.range e → T.E.component b = ⊤)
    (hle₂ : IdealSheafData.IsMaximalContact ((T.withBoundary E' hsnc').X.left ↘ Spec (.of k))
      (T.withBoundary E' hsnc').I m H) :
    step2Seq T hn hmax bd hm hH hle =
      step2Seq (T.withBoundary E' hsnc') hn₂ hmax₂ bd hm hH hle₂ := by
  have e₁ : (step21Seq (T.withBoundary E' hsnc') hn₂ hmax₂ (bd m) (Fintype.card E'.ι)).1 =
      (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1 := by
    rw [step21Seq_indifferent T hn hmax (bd m) E' hsnc' e hn₂ hmax₂ (hind m) (hnil m) hmem htop,
      erasureCount_card]
  exact (step2Seq_indifferent_aux T hn hmax E' hsnc' e bd hm hH hle hind hmem htop _
    (isOrderSeq_step21Seq (T.withBoundary E' hsnc') hn₂ hmax₂ (bd m) _) e₁
    (step22Triple (T.withBoundary E' hsnc') hn₂ hmax₂ bd hm hH hle₂).isSnc _ rfl
    (bdClass_step22Triple (T.withBoundary E' hsnc') hn₂ hmax₂ bd hm hH hle₂)).symm

end Step22

/-! ### The maximal-contact case -/

section MaxContactCase

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hT : Triple.BOClass n m T)
  {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H) (bd : ∀ m j : ℕ,
      BDData.{u} n m j)

/-- **The maximal-contact case of [Kol07, Theorem 103] is indifferent to empty boundary members**
([Kol07, 32] and the reindexing of [Kol07, 34.1] for Steps 1–2 of the proof): for a triple of
`BOClass n m` with a smooth hypersurface `H` of maximal contact, and boundary-clearing data at every
mark that are indifferent to empty members (`hind`) and nil at a unit member (`hnil`), deleting
unit members of `E` does not change `BO^H_{n,m}(X, I, E)`. Through the case split of
`maxContactCase`: at the mark, Step 2 on the tuned triples (`step2Seq_indifferent`; tuning keeps
`E`); below the mark both values are `nil`. -/
theorem maxContactCase_indifferentToEmptyMembers
    (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m))
    (hnil : ∀ m, BDFamily.NilAtUnitMember (bd m)) (E' : DivisorFamily T.X.left) (hsnc' : E'.IsSnc)
    (e : E'.ι ↪o T.E.ι) (hmem : ∀ i, T.E.component (e i) = E'.component i)
    (htop : ∀ b, b ∉ Set.range e → T.E.component b = ⊤)
    (hT' : Triple.BOClass n m { T with E := E', isSnc := hsnc' }) :
    maxContactCase T hT hH hle bd =
      maxContactCase { T with E := E', isSnc := hsnc' } hT' hH hle bd := by
  by_cases h₁ : T.I.maxOrd = m
  · have h₁' : ({ T with E := E', isSnc := hsnc' } : Triple k).I.maxOrd = m := h₁
    rw [maxContactCase_of_maxOrd_eq T hT hH hle bd h₁,
      maxContactCase_of_maxOrd_eq _ hT' hH hle bd h₁']
    exact step2Seq_indifferent (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1)
      (le_of_eq (maxOrd_tuned h₁ hT.1)) E' hsnc' e (hasDimLE_tuned hT'.2.1 m hT'.1)
      (le_of_eq (maxOrd_tuned h₁' hT'.1)) bd (one_le_tuningParam m) hH
      (retune_keeps_maxContact h₁ hT.1 hle) hind hnil hmem htop
      (retune_keeps_maxContact h₁' hT'.1 hle)
  · have hlt : T.I.maxOrd < m := lt_of_le_of_ne hT.2.2 h₁
    exact (maxContactCase_of_maxOrd_lt T hT hH hle bd hlt).trans
      (maxContactCase_of_maxOrd_lt _ hT' hH hle bd hlt).symm

end MaxContactCase

end Hironaka.BO
