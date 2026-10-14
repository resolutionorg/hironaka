/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step21BoundaryClearing
public import Hironaka.Scheme.BlowUpSequence.ConcatPullback
import Hironaka.Resolution.Algebraic.BoundaryClearing.FunctorialityPullback
import Hironaka.Scheme.BlowUpSequence.BaseChangeTriple
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Scheme.Snc.Defs
public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Resolution.Algebraic.Kol07.RefineIrreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Hironaka.Resolution.Algebraic.Snc.SncInvertible
public import Hironaka.Resolution.Algebraic.Tuning.Parameter

/-!
# Step 2.3 of order reduction: functoriality of Step 2.1

[Kol07, 104, Step 2.3]: "Assuming functoriality in dimension `< n`, we have functoriality in
Step 2.1 by the corresponding functoriality in (102)." Step 2.1 (`step21Seq`) is the
concatenation, position by position, of the values `BD_{n,m,j}` of the boundary-clearing functor of
[Kol07, Lemma 102] on the triples induced at the end of the sequence built so far. Its
functoriality is therefore proved round by round through the concatenation:

* the pull-back of a concatenation is the concatenation of the pull-backs, the second along the
  lift of `h` to the last stage (`pullback_concat`, `pullbackLastHom`,
  `Hironaka/Scheme/BlowUpSequence/ConcatPullback.lean`), which is smooth, resp. surjective, when `h`
  is (`smooth_pullbackLastHom`, `surjective_pullbackLastHom`; [Kol07, 30.1]);
* the triple induced at a stage of the pulled-back sequence is the pull-back of the triple induced
  at that stage along the stage lift (`IsPullbackOf.induced_isPullbackOf` in
  `Hironaka/Scheme/BlowUpSequence/BaseChangeTriple.lean`), and at the last stage along the
  last-stage lift (`isPullbackOf_induced_last`); likewise for a change of fields
  (`isBaseChangeOf_induced_last`); the index transport `pullbackStageIdx_last` is the `eqToHom`
  inside `pullbackLastHom`;
* hence, by induction on the number of positions, Step 2.1 commutes with smooth surjections
  (`step21Seq_pullback_of_surjective`, the first clause of [Kol07, 34.1], from the field
  `commutesWithSmooth` of the data) and with change of fields (`step21Seq_baseChange`,
  [Kol07, 34.2], from the field `commutesWithBaseChange`). The induction is run on the whole
  value of `step21Seq`, the sequence with its order and no-empty-centres proofs, so that the
  induced triple of the pulled-back sequence can be rewritten without motive problems; the
  pulled-back triple has the same number of boundary members, as the inverse image keeps the
  index set.

The second clause of [Kol07, 34.1], for an arbitrary smooth morphism, is
`Hironaka/Resolution/Algebraic/OrderReduction/Step21EraseEmpty.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.Snc Hironaka.Local

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The last-stage lift of a smooth morphism is smooth ([Kol07, 30.1]: "if `B` is a smooth blow-up
sequence then so is `h^*B`"). -/
theorem smooth_pullbackLastHom (S : BlowUpSequence X) (h : Y ⟶ X) [Smooth h] :
    Smooth (S.pullbackLastHom h) := by
  unfold BlowUpSequence.pullbackLastHom
  exact MorphismProperty.comp_mem _ _ _ (Hironaka.BD.smooth_eqToHom _)
    (smooth_pullbackStageHom S h _)

/-- The last-stage lift of a flat surjection is surjective (the pull-back of a blow-up sequence
along a morphism, [Kol07, 30.1]; flat base change preserves surjectivity). -/
theorem surjective_pullbackLastHom (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (hs : Function.Surjective h) : Function.Surjective (S.pullbackLastHom h) := by
  have h1 : Surjective (S.pullbackStageHom h (Fin.last _)) :=
    ⟨surjective_pullbackStageHom S h hs _⟩
  have h2 : Surjective (eqToHom (congrArg (S.pullback h).stage (pullbackStageIdx_last S h).symm)) :=
    ⟨surjective_of_isIso _⟩
  exact (eqToHom (congrArg (S.pullback h).stage (pullbackStageIdx_last S h).symm) ≫
    S.pullbackStageHom h (Fin.last _)).surjective

end Hironaka.Sequence

namespace Hironaka.BO

section Induced

variable {k : Type u} [Field k] [CharZero k] {m : ℕ}

/-- The triple induced at the end of the pulled-back sequence is the pull-back of the triple
induced at the end of the sequence, along the last-stage lift (`IsPullbackOf.induced_isPullbackOf`
at the last stage, in the form `IsPullbackOf` of the induced triples). -/
theorem isPullbackOf_induced_last {T T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hS' : (S.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m) :
    (T'.induced (S.pullback h) hS' (Fin.last _)).IsPullbackOf (T.induced S hS (Fin.last _))
      (S.pullbackLastHom h) :=
  Triple.isPullbackOf_induced_of_eq_idx (pullbackStageIdx_last S h)
    (hpb.induced_isPullbackOf hS hS' (Fin.last _))

/-- The triple induced at the end of the base-changed sequence is the base change of the triple
induced at the end of the sequence, along the last-stage lift
(`IsBaseChangeOf.induced_isBaseChangeOf` at the last stage; [Kol07, 34.2]). -/
theorem isBaseChangeOf_induced_last {L : Type u} [Field L] [CharZero L] {T : Triple k}
    {T' : Triple L} (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p)
    {S : BlowUpSequence T.X.left} (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hS' : (S.pullback p).IsOrderSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.E m) :
    (T'.induced (S.pullback p) hS' (Fin.last _)).IsBaseChangeOf (T.induced S hS (Fin.last _)) σ
      (S.pullbackLastHom p) :=
  Triple.isBaseChangeOf_induced_of_eq_idx (pullbackStageIdx_last S p)
    (hbc.induced_isBaseChangeOf hS hS' (Fin.last _))

end Induced

section Step21

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ j : ℕ, BDData.{u} n m j)

/-- The inductive step of `step21Seq_pullback_of_surjective`, on the whole Step 2.1 values
(sequence with its proofs): if the sequence after `j` rounds on the pulled-back data is the
pull-back of the sequence after `j` rounds, so is the sequence after `j + 1` rounds, by
`pullback_concat` and the field `commutesWithSmooth` (first clause) of the boundary-clearing data
on the induced triples at the last stage. -/
theorem step21Seq_pullback_succ_aux {T' : Triple k} (hn' : T'.HasDimLE n)
    (hmax' : T'.I.maxOrd ≤ m) (h : T'.X.left ⟶ T.X.left) [Smooth h] (hs : Function.Surjective h)
    (hpb : T'.IsPullbackOf T h) {j : ℕ}
    (σ' : {S : BlowUpSequence T'.X.left //
      S.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m ∧ S.NoEmptyCenters})
    (σ : {S : BlowUpSequence T.X.left // S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m ∧
      S.NoEmptyCenters})
    (hσ : σ'.1 = σ.1.pullback h) (hj' : j < Fintype.card T'.E.ι) (hj : j < Fintype.card T.E.ι) :
    σ'.1.concat (((bd j).functor k).seq (T'.induced σ'.1 σ'.2.1 (Fin.last _))
        (bdClass_induced_last T' hn' hmax' σ'.2.1 σ'.2.2 hj')) =
      (σ.1.concat (((bd j).functor k).seq (T.induced σ.1 σ.2.1 (Fin.last _))
        (bdClass_induced_last T hn hmax σ.2.1 σ.2.2 hj))).pullback h := by
  obtain ⟨S', hS'⟩ := σ'
  obtain ⟨S, hS⟩ := σ
  dsimp only at hσ ⊢
  subst hσ
  refine Eq.trans ?_ (pullback_concat S _ h).symm
  have : @Smooth (T'.induced (S.pullback h) hS'.1 (Fin.last _)).X.left
      (T.induced S hS.1 (Fin.last _)).X.left (S.pullbackLastHom h) := smooth_pullbackLastHom S h
  have key := ((bd j).commutesWithSmooth k).1 (T.induced S hS.1 (Fin.last _))
    (T'.induced (S.pullback h) hS'.1 (Fin.last _)) (S.pullbackLastHom h)
    (surjective_pullbackLastHom S h hs) (isPullbackOf_induced_last h hpb hS.1 hS'.1)
    (bdClass_induced_last T hn hmax hS.1 hS.2 hj)
    (bdClass_induced_last T' hn' hmax' hS'.1 hS'.2 hj')
  exact congrArg (S.pullback h).concat key

/-- Step 2.1 commutes with smooth surjections ([Kol07, 104, Step 2.3], "functoriality in Step 2.1
by the corresponding functoriality in (102)"; the first clause of [Kol07, 34.1]): round by round
through the concatenation, by the field `commutesWithSmooth` of the boundary-clearing data on the
induced triples. -/
theorem step21Seq_pullback_of_surjective {T' : Triple k} (hn' : T'.HasDimLE n)
    (hmax' : T'.I.maxOrd ≤ m) (h : T'.X.left ⟶ T.X.left) [Smooth h] (hs : Function.Surjective h)
    (hpb : T'.IsPullbackOf T h) (j : ℕ) :
    (step21Seq T' hn' hmax' bd j).1 = ((step21Seq T hn hmax bd j).1).pullback h := by
  have hcard : Fintype.card T'.E.ι = Fintype.card T.E.ι :=
    Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι hpb.2.2))
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [step21Seq]
    by_cases hj : j < Fintype.card T.E.ι
    · have hj' : j < Fintype.card T'.E.ι := hcard ▸ hj
      rw [dite_eq_left hj', dite_eq_left hj]
      exact step21Seq_pullback_succ_aux T hn hmax bd hn' hmax' h hs hpb _ _ ih hj' hj
    · have hj' : ¬ j < Fintype.card T'.E.ι := hcard ▸ hj
      rw [dite_eq_right hj', dite_eq_right hj]
      exact ih

/-- The inductive step of `step21Seq_baseChange`, on the whole Step 2.1 values: `pullback_concat`
and the field `commutesWithBaseChange` of the boundary-clearing data on the induced triples at
the last stage. -/
theorem step21Seq_baseChange_succ_aux {L : Type u} [Field L] [CharZero L] {T' : Triple L}
    (hn' : T'.HasDimLE n) (hmax' : T'.I.maxOrd ≤ m) (σ : k →+* L) (p : T'.X.left ⟶ T.X.left)
    (hbc : T'.IsBaseChangeOf T σ p) {j : ℕ}
    (τ' : {S : BlowUpSequence T'.X.left //
      S.IsOrderSeq (T'.X.left ↘ Spec (.of L)) T'.I T'.E m ∧ S.NoEmptyCenters})
    (τ : {S : BlowUpSequence T.X.left // S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m ∧
      S.NoEmptyCenters})
    (hτ : τ'.1 = τ.1.pullback p) (hj' : j < Fintype.card T'.E.ι) (hj : j < Fintype.card T.E.ι) :
    τ'.1.concat (((bd j).functor L).seq (T'.induced τ'.1 τ'.2.1 (Fin.last _))
        (bdClass_induced_last T' hn' hmax' τ'.2.1 τ'.2.2 hj')) =
      (τ.1.concat (((bd j).functor k).seq (T.induced τ.1 τ.2.1 (Fin.last _))
        (bdClass_induced_last T hn hmax τ.2.1 τ.2.2 hj))).pullback p := by
  obtain ⟨S', hS'⟩ := τ'
  obtain ⟨S, hS⟩ := τ
  dsimp only at hτ ⊢
  subst hτ
  refine Eq.trans ?_ (pullback_concat S _ p).symm
  have key := (bd j).commutesWithBaseChange k L σ (T.induced S hS.1 (Fin.last _))
    (T'.induced (S.pullback p) hS'.1 (Fin.last _)) (S.pullbackLastHom p)
    (isBaseChangeOf_induced_last σ p hbc hS.1 hS'.1)
    (bdClass_induced_last T hn hmax hS.1 hS.2 hj)
    (bdClass_induced_last T' hn' hmax' hS'.1 hS'.2 hj')
  exact congrArg (S.pullback p).concat key

/-- Step 2.1 commutes with change of fields ([Kol07, 104, Step 2.3]; [Kol07, 34.2]): round by
round through the concatenation, by the field `commutesWithBaseChange` of the boundary-clearing
data on the induced triples. -/
theorem step21Seq_baseChange {L : Type u} [Field L] [CharZero L] {T' : Triple L}
    (hn' : T'.HasDimLE n) (hmax' : T'.I.maxOrd ≤ m) (σ : k →+* L) (p : T'.X.left ⟶ T.X.left)
    (hbc : T'.IsBaseChangeOf T σ p) (j : ℕ) :
    (step21Seq T' hn' hmax' bd j).1 = ((step21Seq T hn hmax bd j).1).pullback p := by
  have hcard : Fintype.card T'.E.ι = Fintype.card T.E.ι :=
    Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι hbc.2.2))
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [step21Seq]
    by_cases hj : j < Fintype.card T.E.ι
    · have hj' : j < Fintype.card T'.E.ι := hcard ▸ hj
      rw [dite_eq_left hj', dite_eq_left hj]
      exact step21Seq_baseChange_succ_aux T hn hmax bd hn' hmax' σ p hbc _ _ ih hj' hj
    · have hj' : ¬ j < Fintype.card T'.E.ι := hcard ▸ hj
      rw [dite_eq_right hj', dite_eq_right hj]
      exact ih

end Step21

end Hironaka.BO
