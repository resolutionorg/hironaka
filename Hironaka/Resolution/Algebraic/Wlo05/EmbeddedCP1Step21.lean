/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
import Hironaka.Resolution.Algebraic.Kol07.GoingUp
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Bookkeeping
import Hironaka.Resolution.Algebraic.Kol07.Thm36.EraseEmptyIndex
import Hironaka.Resolution.Algebraic.Wlo05.CenterContainsConcat
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.1 never contains the component

Step 2.1 of the proof of [Kol07, Theorem 103] (item 104, Step 2.1) runs the boundary-clearing
functor `BD_{n,1,j}` of [Kol07, Lemma 102] over the members `E^j` of the boundary in turn. Every
centre of the output of Lemma 102 is the push-forward of a centre on the strict transform of
`E^j` (the proof of [Kol07, Lemma 102]: the output is the push-forward along `E^j ↪ X` of the
run on `E^j`). A centre containing the strict transform `c̃` of the component `c = V(closure {η})`
would therefore put `c̃`, hence its generic point, inside the strict transform of `E^j`; but the
generic point lies on no member of the boundary (`GenericLift.notMem`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericLift`). Hence no centre of Step 2.1 contains
`c̃`, and the statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) holds vacuously along it: the first
containing stage of the order reduction `BO_{n,1}` lies in Step 2.2. This observation is not in the
literature.

Three layers: the raw output `rawSeq` (`not_centerContains_rawSeq`, a strong induction on the
stage with the lifted generic point and
`strictTransformSeq_le_center_pushforward_subschemeι`); the functor of Lemma 102 at the mark `1`
with the data `bdData` — the tuning parameter at the mark `1` is `1` and the empty blow-ups are
deleted (`not_centerContains_bdData_seq`, through `exists_eraseIdx_eq` and
`centerContains_eraseEmpty_iff`); and the iterated concatenation of Step 2.1
(`not_centerContains_step21Seq`, `cp1For_step21Seq`;
`Hironaka.Resolution.Algebraic.OrderReduction.Step21BoundaryClearing`). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step2`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BO Hironaka.BD IsLocalRing

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- **The raw output of Lemma 102 never contains `c̃`** (the proof of [Kol07, Lemma 102]): its
centres are push-forwards of centres on the strict transform of the member `E^j`, and the lifted
generic point of `η` lies on no member. Stated for any ideal sheaf `I` whose generic point `η` is
off the boundary; the centres of the sequence do not involve `I`. -/
theorem not_centerContains_rawSeq {n : ℕ} (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) (hn : T.HasDimLE n)
    {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')
    (I : T.X.left.IdealSheafData) {η : T.X.left} (hη : η ∈ I.support.genericPoints)
    (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) (l : ℕ) :
    ¬ CenterContains (rawSeq T m j hI hmax hn B hDom) (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure {η})) l := by
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  rintro ⟨hl, hle⟩
  obtain ⟨η', hη'⟩ := exists_genericLift (rawSeq T m j hI hmax hn B hDom) I T.E 1 hη hηE hIc
    ⟨l, Nat.lt_succ_of_lt hl⟩ (fun l' hl' => ih l' hl')
  -- the lifted point lies on the centre, hence on the strict transform of `E^j`
  have hmemZ : η' ∈ ((rawSeq T m j hI hmax hn B hDom).center ⟨l, hl⟩).support :=
    Scheme.IdealSheafData.support_antitone hle hη'.mem_support
  have hH : (rawSeq T m j hI hmax hn B hDom).strictTransformSeq (T.E.component j)
      ⟨l, Nat.lt_succ_of_lt hl⟩ ≤ (rawSeq T m j hI hmax hn B hDom).center ⟨l, hl⟩ :=
    strictTransformSeq_le_center_pushforward_subschemeι _ _ ⟨l, hl⟩
  have hmemH := Scheme.IdealSheafData.support_antitone hH hmemZ
  rw [← component_originalIdx (rawSeq T m j hI hmax hn B hDom) T.E ⟨l, Nat.lt_succ_of_lt hl⟩ j]
    at hmemH
  exact hη'.notMem _ hmemH

section Data

variable {N : ℕ} (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
  (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
  (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
    T'.toTriple.HasDimLE (N - 1) → T'.m = tuningParam m → Dom k T')
  (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
    ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
  (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
  (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
    (B k).CommutesWithBaseChange (B L) σ)

/-- **The output of Lemma 102 never contains `c̃`** ([Kol07, Lemma 102] with the data `bdData` at
the mark `1`), for any ideal sheaf `I` whose generic point `η` is off the boundary: the tuning
parameter at the mark `1` is `1`, the value is `rawSeq` with its empty blow-ups deleted, and the
deletion preserves the stop rule (`centerContains_eraseEmpty_iff`). -/
theorem not_centerContains_bdData_seq_of {j : ℕ} (T : Triple k) (hT : Triple.BDClass N 1 j T)
    (I : T.X.left.IdealSheafData) {η : T.X.left} (hη : η ∈ I.support.genericPoints)
    (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) (l : ℕ) :
    ¬ CenterContains (((bdData N 1 j Dom B (hDom 1) hB hsm hbc).functor k).seq T hT)
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) l := by
  change ¬ CenterContains ((dataFunctor N 1 j le_rfl (B k) (hDom 1 k)).seq T hT) _ l
  rcases lt_or_eq_of_le hT.2.1 with hlt | heq
  · rw [dataFunctor_seq_of_maxOrd_lt N 1 j le_rfl (B k) (hDom 1 k) T hT hlt]
    rintro ⟨hl, -⟩
    exact absurd hl (Nat.not_lt_zero _)
  · rw [dataFunctor_seq_of_maxOrd_eq N 1 j le_rfl (B k) (hDom 1 k) T hT heq, functor_seq]
    intro hcont
    obtain ⟨hl, -⟩ := id hcont
    obtain ⟨m', hm', hne, hem⟩ := exists_eraseIdx_eq _ l hl
    rw [← hem] at hcont
    exact not_centerContains_rawSeq (T.tuned 1 le_rfl) (tuningParam 1) _ _ _ _ (B k) (hDom 1 k) I
      hη hηE hIc m' ((centerContains_eraseEmpty_iff _ _ m' hm' hne).mp hcont)

/-- The output of Lemma 102 with the data `bdData` at the mark `1` never contains `c̃`, for the
triple's own ideal (the proof of [Kol07, Lemma 102]). -/
theorem not_centerContains_bdData_seq {j : ℕ} (T : Triple k) (hT : Triple.BDClass N 1 j T)
    {η : T.X.left} (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) (l : ℕ) :
    ¬ CenterContains (((bdData N 1 j Dom B (hDom 1) hB hsm hbc).functor k).seq T hT)
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) l :=
  not_centerContains_bdData_seq_of Dom B hDom hB hsm hbc T hT T.I hη hηE hIc l

variable (T : Triple k) (hn : T.HasDimLE N) (hmax : T.I.maxOrd ≤ 1)

/-- **Step 2.1 never contains `c̃`** ([Kol07, 104, Step 2.1]): by induction on the number of
passes, through the stop rule of the concatenation (`centerContains_concat_iff_of_lt`,
`centerContains_concat_add_iff`), each pass being the output of Lemma 102 on the induced triple
at the lifted generic point (`not_centerContains_bdData_seq_of`). -/
theorem not_centerContains_step21Seq {η : T.X.left} (hη : η ∈ T.I.support.genericPoints)
    (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) (j l : ℕ) :
    ¬ CenterContains
      (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).1
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) l := by
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  induction j generalizing l with
  | zero =>
    rintro ⟨hl, -⟩
    exact absurd hl (Nat.not_lt_zero _)
  | succ j ih =>
    simp only [step21Seq]
    by_cases hj : j < Fintype.card T.E.ι
    · rw [dite_eq_left hj]
      intro hcont
      rcases lt_or_ge l
        (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).1.length with
        hlt | hge
      · exact ih l ((centerContains_concat_iff_of_lt _ _ _ l hlt).mp hcont)
      · obtain ⟨l', rfl⟩ := Nat.exists_eq_add_of_le hge
        have h2 := (centerContains_concat_add_iff _ _ _ l').mp hcont
        obtain ⟨η', hη'⟩ := exists_genericLift
          (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).1 T.I T.E 1
          hη hηE hIc (Fin.last _) (fun l'' _ => ih l'')
        rw [hη'.strict_eq] at h2
        exact not_centerContains_bdData_seq_of Dom B hDom hB hsm hbc
          (T.induced (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).1
            (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).2.1
            (Fin.last _))
          (bdClass_induced_last T hn hmax
            (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).2.1
            (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).2.2 hj)
          ((step21Seq T hn hmax
            (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).1.markedTransformSeq
            T.I 1 (Fin.last _))
          hη'.mem_genericPoints hη'.notMem hη'.stalk_eq l' h2
    · rw [dite_eq_right hj]
      exact ih l

/-- CP1 holds vacuously along Step 2.1. -/
theorem cp1For_step21Seq {η : T.X.left} (hη : η ∈ T.I.support.genericPoints)
    (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) (j : ℕ) :
    CP1For (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc) j).1
      T.I T.E η := fun i hi _ =>
  absurd hi (not_centerContains_step21Seq Dom B hDom hB hsm hbc T hn hmax hη hηE hIc j i.val)

end Data

end Hironaka.Resolution
