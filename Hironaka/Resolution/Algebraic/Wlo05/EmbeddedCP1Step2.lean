/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1At
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Cover
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step21
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 along Step 2, and the Step 2 descent along the tower

Step 2 of the proof of [Kol07, Theorem 103] on a triple with a smooth hypersurface of maximal
contact is Step 2.1 followed by Step 2.2 (`step2Seq`,
`Hironaka.Resolution.Algebraic.OrderReduction.Step22RestrictToHypersurface`). The statement CP1 of
the embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) along
it (`cp1For_step2Seq`) is `cp1For_concat` of CP1 along Step 2.1 (`cp1For_step21Seq`; no centre there
contains `c̃`) and CP1 along Step 2.2 at the lifted generic point (`cp1For_step22`). The tower step
(`cp1BOAt_succ_of_cp1BMOAt`):
`BO_{n+1,1}` is evaluated through the local cover of [Kol07, Theorem 105], on whose pieces a
hypersurface of maximal contact exists and the run is Step 2 on the tuned triple
(`functor_seq_localClass`, `maxContactCase` at `max-ord I = 1`, the tuning at the mark `1` being
the identity); CP1 on the pieces descends to the triple (`cp1For_of_pullback_cover`, the functor
commuting with the cover), and the inductive input is the stage-`n` marked family read through the
amalgam (`amalgam_seq`, `seq_congr_mark`). The tower induction is that of [Kol07, 70]. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Tower` and
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
  (T : Triple k) (hn : T.HasDimLE N) (hmax : T.I.maxOrd ≤ 1) {H : T.X.left.IdealSheafData}
  (hH : IsSmoothDivisor H) (hle : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec
      (.of k)) T.I 1 H)

/-- CP1 along Step 2 with the data `bdData` (Step 2 of the proof of [Kol07, Theorem 103]), from
`cp1For_step21Seq` and `cp1For_step22` through `cp1For_concat`. -/
theorem cp1For_step2Seq
    (hcp1 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 → ∀ η' : T'.X.left,
      η' ∈ T'.I.support.genericPoints → (∀ i, η' ∉ (T'.E.component i).support) →
      T'.I.stalkIdeal η' = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
          {η'})).stalkIdeal η' →
      CP1For ((B k).seq T' hT') T'.I T'.E η')
    {η : T.X.left} (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) :
    CP1For (step2Seq T hn hmax (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) le_rfl hH hle)
      T.I T.E η := by
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact cp1For_concat _ _ T.I T.E hη hηE hIc
    (cp1For_step21Seq Dom B hDom hB hsm hbc T hn hmax hη hηE hIc (Fintype.card T.E.ι))
    (fun η' hlift => cp1For_step22 Dom B hDom hB hsm hbc T hn hmax hH hle hcp1
      hlift.mem_genericPoints hlift.notMem hlift.stalk_eq)

/-- `cp1For_step2Seq` at a mark `m = 1` carried as a variable: the form the tuned triple of
`maxContactCase` produces, whose mark is `tuningParam 1`. -/
theorem cp1For_step2Seq_of_eq_one (m : ℕ) (hm1 : m = 1) (hmax' : T.I.maxOrd ≤ m) (hm : 1 ≤ m)
    (hle' : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)
    (hcp1 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 → ∀ η' : T'.X.left,
      η' ∈ T'.I.support.genericPoints → (∀ i, η' ∉ (T'.E.component i).support) →
      T'.I.stalkIdeal η' = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
          {η'})).stalkIdeal η' →
      CP1For ((B k).seq T' hT') T'.I T'.E η')
    {η : T.X.left} (hη : η ∈ T.I.support.genericPoints) (hηE : ∀ i, η ∉ (T.E.component i).support)
    (hIc : T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal η) :
    CP1For (step2Seq T hn hmax' (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) hm hH hle')
      T.I T.E η := by
  subst hm1
  exact cp1For_step2Seq Dom B hDom hB hsm hbc T hn hmax' hH hle' hcp1 hη hηE hIc

end Step2

section Tower

variable (k)

/-- **The Step 2 descent along the tower** (Step 2 of the proof of [Kol07, Theorem 103],
[Kol07, Theorem 105], [Kol07, 104]): `BO_{n+1,1}` on a triple is evaluated through the local cover
of Theorem 105, on whose pieces a hypersurface of maximal contact exists and the run is Step 2 on
the tuned triple; CP1 there is `cp1For_step2Seq` with the stage-`n` marked family as the inductive
input, and it descends to the triple along the cover. -/
theorem cp1BOAt_succ_of_cp1BMOAt (n : ℕ) (h : CP1BMOAt k n) : CP1BOAt k (n + 1) := by
  intro T hT η hη hηE hIc
  have hne : Nonempty T.X.left := ⟨η⟩
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  -- the run is a smooth order sequence
  have hS : (boRun k (n + 1) T hT).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E :=
    IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (.of k)) n'
      ((((tower stage0 (n + 1)).bo 1).functor k).isOrderSeq T hT)
  -- Theorem 105's local cover with a smooth hypersurface of maximal contact
  obtain ⟨T', g, -, hLT, hM, hsurj, hpb⟩ :=
    Triple.exists_isLocalCover (globalizationData_localClass (n + 1) 1) hT
  obtain ⟨H, hH, hmaxc⟩ := hLT.2
  have hbo' : T'.BOClass (n + 1) 1 := hLT.1
  have hsmg : Smooth g := openImmersionCoprods.smooth hM
  have hpull : boRun k (n + 1) T' hbo' = (boRun k (n + 1) T hT).pullback g :=
    (((tower stage0 (n + 1)).bo 1).commutesWithSmooth k).1 T T' g hsurj hpb hT hbo'
  -- the inductive hypothesis, read as CP1 for the amalgam's runs at the mark `1`
  have hcp1 : ∀ (T₁ : MarkedTriple k) (hT₁ : amalgamDom n k T₁), T₁.m = 1 → ∀ η₁ : T₁.X.left,
      η₁ ∈ T₁.I.support.genericPoints → (∀ i, η₁ ∉ (T₁.E.component i).support) →
      T₁.I.stalkIdeal η₁ = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
          {η₁})).stalkIdeal η₁ →
      CP1For ((amalgam (tower stage0 n).bmo k).seq T₁ hT₁) T₁.I T₁.E η₁ := by
    intro T₁ hT₁ hm η₁ hη₁ hη₁E hI₁c
    have h₂ : T₁.BMOClass n 1 := by
      have h₁ := bmoClass_of_amalgamClass k hT₁
      rwa [hm] at h₁
    have e := amalgam_seq (tower stage0 n).bmo k T₁ hT₁
    rw [e, seq_congr_mark (tower stage0 n).bmo k hm T₁ _ h₂]
    exact h T₁ h₂ η₁ hη₁ hη₁E hI₁c
  -- descend along the cover
  refine cp1For_of_pullback_cover T T' g hM hsurj hpb (boRun k (n + 1) T hT) hS hη hηE hIc ?_
  intro η' _ hη' hη'E hI'c
  rw [← hpull]
  -- on the piece, `BO_{n+1,1}` is Step 2 on the tuned triple
  have h1' : T'.I.maxOrd = ((1 : ℕ) : ℕ∞) := by
    refine le_antisymm hbo'.2.2 ?_
    rw [Nat.cast_one]
    exact ((Scheme.IdealSheafData.one_le_ord_iff _ η').mpr hη'.1).trans
        (Scheme.IdealSheafData.le_maxOrd _ η')
  change CP1For ((((tower stage0 (n + 1)).bo 1).functor k).seq T' hbo') T'.I T'.E η'
  rw [tower_succ_bo, boOfBMO_functor,
    Hironaka.BO.functor_seq_localClass (n + 1) 1 _ T' hbo' hH hmaxc, maxContactCase,
    dite_eq_left h1']
  -- CP1 for the tuned triple; its ideal is `T'.I`
  have hIt : (T'.tuned 1 hbo'.1).I = T'.I := Scheme.IdealSheafData.W_tuningParam_one _ _
  have hη'' : η' ∈ (T'.tuned 1 hbo'.1).I.support.genericPoints := by
    rw [hIt]
    exact hη'
  have hI'c' : (T'.tuned 1 hbo'.1).I.stalkIdeal η' =
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η'})).stalkIdeal η' := by
    rw [hIt]
    exact hI'c
  have key := cp1For_step2Seq_of_eq_one (N := n + 1) (amalgamDom n)
    (fun k _ _ => amalgam (tower stage0 n).bmo k)
    (fun m k _ _ T₁ hd hm => amalgamClass_of_tuningParam k m T₁ hd hm)
    (fun k _ _ T₁ hT₁ => amalgam_maxOrd_endTriple_lt (tower stage0 n).bmo k T₁ hT₁)
    (fun k _ _ => amalgam_commutesWithSmooth (tower stage0 n).bmo k)
    (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange (tower stage0 n).bmo k σ)
    (T'.tuned 1 hbo'.1) (hasDimLE_tuned hbo'.2.1 1 hbo'.1) hH (tuningParam 1) tuningParam_one
    (le_of_eq (maxOrd_tuned h1' hbo'.1)) (one_le_tuningParam 1)
    (retune_keeps_maxContact h1' hbo'.1 hmaxc) hcp1 hη'' hη'E hI'c'
  exact (congrArg (fun J => CP1For _ J T'.E η') hIt).mp key

end Tower

end Hironaka.Resolution
