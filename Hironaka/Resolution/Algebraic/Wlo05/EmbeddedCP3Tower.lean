/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3EraseEmpty
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step1
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step21
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step22
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Transport
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP3 along Step 2 and at every stage of the tower

Step 2 of the proof of [Kol07, Theorem 103] is Step 2.1 followed by Step 2.2 (`step2Seq`); the
statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) along it (`cp3For_step2Seq`) is
`cp3For_concat` of `cp3For_step21Seq` and `cp3For_step22`. The tower step
(`cp3BOAt_succ_of_cp3BMOAt`) is that of CP1 (`cp1BOAt_succ_of_cp1BMOAt`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step2`): `BO_{n+1,1}` is evaluated through the local
cover of [Kol07, Theorem 105], on whose pieces a hypersurface of maximal contact exists and the run
is Step 2 on the tuned triple (`functor_seq_localClass`, `maxContactCase` at `max-ord I = 1`, the
tuning at the mark `1` being the identity); CP3 on the pieces descends to the triple
(`cp3For_of_pullback_cover`), and the inductive input is the stage-`n` marked family read through
the amalgam (`amalgam_seq`, `seq_congr_mark`). The induction of [Kol07, 70] closes: the base
`cp3BMOAt_zero`, the Step 2 descent, and the Step 1 reduction `cp3BMOAt_succ_of_cp3BOAt`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step1`) give `cp3BMOAt`; the run `bmoOneRun` of the
loop `BED` (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) is the marked family of the tower at the
triple's own dimension (`dimFreeBMO_seq`, by `rfl`), so every centre of `bmoOneRun T hm` is
classified at each of its points (`cp3For_bmoOneRun`). This completes the proof of CP3 in its
universal form. Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`.
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

/-- CP3 along Step 2 with the data `bdData` (Step 2 of the proof of [Kol07, Theorem 103]):
`cp3For_concat` of `cp3For_step21Seq` and `cp3For_step22`. -/
theorem cp3For_step2Seq
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 →
      CP3For ((B k).seq T' hT') T'.I T'.E) :
    CP3For (step2Seq T hn hmax (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) le_rfl hH hle)
      T.I T.E :=
  cp3For_concat _ _ T.I T.E
    (cp3For_step21Seq Dom B hDom hB hsm hbc T hn hmax hcp3 (Fintype.card T.E.ι))
    (cp3For_step22 Dom B hDom hB hsm hbc T hn hmax hH hle hcp3)

/-- Step 2 at a mark `m = 1` carried as a variable (the mark of the tuned triple). -/
theorem cp3For_step2Seq_of_eq_one (m : ℕ) (hm1 : m = 1) (hmax' : T.I.maxOrd ≤ m) (hm : 1 ≤ m)
    (hle' : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 →
      CP3For ((B k).seq T' hT') T'.I T'.E) :
    CP3For (step2Seq T hn hmax' (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) hm hH hle')
      T.I T.E := by
  subst hm1
  exact cp3For_step2Seq Dom B hDom hB hsm hbc T hn hmax' hH hle' hcp3

end Step2

section Tower

/-- The Step 2 descent along the tower ([Kol07, Theorem 105], [Kol07, 70]): CP3 for `BO_{n+1,1}`
from CP3 for `BMO_{n,1}` through the local cover of Theorem 105, on whose pieces the run is Step 2
on the tuned triple. -/
theorem cp3BOAt_succ_of_cp3BMOAt (n : ℕ) (h : CP3BMOAt k n) : CP3BOAt k (n + 1) := by
  intro T hT
  by_cases hne : Nonempty T.X.left
  swap
  · intro i q _
    exact absurd ⟨(boRun k (n + 1) T hT).stageMap i.castSucc q⟩ hne
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hS : (boRun k (n + 1) T hT).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E :=
    IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (.of k)) n'
      ((((tower stage0 (n + 1)).bo 1).functor k).isOrderSeq T hT)
  obtain ⟨T', g, -, hLT, hM, hsurj, hpb⟩ :=
    Triple.exists_isLocalCover (globalizationData_localClass (n + 1) 1) hT
  obtain ⟨H, hH, hmaxc⟩ := hLT.2
  have hbo' : T'.BOClass (n + 1) 1 := hLT.1
  have hsmg : Smooth g := openImmersionCoprods.smooth hM
  have hpull : boRun k (n + 1) T' hbo' = (boRun k (n + 1) T hT).pullback g :=
    (((tower stage0 (n + 1)).bo 1).commutesWithSmooth k).1 T T' g hsurj hpb hT hbo'
  have hcp3 : ∀ (T₁ : MarkedTriple k) (hT₁ : amalgamDom n k T₁), T₁.m = 1 →
      CP3For ((amalgam (tower stage0 n).bmo k).seq T₁ hT₁) T₁.I T₁.E := by
    intro T₁ hT₁ hm
    have h₂ : T₁.BMOClass n 1 := by
      have h₁ := bmoClass_of_amalgamClass k hT₁
      rwa [hm] at h₁
    have e := amalgam_seq (tower stage0 n).bmo k T₁ hT₁
    rw [e, seq_congr_mark (tower stage0 n).bmo k hm T₁ _ h₂]
    exact h T₁ h₂
  refine cp3For_of_pullback_cover T T' g hM hsurj hpb (boRun k (n + 1) T hT) hS ?_
  rw [← hpull]
  change CP3For ((((tower stage0 (n + 1)).bo 1).functor k).seq T' hbo') T'.I T'.E
  rw [tower_succ_bo, boOfBMO_functor,
    Hironaka.BO.functor_seq_localClass (n + 1) 1 _ T' hbo' hH hmaxc, maxContactCase]
  by_cases h1' : T'.I.maxOrd = ((1 : ℕ) : ℕ∞)
  · rw [dite_eq_left h1']
    have hIt : (T'.tuned 1 hbo'.1).I = T'.I := Scheme.IdealSheafData.W_tuningParam_one _ _
    have key := cp3For_step2Seq_of_eq_one (N := n + 1) (amalgamDom n)
      (fun k _ _ => amalgam (tower stage0 n).bmo k)
      (fun m k _ _ T₁ hd hm => amalgamClass_of_tuningParam k m T₁ hd hm)
      (fun k _ _ T₁ hT₁ => amalgam_maxOrd_endTriple_lt (tower stage0 n).bmo k T₁ hT₁)
      (fun k _ _ => amalgam_commutesWithSmooth (tower stage0 n).bmo k)
      (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange (tower stage0 n).bmo k σ)
      (T'.tuned 1 hbo'.1) (hasDimLE_tuned hbo'.2.1 1 hbo'.1) hH (tuningParam 1) tuningParam_one
      (le_of_eq (maxOrd_tuned h1' hbo'.1)) (one_le_tuningParam 1)
      (retune_keeps_maxContact h1' hbo'.1 hmaxc) hcp3
    exact (congrArg (fun J => CP3For _ J T'.E) hIt).mp key
  · rw [dite_eq_right h1']
    intro i
    exact i.elim0


/-- **CP3 in its universal form along the tower** ([Kol07, 70]): the base `cp3BMOAt_zero`, the
Step 2 descent `cp3BOAt_succ_of_cp3BMOAt`, the Step 1 reduction `cp3BMOAt_succ_of_cp3BOAt`. -/
theorem cp3BMOAt (n : ℕ) : CP3BMOAt k n := by
  induction n with
  | zero => exact cp3BMOAt_zero
  | succ n ih => exact cp3BMOAt_succ_of_cp3BOAt n (cp3BOAt_succ_of_cp3BMOAt n ih)

/-- **CP3 in its universal form for the dimension-free run** (`dimFreeBMO_seq`,
`bmoClass_of_bmoClassFree`): every centre of `bmoOneRun T hm` is classified at each of its
points. -/
theorem cp3For_bmoOneRun (T : MarkedTriple k) (hm : T.m = 1) : CP3For (bmoOneRun T hm) T.I T.E :=
  cp3BMOAt T.toTriple.dim T (MarkedTriple.bmoClass_of_bmoClassFree ⟨le_rfl, hm⟩)

end Tower

end Hironaka.Resolution
