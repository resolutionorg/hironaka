/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step22RestrictToHypersurface
public import Hironaka.Resolution.Algebraic.Kol07.SubdividesOn
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Bookkeeping
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.2 of order reduction: its values and the order condition for the original boundary

The unfoldings of the definitions of
`Hironaka/Resolution/Algebraic/OrderReduction/Step22RestrictToHypersurface.lean` and the two facts
about the boundary of Step 2.2 that the construction needs.

* **The re-tuning** (`step22Functor_seq_of_maxOrd_eq`, `step22Functor_seq_of_maxOrd_lt`): at the
  mark, the boundary-clearing functor of [Kol07, Lemma 102] through the re-tuning is the functor
  at `s(m)` on the tuned triple; below the mark it is the empty sequence
  (`ofTunedClass_seq_of_maxOrd_eq`, `ofTunedClass_seq_of_maxOrd_lt` instantiated).
* **The values of Step 2.2** (`step22Triple_X`, `step22Triple_I`, `step22Triple_E`, `step22_eq`,
  `step22_of_maxOrd_eq`, `step22_of_maxOrd_lt`) and the two fields of the functor
  (`isOrderSeq_step22`, a smooth blow-up sequence of order `m` for `(I_r, F_r + H_r)`;
  `noEmptyCenters_step22`).
* **The original boundary sees the same centres** ([Kol07, 104, Step 2.2]): at a point of
  `cosupp(I_r, m)` no birational transform of an original member of `E` passes
  (`notOriginal_of_mem_cosupp_step21`, from
  `Hironaka/Resolution/Algebraic/OrderReduction/Step21Disjoint.lean`), so every member of `E_r`
  through the point is a member of `F_r`: `E_r` subdivides `F_r + H_r` along the cosupport
  (`subdividesOn_cosupp_exceptionalFamily_append`), and Step 2.2 is a smooth blow-up sequence of
  order `m` for the original `(I_r, E_r)` (`isOrderSeq_step22_totalTransformSeq`, through
  `isOrderSeq_of_subdividesOn_cosupp`). This is what makes Step 2 a sequence of order `m` for `(X,
  I, E)` in `Hironaka/Resolution/Algebraic/OrderReduction/Step22Assembly.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence IsLocalRing

namespace Hironaka.BO

section Retune

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

/-- At the mark, the re-tuned boundary-clearing functor is the functor at `s(m)` on the tuned
triple ([Kol07, 104, Step 2.2]: "we can again replace `I` by `W(I)`"). -/
theorem step22Functor_seq_of_maxOrd_eq (bd : ∀ m j : ℕ, BDData.{u} n m j) (m j : ℕ) (hm : 1 ≤ m)
    (T : Triple k) (hT : Triple.BDClass n m j T) (h : T.I.maxOrd = m) :
    (step22Functor bd m j hm).seq T hT =
      ((bd (tuningParam m) j).functor k).seq (T.tuned m hm) (bdClass_tuned hT h hm) :=
  ofTunedClass_seq_of_maxOrd_eq _ _ _ T hT h

/-- Below the mark, the re-tuned boundary-clearing functor is the empty sequence (the remark after
[Kol07, Theorem 68]). -/
theorem step22Functor_seq_of_maxOrd_lt (bd : ∀ m j : ℕ, BDData.{u} n m j) (m j : ℕ) (hm : 1 ≤ m)
    (T : Triple k) (hT : Triple.BDClass n m j T) (h : T.I.maxOrd < m) :
    (step22Functor bd m j hm).seq T hT = BlowUpSequence.nil T.X.left :=
  ofTunedClass_seq_of_maxOrd_lt _ _ _ T hT h

end Retune

section Step22

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m j)

/-- At a point of `cosupp(I_r, m)` no member of `E_r` through the point is the birational
transform of an original member of `E`: these transforms are disjoint from the cosupport after
Step 2.1 (`disjoint_cosupp_step21_final`). -/
theorem notOriginal_of_mem_cosupp_step21
    {x : (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.stage (Fin.last _)}
    (hx : (m : ℕ∞) ≤ ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.weakTransformSeq T.I
      (Fin.last _)).ord x)
    {b : ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.totalTransformSeq T.E (Fin.last _)).ι}
    (hb : x ∈ (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.totalTransformSeq T.E
      (Fin.last _)).component b).support) (a : T.E.ι) :
    b ≠ (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.originalIdx T.E (Fin.last _) a := by
  intro hba
  subst hba
  rw [component_originalIdx] at hb
  set e := monoEquivOfFin T.E.ι rfl with he
  have hd := disjoint_cosupp_step21_final T hn hmax (bd m) (e.symm a).2
  have hnth : T.E.nth ⟨(e.symm a).1, (e.symm a).2⟩ = T.E.component a :=
    congrArg T.E.component (e.apply_symm_apply a)
  rw [hnth] at hd
  exact Set.disjoint_left.mp hd hx hb

section MaximalContact

variable (hm : 1 ≤ m) {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)

/-- The Step 2.2 input triple lives on the end result `X_r` of Step 2.1. -/
theorem step22Triple_X :
    (step22Triple T hn hmax bd hm hH hle).X.left =
      (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.stage (Fin.last _) :=
  rfl

/-- The ideal of the Step 2.2 input triple is `I_r = Π⁻¹_* I`. -/
theorem step22Triple_I :
    (step22Triple T hn hmax bd hm hH hle).I =
      (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.weakTransformSeq T.I (Fin.last _) :=
  rfl

/-- The boundary of the Step 2.2 input triple is the exceptional sub-family of `E_r` with `H_r`
appended last. -/
theorem step22Triple_E :
    (step22Triple T hn hmax bd hm hH hle).E =
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).append
        ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H (Fin.last _)) :=
  rfl

/-- Step 2.2 is the re-tuned boundary-clearing functor at the position of `H_r` applied to the
input triple (definitional). -/
theorem step22_eq :
    step22 T hn hmax bd hm hH hle =
      (step22Functor bd m _ hm).seq (step22Triple T hn hmax bd hm hH hle)
        (bdClass_step22Triple T hn hmax bd hm hH hle) :=
  rfl

/-- At the mark, Step 2.2 is the boundary-clearing functor at `s(m)` on the tuned input triple
([Kol07, 104, Step 2.2]). -/
theorem step22_of_maxOrd_eq (h : (step22Triple T hn hmax bd hm hH hle).I.maxOrd = m) :
    step22 T hn hmax bd hm hH hle =
      ((bd (tuningParam m) _).functor k).seq ((step22Triple T hn hmax bd hm hH hle).tuned m hm)
        (bdClass_tuned (bdClass_step22Triple T hn hmax bd hm hH hle) h hm) :=
  step22Functor_seq_of_maxOrd_eq bd m _ hm _ (bdClass_step22Triple T hn hmax bd hm hH hle) h

/-- Below the mark, the cosupport being already empty after Step 2.1, Step 2.2 is the empty
sequence. -/
theorem step22_of_maxOrd_lt (h : (step22Triple T hn hmax bd hm hH hle).I.maxOrd < m) :
    step22 T hn hmax bd hm hH hle = BlowUpSequence.nil _ :=
  step22Functor_seq_of_maxOrd_lt bd m _ hm _ (bdClass_step22Triple T hn hmax bd hm hH hle) h

/-- Step 2.2 is a smooth blow-up sequence of order `m` starting with the input triple
`(X_r, I_r, F_r + H_r)` (the functor's field). -/
theorem isOrderSeq_step22 :
    (step22 T hn hmax bd hm hH hle).IsOrderSeq
      ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k))
      (step22Triple T hn hmax bd hm hH hle).I (step22Triple T hn hmax bd hm hH hle).E m :=
  (step22Functor bd m _ hm).isOrderSeq _ _

/-- Step 2.2 has no empty blow-up ([Kol07, 32]; the functor's field). -/
theorem noEmptyCenters_step22 : (step22 T hn hmax bd hm hH hle).NoEmptyCenters :=
  (step22Functor bd m _ hm).noEmptyCenters _ _

omit hm hH hle in
/-- Along `cosupp(I_r, m)` the boundary `E_r` subdivides `F_r + H_r`: every member of `E_r` through
a point of the cosupport is exceptional (`notOriginal_of_mem_cosupp_step21`), hence a member of
`F_r`, assigned to itself. -/
theorem subdividesOn_cosupp_exceptionalFamily_append :
    ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.totalTransformSeq T.E
        (Fin.last _)).SubdividesOn
      (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).append
        ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H (Fin.last _)))
      {x | (m : ℕ∞) ≤
        ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.weakTransformSeq T.I
          (Fin.last _)).ord x} := by
  classical
  intro x hx
  let q : ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.totalTransformSeq T.E
      (Fin.last _)).ι → Option
        (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).append
          ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H
            (Fin.last _))).ι :=
    fun b => if hb : ∀ a, b ≠ (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.originalIdx T.E
        (Fin.last _) a then
      some (toLex (Sum.inl
        (⟨b, hb⟩ : ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι)))
    else none
  have hq : ∀ b (hb : ∀ a, b ≠ (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.originalIdx T.E
      (Fin.last _) a), q b = some (toLex (Sum.inl
        (⟨b, hb⟩ :
          ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι))) :=
    fun b hb => dite_eq_left hb
  refine ⟨q, ?_, ?_⟩
  · intro b b' hb hb' heq
    have h1 := fun a => notOriginal_of_mem_cosupp_step21 T hn hmax bd hx hb a
    have h2 := fun a => notOriginal_of_mem_cosupp_step21 T hn hmax bd hx hb' a
    rw [hq b h1, hq b' h2] at heq
    exact Subtype.ext_iff.mp (Sum.inl_injective (toLex.injective (Option.some_injective _ heq)))
  · intro b hb
    have h1 := fun a => notOriginal_of_mem_cosupp_step21 T hn hmax bd hx hb a
    exact ⟨_, hq b h1, rfl⟩

/-- Step 2.2 is a smooth blow-up sequence of order `m` for the original boundary `(I_r, E_r)`: the
normal-crossings clause of [Kol07, Definition 66] at its centres sees only the exceptional members
(`isOrderSeq_of_subdividesOn_cosupp`). -/
theorem isOrderSeq_step22_totalTransformSeq :
    (step22 T hn hmax bd hm hH hle).IsOrderSeq
      ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k))
      (step22Triple T hn hmax bd hm hH hle).I
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.totalTransformSeq T.E (Fin.last _))
      m := by
  obtain ⟨n', -, hn'⟩ :=
    hasDimLE_induced_last T hn (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι))
  have : SmoothOfRelativeDimension n' ((step22Triple T hn hmax bd hm hH hle).X.left ↘
    Spec (.of k)) :=
    hn'
  exact isOrderSeq_of_subdividesOn_cosupp n' _ _
    (subdividesOn_cosupp_exceptionalFamily_append T hn hmax bd)
    (isOrderSeq_step22 T hn hmax bd hm hH hle)

end MaximalContact

end Step22

end Hironaka.BO
