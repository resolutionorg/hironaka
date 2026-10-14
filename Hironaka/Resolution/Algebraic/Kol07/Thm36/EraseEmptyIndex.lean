/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersMiss
import Hironaka.Resolution.Algebraic.Kol07.Thm36.IndexTransport
import Hironaka.Resolution.Algebraic.Monomial.Geometric.PullbackErase
import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The stage index of a sequence after deleting its empty blow-ups

Kollár's convention on empty blow-ups [Kol07, 32] and the second clause of functoriality under
smooth morphisms [Kol07, 34.1] ("deleting every blow-up `h^*π_i` whose center is empty", then
reindexing) compare a sequence with the sequence obtained by
deleting its empty blow-ups: the stage `m` of `S` with a nonempty centre becomes the stage
`eraseIdx S m` of `S.eraseEmpty`, the number of nonempty centres of `S` before `m`. The embedded
desingularization loop is transported along a smooth morphism `h` whose pulled-back run has empty
centres (the centres missing the image of `h`), and the affine resolution functor truncates at a
first-centre index, so the predicate `CenterContains` and the
truncation `take` have to be carried across `eraseEmpty`:

* `eraseEmpty_take`: `S.eraseEmpty.take (eraseIdx S m) = (S.take m).eraseEmpty`;
* `centerContains_eraseEmpty_iff`: at a stage `m` with a nonempty centre, the centre of
  `S.eraseEmpty` at `eraseIdx S m` contains the strict transform of `c` if and only if the centre
  of `S` at `m` does; a deleted (empty) blow-up carries the strict transforms along the trivial
  blow-up (`strictTransform_of_eq_top`), an isomorphism, along which the predicate transports
  (`centerContains_pullback_iff_of_isIso`);
* `exists_eraseIdx_eq`: every stage of `S.eraseEmpty` is `eraseIdx S m` for a stage `m` of `S`
  with a nonempty centre; `eraseIdx_mono`.

Used by `Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenterEraseEmpty` and the transport lemmas
of the embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEraseEmpty`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence Scheme.IdealSheafData
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- The reindexing of [Kol07, 34.1]: the stage of `S.eraseEmpty` corresponding to the stage `m` of
`S`, namely the number of nonempty centres of `S` before `m`. -/
noncomputable def eraseIdx : {X : Scheme.{u}} → BlowUpSequence X → ℕ → ℕ
  | _, nil _, _ => 0
  | _, cons _ _ _, 0 => 0
  | _, cons _ D rest, m + 1 =>
    open scoped Classical in
    (if D = ⊤ then 0 else 1) + eraseIdx rest m

theorem eraseIdx_nil (m : ℕ) : eraseIdx (nil X) m = 0 := rfl

theorem eraseIdx_cons_zero (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp) :
    eraseIdx (cons X D rest) 0 = 0 := rfl

/-- A deleted (empty) blow-up does not advance the index. -/
theorem eraseIdx_cons_succ_of_eq_top {D : X.IdealSheafData} (rest : BlowUpSequence D.blowUp)
    (hD : D = ⊤) (m : ℕ) : eraseIdx (cons X D rest) (m + 1) = eraseIdx rest m := by
  classical
  change (if D = ⊤ then 0 else 1) + eraseIdx rest m = eraseIdx rest m
  rw [ite_eq_left hD, zero_add]

/-- A kept (nonempty) blow-up advances the index by one. -/
theorem eraseIdx_cons_succ_of_ne_top {D : X.IdealSheafData} (rest : BlowUpSequence D.blowUp)
    (hD : D ≠ ⊤) (m : ℕ) : eraseIdx (cons X D rest) (m + 1) = eraseIdx rest m + 1 := by
  classical
  change (if D = ⊤ then 0 else 1) + eraseIdx rest m = eraseIdx rest m + 1
  rw [ite_eq_right hD, add_comm]

/-- The index is monotone in the stage. -/
theorem eraseIdx_mono : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) {m m' : ℕ}, m ≤ m' →
    eraseIdx S m ≤ eraseIdx S m'
  | _, nil _, _, _, _ => le_rfl
  | _, cons _ _ _, 0, _, _ => Nat.zero_le _
  | _, cons _ _ _, _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _, cons X D rest, m + 1, m' + 1, h => by
    classical
    change (if D = ⊤ then 0 else 1) + eraseIdx rest m ≤ (if D = ⊤ then 0 else 1) + eraseIdx rest m'
    exact Nat.add_le_add_left (eraseIdx_mono rest (Nat.le_of_succ_le_succ h)) _

/-- The reindexing on the truncations [Kol07, 34.1]: the erased sequence truncated at the index of
`m` is the erased truncation at `m`. -/
theorem eraseEmpty_take : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (m : ℕ),
    S.eraseEmpty.take (eraseIdx S m) = (S.take m).eraseEmpty
  | _, nil _, _ => rfl
  | _, cons X D rest, 0 => by
    have htake : ∀ T : BlowUpSequence X, T.take 0 = nil X := fun T => by cases T <;> rfl
    exact htake _
  | _, cons X D rest, m + 1 => by
    classical
    by_cases hD : D = ⊤
    · have := isIso_blowUpπ_of_eq_top hD
      rw [eraseEmpty_cons_of_eq_top rest hD, eraseIdx_cons_succ_of_eq_top rest hD,
        ← take_pullback, eraseEmpty_take rest m, take_cons_succ, eraseEmpty_cons_of_eq_top _ hD]
    · rw [eraseEmpty_cons_of_ne_top rest hD, eraseIdx_cons_succ_of_ne_top rest hD, take_cons_succ,
        eraseEmpty_take rest m, take_cons_succ, eraseEmpty_cons_of_ne_top _ hD]

/-- The predicate `CenterContains` across the deletion of empty blow-ups [Kol07, 34.1]: at a stage
`m` of `S` with a nonempty centre, the centre of `S.eraseEmpty` at `eraseIdx S m` contains the
strict transform of `c` if and only if the centre of `S` at `m` does. A deleted empty blow-up
carries the strict transform along the trivial blow-up (`strictTransform_top_left`), an isomorphism
along which the predicate transports (`centerContains_pullback_iff_of_isIso`). -/
theorem centerContains_eraseEmpty_iff : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (c : X.IdealSheafData) (m : ℕ) (hm : m < S.length), S.center ⟨m, hm⟩ ≠ ⊤ →
    (CenterContains S.eraseEmpty c (eraseIdx S m) ↔ CenterContains S c m)
  | _, nil _, _, m, hm, _ => absurd hm (Nat.not_lt_zero _)
  | _, cons X D rest, c, 0, _, hD => by
    have hD' : D ≠ ⊤ := hD
    rw [eraseEmpty_cons_of_ne_top rest hD', eraseIdx_cons_zero]
    exact ⟨fun h => ⟨Nat.succ_pos _, h.2⟩, fun h => ⟨Nat.succ_pos _, h.2⟩⟩
  | _, cons X D rest, c, m + 1, hm, hD => by
    classical
    have hm' : m < rest.length := Nat.lt_of_succ_lt_succ hm
    have hD' : rest.center ⟨m, hm'⟩ ≠ ⊤ := hD
    by_cases hDt : D = ⊤
    · have := isIso_blowUpπ_of_eq_top hDt
      rw [eraseEmpty_cons_of_eq_top rest hDt, eraseIdx_cons_succ_of_eq_top rest hDt,
        centerContains_cons_succ_iff, Hironaka.Monomial.PieceFamily.strictTransform_of_eq_top hDt]
      have e := centerContains_pullback_iff_of_isIso rest.eraseEmpty (inv D.blowUpπ)
        (c.comap D.blowUpπ) (eraseIdx rest m)
      rw [comap_comap_inv] at e
      exact e.trans (centerContains_eraseEmpty_iff rest _ m hm' hD')
    · rw [eraseEmpty_cons_of_ne_top rest hDt, eraseIdx_cons_succ_of_ne_top rest hDt,
        centerContains_cons_succ_iff, centerContains_cons_succ_iff]
      exact centerContains_eraseEmpty_iff rest _ m hm' hD'

/-- Every stage of `S.eraseEmpty` is the index of a stage of `S` with a nonempty centre. -/
theorem exists_eraseIdx_eq : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (m' : ℕ),
    m' < S.eraseEmpty.length →
    ∃ m, ∃ hm : m < S.length, S.center ⟨m, hm⟩ ≠ ⊤ ∧ eraseIdx S m = m'
  | _, nil _, _, h => absurd h (Nat.not_lt_zero _)
  | _, cons X D rest, m', h => by
    classical
    by_cases hDt : D = ⊤
    · have := isIso_blowUpπ_of_eq_top hDt
      rw [eraseEmpty_cons_of_eq_top rest hDt, length_pullback] at h
      obtain ⟨m, hm, hne, he⟩ := exists_eraseIdx_eq rest m' h
      exact ⟨m + 1, Nat.succ_lt_succ hm, hne, by rw [eraseIdx_cons_succ_of_eq_top rest hDt, he]⟩
    · rw [eraseEmpty_cons_of_ne_top rest hDt] at h
      cases m' with
      | zero => exact ⟨0, Nat.succ_pos _, hDt, rfl⟩
      | succ m' =>
        obtain ⟨m, hm, hne, he⟩ := exists_eraseIdx_eq rest m' (Nat.lt_of_succ_lt_succ h)
        exact ⟨m + 1, Nat.succ_lt_succ hm, hne, by rw [eraseIdx_cons_succ_of_ne_top rest hDt, he]⟩

/-- A stage of `S.eraseEmpty` below the index of `n` is the index of a nonempty stage below `n`. -/
theorem exists_eraseIdx_eq_of_lt (S : BlowUpSequence X) {n m' : ℕ} (hm' : m' < S.eraseEmpty.length)
    (hlt : m' < eraseIdx S n) :
    ∃ m, ∃ hm : m < S.length, S.center ⟨m, hm⟩ ≠ ⊤ ∧ eraseIdx S m = m' ∧ m < n := by
  obtain ⟨m, hm, hne, he⟩ := exists_eraseIdx_eq S m' hm'
  refine ⟨m, hm, hne, he, ?_⟩
  by_contra hnm
  have := eraseIdx_mono S (Nat.le_of_not_lt hnm)
  omega

end Hironaka.Resolution
