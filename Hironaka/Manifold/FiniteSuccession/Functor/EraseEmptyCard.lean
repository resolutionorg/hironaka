/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmpty
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The count of deleted blow-ups

The length of a list after deleting its empty blow-ups plus the number of empty centres is its
length (`length_eraseEmpty_add_card`; the "reindexing" of [Kol07, 34.1]): by recursion, an empty
head is deleted and counted once, a nonempty head is kept and not counted, and the transport along
the analytic isomorphism of an empty blowing-up keeps the length.
-/

@[expose] public section

noncomputable section

open Set AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

open Classical in
/-- The number of empty centres of a list. -/
def emptyCount {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) : ℕ :=
  (Finset.univ.filter fun i : Fin L.toSuccession.length => L.toSuccession.IsEmptyAt i).card

open Classical in
theorem emptyCount_nil {M : AnalyticManifold.{u} 𝕜 E} : (nil (ψ₀ := ψ₀) M).emptyCount = 0 := by
  change (Finset.univ.filter fun i : Fin 0 => (FiniteSuccession.nil M).IsEmptyAt i).card = 0
  exact Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun i _ => Fin.elim0 i)

open Classical in
theorem emptyCount_cons {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) :
    (cons hY rest).emptyCount = (if Y = ∅ then 1 else 0) + rest.emptyCount := by
  have h := Fin.card_filter_univ_succ' fun i : Fin (rest.toSuccession.length + 1) =>
    (FiniteSuccession.cons ψ₀ hY rest.toSuccession).IsEmptyAt i
  refine h.trans ?_
  have e : (FiniteSuccession.cons ψ₀ hY rest.toSuccession).IsEmptyAt
      (0 : Fin (rest.toSuccession.length + 1)) ↔ Y = ∅ :=
    FiniteSuccession.isEmptyAt_cons_zero hY rest.toSuccession
  congr 1
  simp only [e]

theorem length_eraseEmpty_add_emptyCount : ∀ {M : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M),
    L.eraseEmpty.length + L.emptyCount = L.length
  | _, nil _ => by rw [eraseEmpty_nil, emptyCount_nil, Nat.add_zero]
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest => by
    rw [emptyCount_cons, length_cons]
    by_cases hY₀ : Y = ∅
    · rw [eraseEmpty_cons_of_eq_empty hY rest hY₀, length_map, ite_eq_left hY₀]
      have := length_eraseEmpty_add_emptyCount rest
      omega
    · rw [eraseEmpty_cons_of_ne_empty hY rest hY₀, length_cons, ite_eq_right hY₀]
      have := length_eraseEmpty_add_emptyCount rest
      omega

open Classical in
/-- [Kol07, 34.1] ("reindexing the resulting blow-up sequence"): the length after
deletion plus the number of empty centres is the length (clause on lists). -/
theorem length_eraseEmpty_add_card {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) :
    L.eraseEmpty.length +
      (Finset.univ.filter fun i : Fin L.toSuccession.length => L.toSuccession.IsEmptyAt i).card =
        L.length :=
  length_eraseEmpty_add_emptyCount L

end AnalyticManifold.BlowUpSequence

end
