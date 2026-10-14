/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Basic
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The clauses of `eraseEmpty` and `map` on lists of centres

The recursion `BlowUpSequence.eraseEmpty` (`Hironaka.Manifold.FiniteSuccession.Functor.EraseEmpty`)
deletes the empty steps of a list of centres and carries the tails back along the analytic
isomorphisms `Bl_∅ M ≃ M`; here are its clauses: the equations on `nil` and `cons`
(`eraseEmpty_nil`, `eraseEmpty_cons_of_ne_empty`, `eraseEmpty_cons_empty`); the transport `map`
keeps the length and the (non-)emptiness of the centres (`length_map`, `noEmptyCenters_map_iff`);
the cleaned list has no empty centre (`noEmptyCenters_eraseEmpty`); the deletion is the identity
exactly on lists without empty centres (`eraseEmpty_eq_self_iff`) and is idempotent
(`eraseEmpty_eraseEmpty`); a functor's outputs are fixed by it (`eraseEmpty_seq`, the convention
of [Kol07, 32]). A functor is its assignment of lists (`AnalyticBlowUpSequenceAssignment.ext`).
-/

public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- A functor is its assignment of lists of centres (the other field is a proof). -/
theorem AnalyticBlowUpSequenceAssignment.ext
    {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
    {B B' : AnalyticBlowUpSequenceAssignment ψ₀ Dom}
    (h : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom T),
      B.seq T hT = B'.seq T hT) : B = B' := by
  cases B with
  | mk seq₁ _ =>
  cases B' with
  | mk seq₂ _ =>
  have e : @seq₁ = @seq₂ := by
    funext M T hT
    exact h T hT
  subst e
  rfl

end Manifold

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The equations of `eraseEmpty` -/

@[simp]
theorem eraseEmpty_nil : (nil (ψ₀ := ψ₀) M).eraseEmpty = nil M := rfl

theorem eraseEmpty_cons {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) :
    (cons hY rest).eraseEmpty = eraseEmptyCons hY rest.eraseEmpty := rfl

theorem eraseEmpty_cons_of_ne_empty {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) (hne : Y ≠ ∅) :
    (cons hY rest).eraseEmpty = cons hY rest.eraseEmpty := by
  rw [eraseEmpty_cons, eraseEmptyCons, dite_eq_right hne]

theorem eraseEmpty_cons_of_eq_empty {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) (hY₀ : Y = ∅) :
    (cons hY rest).eraseEmpty = rest.eraseEmpty.map (emptyBlowUpDiffeomorph hY hY₀) := by
  rw [eraseEmpty_cons, eraseEmptyCons, dite_eq_left hY₀]

theorem eraseEmpty_cons_empty {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) (hY₀ : Y = ∅) :
    ∃ g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (blowUp ψ₀ hY) M ω, (∀ p, g p = blowUpπ ψ₀ hY p) ∧
      (cons hY rest).eraseEmpty = rest.eraseEmpty.map g :=
  ⟨emptyBlowUpDiffeomorph hY hY₀, emptyBlowUpDiffeomorph_apply hY hY₀,
    eraseEmpty_cons_of_eq_empty hY rest hY₀⟩

/-! ### Lengths and empty centres -/

theorem length_nil : (nil (ψ₀ := ψ₀) M).length = 0 := rfl

theorem length_cons {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) : (cons hY rest).length = rest.length + 1 := rfl

theorem length_map : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (L : BlowUpSequence ψ₀ M), (L.map g).length = L.length
  | _, _, _, nil _ => rfl
  | _, _, g, cons hY rest => by
    rw [map_cons, length_cons, length_cons, length_map]

/-- No empty centre in `nil`. -/
theorem noEmptyCenters_nil : (nil (ψ₀ := ψ₀) M).NoEmptyCenters := fun i => i.elim0

/-- The first centre of the succession `cons hY R` is empty iff `Y = ∅` (`isEmptyAt_iff`
with `cosupport_idealSheaf`). -/
theorem _root_.AnalyticManifold.FiniteSuccession.isEmptyAt_cons_zero {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (R : FiniteSuccession (blowUp ψ₀ hY)) :
    (FiniteSuccession.cons ψ₀ hY R).IsEmptyAt (0 : Fin (R.length + 1)) ↔ Y = ∅ := by
  refine (FiniteSuccession.isEmptyAt_iff _ _).trans ?_
  change hY.idealSheaf.support = ∅ ↔ Y = ∅
  rw [hY.cosupport_idealSheaf]

/-- The later centres of `cons hY R` are those of `R`. -/
theorem _root_.AnalyticManifold.FiniteSuccession.isEmptyAt_cons_succ {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (R : FiniteSuccession (blowUp ψ₀ hY)) (i : Fin R.length) :
    (FiniteSuccession.cons ψ₀ hY R).IsEmptyAt i.succ ↔ R.IsEmptyAt i := Iff.rfl

/-- `cons hY rest` has no empty centre iff `Y ≠ ∅` and `rest` has none. -/
@[simp]
theorem noEmptyCenters_cons_iff {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) :
    (cons hY rest).NoEmptyCenters ↔ Y ≠ ∅ ∧ rest.NoEmptyCenters := by
  change (∀ i : Fin (rest.length + 1),
    ¬ (FiniteSuccession.cons ψ₀ hY rest.toSuccession).IsEmptyAt i) ↔ _
  rw [Fin.forall_fin_succ]
  refine and_congr ?_ Iff.rfl
  rw [not_iff_not]
  exact FiniteSuccession.isEmptyAt_cons_zero hY rest.toSuccession

/-- The transport along an analytic isomorphism keeps the (non-)emptiness of every centre. -/
theorem noEmptyCenters_map_iff : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (L : BlowUpSequence ψ₀ M),
    (L.map g).NoEmptyCenters ↔ L.NoEmptyCenters
  | _, _, _, nil _ => ⟨fun _ => noEmptyCenters_nil, fun _ => noEmptyCenters_nil⟩
  | _, _, g, cons hY rest => by
    rw [map_cons, noEmptyCenters_cons_iff, noEmptyCenters_cons_iff, noEmptyCenters_map_iff]
    refine and_congr ?_ Iff.rfl
    rw [not_iff_not, Set.image_eq_empty]

theorem noEmptyCenters_eraseEmpty : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M),
    L.eraseEmpty.NoEmptyCenters
  | _, nil _ => noEmptyCenters_nil
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest => by
    by_cases hY₀ : Y = ∅
    · rw [eraseEmpty_cons_of_eq_empty hY rest hY₀, noEmptyCenters_map_iff]
      exact noEmptyCenters_eraseEmpty rest
    · rw [eraseEmpty_cons_of_ne_empty hY rest hY₀, noEmptyCenters_cons_iff]
      exact ⟨hY₀, noEmptyCenters_eraseEmpty rest⟩

theorem eraseEmpty_of_noEmptyCenters : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M),
    L.NoEmptyCenters → L.eraseEmpty = L
  | _, nil _, _ => rfl
  | _, cons hY rest, h => by
    obtain ⟨hne, h'⟩ := (noEmptyCenters_cons_iff hY rest).mp h
    rw [eraseEmpty_cons_of_ne_empty hY rest hne, eraseEmpty_of_noEmptyCenters rest h']

theorem eraseEmpty_eq_self_iff (L : BlowUpSequence ψ₀ M) : L.eraseEmpty = L ↔ L.NoEmptyCenters :=
  ⟨fun h => h ▸ noEmptyCenters_eraseEmpty L, eraseEmpty_of_noEmptyCenters L⟩

theorem eraseEmpty_eraseEmpty (L : BlowUpSequence ψ₀ M) : L.eraseEmpty.eraseEmpty = L.eraseEmpty :=
  eraseEmpty_of_noEmptyCenters _ (noEmptyCenters_eraseEmpty L)

end AnalyticManifold.BlowUpSequence

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- [Kol07, 32]: deleting empty blow-ups from an output of a functor changes nothing. -/
theorem AnalyticBlowUpSequenceAssignment.eraseEmpty_seq
    {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
    (B : AnalyticBlowUpSequenceAssignment ψ₀ Dom) {M : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ M) (hT : Dom T) : (B.seq T hT).eraseEmpty = B.seq T hT :=
  BlowUpSequence.eraseEmpty_of_noEmptyCenters _ (B.noEmptyCenters T hT)

end Manifold

end
