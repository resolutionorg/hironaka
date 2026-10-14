/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Sort

/-!
# Kollár's coordinate order for a blow-up chart

Kollár's chart of the blowing-up [Kol07, Definition 60, (60.2)] lists the coordinates so that the
centre's coordinates other than the divisor coordinate come first (positions `< r`), the divisor
coordinate `x_r` is at position `r`, and the coordinates transversal to the centre come after.
Given the block indices `σ : Fin c ↪ Fin n` of an adapted chart and the index `i` of the blow-up
chart, `exists_kollarPerm` produces `r = c - 1` and a permutation `τ` of `Fin n` with `τ r = σ i`
and `{j | j < r} = τ⁻¹(σ '' {k | k ≠ i})`. These are the hypotheses under which a blow-up chart is
read in Kollár's coordinates (`blowUpChartMap_eq_kollarChart` of
`Hironaka.Manifold.BlowUp.Quadratic`) and the chart-ring homomorphism `exists_chartRing_hom`
of `Hironaka.Manifold.BlowUp.Transform.KollarChart` is built. Pure combinatorics; not in the
sources.
-/

@[expose] public section

namespace Manifold

open Finset

variable {c n : ℕ}

/-- The centre indices other than `σ i`. -/
def kollarFirst (σ : Fin c ↪ Fin n) (i : Fin c) : Finset (Fin n) := (Finset.univ.map σ).erase (σ i)

/-- The indices outside the centre. -/
def kollarLast (σ : Fin c ↪ Fin n) : Finset (Fin n) := (Finset.univ.map σ)ᶜ

theorem card_kollarFirst (σ : Fin c ↪ Fin n) (i : Fin c) : (kollarFirst σ i).card = c - 1 := by
  rw [kollarFirst, Finset.card_erase_of_mem (Finset.mem_map_of_mem _ (Finset.mem_univ i)),
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem card_kollarLast (σ : Fin c ↪ Fin n) : (kollarLast σ).card = n - c := by
  rw [kollarLast, Finset.card_compl, Finset.card_map, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fin]

theorem c_le_n (σ : Fin c ↪ Fin n) : c ≤ n := by
  have := Fintype.card_le_of_injective σ σ.injective
  simpa using this

theorem c_pos (i : Fin c) : 0 < c := Fin.pos i

/-- A permutation `τ` of the coordinate indices with the centre's other coordinates at the
positions `< r = c - 1`, the divisor coordinate `σ i` at `r`, and the transversal coordinates
after, as in Kollár's chart [Kol07, Definition 60, (60.2)]. -/
theorem exists_kollarPerm (σ : Fin c ↪ Fin n) (i : Fin c) :
    ∃ (r : Fin n) (τ : Fin n ≃ Fin n), τ r = σ i ∧ ∀ j, j < r ↔ ∃ k, k ≠ i ∧ τ j = σ k := by
  classical
  have hcn : c ≤ n := c_le_n σ
  have hc : 0 < c := c_pos i
  have hr : c - 1 < n := by omega
  obtain ⟨r, hrval⟩ : ∃ r : Fin n, r.val = c - 1 := ⟨⟨c - 1, hr⟩, rfl⟩
  -- the two enumerations, made opaque
  obtain ⟨eA, heA, hAmem'⟩ : ∃ eA : Fin (c - 1) → Fin n, Function.Injective eA ∧
      ∀ a, eA a ∈ kollarFirst σ i :=
    ⟨(kollarFirst σ i).orderEmbOfFin (card_kollarFirst σ i), (Finset.orderEmbOfFin _ _).injective,
      Finset.orderEmbOfFin_mem _ _⟩
  obtain ⟨eC, heC, hCmem'⟩ : ∃ eC : Fin (n - c) → Fin n, Function.Injective eC ∧
      ∀ a, eC a ∈ kollarLast σ :=
    ⟨(kollarLast σ).orderEmbOfFin (card_kollarLast σ), (Finset.orderEmbOfFin _ _).injective,
      Finset.orderEmbOfFin_mem _ _⟩
  -- the map, made opaque through its three defining equations
  obtain ⟨f, hfA, hfr, hfC⟩ : ∃ f : Fin n → Fin n,
      (∀ (j : Fin n) (h₁ : j.val < c - 1), f j = eA ⟨j.val, h₁⟩) ∧ f r = σ i ∧
      ∀ (j : Fin n) (h₁ : ¬ j.val < c - 1) (h₂ : j.val ≠ c - 1),
        f j = eC ⟨j.val - c, by omega⟩ := by
    refine ⟨fun j => if h₁ : j.val < c - 1 then eA ⟨j.val, h₁⟩
      else if h₂ : j.val = c - 1 then σ i else eC ⟨j.val - c, by omega⟩, ?_, ?_, ?_⟩
    · intro j h₁
      dsimp only
      rw [dite_eq_left h₁]
    · have h₁ : ¬ r.val < c - 1 := by omega
      dsimp only
      rw [dite_eq_right h₁, dite_eq_left hrval]
    · intro j h₁ h₂
      dsimp only
      rw [dite_eq_right h₁, dite_eq_right h₂]
  have hAmem : ∀ (j : Fin n) (h₁ : j.val < c - 1), f j ∈ kollarFirst σ i := fun j h₁ => by
    rw [hfA j h₁]; exact hAmem' _
  have hCmem : ∀ (j : Fin n) (h₁ : ¬ j.val < c - 1) (h₂ : j.val ≠ c - 1), f j ∈ kollarLast σ :=
    fun j h₁ h₂ => by rw [hfC j h₁ h₂]; exact hCmem' _
  have hσA : σ i ∉ kollarFirst σ i := Finset.notMem_erase _ _
  have hσC : σ i ∉ kollarLast σ := by
    rw [kollarLast, Finset.mem_compl, not_not]
    exact Finset.mem_map_of_mem _ (Finset.mem_univ i)
  have hAC : ∀ a ∈ kollarFirst σ i, a ∉ kollarLast σ := fun a ha hb => by
    rw [kollarLast, Finset.mem_compl] at hb
    exact hb (Finset.mem_of_mem_erase ha)
  -- injectivity
  have hinj : Function.Injective f := by
    intro j j' hjj'
    by_cases h₁ : j.val < c - 1 <;> by_cases h₁' : j'.val < c - 1
    · rw [hfA j h₁, hfA j' h₁'] at hjj'
      exact Fin.ext (Fin.mk.inj_iff.mp (heA hjj'))
    · by_cases h₂' : j'.val = c - 1
      · rw [hfA j h₁] at hjj'
        have : f j' = σ i := by
          have : j' = r := Fin.ext (h₂'.trans hrval.symm)
          rw [this, hfr]
        rw [this] at hjj'
        exact (hσA (hjj' ▸ hAmem' _)).elim
      · rw [hfA j h₁, hfC j' h₁' h₂'] at hjj'
        exact (hAC _ (hAmem' _) (hjj' ▸ hCmem' _)).elim
    · by_cases h₂ : j.val = c - 1
      · have : f j = σ i := by
          have : j = r := Fin.ext (h₂.trans hrval.symm)
          rw [this, hfr]
        rw [this, hfA j' h₁'] at hjj'
        exact (hσA (hjj'.symm ▸ hAmem' _)).elim
      · rw [hfC j h₁ h₂, hfA j' h₁'] at hjj'
        exact (hAC _ (hAmem' _) (hjj'.symm ▸ hCmem' _)).elim
    · by_cases h₂ : j.val = c - 1 <;> by_cases h₂' : j'.val = c - 1
      · exact Fin.ext (h₂.trans h₂'.symm)
      · have : f j = σ i := by
          have : j = r := Fin.ext (h₂.trans hrval.symm)
          rw [this, hfr]
        rw [this, hfC j' h₁' h₂'] at hjj'
        exact (hσC (hjj' ▸ hCmem' _)).elim
      · have : f j' = σ i := by
          have : j' = r := Fin.ext (h₂'.trans hrval.symm)
          rw [this, hfr]
        rw [this, hfC j h₁ h₂] at hjj'
        exact (hσC (hjj'.symm ▸ hCmem' _)).elim
      · rw [hfC j h₁ h₂, hfC j' h₁' h₂'] at hjj'
        have := Fin.mk.inj_iff.mp (heC hjj')
        exact Fin.ext (by omega)
  let τ : Fin n ≃ Fin n := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩)
  refine ⟨r, τ, hfr, fun j => ?_⟩
  change j < r ↔ ∃ k, k ≠ i ∧ f j = σ k
  constructor
  · intro hj
    have h₁ : j.val < c - 1 := hrval ▸ hj
    have hmem := hAmem j h₁
    rw [kollarFirst, Finset.mem_erase, Finset.mem_map] at hmem
    obtain ⟨hne, k, -, hk⟩ := hmem
    exact ⟨k, fun hki => hne (by rw [← hk, hki]), hk.symm⟩
  · rintro ⟨k, hki, hk⟩
    by_contra hj
    have h₁ : ¬ j.val < c - 1 := fun h => hj (show j < r from by rw [Fin.lt_def, hrval]; exact h)
    by_cases h₂ : j.val = c - 1
    · have : j = r := Fin.ext (h₂.trans hrval.symm)
      rw [this, hfr] at hk
      exact hki (σ.injective hk).symm
    · have hmem := hCmem j h₁ h₂
      rw [hk, kollarLast, Finset.mem_compl] at hmem
      exact hmem (Finset.mem_map_of_mem _ (Finset.mem_univ k))

end Manifold
