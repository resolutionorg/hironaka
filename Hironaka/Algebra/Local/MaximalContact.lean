/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Hironaka.Algebra.Local.PowerSeries

/-!
# The ideal of maximal contacts and MC-invariance

For `m ≥ 1` the *maximal contact ideal* is `MC_m(I) = D^(m-1) I` [Kol07, 51 and Definition 79];
`I` is *MC-invariant* with respect to `m` if `MC_m(I) · D(I) ⊂ I` [Kol07, 53, (53.1)].  Kollár's
note to Definition 79 — `MC(I)` has order `1` where `ord I = m` and order `0` where `ord I < m`,
so `cosupp MC(I) = cosupp (I, m)` — is the order statement of [Kol07, Lemma 74(3)].  The local
construction of maximal contact [Kol07, 51.2]: if `ord I = m` there is `h ∈ MC_m(I)` of order
`1`, and `h` is the first member of a system of coordinates, with `∂'₁ h = 1`
(`exists_maximalContact`).  Two examples: `⟨xᵢ^m⟩` is MC-invariant and `⟨xᵢ xⱼ⟩` is not
MC-invariant with respect to `2`.

The coordinate half of the construction needs a system of coordinates containing a given
`h ∈ 𝔪 ∖ 𝔪²`: `h = ∑ aⱼ xⱼ` with some `aᵢ` a unit (else `h ∈ 𝔪²`), so `x` with `xᵢ` replaced by
`h` still generates `𝔪` (`exists_span_update`), and the change of coordinates of
`Hironaka/Algebra/Local/Coords.lean` applies under the standing hypothesis that the `∂ᵢ` span the
derivations (as in `changeCoordsOfSpans`); `reindex` moves `h` to the first position.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n)

/-! ### Reindexing and replacing a coordinate -/

/-- Reindexing a coordinate structure along a permutation of the indices. -/
def reindex (σ : Equiv.Perm (Fin n)) : RegularCoords R n where
  x := c.x ∘ σ
  pderiv := c.pderiv ∘ σ
  span_x := by rw [c.span_x, σ.surjective.range_comp]
  card := c.card
  pderiv_x i j := by
    simp only [Function.comp_apply, c.pderiv_x, σ.injective.eq_iff]
  pderiv_comm i j f := c.pderiv_comm (σ i) (σ j) f

@[simp] theorem reindex_x (σ : Equiv.Perm (Fin n)) (i : Fin n) : (c.reindex σ).x i = c.x (σ i) :=
  rfl

@[simp] theorem reindex_pderiv (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (c.reindex σ).pderiv i = c.pderiv (σ i) :=
  rfl

/-- An element `h ∈ 𝔪 ∖ 𝔪²` can replace one of the coordinates as a generator of `𝔪` (the
coordinate step of the local construction of maximal contact, [Kol07, 51.2]). -/
theorem exists_span_update {h : R} (hh : h ∈ maximalIdeal R) (hh' : h ∉ maximalIdeal R ^ 2) :
    ∃ i : Fin n, maximalIdeal R = Ideal.span (Set.range (Function.update c.x i h)) := by
  classical
  have hh1 := hh
  rw [c.span_x] at hh1
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hh1
  by_contra hcon
  push Not at hcon
  have hall : ∀ i, a i ∈ maximalIdeal R := by
    intro i
    by_contra hai
    have hu : IsUnit (a i) := IsLocalRing.notMem_maximalIdeal.mp hai
    apply hcon i
    refine le_antisymm ?_ ?_
    · rw [c.span_x, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hji : j = i
      · subst hji
        have hsum : a j * c.x j + ∑ k ∈ Finset.univ.erase j, a k * c.x k = h :=
          (Finset.add_sum_erase _ (fun k => a k * c.x k) (Finset.mem_univ j)).trans ha
        have hmem : a j * c.x j ∈ Ideal.span (Set.range (Function.update c.x j h)) := by
          rw [← sub_eq_of_eq_add hsum.symm]
          refine Ideal.sub_mem _ (Ideal.subset_span ⟨j, Function.update_self j h c.x⟩)
            (Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, ?_⟩))
          exact Function.update_of_ne (Finset.ne_of_mem_erase hk) h c.x
        have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : R) hmem
        rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this
      · exact Ideal.subset_span ⟨j, Function.update_of_ne hji h c.x⟩
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hji : j = i
      · subst hji
        rw [Function.update_self]
        exact hh
      · rw [Function.update_of_ne hji]
        exact c.x_mem_maximalIdeal j
  apply hh'
  rw [← ha, pow_two]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (hall i) (c.x_mem_maximalIdeal i)

/-- An element of order `1` is a member of some system of coordinates, given that the `∂ᵢ`
span the derivations (the coordinate half of [Kol07, 51.2]). -/
theorem exists_coords_x_eq (hs : c.SpansDerivations ℚ) {h : R} (hh : ordElem h = 1) :
    ∃ (c' : RegularCoords R n) (i : Fin n), c'.x i = h := by
  obtain ⟨hh1, hh2⟩ := ordElem_eq_one_iff.mp hh
  obtain ⟨i, hi⟩ := c.exists_span_update hh1 hh2
  refine ⟨c.changeCoordsOfSpans hs (Function.update c.x i h) hi, i, ?_⟩
  rw [changeCoordsOfSpans, changeCoords_x, Function.update_self]

/-- An element `h` of order `1` is the first coordinate of some system of coordinates `x'`, with
`∂'₁ h = 1`. -/
theorem exists_coords_x_zero_eq (hs : c.SpansDerivations ℚ) {h : R} (hh : ordElem h = 1) :
    ∃ (hn : 0 < n) (c' : RegularCoords R n), c'.x ⟨0, hn⟩ = h ∧ c'.pderiv ⟨0, hn⟩ h = 1 := by
  classical
  obtain ⟨c₁, i, hi⟩ := c.exists_coords_x_eq hs hh
  refine ⟨i.pos, c₁.reindex (Equiv.swap ⟨0, i.pos⟩ i), ?_, ?_⟩
  · rw [reindex_x, Equiv.swap_apply_left, hi]
  · have := (c₁.reindex (Equiv.swap ⟨0, i.pos⟩ i)).pderiv_x ⟨0, i.pos⟩ ⟨0, i.pos⟩
    rwa [ite_eq_left rfl, reindex_x, Equiv.swap_apply_left, hi] at this

/-! ### The maximal contact ideal -/

/-- The **maximal contact ideal** `MC_m(I) = D^(m-1) I` [Kol07, 51 and Definition 79]. -/
def MC (I : Ideal R) (m : ℕ) : Ideal R := c.Dpow (m - 1) I

/-- `I` is **MC-invariant** with respect to `m` if `MC_m(I) · D(I) ≤ I` [Kol07, 53, (53.1)]. -/
def IsMCInvariant (I : Ideal R) (m : ℕ) : Prop := c.MC I m * c.D I ≤ I

/-- `MC(I)` has order `1` where `ord I = m` (the note to [Kol07, Definition 79]). -/
theorem ord_MC_of_ord_eq {I : Ideal R} {m : ℕ} (hm : 1 ≤ m) (hI : ord I = m) :
    ord (c.MC I m) = 1 := by
  rw [MC, c.ord_Dpow_of_ord_eq hI (Nat.sub_le m 1), Nat.sub_sub_self hm, Nat.cast_one]

/-- `MC(I)` has order `0` where `ord I < m` (the note to [Kol07, Definition 79]). -/
theorem MC_eq_top_of_ord_lt {I : Ideal R} {m : ℕ} (hm : 1 ≤ m) (hI : ord I < m) :
    c.MC I m = ⊤ := by
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hI)
  rw [← ha] at hI
  have ham : a < m := by exact_mod_cast hI
  exact c.Dpow_eq_top_of_ord_le (by rw [← ha]; exact_mod_cast (show a ≤ m - 1 by omega))

/-- If `ord I = m ≥ 1` there is `h ∈ MC_m(I)` of order `1` ([Kol07, 51.2]; "pick `x₁ ∈ MC(I)`
that has order `1` at `p`" in the proof of [Kol07, Proposition 99]). -/
theorem exists_mem_MC_ordElem_eq_one {I : Ideal R} {m : ℕ} (hm : 1 ≤ m) (hI : ord I = m) :
    ∃ h ∈ c.MC I m, ordElem h = 1 := by
  have hord := c.ord_MC_of_ord_eq hm hI
  obtain ⟨S, hS, hspan⟩ := Submodule.fg_def.mp (IsNoetherian.noetherian (c.MC I m))
  have hspan' : Ideal.span S = c.MC I m := hspan
  have hne : S.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [← hspan', Ideal.span_empty, ord_bot] at hord
    exact ENat.top_ne_one hord
  obtain ⟨h, hhS, hh⟩ := exists_ord_span_eq_ordElem hS hne
  exact ⟨h, hspan' ▸ Ideal.subset_span hhS, by rw [← hh, hspan', hord]⟩

/-- **The local construction of maximal contact** [Kol07, 51.2]: if `ord I = m ≥ 1` then some
`h ∈ MC_m(I)` has order `1` and is the first coordinate of a system of coordinates `x'` with
`∂'₁ h = 1` (given that the `∂ᵢ` span the derivations). -/
theorem exists_maximalContact (hs : c.SpansDerivations ℚ) {I : Ideal R} {m : ℕ} (hm : 1 ≤ m)
    (hI : ord I = m) :
    ∃ h ∈ c.MC I m, ordElem h = 1 ∧
      ∃ (hn : 0 < n) (c' : RegularCoords R n), c'.x ⟨0, hn⟩ = h ∧ c'.pderiv ⟨0, hn⟩ h = 1 := by
  obtain ⟨h, hmem, hh⟩ := c.exists_mem_MC_ordElem_eq_one hm hI
  exact ⟨h, hmem, hh, c.exists_coords_x_zero_eq hs hh⟩

/-! ### Examples -/

/-- `MC_m ⟨xᵢ^m⟩ = ⟨xᵢ⟩` for `m ≥ 1`. -/
theorem MC_span_singleton_x_pow (i : Fin n) {m : ℕ} (hm : 1 ≤ m) :
    c.MC (Ideal.span {c.x i ^ m}) m = Ideal.span {c.x i} := by
  rw [MC, c.Dpow_span_singleton_x_pow i (Nat.sub_le m 1), Nat.sub_sub_self hm, pow_one]

/-- `⟨xᵢ^m⟩` is MC-invariant with respect to `m ≥ 1` (`MC = ⟨xᵢ⟩`, `D ⟨xᵢ^m⟩ = ⟨xᵢ^(m-1)⟩`). -/
theorem isMCInvariant_span_singleton_x_pow (i : Fin n) {m : ℕ} (hm : 1 ≤ m) :
    c.IsMCInvariant (Ideal.span {c.x i ^ m}) m := by
  unfold IsMCInvariant
  rw [c.MC_span_singleton_x_pow i hm, c.D_span_singleton_x_pow i hm,
    Ideal.span_singleton_mul_span_singleton, ← pow_succ', Nat.sub_add_cancel hm]

/-- `⟨xᵢ xⱼ⟩` is not MC-invariant with respect to `2` as soon as `xᵢ² ∉ ⟨xᵢ xⱼ⟩` (which holds in
`ℚ⟦x₁, x₂⟧`, `X_sq_notMem_span_X_mul_X`), since `MC₂ ⟨xᵢ xⱼ⟩ = D ⟨xᵢ xⱼ⟩ = ⟨xᵢ, xⱼ⟩`. -/
theorem not_isMCInvariant_span_singleton_x_mul_x {i j : Fin n} (hij : i ≠ j)
    (h : c.x i ^ 2 ∉ Ideal.span {c.x i * c.x j}) :
    ¬ c.IsMCInvariant (Ideal.span {c.x i * c.x j}) 2 := by
  intro hinv
  unfold IsMCInvariant at hinv
  rw [MC, Nat.add_one_sub_one, Dpow_one, c.D_span_singleton_x_mul_x hij] at hinv
  apply h
  rw [sq]
  exact hinv (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))

end RegularCoords

end IsLocalRing
