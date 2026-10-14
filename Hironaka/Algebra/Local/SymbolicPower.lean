/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Algebra.Local.CohenIso
import Hironaka.Algebra.Local.CompletionCoords
import Hironaka.Algebra.Local.RegularSystem
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Order along a coordinate subspace: symbolic equals ordinary power

Kollár defines `ord_Z I` at the generic point of `Z` [Kol07, Definition 47] and remarks that
"the number `ord_Z I` equals the multiplicity of `π^* I` along the exceptional divisor" (the
remark following Definition 47); the chart formula for the birational transform
(`Hironaka/Algebra/Local/BirationalTransform.lean`) applies under `ord_Z I ≥ m`, which is what needs
`m ≤ ord_P(I) ⟺ I ≤ Pᵐ` for `P = ⟨x₀, …, x_r⟩`: the symbolic power `Pᵐ R_P ∩ R` equals the
ordinary power `Pᵐ`.

The route goes through the completion: under the Cohen isomorphism `Φ : K⟦X⟧ ≃ R̂` of
`Hironaka/Algebra/Local/CohenIso.lean` (`Φ(Xᵢ) = xᵢ`) and `I R̂ ∩ R = I` of
`Hironaka/Algebra/Local/CompletionCoords.lean`, `f ∈ Pᵐ` iff the series of `f` has weighted order `≥
m` for the weights `1` on `X₀, …, X_r` and `0` elsewhere — the pure power-series fact
`⟨X₀, …, X_r⟩ᵐ = {F | m ≤ weightedOrder F}`, proved by induction on `m` with the division
`F = ∑ᵢ Xᵢ Gᵢ + F'` (`F'` the monomials free of `X₀, …, X_r`).  Since the weighted order is
additive over a field (`MvPowerSeries.weightedOrder_mul`), `s f ∈ Pᵐ` with `s ∉ P` forces
`f ∈ Pᵐ`: `Pᵐ` is `P`-primary, so `Pᵐ R_P ∩ R = Pᵐ`, and `m ≤ ord_P I ⟺ I ≤ Pᵐ` follows from
`le_ord_iff` in `R_P`.  No associated graded ring is used.  Standard commutative algebra, not in
the sources in this form; the final equivalence is used for the order along the exceptional
divisor in `Hironaka/Scheme/IdealSheaf/Order/Exceptional.lean`.

The ideal `P` is `chartCenter c.x r = ⟨xᵢ : i ≤ r⟩` of
`Hironaka/Algebra/Local/BirationalTransform.lean`; it is prime by
`Hironaka/Algebra/Local/RegularSystem.lean`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

/-! ### The power-series fact: `⟨Xᵢ : i ∈ T⟩ᵐ = {F | m ≤ weightedOrder_T F}` -/

section PowerSeries

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The indicator weights of a set `T` of variables: `1` on `T`, `0` elsewhere. -/
abbrev indicatorWeight (T : Finset (Fin n)) : Fin n → ℕ := fun i => if i ∈ T then 1 else 0

theorem weight_indicator_eq_zero_iff (T : Finset (Fin n)) (d : Fin n →₀ ℕ) :
    Finsupp.weight (indicatorWeight T) d = 0 ↔ ∀ i ∈ T, d i = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h i hi
    by_contra hd
    have := h i (Finsupp.mem_support_iff.mpr hd)
    simp [indicatorWeight, hi, hd] at this
  · intro h i hi
    by_cases hiT : i ∈ T
    · exact absurd (h i hiT) (Finsupp.mem_support_iff.mp hi)
    · simp [indicatorWeight, hiT]

theorem indicatorWeight_le_one (T : Finset (Fin n)) (i : Fin n) : indicatorWeight T i ≤ 1 := by
  unfold indicatorWeight
  split_ifs <;> omega

/-- The series of weighted order at least `m` form an ideal (`0` has order `⊤`; the order of a
sum is at least the minimum; the order of a product is at least the sum). -/
def weightedOrderIdeal (w : Fin n → ℕ) (m : ℕ) : Ideal (MvPowerSeries (Fin n) K) where
  carrier := {F | (m : ℕ∞) ≤ F.weightedOrder w}
  add_mem' {F G} hF hG := le_trans (le_min hF hG) (min_weightedOrder_le_add w)
  zero_mem' := by
    change (m : ℕ∞) ≤ (0 : MvPowerSeries (Fin n) K).weightedOrder w
    rw [weightedOrder_zero]
    exact le_top
  smul_mem' a {F} hF := by
    change (m : ℕ∞) ≤ (a * F).weightedOrder w
    exact le_trans (le_add_left hF) (le_weightedOrder_mul w)

theorem mem_weightedOrderIdeal {w : Fin n → ℕ} {m : ℕ} {F : MvPowerSeries (Fin n) K} :
    F ∈ weightedOrderIdeal w m ↔ (m : ℕ∞) ≤ F.weightedOrder w := Iff.rfl

/-- `Xᵢ`, `i ∈ T`, has weighted order `1`. -/
theorem span_X_le_weightedOrderIdeal_one [Nontrivial K] (T : Finset (Fin n)) :
    Ideal.span (X '' (T : Set (Fin n))) ≤
      weightedOrderIdeal (K := K) (indicatorWeight T) 1 := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, hi, rfl⟩
  change ((1 : ℕ) : ℕ∞) ≤ (X i : MvPowerSeries (Fin n) K).weightedOrder _
  rw [X_def, weightedOrder_monomial_of_ne_zero _ one_ne_zero, Finsupp.weight_single, one_smul]
  simp [indicatorWeight, Finset.mem_coe.mp hi]

/-- `⟨Xᵢ : i ∈ T⟩ᵐ ≤ {F | m ≤ weightedOrder_T F}`. -/
theorem span_X_pow_le_weightedOrderIdeal [Nontrivial K] (T : Finset (Fin n)) (m : ℕ) :
    Ideal.span (X '' (T : Set (Fin n))) ^ m ≤
      weightedOrderIdeal (K := K) (indicatorWeight T) m := by
  induction m with
  | zero =>
    intro F _
    rw [mem_weightedOrderIdeal, Nat.cast_zero]
    exact zero_le
  | succ m ih =>
    rw [pow_succ, Ideal.mul_le]
    intro F hF G hG
    rw [mem_weightedOrderIdeal, Nat.cast_succ]
    exact le_trans (add_le_add (ih hF) (span_X_le_weightedOrderIdeal_one T hG))
      (le_weightedOrder_mul _)

/-- The division step of the converse, by induction on the set `T'` of variables that every
monomial of `F` involves: `F = X_a G + F'` with `F'` the monomials free of `X_a`; `G` keeps
weighted order `≥ m` when every monomial of `F` has weight `≥ m + 1`. -/
theorem mem_span_X_mul_weightedOrderIdeal (T : Finset (Fin n)) (m : ℕ) (T' : Finset (Fin n)) :
    T' ⊆ T → ∀ F : MvPowerSeries (Fin n) K,
      (∀ d, coeff d F ≠ 0 →
        m + 1 ≤ Finsupp.weight (indicatorWeight T) d ∧ ∃ i ∈ T', d i ≠ 0) →
      F ∈ Ideal.span (X '' (T : Set (Fin n))) * weightedOrderIdeal (indicatorWeight T) m := by
  induction T' using Finset.induction_on with
  | empty =>
    intro _ F hF
    have : F = 0 := by
      ext d
      by_contra hd
      obtain ⟨_, i, hi, _⟩ := hF d hd
      exact Finset.notMem_empty i hi
    rw [this]
    exact Ideal.zero_mem _
  | insert a T' _ ih =>
    intro hT F hF
    set G : MvPowerSeries (Fin n) K := fun e => coeff (e + Finsupp.single a 1) F with hG
    set F' : MvPowerSeries (Fin n) K := fun d => if d a = 0 then coeff d F else 0 with hF'
    have hsplit : F = X a * G + F' := by
      ext d
      rw [map_add, X_def, coeff_monomial_mul]
      by_cases hda : d a = 0
      · have hnle : ¬ Finsupp.single a 1 ≤ d := by
          rw [Finsupp.single_le_iff]
          omega
        rw [ite_eq_right hnle, zero_add]
        exact (ite_eq_left hda).symm
      · have hle : Finsupp.single a 1 ≤ d := by
          rw [Finsupp.single_le_iff]
          omega
        rw [ite_eq_left hle, one_mul]
        change coeff d F =
          coeff (d - Finsupp.single a 1 + Finsupp.single a 1) F + if d a = 0 then coeff d F else 0
        rw [tsub_add_cancel_of_le hle, ite_eq_right hda, add_zero]
    rw [hsplit]
    refine Ideal.add_mem _ (Ideal.mul_mem_mul
      (Ideal.subset_span ⟨a, hT (Finset.mem_insert_self a T'), rfl⟩) ?_)
      (ih (fun i hi => hT (Finset.mem_insert_of_mem hi)) F' ?_)
    · rw [mem_weightedOrderIdeal]
      refine nat_le_weightedOrder _ fun e he => ?_
      by_contra hne
      obtain ⟨hw, -⟩ := hF (e + Finsupp.single a 1) hne
      rw [map_add, Finsupp.weight_single, one_smul] at hw
      have := indicatorWeight_le_one T a
      omega
    · intro d hd
      have hda : d a = 0 := by
        by_contra h
        exact hd (ite_eq_right h)
      obtain ⟨hw, i, hi, hdi⟩ :=
        hF d (by rwa [show coeff d F' = coeff d F from ite_eq_left hda] at hd)
      refine ⟨hw, i, ?_, hdi⟩
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact absurd hda hdi
      · exact hi'

/-- `{F | m ≤ weightedOrder_T F} ≤ ⟨Xᵢ : i ∈ T⟩ᵐ`, by induction on `m` and the division step. -/
theorem weightedOrderIdeal_le_span_X_pow (T : Finset (Fin n)) (m : ℕ) :
    weightedOrderIdeal (K := K) (indicatorWeight T) m ≤
      Ideal.span (X '' (T : Set (Fin n))) ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact le_top
  | succ m ih =>
    intro F hF
    rw [pow_succ']
    refine Ideal.mul_mono_right ih ?_
    refine mem_span_X_mul_weightedOrderIdeal T m T subset_rfl F fun d hd => ?_
    have hw : m + 1 ≤ Finsupp.weight (indicatorWeight T) d := by
      have h1 := weightedOrder_le (indicatorWeight T) hd
      exact_mod_cast le_trans (mem_weightedOrderIdeal.mp hF) h1
    refine ⟨hw, ?_⟩
    by_contra hcon
    push Not at hcon
    have h0 := (weight_indicator_eq_zero_iff T d).mpr hcon
    omega

/-- The power-series fact: `⟨Xᵢ : i ∈ T⟩ᵐ` is the set of series all of whose monomials have
`T`-degree at least `m`. -/
theorem mem_span_X_pow_iff_le_weightedOrder [Nontrivial K] (T : Finset (Fin n)) (m : ℕ)
    (F : MvPowerSeries (Fin n) K) :
    F ∈ Ideal.span (X '' (T : Set (Fin n))) ^ m ↔
      (m : ℕ∞) ≤ F.weightedOrder (fun i => if i ∈ T then 1 else 0) :=
  ⟨fun h => span_X_pow_le_weightedOrderIdeal T m h, fun h => weightedOrderIdeal_le_span_X_pow T m h⟩

end PowerSeries

/-! ### Transport to `R` through the Cohen isomorphism -/

section Transport

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (x : Fin n → R) (hx : maximalIdeal R = Ideal.span (Set.range x))
  (hn : (n : WithBot ℕ∞) = ringKrullDim R) (r : Fin n)

omit [Algebra ℚ R] in
include hx hn in
/-- `P = ⟨x₀, …, x_r⟩` is prime for a regular system of parameters `x` (`isPrime_span_image_lt`
for the initial segment `{j | j.val < r + 1}`). -/
theorem isPrime_chartCenter : (chartCenter x r).IsPrime := by
  have h := isPrime_span_image_lt x hx hn (r.val + 1)
  have hset : {i : Fin n | i ≤ r} = {j : Fin n | j.val < r.val + 1} := by
    ext j
    change j ≤ r ↔ j.val < r.val + 1
    rw [Fin.le_def]
    omega
  rw [chartCenter, hset]
  exact h

local notation "R̂" => AdicCompletion (maximalIdeal R) R

/-- The Cohen isomorphism for the regular system of parameters `x`: `Φ(Xᵢ) = ι(xᵢ)`. -/
theorem cohenEquiv_X (i : Fin n) :
    cohenEquiv R x hx hn (X i) = algebraMap R R̂ (x i) := by
  rw [cohenEquiv_apply]
  exact cohenMap_X R x _ i

/-- `Pᵐ R̂ = Φ(⟨X₀, …, X_r⟩ᵐ)`. -/
theorem map_chartCenter_pow (m : ℕ) :
    (chartCenter x r ^ m).map (algebraMap R R̂) =
      (Ideal.span (X '' ((Finset.univ.filter (· ≤ r) : Finset (Fin n)) : Set (Fin n))) ^ m).map
        (cohenEquiv R x hx hn) := by
  have hS : ((Finset.univ.filter (· ≤ r) : Finset (Fin n)) : Set (Fin n)) = {i | i ≤ r} := by
    ext i
    simp
  have hfun : (fun i => algebraMap R R̂ (x i)) = fun i => cohenEquiv R x hx hn (X i) := by
    funext i
    rw [cohenEquiv_X]
  rw [Ideal.map_pow, Ideal.map_pow, chartCenter, Ideal.map_span, Ideal.map_span, Set.image_image,
    Set.image_image, hS, hfun]

theorem mem_chartCenter_pow_iff_le_weightedOrder' (f : R) (m : ℕ) :
    f ∈ chartCenter x r ^ m ↔
      (m : ℕ∞) ≤ ((cohenEquiv R x hx hn).symm (algebraMap R R̂ f)).weightedOrder
        (indicatorWeight (Finset.univ.filter (· ≤ r))) := by
  rw [← mem_span_X_pow_iff_le_weightedOrder, ← Ideal.mem_comap, Ideal.comap_symm,
    ← map_chartCenter_pow x hx hn r, ← Ideal.mem_comap, comap_map_adicCompletion]

/-- `f ∈ Pᵐ` iff the series of `f` under the Cohen isomorphism has weighted order `≥ m` for the
weights `1` on `X₀, …, X_r` and `0` elsewhere — "`Pᵐ` is the set of series all of whose
monomials have `x₀, …, x_r`-degree at least `m`". -/
theorem mem_chartCenter_pow_iff_le_weightedOrder (f : R) (m : ℕ) :
    f ∈ chartCenter x r ^ m ↔
      (m : ℕ∞) ≤ ((cohenEquiv R x hx hn).symm (algebraMap R R̂ f)).weightedOrder
        (fun i => if i ≤ r then 1 else 0) := by
  have hw : (fun i : Fin n => if i ≤ r then 1 else 0) =
      indicatorWeight (Finset.univ.filter (· ≤ r)) := by
    funext i
    simp [indicatorWeight]
  rw [hw]
  exact mem_chartCenter_pow_iff_le_weightedOrder' x hx hn r f m

/-- `s ∉ P` iff the series of `s` has weighted order `0`. -/
theorem weightedOrder_symm_algebraMap_eq_zero {s : R} (hs : s ∉ chartCenter x r) :
    ((cohenEquiv R x hx hn).symm (algebraMap R R̂ s)).weightedOrder
      (fun i => if i ≤ r then 1 else 0) = 0 := by
  by_contra hne
  apply hs
  rw [← pow_one (chartCenter x r), mem_chartCenter_pow_iff_le_weightedOrder x hx hn r,
    Nat.cast_one]
  exact Order.one_le_iff_ne_zero.mpr hne

include hx hn in
/-- `Pᵐ` is `P`-primary — `s ∉ P` and `s f ∈ Pᵐ` give `f ∈ Pᵐ`, because the weighted order is
additive (`MvPowerSeries.weightedOrder_mul`) and that of `s` is `0`. -/
theorem mem_chartCenter_pow_of_mul_mem {s f : R} (hs : s ∉ chartCenter x r) {m : ℕ}
    (h : s * f ∈ chartCenter x r ^ m) : f ∈ chartCenter x r ^ m := by
  rw [mem_chartCenter_pow_iff_le_weightedOrder x hx hn r] at h ⊢
  rwa [map_mul, map_mul, weightedOrder_mul, weightedOrder_symm_algebraMap_eq_zero x hx hn r hs,
    zero_add] at h

/-- Symbolic equals ordinary power, `Pᵐ R_P ∩ R = Pᵐ` (`P` prime by `isPrime_chartCenter`). -/
theorem comap_map_localization_chartCenter_pow (m : ℕ) :
    haveI := isPrime_chartCenter x hx hn r
    ((chartCenter x r ^ m).map
        (algebraMap R (Localization.AtPrime (chartCenter x r)))).comap
      (algebraMap R (Localization.AtPrime (chartCenter x r))) = chartCenter x r ^ m := by
  have := isPrime_chartCenter x hx hn r
  refine le_antisymm (fun f hf => ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap, IsLocalization.mem_map_algebraMap_iff (chartCenter x r).primeCompl] at hf
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ := hf
  rw [← map_mul, IsLocalization.eq_iff_exists (chartCenter x r).primeCompl] at h
  obtain ⟨⟨t, ht⟩, ht'⟩ := h
  have hmem : t * s * f ∈ chartCenter x r ^ m := by
    have h1 : t * (f * s) = t * a := ht'
    rw [show t * s * f = t * (f * s) by ring, h1]
    exact Ideal.mul_mem_left _ _ ha
  refine mem_chartCenter_pow_of_mul_mem x hx hn r (fun hts => ?_) hmem
  rcases (Ideal.IsPrime.mem_or_mem inferInstance hts) with h | h
  · exact ht h
  · exact hs h

/-- `m ≤ ord_P(I) ⟺ I ≤ Pᵐ`, with `ord_P` the order along `P` (`Hironaka/Algebra/Local/Order.lean`,
`ordAlong`; Kollár's `ord_Z`, [Kol07, Definition 47]), computed in `R_P` (`P` prime by
`isPrime_chartCenter`). -/
theorem le_ordAlong_chartCenter_iff (I : Ideal R) (m : ℕ) :
    haveI := isPrime_chartCenter x hx hn r
    (m : ℕ∞) ≤ ordAlong (chartCenter x r) I ↔ I ≤ chartCenter x r ^ m := by
  have := isPrime_chartCenter x hx hn r
  rw [ordAlong, le_ord_iff, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
    Ideal.map_le_iff_le_comap, comap_map_localization_chartCenter_pow x hx hn r m]

end Transport

/-- `P = ⟨x₀, …, x_r⟩` is prime for a coordinate structure `c`: the instance form of
`isPrime_chartCenter` at `c.x`. -/
instance RegularCoords.isPrime_chartCenter {R : Type*} [CommRing R] [IsRegularLocalRing R]
    [Algebra ℚ R] {n : ℕ} (c : RegularCoords R n) (r : Fin n) : (chartCenter c.x r).IsPrime :=
  IsLocalRing.isPrime_chartCenter c.x c.span_x c.card r

end IsLocalRing
