/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Hironaka.Analytic.Weierstrass.AdicComplete
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Division of a power series without constant term by the coordinates

A series `c` with `c(0) = 0` is `∑_i X_i · c_i`, where `c_i` collects the monomials of `c` whose
**leading index** (the first variable that occurs) is `i`, divided by `X_i` (`divPart i c`,
`sum_X_mul_divPart`): Hadamard's lemma at the level of power series. The parts are as convergent
as `c` (`‖c_i‖_ρ · ρ_i ≤ ‖c‖_ρ`, `convNorm_divPart_mul_le`, so `Conv K n` is stable,
`divPart_mem_conv`), and they lose exactly one order: `c ∈ 𝔪^(k+1)` gives `c_i ∈ 𝔪^k`
(`divPart_mem_maximalIdeal_pow`). The truncation of a series below a total degree (`truncDeg`) is
a polynomial, hence convergent, and congruent to the series modulo `𝔪^k`.

Not in the sources as such. This is the step that makes the Taylor homomorphism of a germ (the
injective `T_a : 𝒪_{M,a} → F_a[[X]]` of [BM97, (0.3)]) reflect the powers of the maximal ideal,
and gives `𝔪_a = (x_1 − a_1, …, x_n − a_n)` for the germs at a point of a manifold
(`Hironaka/Manifold/Germ`).
-/

@[expose] public noncomputable section

open MvPowerSeries Finsupp
open scoped ENNReal NNReal

namespace Analytic

variable {K : Type*} [RCLike K] {n : ℕ}

local notation "𝔪" => IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K)

/-- `i` is the **leading index** of the exponent `d`: the first variable occurring in `X^d`. -/
def IsLeadIndex (i : Fin n) (d : Fin n →₀ ℕ) : Prop := d i ≠ 0 ∧ ∀ j < i, d j = 0

theorem IsLeadIndex.unique {i j : Fin n} {d : Fin n →₀ ℕ} (hi : IsLeadIndex i d)
    (hj : IsLeadIndex j d) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (hj.2 i h) hi.1
  · exact h
  · exact absurd (hi.2 j h) hj.1

theorem exists_isLeadIndex {d : Fin n →₀ ℕ} (hd : d ≠ 0) : ∃ i, IsLeadIndex i d := by
  have hne : d.support.Nonempty := Finsupp.support_nonempty_iff.mpr hd
  refine ⟨d.support.min' hne, Finsupp.mem_support_iff.mp (d.support.min'_mem hne), fun j hj => ?_⟩
  by_contra h
  exact absurd (d.support.min'_le j (Finsupp.mem_support_iff.mpr h)) (not_le.mpr hj)

open Classical in
/-- The **`i`-th part** of `c`: the monomials of `c` with leading index `i`, divided by `X_i`;
`coeff e (divPart i c) = coeff (e + e_i) c` when `i` leads `e + e_i`, `0` otherwise. -/
def divPart (i : Fin n) (c : MvPowerSeries (Fin n) K) : MvPowerSeries (Fin n) K :=
  fun e => if IsLeadIndex i (e + single i 1) then coeff (e + single i 1) c else 0

open Classical in
theorem coeff_divPart (i : Fin n) (c : MvPowerSeries (Fin n) K) (e : Fin n →₀ ℕ) :
    coeff e (divPart i c) =
      if IsLeadIndex i (e + single i 1) then coeff (e + single i 1) c else 0 := rfl

/-- The coefficients of `X_i · φ`. -/
theorem coeff_X_mul' (i : Fin n) (φ : MvPowerSeries (Fin n) K) (d : Fin n →₀ ℕ) :
    coeff d (X i * φ) = if single i 1 ≤ d then coeff (d - single i 1) φ else 0 := by
  classical
  rw [← pow_one (X i), X_pow_eq, coeff_monomial_mul, one_mul]

/-- Hadamard's lemma at the level of series: `c = ∑_i X_i · divPart i c` when `c(0) = 0`. -/
theorem sum_X_mul_divPart {c : MvPowerSeries (Fin n) K} (hc : constantCoeff c = 0) :
    ∑ i, X i * divPart i c = c := by
  classical
  ext d
  rw [map_sum]
  simp only [coeff_X_mul']
  by_cases hd : d = 0
  · subst hd
    rw [← coeff_zero_eq_constantCoeff_apply] at hc
    rw [hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    intro h
    have := h i
    simp at this
  · obtain ⟨i₀, hi₀⟩ := exists_isLeadIndex hd
    rw [Finset.sum_eq_single i₀]
    · have hle : single i₀ 1 ≤ d := single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi₀.1)
      rw [ite_eq_left hle, coeff_divPart, tsub_add_cancel_of_le hle, ite_eq_left hi₀]
    · intro i _ hi
      split_ifs with hle
      · rw [coeff_divPart, tsub_add_cancel_of_le hle, ite_eq_right]
        exact fun h => hi (h.unique hi₀)
      · rfl
    · intro h
      exact absurd (Finset.mem_univ i₀) h

/-- The parts lose one order: `c ∈ 𝔪^(k+1)` gives `divPart i c ∈ 𝔪^k`. -/
theorem divPart_mem_maximalIdeal_pow {c : MvPowerSeries (Fin n) K} {k : ℕ} (hc : c ∈ 𝔪 ^ (k + 1))
    (i : Fin n) : divPart i c ∈ 𝔪 ^ k := by
  classical
  rw [mem_maximalIdeal_pow_iff] at hc ⊢
  intro e he
  rw [coeff_divPart]
  split_ifs
  · refine hc _ ?_
    rw [map_add, degree_single]
    omega
  · rfl

/-- `‖divPart i c‖_ρ · ρ_i ≤ ‖c‖_ρ`. -/
theorem convNorm_divPart_mul_le (ρ : Fin n → ℝ≥0) (i : Fin n) (c : MvPowerSeries (Fin n) K) :
    ConvNorm ρ (divPart i c) * (ρ i : ℝ≥0∞) ≤ ConvNorm ρ c := by
  classical
  unfold ConvNorm
  rw [← ENNReal.tsum_mul_right]
  calc ∑' e : Fin n →₀ ℕ, ‖coeff e (divPart i c)‖ₑ * (monomialEval ρ e : ℝ≥0∞) * (ρ i : ℝ≥0∞)
      ≤ ∑' e : Fin n →₀ ℕ,
          ‖coeff (e + single i 1) c‖ₑ * (monomialEval ρ (e + single i 1) : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun e => ?_
        rw [monomialEval_add, monomialEval_single_pow, pow_one, ENNReal.coe_mul, ← mul_assoc,
          coeff_divPart]
        split_ifs
        · exact le_rfl
        · simp
    _ ≤ ∑' d : Fin n →₀ ℕ, ‖coeff d c‖ₑ * (monomialEval ρ d : ℝ≥0∞) :=
        ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective (single i 1))
          (fun d => ‖coeff d c‖ₑ * (monomialEval ρ d : ℝ≥0∞))

/-- The parts of a convergent series are convergent. -/
theorem divPart_mem_conv {c : MvPowerSeries (Fin n) K} (hc : c ∈ Conv K n) (i : Fin n) :
    divPart i c ∈ Conv K n := by
  obtain ⟨ρ, hρ⟩ := hc
  refine ⟨ρ, fun h => hρ ?_⟩
  have h1 := convNorm_divPart_mul_le ρ i c
  rw [h, ENNReal.top_mul (ENNReal.coe_ne_zero.mpr (ρ.2 i).ne')] at h1
  exact top_le_iff.mp h1

/-! ## Constants are convergent (monomials and coordinates: `monomial_mem_conv`, `X_mem_conv` in
`Hironaka/Analytic/Weierstrass/Normalize.lean`) -/

theorem C_mem_conv (a : K) : (C a : MvPowerSeries (Fin n) K) ∈ Conv K n := by
  rw [← congrFun monomial_zero_eq_C a]
  exact monomial_mem_conv _ _

/-! ## Truncation below a total degree -/

/-- The exponents of total degree `< k`. -/
def degreeBelow (n k : ℕ) : Finset (Fin n →₀ ℕ) := (Finset.range k).biUnion (degreeSet n)

theorem mem_degreeBelow {k : ℕ} {d : Fin n →₀ ℕ} : d ∈ degreeBelow n k ↔ d.degree < k := by
  simp only [degreeBelow, Finset.mem_biUnion, Finset.mem_range, mem_degreeSet]
  exact ⟨fun ⟨j, hj, hd⟩ => hd ▸ hj, fun h => ⟨_, h, rfl⟩⟩

/-- The truncation of `c` below total degree `k`, a polynomial. -/
def truncDeg (k : ℕ) (c : MvPowerSeries (Fin n) K) : MvPowerSeries (Fin n) K :=
  ∑ d ∈ degreeBelow n k, monomial d (coeff d c)

theorem coeff_truncDeg (k : ℕ) (c : MvPowerSeries (Fin n) K) (d : Fin n →₀ ℕ) :
    coeff d (truncDeg k c) = if d.degree < k then coeff d c else 0 := by
  classical
  unfold truncDeg
  rw [map_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq, mem_degreeBelow]

theorem truncDeg_mem_conv (k : ℕ) (c : MvPowerSeries (Fin n) K) : truncDeg k c ∈ Conv K n :=
  Subalgebra.sum_mem _ fun d _ => monomial_mem_conv d (coeff d c)

/-- `c ≡ truncDeg k c` modulo `𝔪^k`. -/
theorem sub_truncDeg_mem_maximalIdeal_pow (k : ℕ) (c : MvPowerSeries (Fin n) K) :
    c - truncDeg k c ∈ 𝔪 ^ k := by
  rw [mem_maximalIdeal_pow_iff]
  intro d hd
  rw [map_sub, coeff_truncDeg, ite_eq_left hd, sub_self]

end Analytic
