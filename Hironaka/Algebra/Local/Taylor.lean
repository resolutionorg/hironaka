/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.FormalAut
public import Mathlib.RingTheory.MvPowerSeries.Derivative
import Hironaka.Algebra.Local.PowerSeries
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Taylor expansion and Krull's intersection theorem, in the form needed

Kollár's proof of [Kol07, Proposition 94] takes "the Taylor expansion
`f(x₁+b₁, …, xₙ+bₙ) = f + ∑ᵢ bᵢ ∂f/∂xᵢ + ½ ∑ᵢⱼ bᵢbⱼ ∂²f/∂xᵢ∂xⱼ + ⋯`" modulo `𝔪^{s+1}` and lets
`s → ∞` by Krull's intersection theorem (recalled in [Kol07, Definition 55]).  This file
provides what that proof needs (`Hironaka/Algebra/Local/Prop94.lean`):

* the iterated partial derivatives `∂^α = ∏ᵢ ∂ᵢ^{αᵢ}` on `MvPolynomial (Fin n) A` (`pderivPow`) and
  the exact multivariate Taylor formula for polynomials over a `ℚ`-algebra,
  `P(g + b) = ∑_α (1/α!) (∂^α P)(g) b^α`, by the monomial computation
  `∂^α X^β = β!/(β-α)! X^{β-α}` and the binomial theorem;
* truncation and substitution in `K⟦X⟧` and the Taylor formula modulo `𝔪^{s+1}` for power series,
  with its one-direction form (a shift of a single coordinate);
* Krull's intersection theorem in closed form, `I = ⋂ₛ (I + 𝔪^s)`, used also in
  `Hironaka/Algebra/Local/PowerSeriesEndomorphism.lean` and
  `Hironaka/Algebra/Local/CoordsOver.lean`.
-/

@[expose] public section

namespace IsLocalRing

open MvPolynomial

/-! ### Iterated partial derivatives of polynomials -/

section PolynomialTaylor

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The coordinate derivations of `MvPolynomial (Fin n) A` commute (the polynomial analogue of
`MvPowerSeries.pderiv_pderiv_comm`). -/
theorem pderiv_pderiv_comm_mvPolynomial (i j : Fin n) (P : MvPolynomial (Fin n) A) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [pderiv_monomial]
    by_cases hij : i = j
    · subst hij
      rfl
    · rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_of_ne hij,
        Finsupp.single_eq_of_ne (Ne.symm hij), tsub_zero, tsub_zero, tsub_right_comm]
      congr 1
      ring
  | add p q hp hq => simp only [map_add, hp, hq]

/-- `∂ᵢ` as an `A`-linear endomorphism of `MvPolynomial (Fin n) A`. -/
noncomputable abbrev pderivEnd (i : Fin n) : Module.End A (MvPolynomial (Fin n) A) :=
  (pderiv i : Derivation A (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A)).toLinearMap

theorem pderivEnd_apply (i : Fin n) (P : MvPolynomial (Fin n) A) : pderivEnd i P = pderiv i P :=
  rfl

theorem pderivEnd_commute (i j : Fin n) : Commute (pderivEnd (A := A) i) (pderivEnd j) :=
  LinearMap.ext fun P => pderiv_pderiv_comm_mvPolynomial i j P

theorem pderivEnd_pow_pairwise (α : Fin n →₀ ℕ) :
    ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Commute fun i => pderivEnd (A := A) i ^ α i) :=
  fun i _ j _ _ => (pderivEnd_commute i j).pow_pow _ _

/-- The iterated partial derivative `∂^α = ∏ᵢ ∂ᵢ^{αᵢ}` of a multi-index `α`, on polynomials (the
higher derivatives of the Taylor expansion in the proof of [Kol07, Proposition 94]). -/
noncomputable def pderivPow (α : Fin n →₀ ℕ) : Module.End A (MvPolynomial (Fin n) A) :=
  Finset.univ.noncommProd (fun i => pderivEnd (A := A) i ^ α i) (pderivEnd_pow_pairwise α)

theorem pderivPow_zero : pderivPow (A := A) (n := n) 0 = 1 :=
  (Finset.noncommProd_eq_pow_card _ _ _ 1 fun i _ => by simp).trans (one_pow _)

theorem pderivPow_add (α β : Fin n →₀ ℕ) :
    pderivPow (A := A) (α + β) = pderivPow α * pderivPow β := by
  have hc : ∀ f g : Fin n →₀ ℕ, ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      fun i j => Commute (pderivEnd (A := A) i ^ f i) (pderivEnd j ^ g j) :=
    fun _ _ i _ j _ _ => (pderivEnd_commute i j).pow_pow _ _
  exact (Finset.noncommProd_congr rfl (fun i _ => by simp [pow_add]) _).trans
    (Finset.noncommProd_mul_distrib (fun i => pderivEnd (A := A) i ^ α i)
      (fun i => pderivEnd i ^ β i) (hc α α) (hc β β) (hc β α))

theorem pderivPow_single (i : Fin n) (k : ℕ) :
    pderivPow (A := A) (Finsupp.single i k) = pderivEnd i ^ k := by
  classical
  refine (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ i) _
    (pderivEnd_pow_pairwise _)).symm.trans ?_
  refine (congrArg (· * _) ((Finset.noncommProd_eq_pow_card _ _ _ 1 fun j hj => by
    simp only [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj), pow_zero]).trans
      (one_pow _))).trans ?_
  simp

theorem pderivEnd_pow_monomial (i : Fin n) (k : ℕ) (β : Fin n →₀ ℕ) (c : A) :
    (pderivEnd (A := A) i ^ k) (monomial β c) =
      monomial (β - Finsupp.single i k) (c * ((β i).descFactorial k : A)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pderivEnd_apply, pderiv_monomial, Finsupp.tsub_apply,
      Finsupp.single_eq_same, tsub_tsub, ← Finsupp.single_add, Nat.descFactorial_succ]
    congr 1
    push_cast
    ring

/-- `∂^α X^β = (∏ᵢ βᵢ!/(βᵢ-αᵢ)!) X^{β-α}` (zero unless `α ≤ β`). -/
theorem pderivPow_monomial (α β : Fin n →₀ ℕ) (c : A) :
    pderivPow (A := A) α (monomial β c) =
      monomial (β - α) (c * ((∏ i, (β i).descFactorial (α i) : ℕ) : A)) := by
  classical
  induction α using Finsupp.induction with
  | zero => simp [pderivPow_zero]
  | single_add a b f ha _ ih =>
    rw [pderivPow_add, Module.End.mul_apply, ih, pderivPow_single, pderivEnd_pow_monomial]
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    congr 1
    · rw [tsub_tsub, add_comm]
    · rw [Finsupp.tsub_apply, hfa, Nat.sub_zero]
      have h1 : (∏ i, (β i).descFactorial ((Finsupp.single a b + f) i)) =
          (β a).descFactorial b * ∏ i ∈ Finset.univ.erase a, (β i).descFactorial (f i) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero]
        congr 1
        exact Finset.prod_congr rfl fun j hj => by
          simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
      have h2 : (∏ i, (β i).descFactorial (f i)) =
          ∏ i ∈ Finset.univ.erase a, (β i).descFactorial (f i) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), hfa,
          Nat.descFactorial_zero, one_mul]
      rw [h1, h2]
      push_cast
      ring

/-- The factorial `α! = ∏ᵢ αᵢ!` of a multi-index. -/
def multiFactorial (α : Fin n →₀ ℕ) : ℕ := ∏ i, (α i).factorial

theorem multiFactorial_ne_zero (α : Fin n →₀ ℕ) : multiFactorial α ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (α i)

variable {S : Type*} [CommRing S] [Algebra A S] [Algebra ℚ S]

/-- The Taylor formula for a monomial: `(g + b)^β = ∑_{α ≤ β} (1/α!) (∂^α X^β)(g) b^α`, the
binomial theorem in each variable. -/
theorem aeval_add_monomial (g b : Fin n → S) (β : Fin n →₀ ℕ) (c : A) :
    aeval (fun i => g i + b i) (monomial β c) =
      ∑ α ∈ Finset.Iic β,
        ((multiFactorial α : ℚ)⁻¹ • aeval g (pderivPow α (monomial β c))) * ∏ i, b i ^ α i := by
  classical
  have hL : aeval (fun i => g i + b i) (monomial β c) =
      ∑ γ ∈ Fintype.piFinset (fun i => Finset.range (β i + 1)),
        algebraMap A S c * ∏ i, (b i ^ γ i * g i ^ (β i - γ i) * ((β i).choose (γ i) : S)) := by
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), ← Finset.mul_sum]
    congr 1
    calc ∏ i, (g i + b i) ^ β i
        = ∏ i, ∑ k ∈ Finset.range (β i + 1), b i ^ k * g i ^ (β i - k) * ((β i).choose k : S) :=
          Finset.prod_congr rfl fun i _ => by rw [add_comm, add_pow]
      _ = _ := Finset.prod_univ_sum _ _
  rw [hL]
  have hR : ∀ α ∈ Finset.Iic β,
      ((multiFactorial α : ℚ)⁻¹ • aeval g (pderivPow α (monomial β c))) * ∏ i, b i ^ α i =
        algebraMap A S c * ∏ i, (b i ^ α i * g i ^ (β i - α i) * ((β i).choose (α i) : S)) := by
    intro α _
    rw [pderivPow_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    have hdesc : (∏ i, (β i).descFactorial (α i)) =
        multiFactorial α * ∏ i, (β i).choose (α i) := by
      rw [multiFactorial, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => Nat.descFactorial_eq_factorial_mul_choose _ _
    rw [hdesc, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Algebra.smul_def, map_mul,
      map_natCast, Nat.cast_mul, Nat.cast_prod]
    have hinv : algebraMap ℚ S ((multiFactorial α : ℚ)⁻¹) * (multiFactorial α : S) = 1 := by
      rw [← map_natCast (algebraMap ℚ S), ← map_mul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (multiFactorial_ne_zero α)), map_one]
    simp only [Finsupp.tsub_apply]
    calc algebraMap ℚ S ((multiFactorial α : ℚ)⁻¹) *
          (algebraMap A S c * ((multiFactorial α : S) * ∏ i, ((β i).choose (α i) : S)) *
            ∏ i, g i ^ (β i - α i)) * ∏ i, b i ^ α i
        = (algebraMap ℚ S ((multiFactorial α : ℚ)⁻¹) * (multiFactorial α : S)) *
          (algebraMap A S c * ((∏ i, b i ^ α i) * (∏ i, g i ^ (β i - α i)) *
            ∏ i, ((β i).choose (α i) : S))) := by ring
      _ = _ := by rw [hinv, one_mul]
  rw [Finset.sum_congr rfl hR]
  refine Finset.sum_nbij' (fun γ : Fin n → ℕ => Finsupp.equivFunOnFinite.symm γ)
    (fun α : Fin n →₀ ℕ => (α : Fin n → ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    rw [Fintype.mem_piFinset] at hγ
    rw [Finset.mem_Iic]
    intro i
    have := Finset.mem_range.mp (hγ i)
    simpa using Nat.lt_succ_iff.mp this
  · intro α hα
    rw [Finset.mem_Iic] at hα
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hα i)
  · intro γ _
    simp
  · intro α _
    simp
  · intro γ _
    simp

/-- The multivariate Taylor formula (Kollár's "take the Taylor expansion" in the proof of
[Kol07, Proposition 94]; Włodarczyk's "the Taylor formula for `n` unknowns" in the proof of
[Wlo05, Lemma 2.9.6]): for a polynomial `P` over a `ℚ`-algebra and `g, b` in a `ℚ`-algebra `S`,
`P(g + b) = ∑_α (1/α!) (∂^α P)(g) b^α`, the sum over the multi-indices `α ≤ d` for any bound `d`
on the exponents of `P`. -/
theorem taylor_aeval_add (P : MvPolynomial (Fin n) A) (g b : Fin n → S) {d : Fin n →₀ ℕ}
    (hd : ∀ β ∈ P.support, β ≤ d) :
    aeval (fun i => g i + b i) P =
      ∑ α ∈ Finset.Iic d,
        ((multiFactorial α : ℚ)⁻¹ • aeval g (pderivPow α P)) * ∏ i, b i ^ α i := by
  classical
  have hP : ∀ α, aeval g (pderivPow α P) =
      ∑ β ∈ P.support, aeval g (pderivPow α (monomial β (P.coeff β))) := fun α => by
    conv_lhs => rw [P.as_sum]
    rw [map_sum, map_sum]
  simp_rw [hP, Finset.smul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => rw [P.as_sum, map_sum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [aeval_add_monomial]
  refine Finset.sum_subset (Finset.Iic_subset_Iic.mpr (hd β hβ)) fun α _ hαβ => ?_
  rw [Finset.mem_Iic] at hαβ
  obtain ⟨i, hi⟩ : ∃ i, β i < α i := by
    by_contra h
    push Not at h
    exact hαβ fun i => h i
  rw [pderivPow_monomial]
  have : (∏ j, (β j).descFactorial (α j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (Nat.descFactorial_eq_zero_iff_lt.mpr hi)
  simp [this]

/-- The Taylor formula in Kollár's form: `P(X + b) = ∑_α (1/α!) (∂^α P) b^α` for `P ∈ A[X]`,
`b ∈ Aⁿ`. -/
theorem taylor_eq_sum [Algebra ℚ A] (P : MvPolynomial (Fin n) A) (b : Fin n → A) {d : Fin n →₀ ℕ}
    (hd : ∀ β ∈ P.support, β ≤ d) :
    aeval (fun i => X i + C (b i)) P =
      ∑ α ∈ Finset.Iic d, ((multiFactorial α : ℚ)⁻¹ • pderivPow α P) * C (∏ i, b i ^ α i) := by
  rw [taylor_aeval_add P X (fun i => C (b i)) hd]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [aeval_X_left_apply, map_prod]
  simp only [map_pow]

end PolynomialTaylor

/-! ### Iterated partial derivatives and `𝔪`-adic estimates in `K⟦X⟧` -/

section PowerSeriesTaylor

open MvPowerSeries IsLocalRing

variable {K : Type*} [Field K] {n : ℕ}

/-- `∂ᵢ = pderiv K i` as a `K`-linear endomorphism of `K⟦X⟧`. -/
noncomputable abbrev pderivEnd' (i : Fin n) : Module.End K (MvPowerSeries (Fin n) K) :=
  (MvPowerSeries.pderiv (R := K) i).toLinearMap

theorem pderivEnd'_apply (i : Fin n) (f : MvPowerSeries (Fin n) K) :
    pderivEnd' i f = MvPowerSeries.pderiv (R := K) i f :=
  rfl

theorem pderivEnd'_commute (i j : Fin n) :
    Commute (pderivEnd' (K := K) (n := n) i) (pderivEnd' j) :=
  LinearMap.ext fun f => MvPowerSeries.pderiv_pderiv_comm i j f

theorem pderivEnd'_pow_pairwise (α : Fin n →₀ ℕ) :
    ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Commute fun i => pderivEnd' (K := K) i ^ α i) :=
  fun i _ j _ _ => (pderivEnd'_commute i j).pow_pow _ _

/-- The iterated partial derivative `∂^α` on `K⟦X⟧`. -/
noncomputable def pderivPowSeries (α : Fin n →₀ ℕ) : Module.End K (MvPowerSeries (Fin n) K) :=
  Finset.univ.noncommProd (fun i => pderivEnd' (K := K) i ^ α i) (pderivEnd'_pow_pairwise α)

theorem pderivPowSeries_zero : pderivPowSeries (K := K) (n := n) 0 = 1 :=
  (Finset.noncommProd_eq_pow_card _ _ _ 1 fun i _ => by simp).trans (one_pow _)

theorem pderivPowSeries_add (α β : Fin n →₀ ℕ) :
    pderivPowSeries (K := K) (α + β) = pderivPowSeries α * pderivPowSeries β := by
  have hc : ∀ f g : Fin n →₀ ℕ, ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      fun i j => Commute (pderivEnd' (K := K) i ^ f i) (pderivEnd' j ^ g j) :=
    fun _ _ i _ j _ _ => (pderivEnd'_commute i j).pow_pow _ _
  exact (Finset.noncommProd_congr rfl (fun i _ => by simp [pow_add]) _).trans
    (Finset.noncommProd_mul_distrib (fun i => pderivEnd' (K := K) i ^ α i)
      (fun i => pderivEnd' i ^ β i) (hc α α) (hc β β) (hc β α))

theorem pderivPowSeries_single (i : Fin n) (k : ℕ) :
    pderivPowSeries (K := K) (Finsupp.single i k) = pderivEnd' i ^ k := by
  classical
  refine (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ i) _
    (pderivEnd'_pow_pairwise _)).symm.trans ?_
  refine (congrArg (· * _) ((Finset.noncommProd_eq_pow_card _ _ _ 1 fun j hj => by
    simp only [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj), pow_zero]).trans
      (one_pow _))).trans ?_
  simp

theorem pderivEnd'_pow_coe (i : Fin n) (k : ℕ) (P : MvPolynomial (Fin n) K) :
    (pderivEnd' i ^ k) (P : MvPowerSeries (Fin n) K) =
      ((pderivEnd (A := K) i ^ k) P : MvPolynomial (Fin n) K) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact MvPowerSeries.pderiv_coe _

/-- `∂^α` on `K⟦X⟧` restricts to `∂^α` on polynomials. -/
theorem pderivPowSeries_coe (α : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) K) :
    pderivPowSeries α (P : MvPowerSeries (Fin n) K) =
      (pderivPow (A := K) α P : MvPolynomial (Fin n) K) := by
  induction α using Finsupp.induction with
  | zero => simp [pderivPowSeries_zero, pderivPow_zero]
  | single_add a b f _ _ ih =>
    rw [pderivPowSeries_add, pderivPow_add, Module.End.mul_apply, Module.End.mul_apply, ih,
      pderivPowSeries_single, pderivPow_single, pderivEnd'_pow_coe]

theorem mem_maximalIdeal_pow_iff_le_order (k : ℕ) (f : MvPowerSeries (Fin n) K) :
    f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k ↔ (k : ℕ∞) ≤ f.order := by
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X]
  exact MvPowerSeries.mem_span_range_X_pow_iff_le_order k f

theorem constantCoeff_eq_zero_of_mem_maximalIdeal {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K)) : constantCoeff f = 0 := by
  have h1 := (mem_maximalIdeal_pow_iff_le_order 1 f).mp (by simpa using hf)
  have h0 : (0 : ℕ∞) < f.order := lt_of_lt_of_le zero_lt_one h1
  have := MvPowerSeries.coeff_of_lt_order (f := f) (d := 0) (by simpa using h0)
  simpa using this

/-- A coordinate partial lowers the `𝔪`-adic order by at most one (Kollár's step
`∂^α f ∈ 𝔪^{s+1-|α|}` in the proof of [Kol07, Proposition 94]; the `K⟦X⟧` form of
`RegularCoords.D_maximalIdeal_pow`). -/
theorem pderiv_mem_maximalIdeal_pow {k : ℕ} {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ (k + 1)) (i : Fin n) :
    MvPowerSeries.pderiv (R := K) i f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k := by
  classical
  rw [mem_maximalIdeal_pow_iff_le_order] at hf ⊢
  refine MvPowerSeries.le_order fun d hd => ?_
  have hdeg : ((d + Finsupp.single i 1).degree : ℕ∞) < f.order := by
    refine lt_of_lt_of_le ?_ hf
    rw [map_add, Finsupp.degree_single]
    exact_mod_cast Nat.add_lt_add_right (by exact_mod_cast hd) 1
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_of_lt_order hdeg]
  simp

theorem pderivEnd'_pow_mem_maximalIdeal_pow {k : ℕ} {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k) (i : Fin n) (b : ℕ) :
    (pderivEnd' i ^ b) f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ (k - b) := by
  induction b with
  | zero => simpa using hf
  | succ b ih =>
    rw [pow_succ', Module.End.mul_apply, pderivEnd'_apply]
    rcases Nat.eq_zero_or_pos (k - b) with h0 | hpos
    · rw [show k - (b + 1) = 0 by omega, pow_zero]
      simp
    · obtain ⟨m, hm⟩ : ∃ m, k - b = m + 1 := ⟨k - b - 1, by omega⟩
      rw [hm] at ih
      rw [show k - (b + 1) = m by omega]
      exact pderiv_mem_maximalIdeal_pow ih i

/-- `∂^α` lowers the `𝔪`-adic order by at most `|α|`. -/
theorem pderivPowSeries_mem_maximalIdeal_pow {k : ℕ} {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k) (α : Fin n →₀ ℕ) :
    pderivPowSeries α f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ (k - α.degree) := by
  induction α using Finsupp.induction generalizing k with
  | zero => simpa [pderivPowSeries_zero] using hf
  | single_add a b g _ _ ih =>
    rw [pderivPowSeries_add, Module.End.mul_apply, pderivPowSeries_single, map_add,
      Finsupp.degree_single, ← Nat.sub_sub, Nat.sub_right_comm]
    exact pderivEnd'_pow_mem_maximalIdeal_pow (ih hf) a b

/-- `b^α ∈ 𝔪^{|α|}` for `bᵢ ∈ 𝔪`. -/
theorem prod_pow_mem_maximalIdeal_pow {b : Fin n → MvPowerSeries (Fin n) K}
    (hb : ∀ i, b i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) (α : Fin n →₀ ℕ) :
    ∏ i, b i ^ α i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ α.degree := by
  rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hb i) _

/-- `f ≡ truncTotal (s+1) f (mod 𝔪^{s+1})`. -/
theorem sub_truncTotal_mem (f : MvPowerSeries (Fin n) K) (s : ℕ) :
    f - (truncTotal (s + 1) f : MvPolynomial (Fin n) K) ∈
      maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) := by
  rw [mem_maximalIdeal_pow_iff_le_order]
  refine MvPowerSeries.le_order fun d hd => ?_
  have hc : (truncTotal (s + 1) f).coeff d = MvPowerSeries.coeff d f :=
    coeff_truncTotal f (by exact_mod_cast hd)
  rw [map_sub, MvPolynomial.coeff_coe, hc, sub_self]

/-- `Xᵢ ↦ Xᵢ + bᵢ` is a substitution when `bᵢ ∈ 𝔪`. -/
theorem hasSubst_add {b : Fin n → MvPowerSeries (Fin n) K}
    (hb : ∀ i, b i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    HasSubst fun i => (X i : MvPowerSeries (Fin n) K) + b i :=
  hasSubst_of_constantCoeff_zero fun i => by
    rw [map_add, MvPowerSeries.constantCoeff_X, zero_add,
      constantCoeff_eq_zero_of_mem_maximalIdeal (hb i)]

/-- The substitution `Xᵢ ↦ Xᵢ + bᵢ` maps `𝔪^{s+1}` into `𝔪^{s+1}`. -/
theorem substAlgHom_add_mem_maximalIdeal_pow {b : Fin n → MvPowerSeries (Fin n) K}
    (hb : ∀ i, b i ∈ maximalIdeal (MvPowerSeries (Fin n) K)) {k : ℕ}
    {f : MvPowerSeries (Fin n) K} (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k) :
    substAlgHom (R := K) (hasSubst_add hb) f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ k :=
  substAlgHom_mem_maximalIdeal_pow (hasSubst_add hb) hf

/-- The multi-indices of total degree `≤ s` (the index set of Kollár's Taylor sum modulo
`𝔪^{s+1}`). -/
noncomputable def degreeLE (n s : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Fin n => s)).filter fun α => α.degree ≤ s

theorem mem_degreeLE {s : ℕ} {α : Fin n →₀ ℕ} : α ∈ degreeLE n s ↔ α.degree ≤ s := by
  rw [degreeLE, Finset.mem_filter, Finset.mem_Iic]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  simpa using (Finsupp.le_degree i α).trans h

theorem aeval_X_eq_coe (Q : MvPolynomial (Fin n) K) :
    aeval (X : Fin n → MvPowerSeries (Fin n) K) Q = (Q : MvPowerSeries (Fin n) K) := by
  have : aeval (X : Fin n → MvPowerSeries (Fin n) K) =
      MvPolynomial.coeToMvPowerSeries.algHom (σ := Fin n) (R := K) K :=
    MvPolynomial.algHom_ext fun i => by simp
  rw [this, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
    MvPowerSeries.map_id, RingHom.id_apply]

theorem rat_smul_mem_maximalIdeal [CharZero K] (q : ℚ) {b : MvPowerSeries (Fin n) K}
    (hb : b ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    q • b ∈ maximalIdeal (MvPowerSeries (Fin n) K) := by
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ hb

/-- **The Taylor formula modulo `𝔪^{s+1}`** (the proof of [Kol07, Proposition 94], in truncated
form): for `bᵢ ∈ 𝔪`, `f(X + b) ≡ ∑_{|α| ≤ s} (1/α!) (∂^α f) b^α (mod 𝔪^{s+1})`. -/
theorem substAlgHom_add_sub_taylor_mem [CharZero K] (f : MvPowerSeries (Fin n) K)
    {b : Fin n → MvPowerSeries (Fin n) K} (hb : ∀ i, b i ∈ maximalIdeal (MvPowerSeries (Fin n) K))
    (s : ℕ) :
    substAlgHom (R := K) (hasSubst_add hb) f -
      ∑ α ∈ degreeLE n s, ((multiFactorial α : ℚ)⁻¹ • pderivPowSeries α f) * ∏ i, b i ^ α i ∈
        maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : Fin n →₀ ℕ, d = Finsupp.equivFunOnFinite.symm fun _ : Fin n => s :=
    ⟨_, rfl⟩
  set P : MvPolynomial (Fin n) K := truncTotal (s + 1) f with hP
  have hrmem : f - (P : MvPowerSeries (Fin n) K) ∈
      maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) :=
    sub_truncTotal_mem f s
  have hbound : ∀ β ∈ P.support, β ≤ d := by
    intro β hβ i
    have hdeg : β.degree < s + 1 := by
      by_contra h
      push Not at h
      exact (MvPolynomial.mem_support_iff.mp hβ) (coeff_truncTotal_eq_zero f h)
    rw [hd]
    simpa using (Finsupp.le_degree i β).trans (Nat.lt_succ_iff.mp hdeg)
  have hsub : substAlgHom (R := K) (hasSubst_add hb) (P : MvPowerSeries (Fin n) K) =
      aeval (fun i => (X i : MvPowerSeries (Fin n) K) + b i) P := by
    rw [coe_substAlgHom, subst_coe]
  have hTP : aeval (fun i => (X i : MvPowerSeries (Fin n) K) + b i) P =
      ∑ α ∈ Finset.Iic d, ((multiFactorial α : ℚ)⁻¹ •
        pderivPowSeries α (P : MvPowerSeries (Fin n) K)) * ∏ i, b i ^ α i := by
    rw [taylor_aeval_add P (X : Fin n → MvPowerSeries (Fin n) K) b hbound]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [aeval_X_eq_coe, pderivPowSeries_coe]
  have hdeg_sub : degreeLE n s ⊆ Finset.Iic d := by
    rw [degreeLE, hd]
    exact Finset.filter_subset _ _
  -- the terms of high degree, and the terms of the remainder, lie in `𝔪^{s+1}`
  have hA : ∀ (g : MvPowerSeries (Fin n) K) (α : Fin n →₀ ℕ), s < α.degree →
      ((multiFactorial α : ℚ)⁻¹ • pderivPowSeries α g) * ∏ i, b i ^ α i ∈
        maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) := fun g α hα =>
    Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hα (prod_pow_mem_maximalIdeal_pow hb α))
  have hB : ∀ α : Fin n →₀ ℕ, α.degree ≤ s →
      ((multiFactorial α : ℚ)⁻¹ • pderivPowSeries α (f - (P : MvPowerSeries (Fin n) K))) *
        ∏ i, b i ^ α i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) := by
    intro α hα
    rw [Algebra.smul_def, mul_assoc, show s + 1 = (s + 1 - α.degree) + α.degree by omega, pow_add]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (pderivPowSeries_mem_maximalIdeal_pow hrmem α)
      (prod_pow_mem_maximalIdeal_pow hb α))
  -- assemble
  have hfr : f = (P : MvPowerSeries (Fin n) K) + (f - (P : MvPowerSeries (Fin n) K)) :=
    (add_sub_cancel _ _).symm
  have hTf : ∀ α : Fin n →₀ ℕ,
      ((multiFactorial α : ℚ)⁻¹ • pderivPowSeries α f) * ∏ i, b i ^ α i =
        ((multiFactorial α : ℚ)⁻¹ • pderivPowSeries α (P : MvPowerSeries (Fin n) K)) *
          ∏ i, b i ^ α i +
        ((multiFactorial α : ℚ)⁻¹ • pderivPowSeries α (f - (P : MvPowerSeries (Fin n) K))) *
          ∏ i, b i ^ α i := fun α => by
    conv_lhs => rw [hfr]
    rw [map_add, smul_add, add_mul]
  have hsplit : substAlgHom (R := K) (hasSubst_add hb) f =
      aeval (fun i => (X i : MvPowerSeries (Fin n) K) + b i) P +
        substAlgHom (R := K) (hasSubst_add hb) (f - (P : MvPowerSeries (Fin n) K)) := by
    conv_lhs => rw [hfr]
    rw [map_add, hsub]
  rw [hsplit, hTP, ← Finset.sum_sdiff hdeg_sub, Finset.sum_congr rfl fun α _ => hTf α,
    Finset.sum_add_distrib]
  have hrew : ∀ S1 S2 S3 S4 : MvPowerSeries (Fin n) K, S1 + S2 + S4 - (S2 + S3) = S1 + S4 - S3 :=
    fun S1 S2 S3 S4 => by ring
  rw [hrew]
  refine Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.sum_mem _ fun α hα => hA _ α ?_)
    (substAlgHom_add_mem_maximalIdeal_pow hb hrmem)) (Ideal.sum_mem _ fun α hα => hB α ?_)
  · rw [Finset.mem_sdiff, mem_degreeLE] at hα
    exact not_le.mp hα.2
  · exact mem_degreeLE.mp hα

theorem multiFactorial_single (i : Fin n) (k : ℕ) :
    multiFactorial (Finsupp.single i k) = k.factorial := by
  classical
  unfold multiFactorial
  rw [Finset.prod_eq_single i (fun j _ hj => by
    rw [Finsupp.single_eq_of_ne hj, Nat.factorial_zero]) (by simp)]
  rw [Finsupp.single_eq_same]

/-- **The one-direction Taylor formula** (the converse direction of the proof of
[Kol07, Proposition 94]): `f(X₁ + λb, X₂, …) ≡ ∑_{j ≤ s} λ^j (b^j/j!) ∂₁^j f (mod 𝔪^{s+1})` for
`b ∈ 𝔪`, `λ ∈ ℚ`, along any coordinate `i`. -/
theorem substAlgHom_shift_sub_taylor_mem [CharZero K] (f : MvPowerSeries (Fin n) K) (i : Fin n)
    {b : MvPowerSeries (Fin n) K} (hb : b ∈ maximalIdeal (MvPowerSeries (Fin n) K)) (q : ℚ)
    (s : ℕ) :
    substAlgHom (R := K) (hasSubst_shiftSubst i
        (constantCoeff_eq_zero_of_mem_maximalIdeal (rat_smul_mem_maximalIdeal q hb))) f -
      ∑ j ∈ Finset.range (s + 1),
        q ^ j • (((j.factorial : ℚ)⁻¹ • (pderivEnd' i ^ j) f) * b ^ j) ∈
        maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) := by
  classical
  obtain ⟨b', hb'⟩ : ∃ b' : Fin n → MvPowerSeries (Fin n) K, b' = Pi.single i (q • b) := ⟨_, rfl⟩
  have hb'mem : ∀ j, b' j ∈ maximalIdeal (MvPowerSeries (Fin n) K) := fun j => by
    rw [hb']
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same]
      exact rat_smul_mem_maximalIdeal q hb
    · rw [Pi.single_eq_of_ne hj]
      exact zero_mem _
  have hfun : shiftSubst i (q • b) = fun j => (X j : MvPowerSeries (Fin n) K) + b' j := by
    funext j
    rw [hb']
    by_cases hj : j = i
    · subst hj
      rw [shiftSubst_self, Pi.single_eq_same]
    · rw [shiftSubst_of_ne hj, Pi.single_eq_of_ne hj, add_zero]
  have hsubst : substAlgHom (R := K) (hasSubst_shiftSubst i
      (constantCoeff_eq_zero_of_mem_maximalIdeal (rat_smul_mem_maximalIdeal q hb))) f =
      substAlgHom (R := K) (hasSubst_add hb'mem) f := by
    rw [coe_substAlgHom, coe_substAlgHom, hfun]
  have hd := substAlgHom_add_sub_taylor_mem f hb'mem s
  -- the Taylor sum over `degreeLE n s` reduces to the multi-indices `single i j`, `j ≤ s`
  have hsum : ∑ α ∈ degreeLE n s,
      ((multiFactorial α : ℚ)⁻¹ • pderivPowSeries α f) * ∏ j, b' j ^ α j =
        ∑ j ∈ Finset.range (s + 1),
          q ^ j • (((j.factorial : ℚ)⁻¹ • (pderivEnd' i ^ j) f) * b ^ j) := by
    have himage : (Finset.range (s + 1)).image (fun j => Finsupp.single i j) ⊆ degreeLE n s := by
      intro α hα
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hα
      rw [mem_degreeLE, Finsupp.degree_single]
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← Finset.sum_subset himage,
      Finset.sum_image fun _ _ _ _ h => Finsupp.single_injective i h]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [multiFactorial_single, pderivPowSeries_single,
        Finset.prod_eq_single i (fun l _ hl => by
          rw [hb', Pi.single_eq_of_ne hl, Finsupp.single_eq_of_ne hl, pow_zero]) (by simp),
        hb', Pi.single_eq_same, Finsupp.single_eq_same, smul_pow, mul_smul_comm]
    · intro α hαs hα
      have hex : ∃ l, l ≠ i ∧ α l ≠ 0 := by
        by_contra h
        push Not at h
        refine hα (Finset.mem_image.mpr ⟨α i, ?_, ?_⟩)
        · rw [Finset.mem_range]
          exact Nat.lt_succ_of_le ((Finsupp.le_degree i α).trans (mem_degreeLE.mp hαs))
        · ext l
          by_cases hl : l = i
          · subst hl
            simp
          · rw [Finsupp.single_eq_of_ne hl, h l hl]
      obtain ⟨l, hl, hαl⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ l)
        (by rw [hb', Pi.single_eq_of_ne hl, zero_pow hαl]), mul_zero]
  rw [hsubst, ← hsum]
  exact hd

end PowerSeriesTaylor

/-! ### Krull's intersection theorem in closed form -/

section Krull

open IsLocalRing

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Krull's intersection theorem in the form `I = ⋂ₛ (I + 𝔪^s)` recalled in
[Kol07, Definition 55] and used ("letting `s` go to infinity") in the proof of
[Kol07, Proposition 94]: in a Noetherian local ring, `f ∈ I + 𝔪^s` for all `s` implies `f ∈ I`. -/
theorem mem_of_forall_mem_sup_pow {I : Ideal R} {f : R}
    (h : ∀ s : ℕ, f ∈ I ⊔ maximalIdeal R ^ s) : f ∈ I := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ I) (maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hmem : (Ideal.Quotient.mk I f) ∈
      ⨅ s : ℕ, maximalIdeal R ^ s • (⊤ : Submodule R (R ⧸ I)) := by
    refine Submodule.mem_iInf _ |>.mpr fun s => ?_
    obtain ⟨a, ha, g, hg, rfl⟩ := Submodule.mem_sup.mp (h s)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    have h1 : g • (1 : R ⧸ I) = Ideal.Quotient.mk I g := by
      rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
    rw [← h1]
    exact Submodule.smul_mem_smul hg Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

/-- Krull's intersection theorem in closed form: `I = ⋂ₛ (I + 𝔪^s)`. -/
theorem iInf_sup_pow_eq (I : Ideal R) : ⨅ s : ℕ, (I ⊔ maximalIdeal R ^ s) = I :=
  le_antisymm (fun _ hf => mem_of_forall_mem_sup_pow (Ideal.mem_iInf.mp hf))
    (le_iInf fun _ => le_sup_left)

end Krull

end IsLocalRing
