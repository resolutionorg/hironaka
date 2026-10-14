/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Radius
public import Mathlib.Topology.Order.Real
public import Hironaka.Analytic.Weierstrass.Exponents
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Field-free lemmas of the germ theory

Lemmas about exponents and radius vectors that do not depend on the coefficient field: the weight
of a monomial under a shift of one exponent; the degree of an exponent after removing one
coordinate; the identification `ℕ ≃ (Fin 1 →₀ ℕ)` of one-variable exponents and the regrouping
of sums over exponents by degree; the coordinate swap `swapEmb k` of the index set and its action
on exponents; and the splitting `ν = partI I ν + partT I ν` of an exponent into its part on a
set `I` of coordinates and its complement, with the elementary properties used to slice a series
along a coordinate subspace. The germ theory (`Hironaka/Analytic/Germ`) imports this module.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MvPowerSeries Filter

namespace Analytic

variable {m n : ℕ}

/-! ### Shifting an exponent -/

variable {n : ℕ}

theorem monomialEval_add_single (ρ : Fin n → ℝ≥0) (ν : Fin n →₀ ℕ) (k : Fin n) :
    monomialEval ρ (ν + Finsupp.single k 1) = monomialEval ρ ν * ρ k := by
  rw [monomialEval_add, monomialEval_single_pow, pow_one]

/-! ### The degree after removing one coordinate -/

variable {n : ℕ}

theorem degree_tsub_single {θ : Fin n →₀ ℕ} {k : Fin n} (hk : θ k ≠ 0) :
    Finsupp.degree (θ - Finsupp.single k 1) + 1 = Finsupp.degree θ := by
  have h : Finsupp.single k 1 ≤ θ := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hk)
  have h2 := congrArg Finsupp.degree (add_tsub_cancel_of_le h)
  rw [map_add, Finsupp.degree_single] at h2
  omega

/-! ### Exponents in one variable and sums regrouped by degree -/

variable {n : ℕ}

/-- `ℕ ≃ (Fin 1 →₀ ℕ)`, `d ↦ d e_0`. -/
noncomputable def natEquivFin1 : ℕ ≃ (Fin 1 →₀ ℕ) where
  toFun d := Finsupp.single 0 d
  invFun μ := μ 0
  left_inv _ := Finsupp.single_eq_same
  right_inv μ := (Fin1.eq_single μ).symm

theorem natEquivFin1_apply (d : ℕ) : natEquivFin1 d = Finsupp.single 0 d := rfl

/-- Regrouping an `ℝ≥0∞`-valued sum over exponents by degree. -/
theorem ennreal_tsum_eq_tsum_sum_degreeSet (g : (Fin n →₀ ℕ) → ℝ≥0∞) :
    ∑' ν, g ν = ∑' d : ℕ, ∑ ν ∈ degreeSet n d, g ν := by
  classical
  rw [← (Equiv.sigmaFiberEquiv fun ν : Fin n →₀ ℕ => ν.degree).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun d => ?_
  have : Fintype {ν : Fin n →₀ ℕ // ν.degree = d} :=
    Fintype.ofFinset (degreeSet n d) fun _ => mem_degreeSet
  rw [tsum_fintype, Finset.sum_subtype (degreeSet n d) (fun _ => mem_degreeSet) g]
  rfl

theorem degree_fin1 (d : Fin 1 →₀ ℕ) : Finsupp.degree d = d 0 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_one]

/-! ### The coordinate swap on exponents -/

variable {n : ℕ}

/-- The coordinate swap `0 ↔ k` as an embedding of the index set. -/
def swapEmb (k : Fin (n + 1)) : Fin (n + 1) ↪ Fin (n + 1) := (Equiv.swap 0 k).toEmbedding

theorem swapEmb_apply (k i : Fin (n + 1)) : swapEmb k i = Equiv.swap 0 k i := rfl

theorem embDomain_swapEmb_swapEmb (k : Fin (n + 1)) (ν : Fin (n + 1) →₀ ℕ) :
    Finsupp.embDomain (swapEmb k) (Finsupp.embDomain (swapEmb k) ν) = ν := by
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  have h : (⇑(swapEmb k) ∘ ⇑(swapEmb k)) = id := funext fun i => Equiv.swap_apply_self 0 k i
  rw [h, Finsupp.mapDomain_id]

theorem embDomain_swapEmb_apply_zero (k : Fin (n + 1)) (ν : Fin (n + 1) →₀ ℕ) :
    Finsupp.embDomain (swapEmb k) ν 0 = ν k := by
  have h : (0 : Fin (n + 1)) = swapEmb k k := by rw [swapEmb_apply, Equiv.swap_apply_right]
  conv_lhs => rw [h]
  rw [Finsupp.embDomain_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective (swapEmb k).injective ν k

theorem embDomain_swapEmb_apply_k (k : Fin (n + 1)) (ν : Fin (n + 1) →₀ ℕ) :
    Finsupp.embDomain (swapEmb k) ν k = ν 0 := by
  have h : k = swapEmb k 0 := by rw [swapEmb_apply, Equiv.swap_apply_left]
  conv_lhs => rw [h]
  rw [Finsupp.embDomain_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective (swapEmb k).injective ν 0

/-! ### Splitting an exponent along a set of coordinates -/

variable {n : ℕ}

section Split

variable (I : Finset (Fin n))

/-- The part of an exponent supported on `I`. -/
def partI (ν : Fin n →₀ ℕ) : Fin n →₀ ℕ := Finsupp.filter (· ∈ I) ν

/-- The part of an exponent supported off `I`. -/
def partT (ν : Fin n →₀ ℕ) : Fin n →₀ ℕ := Finsupp.filter (· ∉ I) ν

theorem partI_apply (ν : Fin n →₀ ℕ) (k : Fin n) : partI I ν k = if k ∈ I then ν k else 0 :=
  Finsupp.filter_apply _ _ _

theorem partT_apply (ν : Fin n →₀ ℕ) (k : Fin n) : partT I ν k = if k ∉ I then ν k else 0 :=
  Finsupp.filter_apply _ _ _

theorem partI_add_partT (ν : Fin n →₀ ℕ) : partI I ν + partT I ν = ν :=
  Finsupp.filter_add_filter_not ν (· ∈ I)

theorem partI_add (μ ν : Fin n →₀ ℕ) : partI I (μ + ν) = partI I μ + partI I ν :=
  Finsupp.filter_add

theorem partT_add (μ ν : Fin n →₀ ℕ) : partT I (μ + ν) = partT I μ + partT I ν :=
  Finsupp.filter_add

theorem partT_partI (ν : Fin n →₀ ℕ) : partT I (partI I ν) = 0 := by
  ext k
  simp only [partT_apply, partI_apply, Finsupp.zero_apply]
  split_ifs <;> rfl

theorem partI_partT (ν : Fin n →₀ ℕ) : partI I (partT I ν) = 0 := by
  ext k
  simp only [partI_apply, partT_apply, Finsupp.zero_apply]
  split_ifs <;> rfl

theorem partI_eq_self_of_partT_eq_zero {β : Fin n →₀ ℕ} (h : partT I β = 0) : partI I β = β := by
  conv_rhs => rw [← partI_add_partT I β]
  rw [h, add_zero]

theorem partT_eq_self_of_partI_eq_zero {γ : Fin n →₀ ℕ} (h : partI I γ = 0) : partT I γ = γ := by
  conv_rhs => rw [← partI_add_partT I γ]
  rw [h, zero_add]

theorem degree_partI (ν : Fin n →₀ ℕ) : Finsupp.degree (partI I ν) = ∑ k ∈ I, ν k := by
  classical
  rw [Finsupp.degree_eq_sum]
  simp only [partI_apply]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Exponents split into their `I`-part and their complement. -/
noncomputable def splitEquiv :
    {β : Fin n →₀ ℕ // partT I β = 0} × {γ : Fin n →₀ ℕ // partI I γ = 0} ≃ (Fin n →₀ ℕ) where
  toFun p := p.1.1 + p.2.1
  invFun ν := (⟨partI I ν, partT_partI I ν⟩, ⟨partT I ν, partI_partT I ν⟩)
  left_inv p := by
    obtain ⟨⟨β, hβ⟩, ⟨γ, hγ⟩⟩ := p
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change partI I (β + γ) = β
      rw [partI_add, partI_eq_self_of_partT_eq_zero I hβ, hγ, add_zero]
    · change partT I (β + γ) = γ
      rw [partT_add, hβ, zero_add, partT_eq_self_of_partI_eq_zero I hγ]
  right_inv ν := partI_add_partT I ν

end Split

section Series

variable (I : Finset (Fin n))

theorem monomialEval_eq_inv_mul (ρ : Radius n) (β γ : Fin n →₀ ℕ) :
    monomialEval ρ γ = (monomialEval ρ β)⁻¹ * monomialEval ρ (β + γ) := by
  rw [monomialEval_add, ← mul_assoc, inv_mul_cancel₀ (monomialEval_pos' ρ β).ne', one_mul]

/-- Regrouping an `ℝ≥0∞`-valued sum over exponents by `I`-part and complement. -/
theorem ennreal_tsum_split (g : (Fin n →₀ ℕ) → ℝ≥0∞) :
    ∑' ν, g ν = ∑' β : {β : Fin n →₀ ℕ // partT I β = 0},
      ∑' γ : {γ : Fin n →₀ ℕ // partI I γ = 0}, g (β.1 + γ.1) := by
  rw [← (splitEquiv I).tsum_eq, ENNReal.tsum_prod']
  rfl

end Series

end Analytic
