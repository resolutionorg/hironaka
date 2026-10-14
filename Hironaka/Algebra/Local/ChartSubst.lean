/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Kollár's Lemma 61 in local form: the monomial computation

The proof of [Kol07, Lemma 61] takes `f(x₁, …, xₙ) ∈ I` of order `m = max-ord I` at `p`, writes
its birational transform as `π⁻¹_* f = y_r^{-m} f(y₁y_r, …, y_{r-1}y_r, y_r, …, yₙ)`, and observes
that a monomial of degree `m` of `f` becomes a monomial of degree at most `2m` after the
substitution, hence "a monomial of degree `≤ 2m − m = m`" of `π⁻¹_* f`.

This file carries out that computation in the power series ring `K⟦y⟧`.  With the zero-based
indexing of `Hironaka/Algebra/Local/ChartRing.lean` (`xᵢ ↦ yᵢ y_r` for `i < r`, `xⱼ ↦ yⱼ` for `j ≥
r`), the monomial `x^α` goes to `y^{σ(α)}` with `σ(α) = α + (∑_{i<r} αᵢ) e_r` (`chartExp`,
injective, `|σ(α)| = |α| + ∑_{i<r} αᵢ ≤ 2|α|`), so distinct monomials of `f` stay distinct and
`coeff_{σ α}(φ̂ f) = coeff_α f` (`coeff_subst_chartSubst`).  If every monomial of `f` has
`x₀..x_r`-degree `≥ m` (the local form of `f ∈ P̂ᵐ`, `P` the ideal of the centre), then
`φ̂ f = y_r^m g` and, for `order f = m`, `order g ≤ m` (`exists_X_pow_mul_eq_subst_chartSubst`).
The transfer of this bound from `K⟦x⟧` to a regular local ring `R` through the Cohen isomorphism
`R̂ ≅ K⟦x⟧` is made in `Hironaka/Algebra/Local/ChartCompletion.lean` and the modules following it.
-/

@[expose] public section

namespace IsLocalRing

open MvPowerSeries Finset

variable {n : ℕ} (r : Fin n)

/-! ### The exponent substitution -/

/-- The exponent substitution `σ(α) = (α₀, …, α_{r-1}, α₀ + ⋯ + α_r, α_{r+1}, …)`, i.e.
`α + (∑_{i<r} αᵢ) e_r`: the exponent of "the corresponding monomial" in the proof of
[Kol07, Lemma 61]. -/
noncomputable def chartExp (α : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  α + Finsupp.single r (∑ i ∈ univ.filter (· < r), α i)

theorem chartExp_apply_of_ne {i : Fin n} (hi : i ≠ r) (α : Fin n →₀ ℕ) : chartExp r α i = α i := by
  simp [chartExp, hi.symm]

theorem chartExp_apply_self (α : Fin n →₀ ℕ) :
    chartExp r α r = α r + ∑ i ∈ univ.filter (· < r), α i := by
  simp [chartExp]

theorem sum_filter_le_chartExp_apply_self (α : Fin n →₀ ℕ) :
    ∑ i ∈ univ.filter (· ≤ r), α i = chartExp r α r := by
  rw [chartExp_apply_self, add_comm]
  have h : univ.filter (fun i : Fin n => i ≤ r) = insert r (univ.filter (· < r)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact h.le
      · exact h.le
  rw [h, sum_insert (by simp), add_comm]

/-- `σ` is injective. -/
theorem chartExp_injective : Function.Injective (chartExp r) := by
  intro α β h
  have h1 : ∀ i, i ≠ r → α i = β i := fun i hi => by
    rw [← chartExp_apply_of_ne r hi α, h, chartExp_apply_of_ne r hi β]
  have h2 : ∑ i ∈ univ.filter (· < r), α i = ∑ i ∈ univ.filter (· < r), β i :=
    sum_congr rfl fun i hi => h1 i (ne_of_lt (mem_filter.mp hi).2)
  ext i
  by_cases hi : i = r
  · subst hi
    have := congrArg (fun γ : Fin n →₀ ℕ => γ i) h
    simp only [chartExp_apply_self] at this
    omega
  · exact h1 i hi

theorem degree_add' (α β : Fin n →₀ ℕ) : (α + β).degree = α.degree + β.degree := by
  simp only [Finsupp.degree_eq_sum, Finsupp.coe_add, Pi.add_apply, sum_add_distrib]

/-- `|σ(α)| = |α| + ∑_{i<r} αᵢ`. -/
theorem degree_chartExp (α : Fin n →₀ ℕ) :
    (chartExp r α).degree = α.degree + ∑ i ∈ univ.filter (· < r), α i := by
  rw [chartExp, degree_add', Finsupp.degree_single]

theorem sum_filter_lt_le_degree (α : Fin n →₀ ℕ) : ∑ i ∈ univ.filter (· < r), α i ≤ α.degree := by
  rw [Finsupp.degree_eq_sum]
  exact sum_le_sum_of_subset (filter_subset _ _)

/-- `|σ(α)| ≤ 2|α|`. -/
theorem degree_chartExp_le (α : Fin n →₀ ℕ) : (chartExp r α).degree ≤ 2 * α.degree := by
  rw [degree_chartExp]
  have := sum_filter_lt_le_degree r α
  omega

/-- For `|α| = m`, `|σ(α)| − m ≤ m`: the bound "`≤ 2m − m = m`" of the proof of
[Kol07, Lemma 61]. -/
theorem degree_chartExp_sub_le {α : Fin n →₀ ℕ} {m : ℕ} (h : α.degree = m) :
    (chartExp r α).degree - m ≤ m := by
  rw [degree_chartExp, h]
  have := sum_filter_lt_le_degree r α
  omega

/-! ### The substitution `xᵢ ↦ yᵢ y_r` (`i < r`), `xⱼ ↦ yⱼ` (`j ≥ r`) -/

variable {K : Type*} [CommRing K]

/-- The substitution `xᵢ ↦ yᵢ y_r` for `i < r`, `xⱼ ↦ yⱼ` for `j ≥ r`, in `K⟦y⟧`: the
substitution of [Kol07, Definition 60, (60.3)]. -/
noncomputable def chartSubst : Fin n → MvPowerSeries (Fin n) K :=
  fun i => if i < r then X i * X r else X i

theorem hasSubst_chartSubst : HasSubst (chartSubst (K := K) r) :=
  hasSubst_of_constantCoeff_zero fun i => by
    unfold chartSubst
    split_ifs <;> simp

/-- The monomial `x^α` goes to `y^{σ(α)}` under the chart substitution. -/
theorem chartSubst_prod (α : Fin n →₀ ℕ) :
    (α.prod fun s e => chartSubst (K := K) r s ^ e) = monomial (chartExp r α) 1 := by
  classical
  unfold Finsupp.prod
  have h1 : ∀ s ∈ α.support, chartSubst (K := K) r s ^ α s =
      monomial (Finsupp.single s (α s)) 1 * (if s < r then monomial (Finsupp.single r (α s)) 1
        else 1) := by
    intro s _
    unfold chartSubst
    split_ifs with hs
    · rw [mul_pow, X_pow_eq, X_pow_eq]
    · rw [mul_one, X_pow_eq]
  have hA : ∏ x ∈ α.support, monomial (Finsupp.single x (α x)) (1 : K) = monomial α 1 := by
    rw [prod_monomial, prod_const_one,
      show (∑ i ∈ α.support, Finsupp.single i (α i)) = α from Finsupp.sum_single α]
  have hsum : (∑ x ∈ α.support.filter (· < r), α x) = ∑ i ∈ univ.filter (· < r), α i := by
    refine sum_subset (filter_subset_filter _ (subset_univ _)) fun i hi hi' => ?_
    by_contra hne
    exact hi' (mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, (mem_filter.mp hi).2⟩)
  have hB : (∏ x ∈ α.support, if x < r then monomial (Finsupp.single r (α x)) (1 : K) else 1) =
      monomial (Finsupp.single r (∑ i ∈ univ.filter (· < r), α i)) 1 := by
    rw [prod_ite, prod_const_one, mul_one, prod_monomial, prod_const_one,
      ← Finsupp.single_finsetSum, hsum]
  rw [prod_congr rfl h1, prod_mul_distrib, hA, hB, monomial_mul_monomial, mul_one]
  rfl

/-- The coefficient formula `coeff_{σ α}(φ̂ f) = coeff_α f`: since `σ` is injective, the
corresponding monomial of `φ̂ f` has the coefficient of `x^α` in `f`. -/
theorem coeff_subst_chartSubst (f : MvPowerSeries (Fin n) K) (α : Fin n →₀ ℕ) :
    coeff (chartExp r α) (subst (chartSubst r) f) = coeff α f := by
  classical
  rw [coeff_subst (hasSubst_chartSubst r), finsum_eq_single _ α]
  · rw [chartSubst_prod, coeff_monomial, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro d hd
    rw [chartSubst_prod, coeff_monomial, ite_eq_right (fun h => hd (chartExp_injective r h).symm),
      smul_zero]

/-- Every monomial of `φ̂ f` is `y^{σ(d)}` for a monomial `x^d` of `f`. -/
theorem coeff_subst_chartSubst_eq_zero {f : MvPowerSeries (Fin n) K} {β : Fin n →₀ ℕ}
    (hβ : ∀ d, coeff d f ≠ 0 → chartExp r d ≠ β) :
    coeff β (subst (chartSubst (K := K) r) f) = 0 := by
  classical
  rw [coeff_subst (hasSubst_chartSubst r)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : coeff d f = 0
  · rw [hd, zero_smul]
  · rw [chartSubst_prod, coeff_monomial, ite_eq_right (fun h => hβ d hd h.symm), smul_zero]

/-- If every monomial of `f` has `x₀..x_r`-degree `≥ m` (`f ∈ P̂ᵐ`), then every monomial of `φ̂ f`
has `y_r`-exponent `≥ m`. -/
theorem coeff_subst_chartSubst_eq_zero_of_lt {f : MvPowerSeries (Fin n) K} {m : ℕ}
    (hP : ∀ d, coeff d f ≠ 0 → m ≤ ∑ i ∈ univ.filter (· ≤ r), d i) {β : Fin n →₀ ℕ}
    (hβ : β r < m) : coeff β (subst (chartSubst (K := K) r) f) = 0 := by
  refine coeff_subst_chartSubst_eq_zero r fun d hd h => ?_
  have := hP d hd
  rw [sum_filter_le_chartExp_apply_self, h] at this
  omega

/-- **The monomial computation of the proof of [Kol07, Lemma 61]**: if `order f = m` and every
monomial of `f` has `x₀..x_r`-degree `≥ m` (`f ∈ P̂ᵐ`), then `φ̂ f = y_r^m g` with `order g ≤ m` —
the monomial of degree `m` of `f` survives with degree `≤ 2m − m = m`. -/
theorem exists_X_pow_mul_eq_subst_chartSubst {f : MvPowerSeries (Fin n) K} {m : ℕ}
    (hord : f.order = m) (hP : ∀ d, coeff d f ≠ 0 → m ≤ ∑ i ∈ univ.filter (· ≤ r), d i) :
    ∃ g : MvPowerSeries (Fin n) K, X r ^ m * g = subst (chartSubst (K := K) r) f ∧
      g.order ≤ m := by
  classical
  set g : MvPowerSeries (Fin n) K :=
    fun β => coeff (β + Finsupp.single r m) (subst (chartSubst (K := K) r) f) with hg
  have hcoeff : ∀ β, coeff β g =
      coeff (β + Finsupp.single r m) (subst (chartSubst (K := K) r) f) := fun β => rfl
  refine ⟨g, ?_, ?_⟩
  · ext β
    rw [X_pow_eq, coeff_monomial_mul]
    split_ifs with hle
    · rw [one_mul, hcoeff, tsub_add_cancel_of_le hle]
    · rw [coeff_subst_chartSubst_eq_zero_of_lt r hP]
      have := (not_le.mp (fun h => hle (Finsupp.single_le_iff.mpr h)) : β r < m)
      exact this
  · have hfin : f.order.toNat = f.order := by rw [hord]; simp
    obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
    rw [hord] at hdeg
    have hdeg' : d.degree = m := by exact_mod_cast hdeg
    have hle : Finsupp.single r m ≤ chartExp r d := by
      rw [Finsupp.single_le_iff, ← sum_filter_le_chartExp_apply_self]
      exact hP d hd
    have hne : coeff (chartExp r d - Finsupp.single r m) g ≠ 0 := by
      rw [hcoeff, tsub_add_cancel_of_le hle, coeff_subst_chartSubst]
      exact hd
    refine (order_le hne).trans ?_
    have h1 : (chartExp r d - Finsupp.single r m).degree + (Finsupp.single r m).degree =
        (chartExp r d).degree := by
      rw [← degree_add', tsub_add_cancel_of_le hle]
    rw [Finsupp.degree_single] at h1
    have h2 := degree_chartExp_sub_le r hdeg'
    exact_mod_cast (by omega : (chartExp r d - Finsupp.single r m).degree ≤ m)

end IsLocalRing
