/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Radius vectors, exponents and monomials

The part of the convergent-series library that does not depend on the coefficient field, shared by
the real modules `Hironaka/Analytic/ConvSeries/*` and the general ones over `K = ℝ` or `ℂ` in
`Hironaka/Analytic/ConvSeries/*`:

* the monomial `monomialEval x ν = x^ν` of a point `x : Fin m → R` over any commutative monoid `R`;
* radius vectors `ρ : Fin m → ℝ≥0`, their monomials `monomialEval ρ ν = ρ^ν`, and the type
  `Radius m` of radius vectors with positive entries (the polyradii of the majorant norms,
  [GR71, Kap. I]);
* the enumeration `expList ν` of an exponent `ν` of degree `Finsupp.degree ν = |ν|`, the finite set
  `degreeSet m n` of exponents of degree `n`, the count vector `countVec k` of a tuple of
  coordinate indices, and the regrouping of sums over exponents by degree or along antidiagonals
  (`hasSum_sum_degreeSet`, `hasSum_sum_antidiagonal`, stated for any regular topological monoid).

Not in the sources: elementary bookkeeping for the majorant norms and for the evaluation of series.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace Analytic

variable {m : ℕ}

/-! ## Monomials over a commutative monoid -/

section Monomial

variable {R : Type*} [CommMonoid R]

/-- The monomial `x^ν = ∏ k, x k ^ ν k` of a point `x`, over any commutative monoid (the points of
the analytic library are `x : Fin m → K` with `K = ℝ` or `ℂ`, and the radius vectors
`ρ : Fin m → ℝ≥0`). The monoid is read off `x`, not the expected type, so that
`(monomialEval ρ ν : ℝ≥0∞)` coerces a radius monomial. -/
@[elab_without_expected_type]
def monomialEval (x : Fin m → R) (ν : Fin m →₀ ℕ) : R := ν.prod fun k n => x k ^ n

@[simp]
theorem monomialEval_zero (x : Fin m → R) : monomialEval x 0 = 1 := by simp [monomialEval]

theorem monomialEval_add (x : Fin m → R) (μ ν : Fin m →₀ ℕ) :
    monomialEval x (μ + ν) = monomialEval x μ * monomialEval x ν := by
  unfold monomialEval
  rw [Finsupp.prod_add_index' (fun k => pow_zero (x k)) (fun k a b => pow_add (x k) a b)]

/-- `x^ν = ∏_k x_k^{ν_k}` over all coordinates. -/
theorem monomialEval_eq_prod (x : Fin m → R) (ν : Fin m →₀ ℕ) :
    monomialEval x ν = ∏ k, x k ^ ν k :=
  Finsupp.prod_fintype _ _ fun _ => pow_zero _

/-- `x^{n e_k} = x_k^n`. -/
theorem monomialEval_single_pow (x : Fin m → R) (k : Fin m) (n : ℕ) :
    monomialEval x (Finsupp.single k n) = x k ^ n := by
  simp [monomialEval]

theorem monomialEval_cons (x : Fin (m + 1) → R) (k : ℕ) (y : Fin m →₀ ℕ) :
    monomialEval x (Finsupp.cons k y) = x 0 ^ k * monomialEval (Fin.tail x) y := by
  rw [monomialEval_eq_prod, monomialEval_eq_prod, Fin.prod_univ_succ, Finsupp.cons_zero]
  simp only [Finsupp.cons_succ, Fin.tail]

end Monomial

/-! ## Radius vectors -/

theorem monomialEval_pos {ρ : Fin m → ℝ≥0} (hρ : ∀ k, 0 < ρ k) (ν : Fin m →₀ ℕ) :
    0 < monomialEval ρ ν :=
  Finset.prod_pos fun k _ => pow_pos (hρ k) _

theorem monomialEval_le_monomialEval {ρ ρ' : Fin m → ℝ≥0} (h : ∀ k, ρ k ≤ ρ' k) (ν : Fin m →₀ ℕ) :
    monomialEval ρ ν ≤ monomialEval ρ' ν :=
  Finset.prod_le_prod fun k _ => pow_le_pow_left' (h k) _

theorem coe_monomialEval (ρ : Fin m → ℝ≥0) (ν : Fin m →₀ ℕ) :
    ((monomialEval ρ ν : ℝ≥0) : ℝ) = ν.prod fun k n => (ρ k : ℝ) ^ n := by
  simp [monomialEval, Finsupp.prod, NNReal.coe_prod]

theorem monomialEval_one (ν : Fin m →₀ ℕ) : monomialEval (fun _ : Fin m => (1 : ℝ≥0)) ν = 1 := by
  simp [monomialEval]

/-- A radius vector with positive entries, `ρ ∈ (0, ∞)^m`. -/
abbrev Radius (m : ℕ) : Type := {ρ : Fin m → ℝ≥0 // ∀ k, 0 < ρ k}

namespace Radius

instance : CoeFun (Radius m) fun _ => Fin m → ℝ≥0 := ⟨Subtype.val⟩

theorem pos (ρ : Radius m) (k : Fin m) : 0 < ρ k := ρ.2 k

/-- The pointwise minimum of two radius vectors. -/
def min (ρ ρ' : Radius m) : Radius m :=
  ⟨fun k => Min.min (ρ k) (ρ' k), fun k => lt_min (ρ.2 k) (ρ'.2 k)⟩

theorem min_le_left (ρ ρ' : Radius m) (k : Fin m) : (ρ.min ρ') k ≤ ρ k := _root_.min_le_left _ _

theorem min_le_right (ρ ρ' : Radius m) (k : Fin m) : (ρ.min ρ') k ≤ ρ' k := _root_.min_le_right _ _

/-- The constant radius vector `1`. -/
def one (m : ℕ) : Radius m := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The base radius of a radius in `m + 1` variables (the distinguished coordinate is `0`). -/
def tail (ρ : Radius (m + 1)) : Radius m :=
  ⟨fun k => ρ k.succ, fun k => ρ.pos k.succ⟩

/-- Every radius vector admits a positive common lower bound `r ≤ ρ_k` (the product of the
`min 1 ρ_k`). -/
theorem exists_le (ρ : Radius m) : ∃ r : ℝ≥0, 0 < r ∧ ∀ k, r ≤ ρ k := by
  classical
  refine ⟨∏ k, Min.min 1 (ρ k), Finset.prod_pos fun k _ => lt_min one_pos (ρ.pos k), fun k => ?_⟩
  calc ∏ j, Min.min 1 (ρ j) = Min.min 1 (ρ k) * ∏ j ∈ Finset.univ.erase k, Min.min 1 (ρ j) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)).symm
    _ ≤ Min.min 1 (ρ k) * 1 :=
        mul_le_mul' le_rfl
          (Finset.prod_le_one₀ (fun _ _ => zero_le) fun j _ => _root_.min_le_left _ _)
    _ ≤ ρ k := by rw [mul_one]; exact _root_.min_le_right _ _

end Radius

theorem monomialEval_pos' (ρ : Radius m) (ν : Fin m →₀ ℕ) : 0 < monomialEval ρ ν :=
  monomialEval_pos ρ.pos ν

/-! ## Exponents -/

/-- An enumeration of the exponent `ν` as a list with `ν k` entries equal to `k`; its length is
the degree `|ν| = ∑ k, ν k` (`Finsupp.degree`). -/
noncomputable def expList (ν : Fin m →₀ ℕ) : List (Fin m) := ν.toMultiset.toList

theorem length_expList (ν : Fin m →₀ ℕ) : (expList ν).length = ν.degree := by
  rw [expList, Multiset.length_toList, Finsupp.card_toMultiset, Finsupp.degree_apply]
  rfl

/-- The exponents of degree `n`. -/
noncomputable def degreeSet (m n : ℕ) : Finset (Fin m →₀ ℕ) :=
  Finset.finsuppAntidiag Finset.univ n

theorem mem_degreeSet {n : ℕ} {ν : Fin m →₀ ℕ} : ν ∈ degreeSet m n ↔ ν.degree = n := by
  rw [degreeSet, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  simp

/-- Exponents of degree `n` have `ρ^ν ≥ r^n` when `r ≤ ρ_k` for all `k`. -/
theorem pow_le_monomialEval {ρ : Fin m → ℝ≥0} {r : ℝ≥0} (hr : ∀ k, r ≤ ρ k) {n : ℕ}
    {ν : Fin m →₀ ℕ} (hν : ν.degree = n) : r ^ n ≤ monomialEval ρ ν := by
  rw [← hν, Finsupp.degree_eq_sum, monomialEval_eq_prod, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun k _ => pow_le_pow_left' (hr k) _

/-- The degree sets are pairwise disjoint. -/
theorem pairwiseDisjoint_degreeSet (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint (degreeSet m) := by
  intro a _ b _ hab
  rw [Function.onFun, Finset.disjoint_left]
  intro ν ha hb
  exact hab ((mem_degreeSet.mp ha).symm.trans (mem_degreeSet.mp hb))

/-- The count vector `ν(k) = ∑_i single (k i) 1` of a tuple of coordinate indices. -/
noncomputable def countVec {n : ℕ} (k : Fin n → Fin m) : Fin m →₀ ℕ :=
  ∑ i, Finsupp.single (k i) 1

theorem degree_countVec {n : ℕ} (k : Fin n → Fin m) : (countVec k).degree = n := by
  classical
  rw [Finsupp.degree_eq_sum, countVec]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_comm]
  simp

/-- The fibre counts over the exponents of degree `n` add up to `m^n`. -/
theorem sum_card_fiber_countVec (n : ℕ) :
    ∑ ν ∈ degreeSet m n, (((Finset.univ : Finset (Fin n → Fin m)).filter
      (fun k => countVec k = ν)).card : ℝ) = (m : ℝ) ^ n := by
  classical
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise
    (fun k _ => mem_degreeSet.mpr (degree_countVec k))]
  simp

/-! ## Sums regrouped by degree and along antidiagonals -/

/-- The degree-wise sums of a summable nonnegative family are summable, with the same total. -/
theorem summable_sum_degreeSet {w : (Fin m →₀ ℕ) → ℝ} (hw0 : ∀ ν, 0 ≤ w ν) (hw : Summable w) :
    Summable fun n => ∑ ν ∈ degreeSet m n, w ν := by
  classical
  refine summable_of_sum_le (c := ∑' ν, w ν) (fun n => Finset.sum_nonneg fun ν _ => hw0 ν)
    fun s => ?_
  rw [← Finset.sum_biUnion (pairwiseDisjoint_degreeSet s)]
  exact hw.sum_le_tsum _ fun ν _ => hw0 ν

/-- A nonnegative family on the exponents whose degree-wise sums are summable is summable. -/
theorem summable_of_summable_sum_degreeSet {w : (Fin m →₀ ℕ) → ℝ} (hw0 : ∀ ν, 0 ≤ w ν)
    (hs : Summable fun n => ∑ ν ∈ degreeSet m n, w ν) : Summable w := by
  classical
  refine summable_of_sum_le (c := ∑' n, ∑ ν ∈ degreeSet m n, w ν) hw0 fun s => ?_
  calc ∑ ν ∈ s, w ν ≤ ∑ ν ∈ (s.image Finsupp.degree).biUnion (degreeSet m), w ν := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun ν hν => ?_) fun ν _ _ => hw0 ν
        exact Finset.mem_biUnion.mpr ⟨ν.degree, Finset.mem_image_of_mem _ hν,
          mem_degreeSet.mpr rfl⟩
    _ = ∑ n ∈ s.image Finsupp.degree, ∑ ν ∈ degreeSet m n, w ν :=
        Finset.sum_biUnion (pairwiseDisjoint_degreeSet _)
    _ ≤ ∑' n, ∑ ν ∈ degreeSet m n, w ν :=
        hs.sum_le_tsum _ fun n _ => Finset.sum_nonneg fun ν _ => hw0 ν

section Regroup

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [T3Space E] [ContinuousAdd E]

/-- Regrouping a convergent sum over exponents by degree. -/
theorem hasSum_sum_degreeSet {g : (Fin m →₀ ℕ) → E} {a : E} (hg : HasSum g a) :
    HasSum (fun n => ∑ ν ∈ degreeSet m n, g ν) a := by
  classical
  have he := (Equiv.hasSum_iff (Equiv.sigmaFiberEquiv fun ν : Fin m →₀ ℕ => ν.degree)).mpr hg
  refine he.sigma fun n => ?_
  have : Fintype {ν : Fin m →₀ ℕ // ν.degree = n} :=
    Fintype.ofFinset (degreeSet m n) fun _ => mem_degreeSet
  rw [Finset.sum_subtype (degreeSet m n) (fun _ => mem_degreeSet) g]
  exact hasSum_fintype fun c : {ν : Fin m →₀ ℕ // ν.degree = n} => g c.1

/-- A summable family on pairs of exponents, regrouped by the sum of the pair. -/
theorem hasSum_sum_antidiagonal {h : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) → E} {a : E}
    (hh : HasSum h a) :
    HasSum (fun ν => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν, h p) a := by
  classical
  have he := (Equiv.hasSum_iff
    (Equiv.sigmaFiberEquiv fun p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) => p.1 + p.2)).mpr hh
  refine he.sigma fun ν => ?_
  have : Fintype {p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) // p.1 + p.2 = ν} :=
    Fintype.ofFinset (Finset.HasAntidiagonal.antidiagonal ν)
      fun _ => Finset.HasAntidiagonal.mem_antidiagonal
  rw [Finset.sum_subtype (Finset.HasAntidiagonal.antidiagonal ν)
    (fun _ => Finset.HasAntidiagonal.mem_antidiagonal) h]
  exact hasSum_fintype fun c : {p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) // p.1 + p.2 = ν} => h c.1

end Regroup

/-! ## Monomials at the enumeration and the count vector of an exponent -/

section Monomial

variable {R : Type*} [CommMonoid R]

theorem prod_map_expList (x : Fin m → R) (ν : Fin m →₀ ℕ) :
    ((expList ν).map x).prod = monomialEval x ν := by
  rw [expList, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList,
    Finsupp.toMultiset_map, Finsupp.prod_toMultiset, monomialEval,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _]

theorem monomialEval_sum (x : Fin m → R) {ι : Type*} (s : Finset ι) (g : ι → Fin m →₀ ℕ) :
    monomialEval x (∑ i ∈ s, g i) = ∏ i ∈ s, monomialEval x (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, monomialEval_add, ih]

@[simp]
theorem monomialEval_single (x : Fin m → R) (j : Fin m) :
    monomialEval x (Finsupp.single j 1) = x j := by
  simp [monomialEval, Finsupp.prod_single_index]

theorem monomialEval_countVec (x : Fin m → R) {n : ℕ} (k : Fin n → Fin m) :
    monomialEval x (countVec k) = ∏ i, x (k i) := by
  rw [countVec, monomialEval_sum]
  simp

end Monomial

end Analytic
