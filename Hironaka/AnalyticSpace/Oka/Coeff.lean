/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Oka.PolySection
public import Hironaka.AnalyticSpace.Coherent
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The coefficient matrix of a row of polynomials

In the third step of the proof of Oka's coherence theorem [Fre17, Ch. I, 10.3], the entries of the
given row are Weierstrass polynomials in the distinguished variable, and the relations among them of
bounded degree in that variable are read as the kernel of a matrix over the base whose entries are
the coefficients of the polynomials ("our given map `F` induces an `𝒪(V)`-linear map
`𝒪(V)[z_n : m]^p → 𝒪(V)[z_n : m + d]`"). Over a commutative ring `R` (the base stalk, or the ring of
sections over an open subset of the base), for the polynomial `polyOfCoeff c = Σ_k C (c k) X^k`
with coefficient vector `c` (`Hironaka/AnalyticSpace/Oka/PolySection.lean`), this module defines

* `coeffMat P L N`, the `L × (q × N)` matrix `(l, (j, k)) ↦ coeff_{l−k} P_j` (zero for `k > l`);
* `coeff_sum_mul_polyOfCoeff`: the `l`-th coefficient of `Σ_j P_j · polyOfCoeff (c j)` is the `l`-th
  entry of `coeffMat P · c`;
* `sum_mul_polyOfCoeff_eq_zero_iff`: for `P_j` of degree `< d` and `0 < N`,
  `Σ_j P_j · polyOfCoeff (c j) = 0` iff the `d + N` coefficient equations hold, that is, iff `c`
  lies in the kernel of `coeffMat P (d + N) N`, reindexed through `finProdFinEquiv` into `relKer`
  (`sum_mul_polyOfCoeff_eq_zero_iff_mem_relKer`);
* the matrix `coeffMatSec` of sections over the base whose germs at every point form the coefficient
  matrix of the row of polynomials with the germs of the coefficients (`germ_coeffMatSec`), so that
  the relation system of the base matrix is a kernel system of the kind Oka's theorem speaks about.

These are the algebraic identities behind the core step `hasLocalGeneratorsOn_polyRow`
(`Hironaka.AnalyticSpace.Oka.Core`), whose hypothesis `hIH` is the induction hypothesis on the base
applied to `coeffMatSec`; they are not in the sources as separate statements.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Manifold
open Analytic

universe u

namespace AnalyticSpace

section Algebra

variable {R : Type*} [CommRing R]

/-- A polynomial of degree `< N` is the polynomial of its first `N` coefficients. -/
theorem polyOfCoeff_coeff {N : ℕ} (Q : Polynomial R) (hQ : Q.natDegree < N) :
    polyOfCoeff (fun k : Fin N => Q.coeff k) = Q := by
  unfold polyOfCoeff
  rw [Fin.sum_univ_eq_sum_range (fun k => Polynomial.C (Q.coeff k) * Polynomial.X ^ k) N]
  exact (Polynomial.as_sum_range_C_mul_X_pow' Q hQ).symm

/-- Freitag's induced matrix [Fre17, Ch. I, 10.3]: the `(l, (j, k))` entry is the coefficient of
`X^{l−k}` in `P_j` (zero if `k > l`). -/
def coeffMat {q : ℕ} (P : Fin q → Polynomial R) (L N : ℕ) : Fin L → Fin q × Fin N → R :=
  fun l jk => if (jk.2 : ℕ) ≤ l then (P jk.1).coeff (l - jk.2) else 0

/-- The `l`-th coefficient of `Σ_j P_j · polyOfCoeff (c j)` is the `l`-th entry of `coeffMat P · c`.
-/
theorem coeff_sum_mul_polyOfCoeff {q N : ℕ} (P : Fin q → Polynomial R) (c : Fin q → Fin N → R)
    (l : ℕ) :
    (∑ j, P j * polyOfCoeff (c j)).coeff l =
      ∑ jk : Fin q × Fin N,
        (if (jk.2 : ℕ) ≤ l then (P jk.1).coeff (l - jk.2) else 0) * c jk.1 jk.2 := by
  rw [Polynomial.finsetSum_coeff, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold polyOfCoeff
  rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show P j * (Polynomial.C (c j k) * Polynomial.X ^ (k : ℕ)) =
      Polynomial.C (c j k) * (P j * Polynomial.X ^ (k : ℕ)) by ring,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
  split_ifs <;> ring

theorem natDegree_sum_mul_polyOfCoeff_lt {q N d : ℕ} (P : Fin q → Polynomial R)
    (hP : ∀ j, (P j).natDegree < d) (c : Fin q → Fin N → R) (hN : 0 < N) :
    (∑ j, P j * polyOfCoeff (c j)).natDegree < d + N := by
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := d + N - 1) fun j _ => ?_) (by omega)
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 := hP j
  have h2 := natDegree_polyOfCoeff_lt (c j) hN
  omega

/-- For `P_j` of degree `< d` and `0 < N`, the relation `Σ_j P_j · polyOfCoeff (c j) = 0` is the
system of `d + N` coefficient equations `coeffMat P (d + N) N · c = 0`. -/
theorem sum_mul_polyOfCoeff_eq_zero_iff {q N d : ℕ} (P : Fin q → Polynomial R)
    (hP : ∀ j, (P j).natDegree < d) (c : Fin q → Fin N → R) (hN : 0 < N) :
    ∑ j, P j * polyOfCoeff (c j) = 0 ↔
      ∀ l : Fin (d + N),
        ∑ jk : Fin q × Fin N, coeffMat P (d + N) N l jk * c jk.1 jk.2 = 0 := by
  constructor
  · intro h l
    have := congrArg (fun Q => Polynomial.coeff Q l) h
    simp only [Polynomial.coeff_zero] at this
    rw [coeff_sum_mul_polyOfCoeff] at this
    exact this
  · intro h
    ext l
    rw [Polynomial.coeff_zero]
    by_cases hl : l < d + N
    · rw [coeff_sum_mul_polyOfCoeff]
      exact h ⟨l, hl⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le (natDegree_sum_mul_polyOfCoeff_lt P hP c hN) (not_lt.mp hl))

/-- The coefficient matrix with the pairs `(j, k)` reindexed by `finProdFinEquiv`, as a
`Fin`-indexed matrix. -/
def coeffMat' {q : ℕ} (P : Fin q → Polynomial R) (L N : ℕ) : Fin L → Fin (q * N) → R :=
  fun l i => coeffMat P L N l (finProdFinEquiv.symm i)

/-- The reindexed coefficient vector `(j, k) ↦ c j k`. -/
def flatCoeff {q N : ℕ} (c : Fin q → Fin N → R) : Fin (q * N) → R :=
  fun i => c (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

omit [CommRing R] in
theorem flatCoeff_apply {q N : ℕ} (c : Fin q → Fin N → R) (jk : Fin q × Fin N) :
    flatCoeff c (finProdFinEquiv jk) = c jk.1 jk.2 := by
  simp [flatCoeff]

/-- For `P_j` of degree `< d` and `0 < N`, `Σ_j P_j · polyOfCoeff (c j) = 0` iff the flattened
coefficient vector is a relation of the reindexed matrix. -/
theorem sum_mul_polyOfCoeff_eq_zero_iff_mem_relKer {q N d : ℕ} (P : Fin q → Polynomial R)
    (hP : ∀ j, (P j).natDegree < d) (c : Fin q → Fin N → R) (hN : 0 < N) :
    ∑ j, P j * polyOfCoeff (c j) = 0 ↔ flatCoeff c ∈ relKer (coeffMat' P (d + N) N) := by
  rw [sum_mul_polyOfCoeff_eq_zero_iff P hP c hN, mem_relKer_iff]
  refine forall_congr' fun l => ?_
  rw [← Fintype.sum_equiv finProdFinEquiv
    (fun jk => coeffMat P (d + N) N l jk * c jk.1 jk.2)
    (fun i => coeffMat' P (d + N) N l i * flatCoeff c i)
    (fun jk => by simp [coeffMat', flatCoeff])]

end Algebra

section Sections

variable {K : Type} [RCLike K] {m : ℕ}

/-- The matrix of sections over the base whose germs form the coefficient matrix of the row of
polynomials `j ↦ polyOfCoeff (germ ∘ pc j)` (each of degree `< d`): the entry `(l, (j, k))` is
`pc j (l − k)` if `k ≤ l < k + d`, else `0`. -/
def coeffMatSec {q d : ℕ} {V : Opens (Kn.{u} K m)}
    (pc : Fin q → Fin d → (sheafKn K m).presheaf.obj (op V)) (L N : ℕ) :
    Fin L → Fin (q * N) → (sheafKn K m).presheaf.obj (op V) :=
  fun l i =>
    let jk := finProdFinEquiv.symm i
    if h : (jk.2 : ℕ) ≤ l ∧ (l : ℕ) - jk.2 < d then pc jk.1 ⟨l - jk.2, h.2⟩ else 0

/-- The germs of `coeffMatSec` form the coefficient matrix of the polynomials with the germs of the
coefficients. -/
theorem germ_coeffMatSec {q d : ℕ} {V : Opens (Kn.{u} K m)}
    (pc : Fin q → Fin d → (sheafKn K m).presheaf.obj (op V)) (L N : ℕ) {b : Kn.{u} K m}
    (hb : b ∈ V) (l : Fin L) (i : Fin (q * N)) :
    (sheafKn K m).presheaf.germ V b hb (coeffMatSec pc L N l i) =
      coeffMat' (fun j => polyOfCoeff fun k => (sheafKn K m).presheaf.germ V b hb (pc j k))
        L N l i := by
  by_cases h1 : ((finProdFinEquiv.symm i).2 : ℕ) ≤ l
  · by_cases h2 : (l : ℕ) - (finProdFinEquiv.symm i).2 < d
    · simp only [coeffMatSec, coeffMat', coeffMat, coeff_polyOfCoeff,
        dite_eq_left (And.intro h1 h2), ite_eq_left h1, dite_eq_left h2]
    · have hn : ¬ (((finProdFinEquiv.symm i).2 : ℕ) ≤ l ∧
          (l : ℕ) - (finProdFinEquiv.symm i).2 < d) := fun h => h2 h.2
      simp only [coeffMatSec, coeffMat', coeffMat, coeff_polyOfCoeff, ite_eq_left h1,
        dite_eq_right h2]
      rw [dite_eq_right hn, map_zero]
  · have hn : ¬ (((finProdFinEquiv.symm i).2 : ℕ) ≤ l ∧
        (l : ℕ) - (finProdFinEquiv.symm i).2 < d) := fun h => h1 h.1
    simp only [coeffMatSec, coeffMat', coeffMat, coeff_polyOfCoeff, ite_eq_right h1]
    rw [dite_eq_right hn, map_zero]

end Sections

end AnalyticSpace
