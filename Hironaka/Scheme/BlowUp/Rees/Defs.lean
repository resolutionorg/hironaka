/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.ReesAlgebra

/-!
# The graded Rees algebra

Mathlib's `reesAlgebra I` is the subalgebra `R[It] ⊆ R[t]` of the polynomials whose `i`-th
coefficient lies in `I ^ i`; it carries no grading there. The grading of [Hau14, Definition 4.6]
gives the variable `t` degree `1`, so that the `i`-th piece `reesAlgebra.grading I i` is `Iⁱ tⁱ`:
the polynomials all of whose coefficients of index `j ≠ i` vanish. Mathlib's polynomial variable
`X` plays the role of Hauser's `t`. The pieces are independent and span, since a polynomial is the
sum of its monomials and is determined by its coefficients (the degree-`n` component of `p` is
`(coeff n p) tⁿ`, `reesAlgebra.component`), and degrees add under products; so the Rees algebra is
a graded `R`-algebra, `reesAlgebra.gradedAlgebra`, by Mathlib's constructor
`DirectSum.IsInternal.gradedAlgebra`.

The degree-zero piece is `R` itself, embedded by `g ↦ g · t⁰` (`reesAlgebra.gradingZeroEquiv`).
A ring map `φ : R → S` with `φ(I) ⊆ J` sends `Rees(I)` into `Rees(J)` degreewise, by applying `φ`
to the coefficients (`reesAlgebra.mapOfLe`); these are the transition maps of the relative `Proj`
of the Rees algebra of an ideal sheaf [Sta, Tags 01OF and 0804].

`R` is any commutative ring and `I` any ideal: finiteness of `I` belongs to the properness of the
blow-up, not to the construction. For `I = 0` the Rees algebra is `R` in degree `0` and `0` in
positive degrees; for `I = R` it is `R[t]` with the degree grading; for the zero ring everything is
`0` [Hau14, Definition 4.6].
-/

@[expose] public section

open Polynomial
open scoped DirectSum

universe u

section Grading

variable {R : Type u} [CommRing R]

section Pieces

variable (I : Ideal R)

/-- **The graded pieces of the Rees algebra** [Hau14, Definition 4.6]: the variable `t` has
degree `1`, so that the elements of `Iⁱ · tⁱ` have degree `i`.  The `i`-th piece is the
`R`-submodule of `reesAlgebra I` of the polynomials all of whose coefficients of index `j ≠ i`
vanish, that is, of the monomials `c tⁱ` with `c ∈ I ^ i`
(`reesAlgebra.eq_monomial_of_mem_grading`). -/
def reesAlgebra.grading (i : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {p | ∀ j, j ≠ i → (p : R[X]).coeff j = 0}
  add_mem' := fun {p q} hp hq j hj => by
    rw [Subalgebra.coe_add, coeff_add, hp j hj, hq j hj, add_zero]
  zero_mem' := fun j _ => by rw [Subalgebra.coe_zero, coeff_zero]
  smul_mem' := fun r {p} hp j hj => by simp [hp j hj]

variable {I}

/-- Membership: `p` has degree `n` iff its coefficients of index `≠ n` vanish. -/
theorem reesAlgebra.mem_grading_iff {n : ℕ} {p : reesAlgebra I} :
    p ∈ reesAlgebra.grading I n ↔ ∀ j ≠ n, (p : R[X]).coeff j = 0 :=
  Iff.rfl

theorem reesAlgebra.coeff_eq_zero_of_mem_grading {n : ℕ} {p : reesAlgebra I}
    (hp : p ∈ reesAlgebra.grading I n) {j : ℕ} (hj : j ≠ n) : (p : R[X]).coeff j = 0 :=
  reesAlgebra.mem_grading_iff.mp hp j hj

/-- The `n`-th coefficient of an element of the Rees algebra lies in `I ^ n`
(`mem_reesAlgebra_iff`, read on the subtype). -/
theorem reesAlgebra.coeff_mem_pow (p : reesAlgebra I) (n : ℕ) : (p : R[X]).coeff n ∈ I ^ n :=
  (mem_reesAlgebra_iff I p).mp p.2 n

/-- The normal form: an element of degree `n` is the monomial `c tⁿ` of its `n`-th coefficient
`c`, and `c ∈ I ^ n`. -/
theorem reesAlgebra.eq_monomial_of_mem_grading {n : ℕ} {p : reesAlgebra I}
    (hp : p ∈ reesAlgebra.grading I n) :
    (p : R[X]) = monomial n ((p : R[X]).coeff n) ∧ (p : R[X]).coeff n ∈ I ^ n := by
  refine ⟨Polynomial.ext fun j => ?_, reesAlgebra.coeff_mem_pow p n⟩
  rw [coeff_monomial]
  split_ifs with h
  · rw [h]
  · exact reesAlgebra.coeff_eq_zero_of_mem_grading hp (Ne.symm h)

/-- An element of the Rees algebra that is a monomial of degree `i` lies in the `i`-th piece. -/
theorem reesAlgebra.mem_grading_of_coe_eq_monomial {i : ℕ} {p : reesAlgebra I} {c : R}
    (hp : (p : R[X]) = monomial i c) : p ∈ reesAlgebra.grading I i :=
  fun j hj => by rw [hp, coeff_monomial, ite_eq_right (Ne.symm hj)]

/-- The `n`-th piece consists of the monomials `c tⁿ`, `c ∈ I ^ n`. -/
theorem reesAlgebra.mem_grading_iff_exists {n : ℕ} {p : reesAlgebra I} :
    p ∈ reesAlgebra.grading I n ↔ ∃ c ∈ I ^ n, (p : R[X]) = monomial n c :=
  ⟨fun hp => ⟨_, (reesAlgebra.eq_monomial_of_mem_grading hp).2,
      (reesAlgebra.eq_monomial_of_mem_grading hp).1⟩,
    fun ⟨_, _, hp⟩ => reesAlgebra.mem_grading_of_coe_eq_monomial hp⟩

end Pieces

section Components

variable (I : Ideal R)

/-- The degree-`n` component `(coeff n p) tⁿ` of an element `p` of the Rees algebra, as an element
of the `n`-th piece; `R`-linear in `p`.  It recovers a homogeneous element of degree `n`
(`reesAlgebra.component_of_mem`) and kills one of any other degree
(`reesAlgebra.component_of_mem_of_ne`). -/
noncomputable def reesAlgebra.component (n : ℕ) : reesAlgebra I →ₗ[R] reesAlgebra.grading I n where
  toFun p := ⟨⟨monomial n ((p : R[X]).coeff n),
      reesAlgebra.monomial_mem.mpr (reesAlgebra.coeff_mem_pow p n)⟩,
    reesAlgebra.mem_grading_of_coe_eq_monomial rfl⟩
  map_add' p q := Subtype.ext <| Subtype.ext <| by simp
  map_smul' r p := Subtype.ext <| Subtype.ext <| by simp [smul_monomial]

variable {I}


theorem reesAlgebra.component_of_mem {n : ℕ} {p : reesAlgebra I}
    (hp : p ∈ reesAlgebra.grading I n) : reesAlgebra.component I n p = ⟨p, hp⟩ :=
  Subtype.ext <| Subtype.ext (reesAlgebra.eq_monomial_of_mem_grading hp).1.symm

theorem reesAlgebra.component_of_mem_of_ne {m n : ℕ} {p : reesAlgebra I}
    (hp : p ∈ reesAlgebra.grading I m) (h : m ≠ n) : reesAlgebra.component I n p = 0 :=
  Subtype.ext <| Subtype.ext <| by
    change monomial n ((p : R[X]).coeff n) = 0
    simp [reesAlgebra.coeff_eq_zero_of_mem_grading hp (Ne.symm h)]

/-- Independence: the `n`-th component of a finite sum of homogeneous elements is its degree-`n`
summand — a polynomial is determined by its coefficients, and the `n`-th coefficient of the sum
is the `n`-th coefficient of the degree-`n` summand. -/
theorem reesAlgebra.component_coeAddMonoidHom (x : ⨁ i, reesAlgebra.grading I i) (n : ℕ) :
    reesAlgebra.component I n (DirectSum.coeAddMonoidHom (reesAlgebra.grading I) x) = x n := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of x, map_sum, map_sum]
  simp_rw [DirectSum.coeAddMonoidHom_of]
  rw [Finset.sum_eq_single n (fun i _ hi => reesAlgebra.component_of_mem_of_ne (x i).2 hi)
    fun hn => by rw [DFinsupp.notMem_support_iff.mp hn, ZeroMemClass.coe_zero, map_zero]]
  exact reesAlgebra.component_of_mem (x n).2

end Components

section Instances

variable (I : Ideal R)

/-- `1 = 1 · t⁰` has degree `0`, and the product `c tⁱ · d tʲ = cd tⁱ⁺ʲ` of elements of degrees
`i` and `j` has degree `i + j` (`Polynomial.monomial_mul_monomial`). -/
instance reesAlgebra.gradedMonoid : SetLike.GradedMonoid (reesAlgebra.grading I) where
  one_mem := reesAlgebra.mem_grading_of_coe_eq_monomial (c := (1 : R)) (by simp)
  mul_mem := fun {i j p q} hp hq => by
    obtain ⟨c, -, hc⟩ := reesAlgebra.mem_grading_iff_exists.mp hp
    obtain ⟨d, -, hd⟩ := reesAlgebra.mem_grading_iff_exists.mp hq
    exact reesAlgebra.mem_grading_of_coe_eq_monomial (c := c * d)
      (by rw [Subalgebra.coe_mul, hc, hd, monomial_mul_monomial])

/-- `reesAlgebra I` is the internal direct sum of its pieces [Hau14, Definition 4.6].
Independence is `reesAlgebra.component_coeAddMonoidHom` (compare coefficients); spanning is
`Polynomial.as_sum_support`, each monomial `monomial i (coeff i p)` lying in the `i`-th piece by
`reesAlgebra.monomial_mem`. -/
theorem reesAlgebra.isInternal_grading : DirectSum.IsInternal (reesAlgebra.grading I) := by
  classical
  refine ⟨fun x y hxy => DirectSum.ext fun n => ?_, fun p => ?_⟩
  · rw [← reesAlgebra.component_coeAddMonoidHom x n,
      ← reesAlgebra.component_coeAddMonoidHom y n, hxy]
  · refine ⟨∑ n ∈ (p : R[X]).support, DirectSum.of (fun i => reesAlgebra.grading I i) n
      (reesAlgebra.component I n p), ?_⟩
    rw [map_sum]
    simp_rw [DirectSum.coeAddMonoidHom_of]
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (as_sum_support (p : R[X])).symm

/-- **The grading on the Rees algebra**, `reesAlgebra I = ⨁ᵢ Iⁱ tⁱ` as a graded `R`-algebra
[Hau14, Definition 4.6], from Mathlib's constructor `DirectSum.IsInternal.gradedAlgebra` applied
to `reesAlgebra.isInternal_grading`. -/
noncomputable instance reesAlgebra.gradedAlgebra : GradedAlgebra (reesAlgebra.grading I) :=
  (reesAlgebra.isInternal_grading I).gradedAlgebra

end Instances

end Grading

section DegreeZero

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- Degree zero consists of the constant polynomials [Hau14, Definition 4.6]. -/
theorem reesAlgebra.mem_grading_zero_iff {p : reesAlgebra I} :
    p ∈ reesAlgebra.grading I 0 ↔ ∃ r : R, (p : R[X]) = C r := by
  constructor
  · intro hp
    exact ⟨_, (reesAlgebra.eq_monomial_of_mem_grading hp).1.trans (monomial_zero_left (a := _))⟩
  · rintro ⟨r, hr⟩
    exact reesAlgebra.mem_grading_of_coe_eq_monomial (hr.trans (monomial_zero_left (a := r)).symm)

/-- The constant `r · t⁰` has degree zero. -/
theorem reesAlgebra.algebraMap_mem_grading_zero (r : R) :
    algebraMap R (reesAlgebra I) r ∈ reesAlgebra.grading I 0 :=
  reesAlgebra.mem_grading_zero_iff.mpr ⟨r, by rw [Subalgebra.coe_algebraMap, algebraMap_eq]⟩

variable (I)

/-- **Degree zero is `R`** [Hau14, Definition 4.6]: `R` embeds into the Rees algebra by sending
`g` to the degree-zero element `g · t⁰`.  An element of degree zero is the constant polynomial of
its constant coefficient, and `r ∈ R` goes to the constant `algebraMap R (reesAlgebra I) r`.  The
compatibility with the grading-induced algebra structure is
`reesAlgebra.algebraMap_gradingZeroEquiv_symm`. -/
noncomputable def reesAlgebra.gradingZeroEquiv : reesAlgebra.grading I 0 ≃+* R where
  toFun p := ((p : reesAlgebra I) : R[X]).coeff 0
  invFun r := ⟨algebraMap R (reesAlgebra I) r, reesAlgebra.algebraMap_mem_grading_zero r⟩
  left_inv p := Subtype.ext <| Subtype.ext <| by
    obtain ⟨r, hr⟩ := reesAlgebra.mem_grading_zero_iff.mp p.2
    change ((algebraMap R (reesAlgebra I) (((p : reesAlgebra I) : R[X]).coeff 0) :
      reesAlgebra I) : R[X]) = ((p : reesAlgebra I) : R[X])
    rw [Subalgebra.coe_algebraMap, algebraMap_eq, hr, coeff_C_zero]
  right_inv r := by
    change ((algebraMap R (reesAlgebra I) r : reesAlgebra I) : R[X]).coeff 0 = r
    rw [Subalgebra.coe_algebraMap, algebraMap_eq, coeff_C_zero]
  map_mul' p q := by
    change (((p : reesAlgebra I) * q : reesAlgebra I) : R[X]).coeff 0 = _
    rw [Subalgebra.coe_mul, mul_coeff_zero]
  map_add' p q := by
    change (((p : reesAlgebra I) + q : reesAlgebra I) : R[X]).coeff 0 = _
    rw [Subalgebra.coe_add, coeff_add]

end DegreeZero

section GradedMap

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The graded ring map `Rees(I) → Rees(J)` induced by `φ : R →+* S` when `φ(I) ⊆ J`:
`∑ pₙ tⁿ ↦ ∑ φ(pₙ) tⁿ` [Sta, Tag 01OF]. -/
noncomputable def reesAlgebra.mapOfLe (φ : R →+* S) {I : Ideal R} {J : Ideal S}
    (hIJ : I.map φ ≤ J) : reesAlgebra.grading I →+*ᵍ reesAlgebra.grading J where
  toRingHom := (Polynomial.mapRingHom φ).restrict (reesAlgebra I) (reesAlgebra J) fun p hp n => by
    rw [coe_mapRingHom, coeff_map]
    have := Ideal.mem_map_of_mem φ (hp n)
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hIJ n this
  map_mem := fun {i p} hp j hj => by
    change ((p : R[X]).map φ).coeff j = 0
    rw [coeff_map, reesAlgebra.coeff_eq_zero_of_mem_grading hp hj, map_zero]

end GradedMap
