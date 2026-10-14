/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Weierstrass.Basic
public import Hironaka.Analytic.Weierstrass.Exponents
import Hironaka.Analytic.Weierstrass.Poly

/-!
# Series of bounded degree in the distinguished variable, and polynomials over the tail ring

Freitag writes `𝒪_{n−1}[z_n : m]` for the polynomials in `z_n` over `𝒪_{n−1}` of degree `< m`, a
free `𝒪_{n−1}`-module with basis `1, z_n, …, z_n^{m−1}` [Fre17, Ch. I, §10]. With the
distinguished variable `x_0` of the Weierstrass theory (`splitFirst`, `liftTail`,
`weierstrassPoly`), a series `f` in `m + 1` variables has *`x_0`-degree `< N`* (`DegLt N f`) if
`coeff ν f = 0` whenever `N ≤ ν 0`, the remainder condition of the Weierstrass division theorems.
This module collects:

* the algebra of `DegLt` (sums, products with the additive bound, tail series, `X 0`-powers,
  Weierstrass polynomials);
* the correspondence `ofPoly P := splitFirst⁻¹ (P : PowerSeries A)`, `A = MvPowerSeries (Fin m) K`
  the tail ring: polynomials in `x_0` over the tail ring as series,
  `weierstrassPoly e c = ofPoly (weierstrassPolynomial e c)`, and a series of `x_0`-degree `< N`
  is `ofPoly` of its truncation;
* a monic polynomial in `x_0` of degree `e` (a `weierstrassPoly e c` without the vanishing
  condition on `c`) is `x_0`-regular of some order `d' ≤ e` (`exists_isRegularIn_weierstrassPoly`):
  the "normalized polynomials" of Oka's lemma are regular, so the Weierstrass theorems apply to
  them.

Every statement is bookkeeping for Oka's lemma (`Lemma.lean`) and for the polynomial sections of
the coherence theorem (`Hironaka/AnalyticSpace/Oka`).
-/

@[expose] public section

open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- `f` has `x_0`-degree `< N`: every monomial with `x_0`-exponent `≥ N` has coefficient `0`. -/
def DegLt (N : ℕ) (f : MvPowerSeries (Fin (m + 1)) K) : Prop :=
  ∀ ν : Fin (m + 1) →₀ ℕ, N ≤ ν 0 → coeff ν f = 0

namespace DegLt

theorem mono {N N' : ℕ} (h : N ≤ N') {f : MvPowerSeries (Fin (m + 1)) K} (hf : DegLt N f) :
    DegLt N' f :=
  fun ν hν => hf ν (h.trans hν)

theorem zero (N : ℕ) : DegLt N (0 : MvPowerSeries (Fin (m + 1)) K) := fun _ _ => by simp

theorem add {N : ℕ} {f g : MvPowerSeries (Fin (m + 1)) K} (hf : DegLt N f) (hg : DegLt N g) :
    DegLt N (f + g) := fun ν hν => by
  rw [map_add, hf ν hν, hg ν hν, add_zero]

theorem neg {N : ℕ} {f : MvPowerSeries (Fin (m + 1)) K} (hf : DegLt N f) : DegLt N (-f) :=
  fun ν hν => by rw [map_neg, hf ν hν, neg_zero]

theorem sub {N : ℕ} {f g : MvPowerSeries (Fin (m + 1)) K} (hf : DegLt N f) (hg : DegLt N g) :
    DegLt N (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem sum {N : ℕ} {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries (Fin (m + 1)) K}
    (hf : ∀ i ∈ s, DegLt N (f i)) : DegLt N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using DegLt.zero N
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The `x_0`-degrees add under multiplication (`< a` and `< b` give `< a + b`; the sharp form
`< a + b − 1` is `mul_succ`). -/
theorem mul {a b : ℕ} {f g : MvPowerSeries (Fin (m + 1)) K} (hf : DegLt a f) (hg : DegLt b g) :
    DegLt (a + b) (f * g) := by
  classical
  intro ν hν
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hμ' : μ.1 + μ.2 = ν := Finset.HasAntidiagonal.mem_antidiagonal.mp hμ
  have hsum : μ.1 0 + μ.2 0 = ν 0 := by rw [← hμ']; rfl
  by_cases h1 : a ≤ μ.1 0
  · rw [hf _ h1, zero_mul]
  · have h2 : b ≤ μ.2 0 := by omega
    rw [hg _ h2, mul_zero]

/-- The sharp form: degrees `≤ a` and `≤ b` give degree `≤ a + b`. -/
theorem mul_succ {a b : ℕ} {f g : MvPowerSeries (Fin (m + 1)) K} (hf : DegLt (a + 1) f)
    (hg : DegLt (b + 1) g) : DegLt (a + b + 1) (f * g) := by
  classical
  intro ν hν
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hμ' : μ.1 + μ.2 = ν := Finset.HasAntidiagonal.mem_antidiagonal.mp hμ
  have hsum : μ.1 0 + μ.2 0 = ν 0 := by rw [← hμ']; rfl
  by_cases h1 : a + 1 ≤ μ.1 0
  · rw [hf _ h1, zero_mul]
  · have h2 : b + 1 ≤ μ.2 0 := by omega
    rw [hg _ h2, mul_zero]

/-- A series of `x_0`-degree `< 1` (a tail series) times a series of `x_0`-degree `< N`. -/
theorem one_mul {N : ℕ} {f g : MvPowerSeries (Fin (m + 1)) K} (hf : DegLt 1 f) (hg : DegLt N g) :
    DegLt N (f * g) := by
  classical
  intro ν hν
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hμ' : μ.1 + μ.2 = ν := Finset.HasAntidiagonal.mem_antidiagonal.mp hμ
  have hsum : μ.1 0 + μ.2 0 = ν 0 := by rw [← hμ']; rfl
  by_cases h1 : 1 ≤ μ.1 0
  · rw [hf _ h1, zero_mul]
  · have h2 : N ≤ μ.2 0 := by omega
    rw [hg _ h2, mul_zero]

theorem smul {N : ℕ} (c : K) {f : MvPowerSeries (Fin (m + 1)) K} (hf : DegLt N f) :
    DegLt N (c • f) := fun ν hν => by
  rw [MvPowerSeries.coeff_smul, hf ν hν, mul_zero]

end DegLt

theorem degLt_liftTail (c : MvPowerSeries (Fin m) K) :
    DegLt 1 (liftTail c : MvPowerSeries (Fin (m + 1)) K) := by
  intro ν hν
  rw [← Finsupp.cons_tail ν, coeff_cons_liftTail]
  rw [ite_eq_right]
  omega

theorem degLt_X_zero_pow (k : ℕ) : DegLt (k + 1) ((X 0 : MvPowerSeries (Fin (m + 1)) K) ^ k) := by
  intro ν hν
  rw [← Finsupp.cons_tail ν, coeff_cons_X_pow]
  rw [ite_eq_right]
  intro h
  have := h.1
  omega

/-- A monic polynomial in `x_0` of degree `e` with tail coefficients has `x_0`-degree `< e + 1`. -/
theorem degLt_weierstrassPoly (e : ℕ) (c : Fin e → MvPowerSeries (Fin m) K) :
    DegLt (e + 1) (weierstrassPoly e c : MvPowerSeries (Fin (m + 1)) K) := by
  unfold weierstrassPoly
  refine (degLt_X_zero_pow e).add (DegLt.sum _ fun j _ => ?_)
  have := (degLt_liftTail (c j)).one_mul (degLt_X_zero_pow (e - 1 - (j : ℕ)))
  exact this.mono (by omega)

/-- `DegLt` through the split of the first variable: the coefficients of `x_0^k`, `k ≥ N`, vanish.
-/
theorem degLt_iff_splitFirst {N : ℕ} {f : MvPowerSeries (Fin (m + 1)) K} :
    DegLt N f ↔ ∀ k, N ≤ k → PowerSeries.coeff k (splitFirst K m f) = 0 := by
  constructor
  · intro hf k hk
    exact coeff_splitFirst_eq_zero_of_le hf hk
  · intro h ν hν
    have h2 := congrArg (fun φ => MvPowerSeries.coeff (Finsupp.tail ν) φ) (h (ν 0) hν)
    simp only [MvPowerSeries.coeff_coeff_finSuccEquiv, Finsupp.cons_tail] at h2
    rw [h2]
    exact map_zero _

section PolyBridge

/-- Polynomials in `x_0` over the tail ring `A = 𝒪_{n−1}`, as series in all variables: the ring
homomorphism
`A[X] → 𝒪_n`, `X ↦ x_0`, `C a ↦ liftTail a`. -/
noncomputable def ofPolyHom :
    Polynomial (MvPowerSeries (Fin m) K) →+* MvPowerSeries (Fin (m + 1)) K :=
  ((splitFirst K m).symm :
      PowerSeries (MvPowerSeries (Fin m) K) ≃+* MvPowerSeries (Fin (m + 1)) K).toRingHom.comp
    Polynomial.coeToPowerSeries.ringHom

/-- The tail ring `A = 𝒪_{n−1}`-side polynomial `P` in `x_0`, as a series in all variables. -/
noncomputable def ofPoly (P : Polynomial (MvPowerSeries (Fin m) K)) :
    MvPowerSeries (Fin (m + 1)) K :=
  ofPolyHom P

theorem ofPoly_def (P : Polynomial (MvPowerSeries (Fin m) K)) :
    ofPoly P = (splitFirst K m).symm (P : PowerSeries (MvPowerSeries (Fin m) K)) := rfl

theorem splitFirst_ofPoly (P : Polynomial (MvPowerSeries (Fin m) K)) :
    splitFirst K m (ofPoly P) = (P : PowerSeries (MvPowerSeries (Fin m) K)) :=
  (splitFirst K m).apply_symm_apply _

theorem ofPoly_add (P Q : Polynomial (MvPowerSeries (Fin m) K)) :
    ofPoly (P + Q) = ofPoly P + ofPoly Q := map_add ofPolyHom P Q

theorem ofPoly_mul (P Q : Polynomial (MvPowerSeries (Fin m) K)) :
    ofPoly (P * Q) = ofPoly P * ofPoly Q := map_mul ofPolyHom P Q

theorem ofPoly_neg (P : Polynomial (MvPowerSeries (Fin m) K)) : ofPoly (-P) = -ofPoly P :=
  map_neg ofPolyHom P

theorem ofPoly_zero : ofPoly (0 : Polynomial (MvPowerSeries (Fin m) K)) = 0 := map_zero ofPolyHom

theorem ofPoly_one : ofPoly (1 : Polynomial (MvPowerSeries (Fin m) K)) = 1 := map_one ofPolyHom

theorem ofPoly_pow (P : Polynomial (MvPowerSeries (Fin m) K)) (k : ℕ) :
    ofPoly (P ^ k) = ofPoly P ^ k := map_pow ofPolyHom P k

theorem ofPoly_sum {ι : Type*} (s : Finset ι) (P : ι → Polynomial (MvPowerSeries (Fin m) K)) :
    ofPoly (∑ i ∈ s, P i) = ∑ i ∈ s, ofPoly (P i) := map_sum ofPolyHom P s

theorem ofPoly_X : ofPoly (Polynomial.X : Polynomial (MvPowerSeries (Fin m) K)) = X 0 := by
  rw [ofPoly_def, Polynomial.coe_X, ← splitFirst_X_zero, (splitFirst K m).symm_apply_apply]

theorem ofPoly_C (a : MvPowerSeries (Fin m) K) : ofPoly (Polynomial.C a) = liftTail a := by
  rw [ofPoly_def, Polynomial.coe_C, ← splitFirst_liftTail, (splitFirst K m).symm_apply_apply]

theorem ofPoly_weierstrassPolynomial (e : ℕ) (c : Fin e → MvPowerSeries (Fin m) K) :
    ofPoly (weierstrassPolynomial e c) = weierstrassPoly e c := by
  rw [ofPoly_def, ← splitFirst_weierstrassPoly, (splitFirst K m).symm_apply_apply]

/-- `ofPoly P` has `x_0`-degree `< natDegree P + 1`. -/
theorem degLt_ofPoly (P : Polynomial (MvPowerSeries (Fin m) K)) :
    DegLt (P.natDegree + 1) (ofPoly P) := by
  rw [degLt_iff_splitFirst, splitFirst_ofPoly]
  intro k hk
  rw [Polynomial.coeff_coe]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- `ofPoly` of a polynomial of degree `< N` (as a natural-number bound) has `x_0`-degree `< N`. -/
theorem degLt_ofPoly_of_natDegree_lt {N : ℕ} {P : Polynomial (MvPowerSeries (Fin m) K)}
    (hP : P.natDegree < N) : DegLt N (ofPoly P) :=
  (degLt_ofPoly P).mono (by omega)

/-- The truncation of a series of `x_0`-degree `< N`, as a polynomial over the tail ring. -/
noncomputable def toPoly (N : ℕ) (f : MvPowerSeries (Fin (m + 1)) K) :
    Polynomial (MvPowerSeries (Fin m) K) :=
  PowerSeries.trunc N (splitFirst K m f)

theorem ofPoly_toPoly {N : ℕ} {f : MvPowerSeries (Fin (m + 1)) K} (hf : DegLt N f) :
    ofPoly (toPoly N f) = f := by
  rw [ofPoly_def, toPoly, ← splitFirst_eq_trunc hf, (splitFirst K m).symm_apply_apply]

theorem natDegree_toPoly_lt (N : ℕ) (f : MvPowerSeries (Fin (m + 1)) K) (hN : 0 < N) :
    (toPoly N f).natDegree < N := by
  unfold toPoly
  have := PowerSeries.degree_trunc_lt (splitFirst K m f) N
  rcases eq_or_ne (PowerSeries.trunc N (splitFirst K m f)) 0 with h | h
  · rw [h, Polynomial.natDegree_zero]; exact hN
  · exact Polynomial.natDegree_lt_iff_degree_lt h |>.2 this

end PolyBridge

section Monic

/-- A "normalized polynomial" in the sense of [Fre17, Ch. I, §10], `ofPoly Q` for a monic `Q` in
`x_0` over the tail ring, is `x_0`-regular of some order `d' ≤ natDegree Q` (the order of `Q` with
its coefficients reduced modulo the maximal ideal), so the Weierstrass division and preparation
theorems apply to it. -/
theorem exists_isRegularIn_ofPoly {Q : Polynomial (MvPowerSeries (Fin m) K)} (hQ : Q.Monic) :
    ∃ d' : ℕ, d' ≤ Q.natDegree ∧ IsRegularIn (ofPoly Q) d' := by
  set φ := (splitFirst K m (ofPoly Q)).map (IsLocalRing.residue (MvPowerSeries (Fin m) K)) with hφ
  have hcoe : PowerSeries.coeff Q.natDegree φ ≠ 0 := by
    rw [hφ, PowerSeries.coeff_map, splitFirst_ofPoly, Polynomial.coeff_coe, hQ.coeff_natDegree,
      map_one]
    exact one_ne_zero
  have hle : φ.order ≤ Q.natDegree := PowerSeries.order_le _ hcoe
  have hne : φ.order ≠ ⊤ := ne_top_of_le_ne_top (WithTop.coe_ne_top) hle
  have hcast : (φ.order.toNat : ℕ∞) = φ.order := ENat.natCast_toNat_eq_self.mpr hne
  refine ⟨φ.order.toNat, ?_, ?_⟩
  · have : (φ.order.toNat : ℕ∞) ≤ Q.natDegree := hcast ▸ hle
    exact_mod_cast this
  · change φ.order = _
    exact hcast.symm

theorem exists_isRegularIn_weierstrassPoly (e : ℕ) (c : Fin e → MvPowerSeries (Fin m) K) :
    ∃ d' : ℕ, d' ≤ e ∧ IsRegularIn (weierstrassPoly e c : MvPowerSeries (Fin (m + 1)) K) d' := by
  obtain ⟨d', hd', hreg⟩ := exists_isRegularIn_ofPoly (monic_weierstrassPolynomial e c)
  rw [ofPoly_weierstrassPolynomial] at hreg
  rw [natDegree_weierstrassPolynomial] at hd'
  exact ⟨d', hd', hreg⟩

end Monic

end Analytic
