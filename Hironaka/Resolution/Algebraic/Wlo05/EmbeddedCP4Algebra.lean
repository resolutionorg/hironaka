/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealInf
import Hironaka.Scheme.Snc.ParameterSubset
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The algebra of one blow-up along a chain stratum

The commutative algebra of the statement CP4 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4`): what happens to a chain form under the blow-up
of a chain stratum, stated in a domain `R` — the local ring `𝒪_{B,q}` of the blow-up at a point `q`
of the exceptional divisor — with a fixed element `ε`, the exceptional coordinate of the chart.

* **The ε-orders.** After the chart substitution the `i`-th generator of a chain form is
  `ε^{E_i} · (ε-free part)` with `E_i = e₀ + ∑_{i' < i} e_{i'} + δ_i` (`epsOrder`), where `e₀` and
  `e_i` are the ε-orders of the top monomial and of the level monomials, and `δ_i ∈ {0, 1}`
  records whether the `i`-th chain equation is an equation of the centre
  (`span_mul_chainIdeal_pow_eq`).
* **The division by `ε`.** When every `E_i ≥ 1`, `(ε · A) : (ε) = A` in a domain
  (`colon_span_singleton_mul_self`), and when moreover `(E_i)` is non-decreasing — this is where
  the admissibility condition (★) of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAdmissibleStratum`
  enters — the telescoping `ε^{E_i − 1} = ε^{E_0 − 1} ∏_{i' < i} ε^{E_{i'+1} − E_{i'}}`
  (`sum_filter_lt_tsub`) exhibits `ε⁻¹π^*K` as a chain form with the level monomials `M'_i =
  ε^{E_{i+1} − E_i} N_i` and the top monomial `ε^{E_0 − 1} m₀` (`colon_span_mul_chainIdeal_pow`;
  `colon_span_mul_chainKIdeal_pow` for the K-shape, whose last equation is `1`).
* **Saturation** (the strict transforms): `(J : ε^∞) = P` for a prime `P ∌ ε` with
  `J ⊆ P ⊆ (J : ε^t)` (`iSup_colon_pow_span_singleton_eq_of_isPrime`), and `(J : ε^∞) = 𝒪` when a
  power of `ε` lies in `J` (`iSup_colon_pow_eq_top_of_pow_mem`: in the chart of a chain equation
  `f_l` the strict transform of `Γ` is missed).
* **Units** drop from chain forms (`chainIdeal_isUnit_mul`: the ratio coordinates of the members
  whose strict transform misses `q`).
* **Coordinate primes.** A monomial in a regular system of parameters lies in the prime
  `(z_k : k ∈ t)` iff one of its coordinates with positive exponent is in `t`
  (`monomialOf_mem_span_image_iff`), whence the characterisation of `K ≤ Z` as the cumulative
  condition (`span_mul_chainKIdeal_le_stratum_iff`).
* **A chain equation that is a unit** makes the un-isolated chain form and the K-shape coincide
  (`chainIdeal_eq_chainKIdeal_of_isUnit`).

The chart is that of [Kol07, Definition 60] (the local coordinates in which the blow-up is
monomial). The identities are elementary and not taken from the literature; the scheme-level
statements are in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Chart`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4NewCoords` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4`.
-/

@[expose] public section

universe u

open Ideal IsLocalRing

namespace Hironaka.Resolution

/-! ### Monomials -/

section Monomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A monomial in a pointwise product of two coordinate families is the product of the monomials. -/
theorem monomialOf_mul (u v : Fin n → R) (a : Fin n → ℕ) :
    monomialOf (fun k => u k * v k) a = monomialOf u a * monomialOf v a := by
  unfold monomialOf
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => mul_pow _ _ _

/-- The monomial in the family which is `ε` on `C` and `1` off `C` is `ε` to the total exponent
on `C`. -/
theorem monomialOf_ite_mem (ε : R) (C : Finset (Fin n)) (a : Fin n → ℕ) :
    monomialOf (fun k => if k ∈ C then ε else 1) a = ε ^ ∑ k ∈ C, a k := by
  unfold monomialOf
  rw [← Finset.prod_pow_eq_pow_sum]
  refine (Finset.prod_subset C.subset_univ fun k _ hk => ?_).symm.trans
    (Finset.prod_congr rfl fun k hk => ?_)
  · simp [hk]
  · simp [hk]

/-- A monomial in units is a unit. -/
theorem isUnit_monomialOf {u : Fin n → R} (hu : ∀ k, IsUnit (u k)) (a : Fin n → ℕ) :
    IsUnit (monomialOf u a) := by
  choose v hv using hu
  have : monomialOf u a = ↑(∏ k, v k ^ a k) := by
    rw [Units.coe_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [Units.val_pow_eq_pow_val, hv k]
  rw [this]
  exact Units.isUnit _

/-- A product of units is a unit. -/
theorem isUnit_prod_of_forall_isUnit {ι : Type*} (s : Finset ι) {u : ι → R}
    (hu : ∀ i, IsUnit (u i)) : IsUnit (∏ i ∈ s, u i) := by
  choose v hv using hu
  have : ∏ i ∈ s, u i = ↑(∏ i ∈ s, v i) := by
    rw [Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => (hv i).symm
  rw [this]
  exact Units.isUnit _

end Monomial

/-! ### Chain generators after the chart substitution -/

section Core

variable {R : Type*} [CommRing R] {r : ℕ}

/-- `span {x} · span (range g) = span (range (x · g))`. -/
theorem span_singleton_mul_span_range {ι : Type*} (x : R) (g : ι → R) :
    span {x} * span (Set.range g) = span (Set.range fun i => x * g i) := by
  rw [span_mul_span, Set.singleton_mul, ← Set.range_comp]
  rfl

/-- Units multiplying the level monomials do not change the chain ideal. -/
theorem chainIdeal_isUnit_mul (φ M : Fin r → R) {u : Fin r → R} (hu : ∀ i, IsUnit (u i)) :
    chainIdeal φ (fun i => u i * M i) = chainIdeal φ M := by
  rw [chainIdeal_eq_span_range_chainGen, chainIdeal_eq_span_range_chainGen]
  have key : ∀ i, chainGen φ (fun i => u i * M i) i =
      (∏ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), u i') * chainGen φ M i := by
    intro i
    unfold chainGen
    rw [Finset.prod_mul_distrib, mul_assoc]
  have hunit : ∀ i, IsUnit (∏ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), u i') :=
    fun i => isUnit_prod_of_forall_isUnit _ hu
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨i, rfl⟩
    rw [key]
    exact mul_mem_left _ _ (subset_span ⟨i, rfl⟩)
  · rw [span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨w, hw⟩ := hunit i
    have : chainGen φ M i = ↑w⁻¹ * chainGen φ (fun i => u i * M i) i := by
      rw [key, ← hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact mul_mem_left _ _ (subset_span ⟨i, rfl⟩)

/-- Units multiplying the level monomials do not change the K-shape. -/
theorem chainKIdeal_isUnit_mul (φ M : Fin (r + 1) → R) {u : Fin (r + 1) → R}
    (hu : ∀ i, IsUnit (u i)) : chainKIdeal φ (fun i => u i * M i) = chainKIdeal φ M :=
  chainIdeal_isUnit_mul _ M hu

/-- The `i`-th chain generator after the substitution `f_i ↦ ε^{δ_i} φ_i`, `M_i ↦ ε^{e_i} N_i`
carries `ε` to the power `∑_{i' < i} e_{i'} + δ_i`. -/
theorem chainGen_pow_mul (ε : R) (δ e : Fin r → ℕ) (φ N : Fin r → R) (i : Fin r) :
    chainGen (fun i => ε ^ δ i * φ i) (fun i => ε ^ e i * N i) i =
      ε ^ ((∑ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), e i') + δ i) *
        chainGen φ N i := by
  unfold chainGen
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add]
  ring

/-- The `i`-th chain generator with level monomials `ε^{e_i} N_i` carries
`ε^{∑_{i' < i} e_{i'}}`. -/
theorem chainGen_pow_mul_left (ε : R) (e : Fin r → ℕ) (φ N : Fin r → R) (i : Fin r) :
    chainGen φ (fun i => ε ^ e i * N i) i =
      ε ^ (∑ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), e i') * chainGen φ N i := by
  unfold chainGen
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- The ε-order `E_i = e₀ + ∑_{i' < i} e_{i'} + δ_i` of the `i`-th pulled-back chain generator
(`e₀` the ε-order of the top monomial, `e_{i'}` those of the level monomials, `δ_i` that of the
`i`-th chain equation). -/
def epsOrder (e₀ : ℕ) (e δ : Fin r → ℕ) (i : Fin r) : ℕ :=
  e₀ + (∑ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), e i') + δ i

/-- The pulled-back chain form is generated by `ε^{E_i} · m₀ · (∏_{i' < i} N_{i'}) φ_i`. -/
theorem span_mul_chainIdeal_pow_eq (ε m₀ : R) (e₀ : ℕ) (δ e : Fin r → ℕ) (φ N : Fin r → R) :
    span {ε ^ e₀ * m₀} * chainIdeal (fun i => ε ^ δ i * φ i) (fun i => ε ^ e i * N i) =
      span (Set.range fun i => ε ^ epsOrder e₀ e δ i * (m₀ * chainGen φ N i)) := by
  rw [chainIdeal_eq_span_range_chainGen, span_singleton_mul_span_range]
  congr 1
  refine congrArg Set.range (funext fun i => ?_)
  rw [chainGen_pow_mul, epsOrder, pow_add, pow_add]
  ring

/-- In a domain, `(ε · J) : (ε) = J` for `ε ≠ 0`. -/
theorem colon_span_singleton_mul_self [IsDomain R] {ε : R} (hε : ε ≠ 0) (J : Ideal R) :
    (span {ε} * J).colon (span {ε}) = J := by
  ext x
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul, mem_span_singleton_mul]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have : z = x := mul_left_cancel₀ hε (hzx.trans (mul_comm _ _))
    exact this ▸ hz
  · intro hx
    exact ⟨x, hx, mul_comm _ _⟩

/-- The telescoping sum of the increments of a non-decreasing sequence on `Fin (r + 1)`. -/
theorem sum_filter_lt_tsub (E D : Fin (r + 1) → ℕ)
    (hmono : ∀ i : Fin r, E i.castSucc ≤ E i.succ)
    (hD : ∀ i : Fin r, D i.castSucc = E i.succ - E i.castSucc) (i : Fin (r + 1)) :
    ∑ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i), D i' = E i - E 0 := by
  have hmon : Monotone E := Fin.monotone_iff_le_succ.mpr hmono
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have hfilt : Finset.univ.filter (fun i' : Fin (r + 1) => i' < i.succ) =
        insert i.castSucc (Finset.univ.filter (fun i' : Fin (r + 1) => i' < i.castSucc)) := by
      ext i'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.lt_def, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
      omega
    have hnot : i.castSucc ∉ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i.castSucc) := by
      simp
    rw [hfilt, Finset.sum_insert hnot, ih, hD i]
    have h1 := hmon (Fin.zero_le i.castSucc)
    have h2 := hmono i
    omega

/-- A non-decreasing sequence on `Fin (r + 1)` is bounded below by its first value. -/
theorem zero_le_of_forall_castSucc_le_succ (E : Fin (r + 1) → ℕ)
    (hmono : ∀ i : Fin r, E i.castSucc ≤ E i.succ) (i : Fin (r + 1)) : E 0 ≤ E i :=
  (Fin.monotone_iff_le_succ.mpr hmono) (Fin.zero_le i)

/-- **The division by `ε`, the algebraic core of CP4**: in a domain, when the ε-orders `E_i` of
the pulled-back chain generators are `≥ 1` and non-decreasing (the content of the admissibility
condition (★)), the colon by `(ε)` of the pulled-back chain form is again a chain form: the same
equations `φ`, level monomials `ε^{E_{i+1} − E_i} N_i` (recorded as `D`) and top monomial
`ε^{E_0 − 1} m₀` — the telescoping `ε^{E_i − 1} = ε^{E_0 − 1} ∏_{i' < i} ε^{E_{i'+1} − E_{i'}}`. -/
theorem colon_span_mul_chainIdeal_pow [IsDomain R] {ε : R} (hε : ε ≠ 0) (m₀ : R) (e₀ : ℕ)
    (δ e : Fin (r + 1) → ℕ) (φ N : Fin (r + 1) → R) (hpos : 1 ≤ epsOrder e₀ e δ 0)
    (hmono : ∀ i : Fin r, epsOrder e₀ e δ i.castSucc ≤ epsOrder e₀ e δ i.succ)
    (D : Fin (r + 1) → ℕ)
    (hD : ∀ i : Fin r, D i.castSucc = epsOrder e₀ e δ i.succ - epsOrder e₀ e δ i.castSucc) :
    (span {ε ^ e₀ * m₀} *
        chainIdeal (fun i => ε ^ δ i * φ i) (fun i => ε ^ e i * N i)).colon (span {ε}) =
      span {ε ^ (epsOrder e₀ e δ 0 - 1) * m₀} * chainIdeal φ (fun i => ε ^ D i * N i) := by
  set E := epsOrder e₀ e δ with hE
  have hle : ∀ i, E 0 ≤ E i := zero_le_of_forall_castSucc_le_succ E hmono
  -- the pulled-back form is `ε` times the target
  have hfactor : span {ε ^ e₀ * m₀} *
      chainIdeal (fun i => ε ^ δ i * φ i) (fun i => ε ^ e i * N i) =
        span {ε} * (span {ε ^ (E 0 - 1) * m₀} * chainIdeal φ (fun i => ε ^ D i * N i)) := by
    rw [span_mul_chainIdeal_pow_eq, chainIdeal_eq_span_range_chainGen,
      span_singleton_mul_span_range, span_singleton_mul_span_range]
    congr 1
    refine congrArg Set.range (funext fun i => ?_)
    rw [chainGen_pow_mul_left, sum_filter_lt_tsub E D hmono hD i]
    have h1 := hpos
    have h2 := hle i
    calc ε ^ E i * (m₀ * chainGen φ N i)
        = ε ^ (1 + (E 0 - 1) + (E i - E 0)) * (m₀ * chainGen φ N i) := by
          congr 2
          omega
      _ = ε * (ε ^ (E 0 - 1) * m₀ * (ε ^ (E i - E 0) * chainGen φ N i)) := by
          rw [pow_add, pow_add, pow_one]
          ring
  rw [hfactor, colon_span_singleton_mul_self hε]

/-- The K-shape substitution: the last equation `1` is untouched. -/
theorem update_pow_mul_last (ε : R) (δ : Fin (r + 1) → ℕ) (φ : Fin (r + 1) → R) :
    Function.update (fun i => ε ^ δ i * φ i) (Fin.last r) 1 =
      fun i => ε ^ Function.update δ (Fin.last r) 0 i * Function.update φ (Fin.last r) 1 i := by
  funext i
  by_cases hi : i = Fin.last r
  · subst hi
    simp
  · simp [Function.update_of_ne hi]

/-- The division by `ε` for the K-shape: the colon by `(ε)` of the pulled-back K-shape is the
K-shape with the new monomials, the ε-orders being those with `δ_r = 0` for the last generator
(which carries no equation). -/
theorem colon_span_mul_chainKIdeal_pow [IsDomain R] {ε : R} (hε : ε ≠ 0) (m₀ : R) (e₀ : ℕ)
    (δ e : Fin (r + 1) → ℕ) (φ N : Fin (r + 1) → R)
    (hpos : 1 ≤ epsOrder e₀ e (Function.update δ (Fin.last r) 0) 0)
    (hmono : ∀ i : Fin r, epsOrder e₀ e (Function.update δ (Fin.last r) 0) i.castSucc ≤
      epsOrder e₀ e (Function.update δ (Fin.last r) 0) i.succ)
    (D : Fin (r + 1) → ℕ)
    (hD : ∀ i : Fin r, D i.castSucc = epsOrder e₀ e (Function.update δ (Fin.last r) 0) i.succ -
      epsOrder e₀ e (Function.update δ (Fin.last r) 0) i.castSucc) :
    (span {ε ^ e₀ * m₀} *
        chainKIdeal (fun i => ε ^ δ i * φ i) (fun i => ε ^ e i * N i)).colon (span {ε}) =
      span {ε ^ (epsOrder e₀ e (Function.update δ (Fin.last r) 0) 0 - 1) * m₀} *
        chainKIdeal φ (fun i => ε ^ D i * N i) := by
  unfold chainKIdeal
  rw [update_pow_mul_last]
  exact colon_span_mul_chainIdeal_pow hε m₀ e₀ _ e _ N hpos hmono D hD

end Core

/-! ### Saturation by a coordinate -/

section Saturation

variable {R : Type*} [CommRing R]

/-- `(J : ε^∞) = P` for a prime `P ∌ ε` with `J ⊆ P` and `P · ε^t ⊆ J`: the strict transform of a
coordinate subspace through the centre. -/
theorem iSup_colon_pow_span_singleton_eq_of_isPrime {J P : Ideal R} (hP : P.IsPrime) {ε : R}
    (hε : ε ∉ P) (hJP : J ≤ P) {t : ℕ} (hPJ : ∀ x ∈ P, x * ε ^ t ∈ J) :
    ⨆ i : ℕ, J.colon ((span {ε} ^ i : Ideal R) : Set R) = P := by
  apply le_antisymm
  · refine iSup_le fun i x hx => ?_
    rw [span_singleton_pow, Submodule.mem_colon_span_singleton, smul_eq_mul] at hx
    exact (hP.mem_or_mem (hJP hx)).resolve_right fun h => hε (hP.mem_of_pow_mem _ h)
  · refine le_iSup_of_le t fun x hx => ?_
    rw [span_singleton_pow, Submodule.mem_colon_span_singleton, smul_eq_mul]
    exact hPJ x hx

/-- `(J : ε^∞) = 𝒪` when a power of `ε` lies in `J` (the charts of the chain equations `f_l`, where
the exceptional coordinate is a pulled-back equation of the strict transform's centre). -/
theorem iSup_colon_pow_eq_top_of_pow_mem {J : Ideal R} {ε : R} {t : ℕ} (hJ : ε ^ t ∈ J) :
    ⨆ i : ℕ, J.colon ((span {ε} ^ i : Ideal R) : Set R) = ⊤ := by
  refine eq_top_iff.mpr (le_iSup_of_le t fun x _ => ?_)
  rw [span_singleton_pow, Submodule.mem_colon_span_singleton, smul_eq_mul]
  exact J.mul_mem_left x hJ

/-- `((w ε^t) : ε^∞) = (w)` for a prime element `w` not dividing `ε` (the strict transform of a
member through the centre). -/
theorem iSup_colon_pow_span_singleton_mul_pow {w ε : R} (hw : Prime w)
    (hε : ε ∉ span {w}) (t : ℕ) :
    ⨆ i : ℕ, (span {w * ε ^ t}).colon ((span {ε} ^ i : Ideal R) : Set R) = span {w} := by
  refine iSup_colon_pow_span_singleton_eq_of_isPrime
    ((span_singleton_prime hw.ne_zero).mpr hw) hε ?_ (t := t) fun x hx => ?_
  · rw [span_singleton_le_span_singleton]
    exact dvd_mul_right _ _
  · obtain ⟨c, rfl⟩ := mem_span_singleton'.mp hx
    exact mem_span_singleton'.mpr ⟨c, by ring⟩

end Saturation

/-! ### Monomials in coordinate primes -/

section Regular

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
  (hz : IsLocalRing.maximalIdeal R = span (Set.range z)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)

include hz hn

/-- A monomial in a regular system of parameters lies in the coordinate prime `(z_k : k ∈ t)` iff
one of its coordinates with positive exponent lies in `t`. -/
theorem monomialOf_mem_span_image_iff (t : Finset (Fin n)) (a : Fin n → ℕ) :
    monomialOf z a ∈ span (z '' ↑t) ↔ ∃ k ∈ t, a k ≠ 0 := by
  have hP := isPrime_span_image_finset hz hn t
  constructor
  · intro h
    unfold monomialOf at h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).mp h
    refine ⟨k, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (a k) with h0 | h0
      · rw [h0, pow_zero] at hk
        exact absurd (Ideal.eq_top_iff_one _ |>.mpr hk) hP.ne_top
      · exact (AlgebraicGeometry.mem_span_image_iff hz hn t k).mp (hP.mem_of_pow_mem _ hk)
    · intro h0
      rw [h0, pow_zero] at hk
      exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr hk)
  · rintro ⟨k, hk, hak⟩
    have hdvd : z k ∣ monomialOf z a :=
      (dvd_pow_self (z k) hak).trans
        (Finset.dvd_prod_of_mem (fun k => z k ^ a k) (Finset.mem_univ k))
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, mul_comm]
    exact mul_mem_left _ _ (subset_span ⟨k, hk, rfl⟩)

/-- A monomial supported off the range of `σ` lies in the coordinate prime of `σ '' T ∪ s` iff it
lies in the coordinate prime of `s`. -/
theorem monomialOf_mem_span_image_union_iff {r : ℕ} {σ : Fin (r + 1) → Fin n}
    (T : Finset (Fin (r + 1))) (s : Finset (Fin n)) {a : Fin n → ℕ}
    (ha : ∀ k, a k ≠ 0 → k ∉ Set.range σ) :
    monomialOf z a ∈ span (z '' ↑(T.image σ ∪ s)) ↔ monomialOf z a ∈ span (z '' ↑s) := by
  rw [monomialOf_mem_span_image_iff hz hn, monomialOf_mem_span_image_iff hz hn]
  constructor
  · rintro ⟨k, hk, hak⟩
    refine ⟨k, ?_, hak⟩
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
      exact absurd ⟨i, rfl⟩ (ha _ hak)
    · exact hk
  · rintro ⟨k, hk, hak⟩
    exact ⟨k, Finset.mem_union_right _ hk, hak⟩

end Regular

section StarAlgebra

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- The characterisation of `K ≤ Z`: the K-shape lies in the ideal of the chain stratum iff the
monomial `M⁰ · M₀ ⋯ M_{l−1}` lies in `(z_s)` — the CUMULATIVE condition, weaker than the
admissibility condition (★) and not automatic; (★) implies it. -/
theorem span_mul_chainKIdeal_le_stratum_iff {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : Function.Injective σ) (s : Finset (Fin n)) (hs : ∀ i, σ i ∉ s) (b : Fin n → ℕ)
    (a : Fin (r + 1) → Fin n → ℕ) (hb : ∀ k, b k ≠ 0 → k ∉ Set.range σ)
    (ha : ∀ i k, a i k ≠ 0 → k ∉ Set.range σ) {l : ℕ} (hl : l ≤ r) :
    Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) ≤
        Ideal.span ((z ∘ σ) '' {i | i.val < l}) ⊔ Ideal.span (z '' ↑s) ↔
      monomialOf z b * ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => i.val < l),
        monomialOf z (a i) ∈ Ideal.span (z '' ↑s) := by
  classical
  have hz' : IsLocalRing.maximalIdeal R = span (Set.range z) := hz.1.symm
  have hn := hz.2
  -- the stratum's ideal is the coordinate prime of `σ '' {i < l} ∪ s`
  set T : Finset (Fin (r + 1)) := Finset.univ.filter (fun i : Fin (r + 1) => i.val < l) with hT
  have hQ : span ((z ∘ σ) '' {i | i.val < l}) ⊔ span (z '' ↑s) =
      span (z '' ↑(T.image σ ∪ s)) := by
    rw [Finset.coe_union, Finset.coe_image, Set.image_union, Ideal.span_union, Set.image_image,
      hT, Finset.coe_filter]
    simp only [Finset.mem_univ, true_and]
    rfl
  set Q := span (z '' ↑(T.image σ ∪ s)) with hQdef
  have hQP : Q.IsPrime := isPrime_span_image_finset hz' hn _
  have hsP : (span (z '' ↑s)).IsPrime := isPrime_span_image_finset hz' hn s
  have hsQ : span (z '' ↑s) ≤ Q := span_mono (Set.image_mono (by
    rw [Finset.coe_union]; exact Set.subset_union_right))
  -- the chain coordinates of index `≥ l` are not in `Q`
  have hσQ : ∀ i : Fin (r + 1), l ≤ i.val → z (σ i) ∉ Q := by
    intro i hi hmem
    have := (AlgebraicGeometry.mem_span_image_iff hz' hn _ _).mp hmem
    rcases Finset.mem_union.mp this with h | h
    · obtain ⟨i', hi', hii'⟩ := Finset.mem_image.mp h
      have := hσ hii'
      subst this
      rw [hT, Finset.mem_filter] at hi'
      omega
    · exact hs i h
  -- monomials with exponents off `σ`: membership in `Q` is membership in `(z_s)`
  have hmonoQ : ∀ (c : Fin n → ℕ), (∀ k, c k ≠ 0 → k ∉ Set.range σ) →
      (monomialOf z c ∈ Q ↔ monomialOf z c ∈ span (z '' ↑s)) :=
    fun c hc => monomialOf_mem_span_image_union_iff hz' hn T s hc
  -- the cumulative monomial `m_l = M⁰ ∏_{i < l} M_i`
  set m : R := monomialOf z b * ∏ i ∈ T, monomialOf z (a i) with hm
  have hmQ : m ∈ Q ↔ m ∈ span (z '' ↑s) := by
    rw [hm, hQP.mul_mem_iff_mem_or_mem, hsP.mul_mem_iff_mem_or_mem,
      Ideal.IsPrime.prod_mem_iff (hp := hQP), Ideal.IsPrime.prod_mem_iff (hp := hsP),
      hmonoQ b hb]
    exact or_congr Iff.rfl (exists_congr fun i => and_congr Iff.rfl (hmonoQ (a i) (ha i)))
  -- the generators
  rw [hQ, chainKIdeal, chainIdeal_eq_span_range_chainGen, span_singleton_mul_span_range, span_le,
    Set.range_subset_iff]
  have hgen : ∀ i : Fin (r + 1), monomialOf z b * chainGen (Function.update (z ∘ σ) (Fin.last r) 1)
      (fun i => monomialOf z (a i)) i = monomialOf z b *
        ((∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i), monomialOf z (a i')) *
          Function.update (z ∘ σ) (Fin.last r) 1 i) := fun i => rfl
  constructor
  · intro h
    -- the generator of index `l`
    have hlr : l < r + 1 := by omega
    have hl' := h ⟨l, hlr⟩
    rw [hgen] at hl'
    have hfilt :
        Finset.univ.filter (fun i' : Fin (r + 1) => i' < (⟨l, hlr⟩ : Fin (r + 1))) = T := by
      rw [hT]
      exact Finset.filter_congr fun i _ => by simp only [Fin.lt_def]
    rw [hfilt] at hl'
    by_cases hlt : l < r
    · have hne : (⟨l, hlr⟩ : Fin (r + 1)) ≠ Fin.last r := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      rw [Function.update_of_ne hne, Function.comp_apply, ← mul_assoc] at hl'
      have hnot := hσQ ⟨l, hlr⟩ le_rfl
      exact hmQ.mp ((hQP.mul_mem_iff_mem_or_mem.mp hl').resolve_right hnot)
    · have hlast : (⟨l, hlr⟩ : Fin (r + 1)) = Fin.last r := Fin.ext (by simp; omega)
      rw [hlast, Function.update_self, mul_one] at hl'
      exact hmQ.mp hl'
  · intro h i
    rw [hgen]
    by_cases hi : i.val < l
    · -- the equation `z (σ i)` is one of the stratum's
      have hne : i ≠ Fin.last r := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      rw [Function.update_of_ne hne]
      refine mul_mem_left _ _ (mul_mem_left _ _ (subset_span ?_))
      rw [Finset.coe_union, Finset.coe_image, Set.image_union]
      refine Set.mem_union_left _ ⟨σ i, ⟨i, ?_, rfl⟩, rfl⟩
      rw [hT, Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi⟩
    · -- the generator is a multiple of `m_l`
      push Not at hi
      have hsplit : ∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i),
          monomialOf z (a i') = (∏ i' ∈ T, monomialOf z (a i')) *
            ∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => l ≤ i'.val ∧ i' < i),
              monomialOf z (a i') := by
        rw [← Finset.prod_filter_mul_prod_filter_not
          (Finset.univ.filter (fun i' : Fin (r + 1) => i' < i)) (fun i' => i'.val < l),
          Finset.filter_filter, Finset.filter_filter]
        congr 1
        · rw [hT]
          exact Finset.prod_congr (Finset.filter_congr fun i' _ => by
            simp only [Fin.lt_def]; omega) fun _ _ => rfl
        · exact Finset.prod_congr (Finset.filter_congr fun i' _ => by
            simp only [Fin.lt_def]; omega) fun _ _ => rfl
      rw [hsplit]
      have hmQ' : m ∈ Q := hmQ.mpr h
      have heq : monomialOf z b * ((∏ i' ∈ T, monomialOf z (a i')) *
            (∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => l ≤ i'.val ∧ i' < i),
              monomialOf z (a i')) * Function.update (z ∘ σ) (Fin.last r) 1 i) =
          m * ((∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => l ≤ i'.val ∧ i' < i),
              monomialOf z (a i')) * Function.update (z ∘ σ) (Fin.last r) 1 i) := by
        rw [hm]; ring
      rw [heq]
      exact mul_mem_right _ _ hmQ'

end StarAlgebra

/-! ### The ε-orders of an admissible or terminal-normal stratum -/

section Star

variable {n r : ℕ} (σ : Fin (r + 1) → Fin n) (s : Finset (Fin n))

/-- The coordinates of the chain stratum `(f_i : i < l) + (e_j : j ∈ s)`. -/
def stratumCoords (l : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin (r + 1) => i.val < l)).image σ ∪ s

variable (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ s)

include hσ hs in
/-- A chain coordinate lies among the stratum's coordinates iff its level is below `l`. -/
theorem mem_stratumCoords_iff (l : ℕ) (i : Fin (r + 1)) :
    σ i ∈ stratumCoords σ s l ↔ i.val < l := by
  classical
  rw [stratumCoords, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨i', hi', h⟩ | h)
    · rw [Finset.mem_filter] at hi'
      rw [← hσ h]
      exact hi'.2
    · exact absurd h (hs i)
  · intro hi
    exact Or.inl ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

/-- The total exponent over the stratum's coordinates of an exponent vector supported off the chain
is its total exponent over `s`. -/
theorem sum_stratumCoords_eq (l : ℕ) (c : Fin n → ℕ) (hc : ∀ k, c k ≠ 0 → k ∉ Set.range σ) :
    ∑ k ∈ stratumCoords σ s l, c k = ∑ k ∈ s, c k := by
  classical
  rw [stratumCoords]
  refine (Finset.sum_subset Finset.subset_union_right fun k _ hk => ?_).symm
  by_contra h
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp ‹k ∈ _›).resolve_right hk)
  exact hc _ h ⟨i, rfl⟩

/-- The stratum's ideal is the coordinate prime of its coordinates. -/
theorem span_image_comp_sup_eq {R : Type*} [CommRing R] (z : Fin n → R) (l : ℕ) :
    span ((z ∘ σ) '' {i | i.val < l}) ⊔ span (z '' ↑s) = span (z '' ↑(stratumCoords σ s l)) := by
  classical
  rw [stratumCoords, Finset.coe_union, Finset.coe_image, Set.image_union, Ideal.span_union,
    Set.image_image, Finset.coe_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

/-- The ε-order of the `i`-th generator, unfolded at `0`. -/
theorem epsOrder_zero (e₀ : ℕ) (e δ : Fin (r + 1) → ℕ) : epsOrder e₀ e δ 0 = e₀ + δ 0 := by
  simp [epsOrder]

/-- The ε-orders of consecutive generators differ by `e_i + δ_{i+1} − δ_i`. -/
theorem epsOrder_succ (e₀ : ℕ) (e δ : Fin (r + 1) → ℕ) (i : Fin r) :
    epsOrder e₀ e δ i.succ + δ i.castSucc =
      epsOrder e₀ e δ i.castSucc + e i.castSucc + δ i.succ := by
  have hfilt : Finset.univ.filter (fun i' : Fin (r + 1) => i' < i.succ) =
      insert i.castSucc (Finset.univ.filter (fun i' : Fin (r + 1) => i' < i.castSucc)) := by
    ext i'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
      Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
    omega
  have hnot : i.castSucc ∉ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i.castSucc) := by
    simp
  rw [epsOrder, epsOrder, hfilt, Finset.sum_insert hnot]
  ring

/-- Monotonicity of the ε-orders from the level condition `δ_i ≤ e_i + δ_{i+1}`. -/
theorem epsOrder_mono_of (e₀ : ℕ) (e δ : Fin (r + 1) → ℕ)
    (h : ∀ i : Fin r, δ i.castSucc ≤ e i.castSucc + δ i.succ) (i : Fin r) :
    epsOrder e₀ e δ i.castSucc ≤ epsOrder e₀ e δ i.succ := by
  have := epsOrder_succ e₀ e δ i
  have := h i
  omega

end Star

/-! ### A chain equation that is a unit -/

section UnitEquation

variable {R : Type*} [CommRing R] {r : ℕ}

/-- The monomial `∏_{i < r} M_i` of the K-shape's last generator is a multiple of the monomial
`∏_{i < i₀} M_i` of any earlier generator. -/
theorem prod_filter_lt_last_eq_mul (M : Fin (r + 1) → R) (i₀ : Fin (r + 1)) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => i < Fin.last r), M i =
      (∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => i < i₀), M i) *
        ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => i < Fin.last r ∧ ¬ i < i₀), M i := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ.filter fun i : Fin (r + 1) => i < Fin.last r) (fun i => i < i₀),
    Finset.filter_filter, Finset.filter_filter]
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.val_last]
  have := i.2
  have := i₀.2
  omega

/-- When one of the chain equations is a unit, the un-isolated chain form and the K-shape coincide
— both are generated by the generators below that level and the monomial of that level. -/
theorem chainIdeal_eq_chainKIdeal_of_isUnit (φ M : Fin (r + 1) → R) {i₀ : Fin (r + 1)}
    (hu : IsUnit (φ i₀)) : chainIdeal φ M = chainKIdeal φ M := by
  classical
  refine le_antisymm (chainIdeal_le_chainKIdeal φ M) ?_
  rw [chainKIdeal, chainIdeal_eq_span_range_chainGen, span_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = Fin.last r
  · subst hi
    -- the last generator `∏_{i < r} M_i` is a multiple of `∏_{i < i₀} M_i = G_{i₀} · (φ i₀)⁻¹`
    obtain ⟨u, hu'⟩ := hu
    have hG : (∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => i < i₀), M i) =
        chainGen φ M i₀ * ↑u⁻¹ := by
      rw [chainGen, ← hu', mul_assoc, Units.mul_inv, mul_one]
    change (∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => i < Fin.last r), M i) *
      Function.update φ (Fin.last r) 1 (Fin.last r) ∈ chainIdeal φ M
    rw [Function.update_self, mul_one, prod_filter_lt_last_eq_mul M i₀, hG]
    exact mul_mem_right _ _ (mul_mem_right _ _ (chainGen_mem φ M i₀))
  · change (∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < i), M i') *
      Function.update φ (Fin.last r) 1 i ∈ chainIdeal φ M
    rw [Function.update_of_ne hi]
    exact chainGen_mem φ M i

end UnitEquation

end Hironaka.Resolution
