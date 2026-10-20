/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon
import Hironaka.Scheme.Snc.ParameterAlgebra
import Hironaka.Scheme.Snc.ParameterSubset
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The colon of the chain ideal by the chain in a regular local ring

For a regular system of parameters `z` of a regular local ring `R`, chain equations `f = z ∘ σ`
(`σ` injective) and monomials `M_i = ∏_k z_k^{a_{ik}}` in the OTHER coordinates (`a_{ik} = 0` for
`k` in the range of `σ`), the two cancellation clauses of
`Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon` hold at every level, so `(chainIdeal f M) :
(f) = chainKIdeal f M` (`chainIdeal_colon_span_eq`), and with a top-level monomial factor `M⁰` in
the other coordinates `(M⁰ · chainIdeal f M) : (f) = M⁰ · chainKIdeal f M`
(`chainIdeal_colon_span_eq'`). This is the statement CP2 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): the isolated ideal `I_n : I_{Γ̃}` at
the absorbing stage has the K-shape — for example `(x, e a, e² y) : (x, a, y) = (x, e a, e²)`.

The clauses come from the parameter-subset facts of `Hironaka.Scheme.Snc.ParameterSubset`: the ideal
`(z_l : l ∈ s)` of a sub-family is prime (the quotient is regular local, hence a domain), a
coordinate outside `s` is not in it, and in `R/(z_l : l ∈ s)` the class of a coordinate `z_k`,
`k ∉ s`, is a prime element (the quotient by it is `R/(z_l : l ∈ insert k s)`, again a domain).
The cancellation of a monomial against a later chain equation is then Mathlib's
`Prime.pow_dvd_of_dvd_mul_right`, one prime power at a time, cancelling each power in the domain
before the next (`dvd_of_prod_pow_dvd_mul`). The colon identity is used at the entry into the
protected state (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainColon`) and in the analysis of
the last round (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Tools`).
-/

@[expose] public section

universe u

open Ideal IsLocalRing

namespace Hironaka.Resolution

/-! ### Cancellation of a monomial in a domain -/

/-- In a domain, a product of prime powers `∏ p_k^{a_k}` dividing `x u`, where no `p_k` with
`a_k ≠ 0` divides `u`, divides `x` — one power at a time (`Prime.pow_dvd_of_dvd_mul_right`),
cancelling it before the next. -/
theorem dvd_of_prod_pow_dvd_mul {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (K : Finset ι) (p : ι → R) (a : ι → ℕ) (u : R)
    (hp : ∀ k ∈ K, a k ≠ 0 → Prime (p k) ∧ ¬ p k ∣ u) :
    ∀ x : R, (∏ k ∈ K, p k ^ a k) ∣ x * u → (∏ k ∈ K, p k ^ a k) ∣ x := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    intro x _
    simp
  | insert k K hk ih =>
    intro x hx
    rw [Finset.prod_insert hk] at hx ⊢
    have hK : ∀ k' ∈ K, a k' ≠ 0 → Prime (p k') ∧ ¬ p k' ∣ u :=
      fun k' hk' => hp k' (Finset.mem_insert_of_mem hk')
    by_cases ha : a k = 0
    · rw [ha, pow_zero, one_mul] at hx ⊢
      exact ih hK x hx
    · obtain ⟨hprime, hpu⟩ := hp k (Finset.mem_insert_self k K) ha
      have h1 : p k ^ a k ∣ x * u := dvd_trans (dvd_mul_right _ _) hx
      obtain ⟨x', rfl⟩ := hprime.pow_dvd_of_dvd_mul_right (a k) hpu h1
      have hne : p k ^ a k ≠ 0 := pow_ne_zero _ hprime.ne_zero
      rw [mul_assoc, mul_dvd_mul_iff_left hne] at hx
      exact mul_dvd_mul_left _ (ih hK x' hx)

/-! ### The classes of the coordinates in a quotient by a sub-family are prime -/

section Regular

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
  (hz : IsLocalRing.maximalIdeal R = span (Set.range z)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)

include hz hn in
/-- The quotient of a regular local ring by a sub-family of a regular system of parameters is a
domain (`AlgebraicGeometry.isRegularLocalRing_quotient_span_image_finset`). -/
theorem isDomain_quotient_span_image_finset (s : Finset (Fin n)) :
    IsDomain (R ⧸ span (z '' ↑s)) := by
  have := AlgebraicGeometry.isRegularLocalRing_quotient_span_image_finset hz hn s
  infer_instance

include hz hn in
/-- The ideal of a sub-family of a regular system of parameters is prime. -/
theorem isPrime_span_image_finset (s : Finset (Fin n)) : (span (z '' ↑s)).IsPrime := by
  have := isDomain_quotient_span_image_finset hz hn s
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

include hz hn in
/-- In `R/(z_l : l ∈ s)` the class of a coordinate `z_k`, `k ∉ s`, is a prime element: the
quotient by it is `R/(z_l : l ∈ insert k s)`, a domain, and the class is nonzero. -/
theorem prime_mk_of_notMem (s : Finset (Fin n)) {k : Fin n} (hk : k ∉ s) :
    Prime (Ideal.Quotient.mk (span (z '' ↑s)) (z k)) := by
  have hne : Ideal.Quotient.mk (span (z '' ↑s)) (z k) ≠ 0 := fun h =>
    AlgebraicGeometry.notMem_span_image_of_notMem hz hn hk (Ideal.Quotient.eq_zero_iff_mem.mp h)
  refine (Ideal.span_singleton_prime hne).mp ?_
  rw [← Ideal.Quotient.isDomain_iff_prime]
  have hmap : map (Ideal.Quotient.mk (span (z '' ↑s))) (span {z k}) =
      span {Ideal.Quotient.mk (span (z '' ↑s)) (z k)} := by
    rw [map_span, Set.image_singleton]
  rw [← hmap]
  have hsup : span (z '' ↑s) ⊔ span {z k} = span (z '' ↑(insert k s)) :=
    (AlgebraicGeometry.span_image_insert z s k).symm
  have : IsDomain (R ⧸ (span (z '' ↑s) ⊔ span {z k})) := by
    rw [hsup]
    exact isDomain_quotient_span_image_finset hz hn _
  exact MulEquiv.isDomain _
    (DoubleQuot.quotQuotEquivQuotSup (span (z '' ↑s)) (span {z k})).toMulEquiv

end Regular

/-! ### The top-level monomial factor -/

/-- In a domain, for `m ≠ 0` that cancels against every `f_j` (`m ∣ x f_j → m ∣ x`), the colon of
`m · I` by `(f)` is `m · (I : (f))` (the family `f` nonempty). -/
theorem colon_span_singleton_mul_eq {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    [Nonempty ι] (m : R) (hm0 : m ≠ 0) (f : ι → R) (I : Ideal R)
    (hm : ∀ (j : ι) (x : R), m ∣ x * f j → m ∣ x) :
    (span {m} * I).colon (span (Set.range f)) = span {m} * I.colon (span (Set.range f)) := by
  apply le_antisymm
  · intro h hh
    rw [mem_colon_span_range_iff] at hh
    obtain ⟨j₀⟩ := ‹Nonempty ι›
    have hdiv : m ∣ h := hm j₀ h (mem_span_singleton.mp
      (IsConcreteLE.le_iff.mp (Ideal.mul_le.mpr fun a ha b _ => Ideal.mul_mem_right b _ ha)
        (hh j₀)))
    obtain ⟨h', rfl⟩ := hdiv
    refine Ideal.mul_mem_mul (mem_span_singleton_self m) ?_
    rw [mem_colon_span_range_iff]
    intro j
    obtain ⟨w, hw, hmw⟩ := Ideal.mem_span_singleton_mul.mp (hh j)
    have : w = h' * f j := mul_left_cancel₀ hm0 (by rw [hmw, mul_assoc])
    rwa [this] at hw
  · rw [span_singleton_mul_le_iff]
    intro z hz
    rw [mem_colon_span_range_iff] at hz ⊢
    intro j
    rw [mul_assoc]
    exact Ideal.mul_mem_mul (mem_span_singleton_self m) (hz j)

section TopLevel

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
  (hz' : IsLocalRing.maximalIdeal R = span (Set.range z))
  (hn : (n : WithBot ℕ∞) = ringKrullDim R)

include hz' hn in
/-- A monomial in the coordinates is nonzero. -/
theorem monomialOf_ne_zero (b : Fin n → ℕ) : monomialOf z b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (AlgebraicGeometry.ne_zero_of_parameters hz'
      hn k)

include hz' hn in
/-- A monomial in coordinates off the range of `σ` cancels against every `z (σ j)`. -/
theorem monomialOf_dvd_of_dvd_mul {r : ℕ} {σ : Fin (r + 1) → Fin n} (b : Fin n → ℕ)
    (hb : ∀ k, k ∈ Set.range σ → b k = 0) (j : Fin (r + 1)) (x : R)
    (h : monomialOf z b ∣ x * z (σ j)) : monomialOf z b ∣ x := by
  refine dvd_of_prod_pow_dvd_mul Finset.univ z b (z (σ j)) ?_ x h
  intro k _ hk
  refine ⟨AlgebraicGeometry.prime_of_parameters hz' hn k, fun hdvd => hk (hb k ⟨j, ?_⟩)⟩
  rw [← mem_span_singleton] at hdvd
  have : z (σ j) ∈ span (z '' ↑({k} : Finset (Fin n))) := by simpa using hdvd
  exact Finset.mem_singleton.mp ((AlgebraicGeometry.mem_span_image_iff hz' hn _ _).mp this)

end TopLevel

/-! ### The colon identity (CP2) -/

section CP2

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
  (hz : IsRegularSystemOfParameters z) {r : ℕ} {σ : Fin (r + 1) → Fin n}
  (hσ : Function.Injective σ) {a : Fin (r + 1) → Fin n → ℕ}
  (ha : ∀ i k, k ∈ Set.range σ → a i k = 0)

/-- The coordinate indices of the chain segment `f₀, …, f_i`. -/
def chainSeg (σ : Fin (r + 1) → Fin n) (i : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun j : Fin (r + 1) => j.val ≤ i)).image σ

theorem mem_chainSeg_iff {σ : Fin (r + 1) → Fin n} {i : ℕ} {k : Fin n} :
    k ∈ chainSeg σ i ↔ ∃ j : Fin (r + 1), j.val ≤ i ∧ σ j = k := by
  simp [chainSeg]

omit [CommRing R] [IsRegularLocalRing R] in
theorem image_comp_le_eq (z : Fin n → R) (σ : Fin (r + 1) → Fin n) (i : ℕ) :
    (z ∘ σ) '' {j : Fin (r + 1) | j.val ≤ i} = z '' ↑(chainSeg σ i) := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply, Finset.mem_coe,
    mem_chainSeg_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨σ j, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨k, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, rfl⟩

include ha in
/-- A monomial in the coordinates off the chain is not in the ideal of a chain segment. -/
theorem monomialOf_notMem_span_chainSeg (hz' : IsLocalRing.maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (i : Fin (r + 1)) (l : ℕ) :
    monomialOf z (a i) ∉ span (z '' ↑(chainSeg σ l)) := by
  intro h
  have hP := isPrime_span_image_finset hz' hn (chainSeg σ l)
  obtain ⟨k, -, hk⟩ := hP.prod_mem_iff.mp h
  by_cases hak : a i k = 0
  · rw [hak, pow_zero] at hk
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr hk)
  · have hkP : z k ∈ span (z '' ↑(chainSeg σ l)) :=
      (hP.pow_mem_iff_mem _ (Nat.pos_of_ne_zero hak)).mp hk
    obtain ⟨j, -, rfl⟩ := mem_chainSeg_iff.mp ((AlgebraicGeometry.mem_span_image_iff hz' hn _ _).mp
        hkP)
    exact hak (ha i (σ j) ⟨j, rfl⟩)

include ha in
/-- Clause (C) of `Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon` for chain coordinates: a
monomial off the chain is a nonzerodivisor modulo a chain segment. -/
theorem clauseC (hz' : IsLocalRing.maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (i : Fin r) (y : R)
    (hy : monomialOf z (a i.castSucc) * y ∈ span ((z ∘ σ) '' {j | j.val ≤ i.val})) :
    y ∈ span ((z ∘ σ) '' {j | j.val ≤ i.val}) := by
  rw [image_comp_le_eq] at hy ⊢
  have hP := isPrime_span_image_finset hz' hn (chainSeg σ i.val)
  exact (hP.mem_or_mem hy).resolve_left (monomialOf_notMem_span_chainSeg ha hz' hn _ _)

include hσ ha in
/-- Clause (B) of `Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon` for chain coordinates: a
monomial off the chain cancels against a later chain equation modulo a chain segment. -/
theorem clauseB (hz' : IsLocalRing.maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (i : Fin r) (j : Fin (r + 1)) (hij : i.val < j.val)
    (x : R)
    (hx : x * (z ∘ σ) j ∈ span ((z ∘ σ) '' {j' | j'.val ≤ i.val}) ⊔
      span {monomialOf z (a i.castSucc)}) :
    x ∈ span ((z ∘ σ) '' {j' | j'.val ≤ i.val}) ⊔ span {monomialOf z (a i.castSucc)} := by
  rw [image_comp_le_eq] at hx ⊢
  have hdom := isDomain_quotient_span_image_finset hz' hn (chainSeg σ i.val)
  -- pass to the quotient by the chain segment
  have hmap : ∀ y : R, y ∈ span (z '' ↑(chainSeg σ i.val)) ⊔ span {monomialOf z (a i.castSucc)} ↔
      Ideal.Quotient.mk (span (z '' ↑(chainSeg σ i.val))) (monomialOf z (a i.castSucc)) ∣
        Ideal.Quotient.mk (span (z '' ↑(chainSeg σ i.val))) y := by
    intro y
    rw [sup_comm, ← Ideal.mem_quotient_iff_mem_sup, map_span, Set.image_singleton,
      mem_span_singleton]
  rw [hmap] at hx ⊢
  rw [Function.comp_apply, map_mul] at hx
  have hprod : Ideal.Quotient.mk (span (z '' ↑(chainSeg σ i.val))) (monomialOf z (a i.castSucc)) =
      ∏ k, Ideal.Quotient.mk (span (z '' ↑(chainSeg σ i.val))) (z k) ^ a i.castSucc k := by
    simp [monomialOf, map_prod, map_pow]
  rw [hprod] at hx ⊢
  refine dvd_of_prod_pow_dvd_mul Finset.univ _ _ _ ?_ _ hx
  intro k _ hak
  have hkσ : k ∉ Set.range σ := fun hk => hak (ha _ k hk)
  have hkT : k ∉ chainSeg σ i.val := fun hk => by
    obtain ⟨j', -, rfl⟩ := mem_chainSeg_iff.mp hk
    exact hkσ ⟨j', rfl⟩
  refine ⟨prime_mk_of_notMem hz' hn _ hkT, fun hdvd => ?_⟩
  rw [← mem_span_singleton, ← Set.image_singleton, ← map_span, Ideal.mem_quotient_iff_mem_sup,
    sup_comm, ← AlgebraicGeometry.span_image_insert, AlgebraicGeometry.mem_span_image_iff hz' hn,
    Finset.mem_insert] at hdvd
  rcases hdvd with h | h
  · exact hkσ ⟨j, h⟩
  · obtain ⟨j', hj', hjj⟩ := mem_chainSeg_iff.mp h
    rw [hσ hjj] at hj'
    omega

include hz hσ ha in
/-- **CP2**, the colon identity: in a regular local ring with a regular system of parameters `z`,
for chain equations `f = z ∘ σ` and monomials `M_i = ∏_k z_k^{a_{ik}}` in the coordinates off the
chain, the colon of the chain ideal by the chain is the K-shape:
`(f₀, M₀ f₁, …, (∏_{i<r} M_i) f_r) : (f₀, …, f_r) = (f₀, M₀ f₁, …, ∏_{i<r} M_i)`. -/
theorem chainIdeal_colon_span_eq :
    (chainIdeal (z ∘ σ) fun i => monomialOf z (a i)).colon (span (Set.range (z ∘ σ))) =
      chainKIdeal (z ∘ σ) fun i => monomialOf z (a i) :=
  colon_chainIdeal_eq_chainKIdeal r R (z ∘ σ) (fun i => monomialOf z (a i))
    (fun i y hy => clauseC ha hz.1.symm hz.2 i y hy)
    (fun i j hij x hx => clauseB hσ ha hz.1.symm hz.2 i j hij x hx)

include hz hσ ha in
/-- CP2 with the top-level monomial factor: for a top-level monomial `M⁰ = ∏_k z_k^{b_k}` in the
coordinates off the chain, `(M⁰ · chainIdeal f M) : (f) = M⁰ · chainKIdeal f M`. -/
theorem chainIdeal_colon_span_eq' (b : Fin n → ℕ) (hb : ∀ k, k ∈ Set.range σ → b k = 0) :
    (span {monomialOf z b} * chainIdeal (z ∘ σ) fun i => monomialOf z (a i)).colon
        (span (Set.range (z ∘ σ))) =
      span {monomialOf z b} * chainKIdeal (z ∘ σ) fun i => monomialOf z (a i) := by
  rw [colon_span_singleton_mul_eq _ (monomialOf_ne_zero hz.1.symm hz.2 b) (z ∘ σ) _
    (fun j x h => monomialOf_dvd_of_dvd_mul hz.1.symm hz.2 b hb j x h),
    chainIdeal_colon_span_eq hz hσ ha]

end CP2

end Hironaka.Resolution
