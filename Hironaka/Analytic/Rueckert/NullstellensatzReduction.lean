/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.ZeroSet
public import Hironaka.Analytic.Germ.Coordinate
public import Hironaka.Analytic.Rueckert.Subst
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Hironaka.Analytic.ConvSeries.Units
import Hironaka.Analytic.Germ.Prime
import Hironaka.Analytic.Rueckert.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Reductions for Rückert's Nullstellensatz, and the failure over `ℝ`

Three pieces of elementary algebra on the zero sets and vanishing ideals of `ZeroSet.lean`, used
by the proof of Rückert's Nullstellensatz (`Nullstellensatz.lean`):

* **Reduction to prime ideals** (the first step of the proof of [Fre17, Ch. I, 9.1]: a proper
  radical ideal in a Noetherian ring is a finite intersection of primes, so the Nullstellensatz
  for prime ideals gives it for all radical ideals): with Mathlib's `Ideal.sInf_minimalPrimes`
  (`√I` is the intersection of the minimal primes over `I`, no finiteness needed) and the
  monotonicity of `vanishingIdeal`, the inclusion `𝓘(V(p)) ⊆ p` for every prime `p` gives
  `𝓘(V(I)) = √I` for every ideal `I` (`vanishingIdeal_eq_radical_of_forall_isPrime`); the
  pointwise form of the statement follows (`mem_radical_of_vanishesOn_of_eq`).
* **Invariance under linear changes of coordinates** (the "suitable linear transformation of the
  coordinates" of [Fre17, Ch. I, 7.4]; the automorphism `P(z) ↦ P(Az)` is `substEquiv` of
  `Subst.lean`): `V(σ(S)) = L⁻¹(V(S))` near `0` because
  `evalSeries (substConv L g) = evalSeries g ∘ L` near `0` (`evalSeries_substConv`) and `L` is a
  homeomorphism fixing `0`; hence `σ f ∈ 𝓘(V(σ(I)))` iff `f ∈ 𝓘(V(I))`, and the Nullstellensatz
  inclusion for `σ(I)` gives it for `I` (`vanishingIdeal_le_radical_of_map_substEquiv`; Mathlib's
  `Ideal.map_radical_of_surjective`).
* **The failure over `ℝ`**: `V(x² + y²) = {0}` but `x ∉ √(x² + y²)` (the same phenomenon as in
  [BM97, Example 3.16]): in `Conv ℝ 2`, `x` vanishes on the zero set of `x² + y²` near `0` (over
  `ℝ`, `x² + y² = 0` forces `x = 0`), while `x^k ∈ (x² + y²)` would make `x² + y²` a divisor of a
  power of the prime `x` (`prime_convX`), hence a unit or divisible by `x`; neither is the case
  (constant coefficient `0`; coefficient of `y²` equal to `1`).
-/

public section

open Filter Topology MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {n : ℕ}

/-! ### Reduction to prime ideals -/

/-- If `𝓘(V(p)) ⊆ p` for every minimal prime `p` over `I`, then `𝓘(V(I)) ⊆ √I`: `√I` is the
intersection of its minimal primes and `𝓘(V(·))` is monotone. -/
theorem vanishingIdeal_le_radical_of_minimalPrimes {I : Ideal (Conv K n)}
    (h : ∀ p ∈ I.minimalPrimes, vanishingIdeal p ≤ p) : vanishingIdeal I ≤ I.radical := by
  rw [← Ideal.sInf_minimalPrimes]
  exact le_sInf fun p hp => (vanishingIdeal_mono hp.1.2).trans (h p hp)

/-- The Nullstellensatz for prime ideals (`𝓘(V(P)) ⊆ P`) gives `𝓘(V(I)) = √I` for every ideal
(the reduction step of [Fre17, Ch. I, 9.1]). -/
theorem vanishingIdeal_eq_radical_of_forall_isPrime
    (h : ∀ P : Ideal (Conv K n), P.IsPrime → vanishingIdeal P ≤ P) (I : Ideal (Conv K n)) :
    vanishingIdeal I = I.radical :=
  le_antisymm (vanishingIdeal_le_radical_of_minimalPrimes fun p hp =>
    h p hp.1.1) (radical_le_vanishingIdeal I)

/-- The pointwise form from the ideal-theoretic one: a series vanishing near `0` on the zero set
of a finite system of generators of `I` lies in `√I`. -/
theorem mem_radical_of_vanishesOn_of_eq {S : Finset (Conv K n)} {f : Conv K n}
    (h : vanishingIdeal (Ideal.span (S : Set (Conv K n))) =
      (Ideal.span (S : Set (Conv K n))).radical) (hf : VanishesOn S f) :
    f ∈ (Ideal.span (S : Set (Conv K n))).radical := by
  rw [← h]
  exact (mem_vanishingIdeal_iff rfl).mpr hf

/-! ### Invariance under linear changes of coordinates -/

/-- A continuous linear automorphism of `K^n` carries the neighbourhood filter of `0` to itself. -/
theorem map_nhds_zero_clequiv (L : (Fin n → K) ≃L[K] (Fin n → K)) :
    Filter.map L (𝓝 (0 : Fin n → K)) = 𝓝 0 := by
  rw [L.map_nhds_eq, map_zero]

/-- `V(σ(S)) = L⁻¹(V(S))` near `0` for `σ = substEquiv L`, so `σ f` vanishes on `V(σ(S))` iff `f`
vanishes on `V(S)`. -/
theorem vanishesOn_image_substEquiv [DecidableEq (Conv K n)] (L : (Fin n → K) ≃L[K] (Fin n → K))
    (S : Finset (Conv K n)) (f : Conv K n) :
    VanishesOn (S.image (substEquiv L)) (substEquiv L f) ↔ VanishesOn S f := by
  classical
  -- the zero set of the transformed family is the preimage of the zero set of `S`, near `0`
  have hz : ∀ᶠ x in 𝓝 (0 : Fin n → K),
      (x ∈ zeroSet (S.image (substEquiv L)) ↔ L x ∈ zeroSet S) := by
    have hS : ∀ g ∈ S, evalSeries ((substEquiv L g : Conv K n) : MvPowerSeries (Fin n) K) =ᶠ[𝓝 0]
        evalSeries (g : MvPowerSeries (Fin n) K) ∘ L := fun g _ => by
      rw [substEquiv_apply]
      exact evalSeries_substConv _ g
    filter_upwards [(eventually_all_finset S).mpr hS] with x hx
    simp only [mem_zeroSet_iff, Finset.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun g hg => by rw [hx g hg]; rfl
  have hf : evalSeries ((substEquiv L f : Conv K n) : MvPowerSeries (Fin n) K) =ᶠ[𝓝 0]
      evalSeries (f : MvPowerSeries (Fin n) K) ∘ L := by
    rw [substEquiv_apply]
    exact evalSeries_substConv _ f
  have key : VanishesOn (S.image (substEquiv L)) (substEquiv L f) ↔
      ∀ᶠ x in 𝓝 (0 : Fin n → K), L x ∈ zeroSet S →
        evalSeries (f : MvPowerSeries (Fin n) K) (L x) = 0 := by
    constructor
    · intro h
      filter_upwards [h, hz, hf] with x h hz hf hx
      rw [Function.comp_apply] at hf
      rw [← hf]
      exact h (hz.mpr hx)
    · intro h
      filter_upwards [h, hz, hf] with x h hz hf hx
      rw [hf, Function.comp_apply]
      exact h (hz.mp hx)
  rw [key]
  unfold VanishesOn
  have := eventually_map (f := 𝓝 (0 : Fin n → K)) (m := (L : (Fin n → K) → (Fin n → K)))
    (P := fun y => y ∈ zeroSet S → evalSeries (f : MvPowerSeries (Fin n) K) y = 0)
  rw [map_nhds_zero_clequiv L] at this
  exact this.symm

/-- `σ f ∈ 𝓘(V(σ(I)))` iff `f ∈ 𝓘(V(I))` for a linear change `σ`. -/
theorem mem_vanishingIdeal_map_substEquiv (L : (Fin n → K) ≃L[K] (Fin n → K))
    (I : Ideal (Conv K n)) (f : Conv K n) :
    substEquiv L f ∈
        vanishingIdeal (I.map ((substEquiv L).toRingEquiv : Conv K n →+* Conv K n)) ↔
      f ∈ vanishingIdeal I := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_span_eq I
  have hS' : Ideal.span ((S.image (substEquiv L) : Finset (Conv K n)) : Set (Conv K n)) =
      I.map ((substEquiv L).toRingEquiv : Conv K n →+* Conv K n) := by
    rw [Finset.coe_image, ← hS, Ideal.map_span]
    rfl
  rw [mem_vanishingIdeal_iff hS', mem_vanishingIdeal_iff hS, vanishesOn_image_substEquiv]

/-- The Nullstellensatz inclusion for the image `σ(I)` under a linear change of coordinates gives
it for `I` (the linear transformation of the coordinates of [Fre17, Ch. I, 7.4]). -/
theorem vanishingIdeal_le_radical_of_map_substEquiv (L : (Fin n → K) ≃L[K] (Fin n → K))
    {I : Ideal (Conv K n)}
    (h : vanishingIdeal (I.map ((substEquiv L).toRingEquiv : Conv K n →+* Conv K n)) ≤
      (I.map ((substEquiv L).toRingEquiv : Conv K n →+* Conv K n)).radical) :
    vanishingIdeal I ≤ I.radical := by
  intro f hf
  obtain ⟨σ, hσ⟩ : ∃ σ : Conv K n ≃+* Conv K n, σ = (substEquiv L).toRingEquiv := ⟨_, rfl⟩
  have h1 := h ((mem_vanishingIdeal_map_substEquiv L I f).mpr hf)
  rw [← hσ] at h1
  have hker : RingHom.ker (σ : Conv K n →+* Conv K n) ≤ I := by
    rw [(RingHom.injective_iff_ker_eq_bot (σ : Conv K n →+* Conv K n)).mp σ.injective]
    exact bot_le
  rw [← Ideal.map_radical_of_surjective (f := (σ : Conv K n →+* Conv K n)) σ.surjective hker,
    Ideal.map_comap_of_equiv, Ideal.mem_comap] at h1
  have h2 : σ.symm ((substEquiv L) f) = f := by
    rw [hσ]
    exact (substEquiv L).toRingEquiv.symm_apply_apply f
  rwa [h2] at h1

/-! ### The failure over `ℝ` -/

/-- The failure of the Nullstellensatz over `ℝ`: in `Conv ℝ 2`, `x` vanishes on the zero-set germ
of `(x² + y²)` (which is `{0}`) but is not in its radical (the same phenomenon as in
[BM97, Example 3.16]). -/
theorem not_nullstellensatz_real :
    convX ℝ (0 : Fin 2) ∈
        vanishingIdeal (Ideal.span {convX ℝ (0 : Fin 2) ^ 2 + convX ℝ (1 : Fin 2) ^ 2}) ∧
      convX ℝ (0 : Fin 2) ∉
        (Ideal.span {convX ℝ (0 : Fin 2) ^ 2 + convX ℝ (1 : Fin 2) ^ 2}).radical := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : Conv ℝ 2, g = convX ℝ (0 : Fin 2) ^ 2 + convX ℝ (1 : Fin 2) ^ 2 :=
    ⟨_, rfl⟩
  rw [← hg]
  have hgcoe : (g : MvPowerSeries (Fin 2) ℝ) = X 0 ^ 2 + X 1 ^ 2 := by
    rw [hg, Subalgebra.coe_add, Subalgebra.coe_pow, Subalgebra.coe_pow, coe_convX, coe_convX]
  constructor
  · rw [mem_vanishingIdeal_iff (S := {g}) (by rw [Finset.coe_singleton])]
    have h := evalSeries_add_eventually (convX ℝ (0 : Fin 2) ^ 2).2 (convX ℝ (1 : Fin 2) ^ 2).2
    filter_upwards [h] with x hx hxg
    have hgx := hxg g (Finset.mem_singleton_self g)
    rw [hg, Subalgebra.coe_add, hx, Subalgebra.coe_pow, Subalgebra.coe_pow, coe_convX, coe_convX,
      evalSeries_X_pow, evalSeries_X_pow] at hgx
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    rw [coe_convX, ← pow_one (X (0 : Fin 2)), evalSeries_X_pow, pow_one, h0]
  · intro hmem
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hmem
    rw [Ideal.mem_span_singleton] at hk
    obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow (prime_convX (0 : Fin 2)) k).mp hk
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [pow_zero, associated_one_iff_isUnit] at hassoc
      have hunit := (isUnit_iff_constantCoeff_ne_zero g.2).mp (by rwa [Subtype.coe_eta])
      apply hunit
      rw [hgcoe, map_add, map_pow, map_pow, constantCoeff_X, constantCoeff_X, zero_pow two_ne_zero,
        add_zero]
    · have hdvd : (X 0 : MvPowerSeries (Fin 2) ℝ) ∣ (g : MvPowerSeries (Fin 2) ℝ) := by
        obtain ⟨c, hc⟩ := hassoc.dvd'
        refine ⟨(X 0 : MvPowerSeries (Fin 2) ℝ) ^ (i - 1) * (c : MvPowerSeries (Fin 2) ℝ), ?_⟩
        rw [hc, Subalgebra.coe_mul, Subalgebra.coe_pow, coe_convX, ← mul_assoc, ← pow_succ',
          Nat.sub_add_cancel hi0]
      rw [X_dvd_iff] at hdvd
      have h1 := hdvd (Finsupp.single 1 2) (by simp)
      rw [hgcoe, map_add, coeff_X_pow, coeff_X_pow] at h1
      have hne : (Finsupp.single (1 : Fin 2) (2 : ℕ)) ≠ Finsupp.single (0 : Fin 2) (2 : ℕ) := by
        intro h
        have := DFunLike.congr_fun h (1 : Fin 2)
        simp at this
      rw [ite_eq_right hne, ite_eq_left rfl, zero_add] at h1
      exact one_ne_zero h1

end Analytic
