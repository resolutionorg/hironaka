/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# D-balanced ideals

An ideal `I` with `m = max-ord I` is *D-balanced* if `(Dⁱ I)^m ⊂ I^(m-i)` for all `i < m`
[Kol07, 52 and Definition 83].  Locally the parameter `m` is explicit.  Kollár's consequence
"at every point it has order either `m` or `0`" is `IsDBalanced.ord_eq_zero_or_le`: if
`ord I < m` then `D^(m-1) I = R` ([Kol07, Lemma 74(3)]), so `R = (D^(m-1) I)^m ⊂ I`.  The
D-balanced inclusions pass to any coordinate-compatible ring map (`IsDBalanced.map`), in
particular to the restriction `R → R/⟨x₁⟩` to a coordinate hypersurface.  Two examples close
the file: `⟨xᵢ^m⟩` is D-balanced with respect to `m`, and `⟨xᵢ xⱼ⟩` is not D-balanced with
respect to `2`, since `D ⟨xᵢ xⱼ⟩ = ⟨xᵢ, xⱼ⟩` and `xᵢ² ∉ ⟨xᵢ xⱼ⟩` in `K⟦X⟧`
(`X_sq_notMem_span_X_mul_X`); their instances in `ℚ⟦x₀, x₁⟧` are
`HironakaExamples/Balanced/PowerSeriesTwoVariables.lean`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n)

/-- `I` is **D-balanced** with respect to `m` if `(Dⁱ I)^m ≤ I^(m-i)` for all `i < m`
[Kol07, 52 and Definition 83]. -/
def IsDBalanced (I : Ideal R) (m : ℕ) : Prop := ∀ i < m, c.Dpow i I ^ m ≤ I ^ (m - i)

variable {c}

/-- A D-balanced ideal with respect to `m ≥ 1` of order `< m` is the unit ideal
("`(D^(m-1) I)_p = 𝒪_p`, thus `I^(m-1)` and `I` both contain a unit at `p`",
[Kol07, Definition 83]). -/
theorem IsDBalanced.eq_top_of_ord_lt {I : Ideal R} {m : ℕ} (h : c.IsDBalanced I m) (hm : 1 ≤ m)
    (hord : ord I < m) : I = ⊤ := by
  have hle : ord I ≤ ((m - 1 : ℕ) : ℕ∞) := by
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hord)
    rw [← ha] at hord ⊢
    have ham : a < m := by exact_mod_cast hord
    exact_mod_cast (show a ≤ m - 1 by omega)
  have := h (m - 1) (by omega)
  rw [c.Dpow_eq_top_of_ord_le hle, Ideal.top_pow, Nat.sub_sub_self hm, pow_one] at this
  exact top_le_iff.mp this

/-- "At every point it has order either `m` or `0`" [Kol07, Definition 83], locally: `ord I = 0`
or `m ≤ ord I`. -/
theorem IsDBalanced.ord_eq_zero_or_le {I : Ideal R} {m : ℕ} (h : c.IsDBalanced I m) (hm : 1 ≤ m) :
    ord I = 0 ∨ (m : ℕ∞) ≤ ord I := by
  by_cases hle : (m : ℕ∞) ≤ ord I
  · exact Or.inr hle
  · exact Or.inl (ord_eq_zero_iff.mpr (h.eq_top_of_ord_lt hm (not_le.mp hle)))

/-- If moreover `ord I ≤ m` then `ord I ∈ {0, m}`. -/
theorem IsDBalanced.ord_eq_zero_or_eq {I : Ideal R} {m : ℕ} (h : c.IsDBalanced I m) (hm : 1 ≤ m)
    (hle : ord I ≤ m) : ord I = 0 ∨ ord I = m :=
  (h.ord_eq_zero_or_le hm).imp id fun h' => le_antisymm hle h'

/-- Kollár's "`cosupp (I, m) = cosupp I`" [Kol07, Definition 83], locally:
`m ≤ ord I ↔ 1 ≤ ord I`. -/
theorem IsDBalanced.le_ord_iff_one_le {I : Ideal R} {m : ℕ} (h : c.IsDBalanced I m) (hm : 1 ≤ m) :
    (m : ℕ∞) ≤ ord I ↔ 1 ≤ ord I := by
  refine ⟨fun h' => le_trans (by exact_mod_cast hm) h', fun h1 => ?_⟩
  rcases h.ord_eq_zero_or_le hm with h0 | hle
  · rw [h0] at h1
    exact absurd h1 (by simp)
  · exact hle

/-- The D-balanced inclusions pass to the image under a ring map whose target derivations are
induced by the source ones (`∂'ⱼ ∘ φ = φ ∘ ∂_{e j}`), such as the restriction to a coordinate
hypersurface `R/⟨x₁⟩`: the algebra behind Kollár's remark that D-balanced ideals "behave very
well with respect to restriction to smooth subvarieties" [Kol07, 52]. -/
theorem IsDBalanced.map {R' : Type*} [CommRing R'] [IsRegularLocalRing R'] [Algebra ℚ R']
    {n' : ℕ} (c' : RegularCoords R' n') (φ : R →+* R') (e : Fin n' → Fin n)
    (hφ : ∀ j f, c'.pderiv j (φ f) = φ (c.pderiv (e j) f)) {I : Ideal R} {m : ℕ}
    (h : c.IsDBalanced I m) : c'.IsDBalanced (I.map φ) m := by
  intro i hi
  calc c'.Dpow i (I.map φ) ^ m
      ≤ ((c.Dpow i I).map φ) ^ m := Ideal.pow_right_mono (c.Dpow_map_le c' φ e hφ i I) m
    _ = (c.Dpow i I ^ m).map φ := by rw [Ideal.map_pow]
    _ ≤ (I ^ (m - i)).map φ := Ideal.map_mono (h i hi)
    _ = (I.map φ) ^ (m - i) := by rw [Ideal.map_pow]

variable (c)

/-- `⟨xᵢ^m⟩` is D-balanced with respect to `m`, since `Dⁱ ⟨xᵢ^m⟩ = ⟨xᵢ^(m-i)⟩` and
`⟨xᵢ^(m-i)⟩^m = ⟨xᵢ^m⟩^(m-i)`. -/
theorem isDBalanced_span_singleton_x_pow (i : Fin n) (m : ℕ) :
    c.IsDBalanced (Ideal.span {c.x i ^ m}) m := by
  intro k hk
  rw [c.Dpow_span_singleton_x_pow i hk.le, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    ← pow_mul, ← pow_mul, Nat.mul_comm (m - k) m]

/-- `⟨xᵢ xⱼ⟩` is not D-balanced with respect to `2` as soon as `xᵢ² ∉ ⟨xᵢ xⱼ⟩` (which holds in
`ℚ⟦x₁, x₂⟧`: `X_sq_notMem_span_X_mul_X` below), since `D ⟨xᵢ xⱼ⟩ = ⟨xᵢ, xⱼ⟩`. -/
theorem not_isDBalanced_span_singleton_x_mul_x {i j : Fin n} (hij : i ≠ j)
    (h : c.x i ^ 2 ∉ Ideal.span {c.x i * c.x j}) :
    ¬ c.IsDBalanced (Ideal.span {c.x i * c.x j}) 2 := by
  intro hb
  have h1 := hb 1 one_lt_two
  rw [Dpow_one, c.D_span_singleton_x_mul_x hij] at h1
  apply h
  have hx : c.x i ^ 2 ∈ Ideal.span {c.x i, c.x j} ^ 2 := by
    rw [sq, sq]
    exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  simpa using h1 hx

end RegularCoords

/-- In `K⟦X⟧` (any field `K`, `i ≠ j`), `Xᵢ² ∉ ⟨Xᵢ Xⱼ⟩`: the coefficient of `Xᵢ²` in a multiple of
`Xⱼ` vanishes. -/
theorem X_sq_notMem_span_X_mul_X {σ K : Type*} [Field K] {i j : σ} (hij : i ≠ j) :
    (MvPowerSeries.X i : MvPowerSeries σ K) ^ 2 ∉
      Ideal.span {(MvPowerSeries.X i * MvPowerSeries.X j : MvPowerSeries σ K)} := by
  classical
  intro h
  have hdvd : (MvPowerSeries.X j : MvPowerSeries σ K) ∣ MvPowerSeries.X i ^ 2 :=
    (dvd_mul_left _ _).trans (Ideal.mem_span_singleton.mp h)
  rw [MvPowerSeries.X_dvd_iff] at hdvd
  have := hdvd (Finsupp.single i 2) (by simp [hij])
  rw [MvPowerSeries.coeff_X_pow, ite_eq_left rfl] at this
  exact one_ne_zero this

end IsLocalRing
