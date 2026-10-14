/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Chart
public import Hironaka.Algebra.Local.ChartLocal
public import Mathlib.RingTheory.Derivation.Lie

/-!
# Coordinates on the local ring of the chart at its origin

On the chart `x_r ≠ 0` of the blow-up of `⟨x₀, …, x_r⟩` the functions `yᵢ = xᵢ/x_r` (`i < r`),
`y_r = x_r`, `yⱼ = xⱼ` (`j > r`) are local coordinates [Kol07, Definition 60], and the
transformed derivations `∂'ⱼ` of `Hironaka/Algebra/Local/ChartRing.lean` (`∂'ⱼ = x_r ∂ⱼ` for `j <
r`, `∂'_r = ∂_r + ∑_{i<r} yᵢ ∂ᵢ`, `∂'ⱼ = ∂ⱼ` for `j > r`) satisfy `∂'ⱼ yₖ = δⱼₖ`
(`Hironaka/Algebra/Local/Chart.lean`).  This module packages `A' = R'_{𝔪'}` with the images of the
`yᵢ` and the localized `∂'ⱼ` as a `RegularCoords A' n`, the coordinate structure of the chart at its
origin:

* the ring-theoretic fields (regularity, `𝔪' A' = ⟨yᵢ⟩`, `dim A' = n`) are proved in
  `Hironaka/Algebra/Local/ChartLocal.lean`;
* `∂'ⱼ yₖ = δⱼₖ` transfers along the localization map (`Derivation.localization_algebraMap`);
* the `∂'ⱼ` commute.  The `∂ⱼ` extended to `R[1/x_r]` commute (the extension of a commutator is
  the commutator of the extensions, `Derivation.localization_comm`), and for two commuting
  derivations `D₁`, `D₂` and ring elements `f`, `g` one has the derivation identity
  `[f D₁, g D₂] = f (D₁ g) D₂ − g (D₂ f) D₁`; the five cases `i < j < r`, `i < j = r`,
  `i < r < j`, `i = r < j`, `r < i < j` are then read off the table `∂ⱼ x_r = δⱼᵣ`,
  `∂ⱼ yₖ = δⱼₖ u − δⱼᵣ xₖ u²` (`k < r`, `u = 1/x_r`) of `Hironaka/Algebra/Local/Chart.lean` — e.g.
  for `i < j = r`,
  `[x_r ∂ᵢ, ∂_r] = −∂ᵢ` and `∑_{k<r} [x_r ∂ᵢ, yₖ ∂ₖ] = ∑_{k<r} δᵢₖ x_r u ∂ₖ = ∂ᵢ`.  The
  commutation then descends to `R'` (`chartDerivRing`) and extends to `A'`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

/-! ### Commutators of scaled derivations -/

section Commutator

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]

/-- `[f D₁, g D₂] = f (D₁ g) D₂ − g (D₂ f) D₁` for commuting derivations `D₁`, `D₂`. -/
theorem _root_.Derivation.commutator_smul_smul (D₁ D₂ : Derivation k B B) (h : ⁅D₁, D₂⁆ = 0)
    (f g : B) : ⁅f • D₁, g • D₂⁆ = (f * D₁ g) • D₂ - (g * D₂ f) • D₁ := by
  ext z
  have h' : D₁ (D₂ z) = D₂ (D₁ z) := by
    have := congrArg (fun D : Derivation k B B => D z) h
    simpa [Derivation.commutator_apply, sub_eq_zero] using this
  simp only [Derivation.commutator_apply, Derivation.smul_apply, Derivation.sub_apply,
    Derivation.leibniz, smul_eq_mul, h']
  ring

end Commutator

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n) (r : Fin n)

/-- The extended coordinate derivations `∂ᵢ`, `∂ⱼ` of `R[1/x_r]` commute. -/
theorem awayPderiv_commutator (i j : Fin n) : ⁅c.awayPderiv r i, c.awayPderiv r j⁆ = 0 := by
  ext z
  rw [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero]
  exact Derivation.localization_comm _ (c.pderiv i) (c.pderiv j) (c.pderiv_comm i j) z

/-- The transformed derivations `∂'ᵢ`, `∂'ⱼ` commute, `i < j` (the five cases of the module
docstring). -/
theorem chartDeriv_commutator_of_lt {i j : Fin n} (hij : i < j) :
    ⁅c.chartDeriv r i, c.chartDeriv r j⁆ = 0 := by
  classical
  have hE := c.awayPderiv_commutator r
  rcases lt_trichotomy j r with hj | hj | hj
  · -- `i < j < r`
    rw [c.chartDeriv_of_lt r (hij.trans hj), c.chartDeriv_of_lt r hj,
      Derivation.commutator_smul_smul _ _ (hE i j), awayPderiv_algebraMap_x,
      awayPderiv_algebraMap_x, ite_eq_right (hij.trans hj).ne, ite_eq_right hj.ne]
    simp
  · -- `i < j = r`
    rw [hj]
    have hir : i < r := hj ▸ hij
    rw [c.chartDeriv_of_lt r hir, c.chartDeriv_self r, lie_add, lie_sum]
    have h1 : ⁅algebraMap R (Localization.Away (c.x r)) (c.x r) • c.awayPderiv r i,
        c.awayPderiv r r⁆ = -c.awayPderiv r i := by
      rw [← one_smul (Localization.Away (c.x r)) (c.awayPderiv r r),
        Derivation.commutator_smul_smul _ _ (hE i r), awayPderiv_algebraMap_x, ite_eq_left rfl,
        Derivation.map_one_eq_zero]
      simp
    have h2 : ∀ k ∈ Finset.univ.filter (fun k : Fin n => k < r),
        ⁅algebraMap R (Localization.Away (c.x r)) (c.x r) • c.awayPderiv r i,
          chartY c.x r k • c.awayPderiv r k⁆ = if i = k then c.awayPderiv r i else 0 := by
      intro k hk
      have hk' : k < r := (Finset.mem_filter.mp hk).2
      rw [Derivation.commutator_smul_smul _ _ (hE i k), awayPderiv_algebraMap_x,
        ite_eq_right hk'.ne, awayPderiv_chartY_of_lt c r i hk', ite_eq_right hir.ne]
      by_cases hik : i = k
      · subst hik
        simp [algebraMap_mul_invX]
      · simp [hik]
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_ite_eq]
    simp [hir]
  · -- `r < j`
    rw [c.chartDeriv_of_gt r hj]
    rcases lt_trichotomy i r with hi | hi | hi
    · -- `i < r < j`
      rw [c.chartDeriv_of_lt r hi, ← one_smul (Localization.Away (c.x r)) (c.awayPderiv r j),
        Derivation.commutator_smul_smul _ _ (hE i j), Derivation.map_one_eq_zero,
        awayPderiv_algebraMap_x, ite_eq_right hj.ne']
      simp
    · -- `i = r < j`
      rw [hi, c.chartDeriv_self r, add_lie, sum_lie, hE r j, zero_add]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' : k < r := (Finset.mem_filter.mp hk).2
      rw [← one_smul (Localization.Away (c.x r)) (c.awayPderiv r j),
        Derivation.commutator_smul_smul _ _ (hE k j), Derivation.map_one_eq_zero,
        awayPderiv_chartY_of_lt c r j hk', ite_eq_right (hk'.trans hj).ne', ite_eq_right hj.ne']
      simp
    · -- `r < i < j`
      rw [c.chartDeriv_of_gt r hi, hE i j]

/-- The transformed derivations commute. -/
theorem chartDeriv_commutator (i j : Fin n) : ⁅c.chartDeriv r i, c.chartDeriv r j⁆ = 0 := by
  rcases lt_trichotomy i j with h | h | h
  · exact c.chartDeriv_commutator_of_lt r h
  · rw [h]; exact lie_self _
  · rw [← lie_skew, c.chartDeriv_commutator_of_lt r h, neg_zero]

theorem chartDeriv_comm (i j : Fin n) (z : Localization.Away (c.x r)) :
    c.chartDeriv r i (c.chartDeriv r j z) = c.chartDeriv r j (c.chartDeriv r i z) := by
  have := congrArg (fun D : Derivation ℚ (Localization.Away (c.x r)) (Localization.Away (c.x r)) =>
    D z) (c.chartDeriv_commutator r i j)
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem chartDerivRing_comm (i j : Fin n) (z : chartRing c.x r) :
    c.chartDerivRing r i (c.chartDerivRing r j z) =
      c.chartDerivRing r j (c.chartDerivRing r i z) :=
  Subtype.ext (c.chartDeriv_comm r i j z)

/-- `∂'ᵢ yⱼ = δᵢⱼ` in the chart ring `R'`. -/
theorem chartDerivRing_chartYR (i j : Fin n) :
    c.chartDerivRing r i (chartYR c.x r j) = if i = j then 1 else 0 := by
  apply Subtype.ext
  rw [coe_chartDerivRing]
  change c.chartDeriv r i (chartY c.x r j) = _
  rw [chartDeriv_chartY]
  split_ifs <;> simp

/-! ### The coordinate structure on `R'_{𝔪'}` -/

section ChartCoords

instance chartOrigin_isPrime : (chartOrigin c.x r).IsPrime :=
  (chartOrigin_isMaximal c.x r c.span_x c.card).isPrime

/-- `∂'ᵢ yⱼ = δᵢⱼ` in `R'_{𝔪'}`. -/
theorem localization_chartDerivRing_algebraMap_chartYR (i j : Fin n) :
    (c.chartDerivRing r i).localization (chartOrigin c.x r).primeCompl
      (algebraMap (chartRing c.x r) (Localization.AtPrime (chartOrigin c.x r))
        (chartYR c.x r j)) =
      if i = j then 1 else 0 := by
  rw [Derivation.localization_algebraMap, chartDerivRing_chartYR]
  split_ifs <;> simp

/-- The coordinate structure on `A' = R'_{𝔪'}`: parameters the images of `y₀, …, y_{n-1}`,
derivations the localized `∂'ⱼ` — Kollár's local coordinates on the chart
[Kol07, Definition 60]. -/
noncomputable def chartCoords :
    haveI := isRegularLocalRing_localization_chartOrigin c.x r c.span_x c.card
    RegularCoords (Localization.AtPrime (chartOrigin c.x r)) n :=
  haveI := isRegularLocalRing_localization_chartOrigin c.x r c.span_x c.card
  { x := fun i => algebraMap (chartRing c.x r) _ (chartYR c.x r i)
    pderiv := fun j => (c.chartDerivRing r j).localization (chartOrigin c.x r).primeCompl
    span_x := maximalIdeal_localization_chartOrigin c.x r
    card := (ringKrullDim_localization_chartOrigin c.x r c.span_x c.card).symm
    pderiv_x := localization_chartDerivRing_algebraMap_chartYR c r
    pderiv_comm := fun i j f => Derivation.localization_comm _ (c.chartDerivRing r i)
      (c.chartDerivRing r j) (c.chartDerivRing_comm r i j) f }

/-- The coordinate structure of the chart in existential form: `R'_{𝔪'}` is regular local and
carries coordinates whose parameters are the images of the `yᵢ` and whose derivations extend
the transformed derivations `∂'ⱼ` of `R'`. -/
theorem exists_chartCoords :
    ∃ h : IsRegularLocalRing (Localization.AtPrime (chartOrigin c.x r)),
      letI := h
      ∃ c' : RegularCoords (Localization.AtPrime (chartOrigin c.x r)) n,
        c'.x = (fun i => algebraMap (chartRing c.x r) _ (chartYR c.x r i)) ∧
        ∀ (j : Fin n) (f : chartRing c.x r), ∃ g : chartRing c.x r,
          (g : Localization.Away (c.x r)) = c.chartDeriv r j f ∧
          c'.pderiv j (algebraMap (chartRing c.x r) _ f) = algebraMap (chartRing c.x r) _ g :=
  ⟨isRegularLocalRing_localization_chartOrigin c.x r c.span_x c.card, c.chartCoords r, rfl,
    fun j f => ⟨c.chartDerivRing r j f, rfl, Derivation.localization_algebraMap _ _ f⟩⟩

end ChartCoords

end RegularCoords

end IsLocalRing
