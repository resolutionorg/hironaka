/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Chart
public import Hironaka.Manifold.BlowUp.Defs
public import Hironaka.Manifold.Germ.CoordDeriv
public import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Algebra.Local.ChartCoords
import Hironaka.Manifold.BlowUp.CoordGerm
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.IdealSheaf.GermMapChainRule
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's chart formulas: the transformed derivations of the chart ring

Kollár computes, in the blow-up chart with coordinates `y_j = x_j / x_r` (`j < r`), `y_r = x_r`,
`y_j = x_j` (`j > r`), the derivatives of `f ∘ π` by the chain rule:
`∂_{y_j}(f ∘ π) = x_r (∂_{x_j} f) ∘ π` for `j < r`, `(∂_{x_j} f) ∘ π` for `j > r`, and
`(∂_{x_r} f) ∘ π + ∑_{i<r} y_i (∂_{x_i} f) ∘ π` for `j = r`: the unmarked content of
[Kol07, 75, (75.1)–(75.3)]. The version for schemes packages exactly these three formulas as the
transformed derivations `∂'_j` of the chart ring `R' = R[x_i/x_r : i < r]` (`chartDerivRing` of
`Hironaka.Algebra.Local.ChartCoords`). This file proves that the ring map `χ : R' → 𝒪_{M', a'}` of
`Hironaka.Manifold.BlowUp.Transform.KollarChart` carries `∂'_j` to the partial derivative
`∂_{u_{τ j}}` of the blow-up chart `Φ` (`τ` Kollár's order of the coordinates, `τ r = σ i`):

* `chartRingHom_chartDerivRing_eq_coordDerivStalk`: `χ(∂'_j g) = ∂_{u_{τ j}}(χ g)` for every `g`.

Both sides are derivations of `R'` along `χ` (additive, Leibniz along `χ`), so it suffices to
compare them on the generators of `R'` over `R`: on `algebraMap R R'` the comparison is the chain
rule for germs (`derivation_germMap_eq_sum_coordDerivStalk`) together with the pullbacks of the
coordinates along the blow-up chart (`x_k ∘ π = u_{σ i} u_k` on the centre block, `= u_k`
transversally), and on the `y_i` both sides are `δ_{ij}` (`chartDerivRing_chartYR`;
`χ(y_i) = u_{τ i}`).

This is the rule by which the derivative of a birational transform is computed in
`Hironaka.Manifold.BlowUp.Transform.DerivTransform`.
-/

public section

noncomputable section

open TopologicalSpace IsLocalRing
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] {Y : Set M} {c : ℕ} {M' : Type u}
  [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M} {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
  {i : Fin c} {Φ : OpenPartialHomeomorph M' E}

section Coordinates

variable (h : IsBlowUp ψ Y c π) (hφ : IsAdaptedChart ψ Y φ σ) (hΦ : IsBlowUpChart ψ π φ σ i Φ)
  {a' : M'} (ha' : a' ∈ Φ.source) (haY : π a' ∈ Y)
  (x : Fin n → (structureSheaf 𝕜 E M).presheaf.stalk (π a')) (r : Fin n) (τ : Fin n ≃ Fin n)
  (hτr : τ r = σ i)
  (hτ : ∀ j, x j = coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ j) -
    const 𝕜 E M (π a') (eval 𝕜 E M (π a') (coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ j))))
  (hlt : ∀ j, j < r ↔ ∃ k, k ≠ i ∧ τ j = σ k)

include haY hτ

omit [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] in
/-- On the centre block the centred coordinates are the adapted coordinates (which vanish at the
points of `Y`). -/
theorem x_eq_coord_of_eq_σ {m : Fin n} {k : Fin c} (hmk : τ m = σ k) :
    x m = coord E ψ φ hφ.1 (hΦ.source_subset ha') (σ k) := by
  rw [hτ m, hmk, eval_coord, (hφ.2 _ (hΦ.source_subset ha')).1 haY k, map_zero, sub_zero]

include hτr hlt in
omit [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] in
/-- [Kol07, Definition 60, (60.2)] for the centre block: `x_m ∘ π = u_{τ r} u_{τ m}` for `m < r`. -/
theorem germMap_x_of_lt {m : Fin n} (hm : m < r) :
    germMap π h.contMDiff a' (x m) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ r) * coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ m) := by
  obtain ⟨k, hk, hmk⟩ := (hlt m).mp hm
  rw [x_eq_coord_of_eq_σ hφ hΦ ha' haY x τ hτ hmk,
    IsBlowUpChart.germMap_coord_of_ne h.contMDiff hφ.1 hΦ ha' hk, ← hτr, ← hmk]

include hτr in
omit [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] in
/-- [Kol07, Definition 60, (60.2)] for the divisor coordinate: `x_r ∘ π = u_{τ r}`. -/
theorem germMap_x_self :
    germMap π h.contMDiff a' (x r) = coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ r) := by
  rw [x_eq_coord_of_eq_σ hφ hΦ ha' haY x τ hτ hτr,
    IsBlowUpChart.germMap_coord_self h.contMDiff hφ.1 hΦ ha', hτr]

include hτr hlt in
omit haY [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] in
/-- [Kol07, Definition 60, (60.2)] for the transversal coordinates:
`x_m ∘ π = u_{τ m} − u_{τ m}(a')` for `m > r`. -/
theorem germMap_x_of_gt {m : Fin n} (hm : r < m) :
    germMap π h.contMDiff a' (x m) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ m) -
        const 𝕜 E M' a' (eval 𝕜 E M (π a') (coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ m))) := by
  have hoff : ∀ k, σ k ≠ τ m := by
    intro k hk
    by_cases hki : k = i
    · subst hki
      exact hm.ne (τ.injective (hτr.trans hk))
    · exact absurd ((hlt m).mpr ⟨k, hki, hk.symm⟩) (not_lt.mpr hm.le)
  rw [hτ m, map_sub, IsBlowUpChart.germMap_coord_off h.contMDiff hφ.1 hΦ ha' hoff]
  congr 1
  exact germMap_algebraMap π h.contMDiff a' _

end Coordinates

section Formulas

variable (h : IsBlowUp ψ Y c π) (hφ : IsAdaptedChart ψ Y φ σ) (hΦ : IsBlowUpChart ψ π φ σ i Φ)
  {a' : M'} (ha' : a' ∈ Φ.source) (haY : π a' ∈ Y)
  (κ : RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) n) (r : Fin n)
  (τ : Fin n ≃ Fin n) (hτr : τ r = σ i)
  (hτ : ∀ j, κ.x j = coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ j) -
    const 𝕜 E M (π a') (eval 𝕜 E M (π a') (coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ j))))
  (hpd : ∀ j, κ.pderiv j =
    (coordDerivStalk E ψ φ hφ.1 (hΦ.source_subset ha') (τ j)).restrictScalars ℚ)
  (hlt : ∀ j, j < r ↔ ∃ k, k ≠ i ∧ τ j = σ k)
  (χ : chartRing κ.x r →+* (structureSheaf 𝕜 E M').presheaf.stalk a')
  (hχ : ∀ s, χ (algebraMap _ _ s) = germMap π h.contMDiff a' s)
  (hχy : ∀ j, j < r → χ (chartYR κ.x r j) = coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j))

include haY hτr hτ hpd hlt hχ hχy

/-- The transformed derivations `∂'_j` of
the chart ring (`chartDerivRing`) are carried by the chart-ring map `χ` to the
partial derivatives `∂_{u_{τ j}}` of the blow-up chart: `χ(∂'_j g) = ∂_{u_{τ j}}(χ g)`
[Kol07, 75, (75.1)–(75.3)]. -/
theorem chartRingHom_chartDerivRing_eq_coordDerivStalk (j : Fin n) (g : chartRing κ.x r) :
    χ (κ.chartDerivRing r j g) = coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) (χ g) := by
  classical
  have haφ : π a' ∈ φ.source := hΦ.source_subset ha'
  -- `δ` on the coordinates of the blow-up chart
  have hδu : ∀ m, coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)
      (coord E ψ Φ hΦ.mem_maximalAtlas ha' m) = if τ j = m then 1 else 0 :=
    fun m => coordDerivStalk_coord_eq_ite hΦ.mem_maximalAtlas ha' (τ j) m
  -- `δ` of the pulled-back coordinates
  have hδx_lt : ∀ m, m < r → coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)
      (germMap π h.contMDiff a' (κ.x m)) =
        coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ r) * (if τ j = τ m then 1 else 0) +
          coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ m) * (if τ j = τ r then 1 else 0) := by
    intro m hm
    rw [germMap_x_of_lt h hφ hΦ ha' haY κ.x r τ hτr hτ hlt hm, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul, hδu, hδu]
  have hδx_r : coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)
      (germMap π h.contMDiff a' (κ.x r)) = if τ j = τ r then 1 else 0 := by
    rw [germMap_x_self h hφ hΦ ha' haY κ.x r τ hτr hτ, hδu]
  have hδx_gt : ∀ m, r < m → coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)
      (germMap π h.contMDiff a' (κ.x m)) = if τ j = τ m then 1 else 0 := by
    intro m hm
    rw [germMap_x_of_gt h hφ hΦ ha' κ.x r τ hτr hτ hlt hm, map_sub, hδu,
      coordDerivStalk_const, sub_zero]
  -- the two closed forms of `δ (x_m ∘ π)`
  have hδx_ne : j ≠ r → ∀ m, m ≠ j →
      coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)
        (germMap π h.contMDiff a' (κ.x m)) = 0 := by
    intro hjr m hmj
    have h1 : τ j ≠ τ m := τ.injective.ne (Ne.symm hmj)
    have h2 : τ j ≠ τ r := τ.injective.ne hjr
    rcases lt_trichotomy m r with hm | rfl | hm
    · rw [hδx_lt m hm, ite_eq_right h1, ite_eq_right h2, mul_zero, mul_zero, add_zero]
    · rw [hδx_r, ite_eq_right h2]
    · rw [hδx_gt m hm, ite_eq_right h1]
  have hδx_self : j ≠ r → coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)
      (germMap π h.contMDiff a' (κ.x j)) =
        if j < r then coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ r) else 1 := by
    intro hjr
    have h2 : τ j ≠ τ r := τ.injective.ne hjr
    rcases lt_trichotomy j r with hj | hj | hj
    · rw [hδx_lt j hj, ite_eq_left rfl, ite_eq_right h2, ite_eq_left hj, mul_one, mul_zero,
        add_zero]
    · exact absurd hj hjr
    · rw [hδx_gt j hj, ite_eq_left rfl, ite_eq_right (not_lt.mpr hj.le)]
  -- the chain rule, reindexed by `τ`
  have hchain : ∀ f, coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)
      (germMap π h.contMDiff a' f) =
        ∑ m, coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)
          (germMap π h.contMDiff a' (κ.x m)) * germMap π h.contMDiff a' (κ.pderiv m f) := by
    intro f
    rw [derivation_germMap_eq_sum_coordDerivStalk ψ π h.contMDiff φ hφ.1 haφ]
    exact (Fintype.sum_equiv τ _ _ fun m => by
      rw [hpd m, Derivation.restrictScalars_apply, hτ m]).symm
  -- on `algebraMap R R'`
  have hGalg : ∀ f : (structureSheaf 𝕜 E M).presheaf.stalk (π a'),
      χ (κ.chartDerivRing r j (algebraMap _ _ f)) =
      coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) (χ (algebraMap _ _ f)) := by
    intro f
    rw [hχ, hchain]
    rcases lt_trichotomy j r with hj | rfl | hj
    · -- (75.1): `∂'_j = x_r ∂_j`
      have hL : κ.chartDerivRing r j (algebraMap _ _ f) =
          algebraMap _ _ (κ.x r) * algebraMap _ _ (κ.pderiv j f) := by
        apply Subtype.ext
        rw [κ.coe_chartDerivRing r j]
        simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
        rw [κ.chartDeriv_of_lt r hj, Derivation.smul_apply, smul_eq_mul,
          κ.awayPderiv_algebraMap r j f]
      rw [hL, map_mul, hχ, hχ, germMap_x_self h hφ hΦ ha' haY κ.x r τ hτr hτ,
        Finset.sum_eq_single j (fun m _ hm => by rw [hδx_ne hj.ne m hm, zero_mul])
          (fun hj' => absurd (Finset.mem_univ j) hj'),
        hδx_self hj.ne, ite_eq_left hj]
    · -- (75.3): `∂'_r = ∂_r + ∑_{i<r} y_i ∂_i`
      have hL : κ.chartDerivRing j j (algebraMap _ _ f) =
          algebraMap _ _ (κ.pderiv j f) +
            ∑ m ∈ Finset.univ.filter (fun m : Fin n => m < j),
              chartYR κ.x j m * algebraMap _ _ (κ.pderiv m f) := by
        apply Subtype.ext
        rw [κ.coe_chartDerivRing j j]
        simp only [Subalgebra.coe_add, Subalgebra.coe_algebraMap, AddSubmonoidClass.coe_finsetSum,
          Subalgebra.coe_mul]
        rw [κ.chartDeriv_self j, Derivation.add_apply, derivation_sum_apply,
          κ.awayPderiv_algebraMap j j f]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Derivation.smul_apply, smul_eq_mul, κ.awayPderiv_algebraMap j m f]
        rfl
      rw [hL, map_add, map_sum, hχ]
      have hR : ∀ m, coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)
          (germMap π h.contMDiff a' (κ.x m)) * germMap π h.contMDiff a' (κ.pderiv m f) =
            if m < j then coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ m) *
              germMap π h.contMDiff a' (κ.pderiv m f)
            else if m = j then germMap π h.contMDiff a' (κ.pderiv j f) else 0 := by
        intro m
        rcases lt_trichotomy m j with hm | rfl | hm
        · rw [hδx_lt m hm, ite_eq_left hm, ite_eq_right (τ.injective.ne hm.ne'), ite_eq_left rfl,
            mul_zero, zero_add, mul_one]
        · rw [hδx_r, ite_eq_left rfl, ite_eq_right (lt_irrefl m), ite_eq_left rfl, one_mul]
        · rw [hδx_gt m hm, ite_eq_right (τ.injective.ne hm.ne), ite_eq_right (not_lt.mpr hm.le),
            ite_eq_right hm.ne', zero_mul]
      rw [Finset.sum_congr rfl fun m _ => hR m, Finset.sum_ite, Finset.sum_ite_eq',
        ite_eq_left (by simp), add_comm]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [map_mul, hχy m (Finset.mem_filter.mp hm).2, hχ]
    · -- (75.2): `∂'_j = ∂_j`
      have hL : κ.chartDerivRing r j (algebraMap _ _ f) = algebraMap _ _ (κ.pderiv j f) := by
        apply Subtype.ext
        rw [κ.coe_chartDerivRing r j]
        simp only [Subalgebra.coe_algebraMap]
        rw [κ.chartDeriv_of_gt r hj, κ.awayPderiv_algebraMap r j f]
      rw [hL, hχ,
        Finset.sum_eq_single j (fun m _ hm => by rw [hδx_ne hj.ne' m hm, zero_mul])
          (fun hj' => absurd (Finset.mem_univ j) hj'),
        hδx_self hj.ne', ite_eq_right (not_lt.mpr hj.le), one_mul]
  -- on the `y_k`
  have hGy : ∀ k, k < r → χ (κ.chartDerivRing r j (chartYR κ.x r k)) =
      coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) (χ (chartYR κ.x r k)) := by
    intro k hk
    rw [κ.chartDerivRing_chartYR r j k, hχy k hk, hδu]
    split_ifs with h1 h2 h2
    · exact map_one χ
    · exact absurd (congrArg τ h1) h2
    · exact absurd (τ.injective h2) h1
    · exact map_zero χ
  -- the generators of the chart ring
  obtain ⟨z, hz⟩ := g
  refine Algebra.adjoin_induction
    (p := fun z hz => χ (κ.chartDerivRing r j ⟨z, hz⟩) =
      coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) (χ ⟨z, hz⟩)) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨k, hk, rfl⟩
    have hy : (⟨Localization.mk (κ.x k) ⟨κ.x r, Submonoid.mem_powers _⟩, Algebra.subset_adjoin
        ⟨k, hk, rfl⟩⟩ : chartRing κ.x r) = chartYR κ.x r k :=
      Subtype.ext (chartYOf_of_lt κ.x r (κ.x r) hk).symm
    rw [hy]
    exact hGy k hk
  · intro f
    exact hGalg f
  · intro z w hz hw ihz ihw
    change χ (κ.chartDerivRing r j (⟨z, hz⟩ + ⟨w, hw⟩)) =
      coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) (χ (⟨z, hz⟩ + ⟨w, hw⟩))
    rw [map_add, map_add, ihz, ihw, map_add, map_add]
  · intro z w hz hw ihz ihw
    change χ (κ.chartDerivRing r j (⟨z, hz⟩ * ⟨w, hw⟩)) =
      coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) (χ (⟨z, hz⟩ * ⟨w, hw⟩))
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, ihz, ihw,
      map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm]

end Formulas

end Manifold

end
