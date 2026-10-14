/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Germ.StalkNoetherian
public import Hironaka.Algebra.Local.FormalAut
public import Hironaka.Algebra.Local.PowerSeriesRegular
public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Algebra.Local.Prop94
import Hironaka.Manifold.Chart.MaximalContact
import Hironaka.Manifold.Germ.CoordDerivChart
import Hironaka.Manifold.Germ.CoordDerivCoords
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Proposition 94 for the analytic stalk, through the Taylor homomorphism

Kollár applies his Proposition 94 to the completed ideal `Î ⊆ 𝒪̂_p ≅ 𝕜⟦X⟧` of an MC-invariant `I`
[Kol07, 95]. The analytic bridge is the Taylor homomorphism `T_e : 𝒪_{M,p} → 𝕜⟦X⟧` of a chart `e`
at `p` (`Hironaka/Manifold/Germ/TaylorHom.lean`), which is injective and carries the coordinate
derivations to the formal partial derivatives (`IsTaylorHom.pderiv`):

* `D_map_taylorHom`, `Dpow_map_taylorHom`, `MC_map_taylorHom`: the derivative ideals of the
  `Hironaka` library's regular coordinates (`IsLocalRing.RegularCoords`) transport along `T_e`,
  `T_e(D(J)) 𝕜⟦X⟧ = D(T_e(J) 𝕜⟦X⟧)` (`RegularCoords.D_map` for the regular coordinates of the
  stalk and of `𝕜⟦X⟧`);
* `isMCInvariant_map_taylorHom`: MC-invariance of `I` (the sheaf inequality `MC(I) · D(I) ≤ I`)
  gives MC-invariance of `Î := T_e(I_p) 𝕜⟦X⟧` in the standard coordinates;
* `map_taylorHom_MC_le_maximalIdeal`: at a point of order exactly `m ≥ 1`, `T_e(MC(I)_p) ⊆ (X)`;
* `isInvariantOnePlus_map_taylorHom`: hence, by Proposition 94
  (`isMCInvariant_iff_isInvariantOnePlus` of `Hironaka/Algebra/Local/Prop94.lean`), `Î` is invariant
  under every automorphism of `𝕜⟦X⟧` of the form `1 + T_e(MC(I)_p)` [Kol07, Proposition 94].

This is the input of the coordinate swap's action on `I_p`
(`Hironaka/Resolution/Analytic/MaximalContact/SwapRealizes.lean`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace IsLocalRing MvPowerSeries
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-! ### Transport of the derivative ideals along the Taylor homomorphism -/

section Transport

variable [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] (φ : OpenPartialHomeomorph M E)
  (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M} (ha : a ∈ φ.source)

include ψ in
/-- The dimension of the stalk is `n`. -/
theorem dim_stalk_eq :
    (n : WithBot ℕ∞) = ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk a) := by
  rw [ringKrullDim_stalk E a, LinearEquiv.finrank_eq ψ.toLinearEquiv, Module.finrank_fin_fun]

/-- The transport of the derivative ideal along the Taylor homomorphism (`RegularCoords.D_map`;
`T_e` carries the coordinate derivations of the stalk to the formal partial derivatives):
`D(T_e(J)) = T_e(D(J))` for the regular coordinates `c` of the stalk in the chart `e` and the
standard coordinates of `𝕜⟦X⟧`. -/
theorem D_map_taylorHom (c : RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk a) n)
    (hcp : ∀ i, c.pderiv i = (coordDerivStalk E ψ φ hφ ha i).restrictScalars ℚ)
    (J : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk a)) :
    (RegularCoords.stdMvPowerSeries 𝕜 n).D (J.map (taylorHom E ψ φ ha hφ)) =
      (c.D J).map (taylorHom E ψ φ ha hφ) := by
  refine RegularCoords.D_map c (RegularCoords.stdMvPowerSeries 𝕜 n) (taylorHom E ψ φ ha hφ) id
    (fun i f => ?_) (fun j hj => absurd ⟨j, rfl⟩ hj) J
  change (MvPowerSeries.pderiv (R := 𝕜) i).restrictScalars ℚ (taylorHom E ψ φ ha hφ f) = _
  rw [hcp, Derivation.restrictScalars_apply, Derivation.restrictScalars_apply,
    IsTaylorHom.pderiv E ψ φ hφ ha (isTaylorHom_taylorHom E ψ φ ha hφ)]

/-- The iterated derivative ideals transport along the Taylor homomorphism. -/
theorem Dpow_map_taylorHom (c : RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk a) n)
    (hcp : ∀ i, c.pderiv i = (coordDerivStalk E ψ φ hφ ha i).restrictScalars ℚ) (r : ℕ)
    (J : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk a)) :
    (RegularCoords.stdMvPowerSeries 𝕜 n).Dpow r (J.map (taylorHom E ψ φ ha hφ)) =
      (c.Dpow r J).map (taylorHom E ψ φ ha hφ) := by
  induction r generalizing J with
  | zero => rfl
  | succ r ih =>
    rw [RegularCoords.Dpow_succ', RegularCoords.Dpow_succ', D_map_taylorHom E ψ φ hφ ha c hcp, ih]

/-- The maximal contact ideal transports along the Taylor homomorphism. -/
theorem MC_map_taylorHom (c : RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk a) n)
    (hcp : ∀ i, c.pderiv i = (coordDerivStalk E ψ φ hφ ha i).restrictScalars ℚ) (m : ℕ)
    (J : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk a)) :
    (RegularCoords.stdMvPowerSeries 𝕜 n).MC (J.map (taylorHom E ψ φ ha hφ)) m =
      (c.MC J m).map (taylorHom E ψ φ ha hφ) :=
  Dpow_map_taylorHom E ψ φ hφ ha c hcp (m - 1) J

end Transport

/-! ### MC-invariance of the Taylor image and Proposition 94 -/

section Prop94

variable {M : AnalyticManifold.{u} 𝕜 E} [FiniteDimensional 𝕜 E]
  (I : AnalyticManifold.IdealSheaf M)
  {m : ℕ} (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) {p : M}
  (hpe : p ∈ e.source)

/-- The MC-invariance `MC(I) · D(I) ≤ I` of the ideal sheaf gives, at `p`, the MC-invariance of
`Î = T_e(I_p) 𝕜⟦X⟧` in the standard coordinates (Kollár's `MC(I)` and `MC(Î)`, [Kol07, 95]). -/
theorem isMCInvariant_map_taylorHom (hI : I.iteratedDeriv (m - 1) * I.deriv ≤ I) :
    (RegularCoords.stdMvPowerSeries 𝕜 n).IsMCInvariant
      ((I.stalkIdeal p).map (taylorHom E ψ e hpe he)) m := by
  obtain ⟨c, -, hcp, hk, hs⟩ := exists_regularCoords_stalk E ψ e he hpe (dim_stalk_eq E ψ)
  have h1 : c.MC (I.stalkIdeal p) m * c.D (I.stalkIdeal p) ≤ I.stalkIdeal p := by
    have := IdealSheaf.le_def.mp hI p
    rwa [IdealSheaf.stalkIdeal_mul, IdealSheaf.stalkIdeal_iteratedDeriv_eq_Dpow (J := I) c hk hs,
      IdealSheaf.stalkIdeal_deriv_eq_D (J := I) c hk hs] at this
  change (RegularCoords.stdMvPowerSeries 𝕜 n).MC _ m * (RegularCoords.stdMvPowerSeries 𝕜 n).D _ ≤ _
  rw [MC_map_taylorHom E ψ e he hpe c hcp, D_map_taylorHom E ψ e he hpe c hcp, ← Ideal.map_mul]
  exact Ideal.map_mono h1

/-- At a point of order exactly `m ≥ 1`, the Taylor image of `MC(I)_p` lies in the maximal ideal
`(X)` of `𝕜⟦X⟧` (`MC(I)` has order `1` there, `ord_iteratedDeriv_eq_one`). -/
theorem map_taylorHom_MC_le_maximalIdeal (hm : 1 ≤ m) (hp : I.ord p = m) :
    ((I.iteratedDeriv (m - 1)).stalkIdeal p).map (taylorHom E ψ e hpe he) ≤
      maximalIdeal (MvPowerSeries (Fin n) 𝕜) := by
  have h1 : (I.iteratedDeriv (m - 1)).stalkIdeal p ≤
      maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk p) := by
    have h := ord_iteratedDeriv_eq_one (E := E) (I := I) hm hp
    have h2 : ((1 : ℕ) : ℕ∞) ≤ (I.iteratedDeriv (m - 1)).ord p := by rw [h]; rfl
    rw [IdealSheaf.ord, le_ord_iff, pow_one] at h2
    exact h2
  rw [Ideal.map_le_iff_le_comap]
  intro s hs
  rw [Ideal.mem_comap, ← pow_one (maximalIdeal (MvPowerSeries (Fin n) 𝕜)),
    taylorHom_mem_maximalIdeal_pow_iff, pow_one]
  exact h1 hs

/-- Kollár's Proposition 94 applied ([Kol07, Proposition 94]; [Kol07, 95]): for `I` MC-invariant
and `p` of order exactly `m ≥ 1`, the ideal `Î = T_e(I_p) 𝕜⟦X⟧` is invariant under every
automorphism of `𝕜⟦X⟧` of the form `1 + T_e(MC(I)_p)`. -/
theorem isInvariantOnePlus_map_taylorHom (hm : 1 ≤ m) (hI : I.iteratedDeriv (m - 1) * I.deriv ≤ I)
    (hp : I.ord p = m) :
    IsInvariantOnePlus ((I.stalkIdeal p).map (taylorHom E ψ e hpe he))
      (((I.iteratedDeriv (m - 1)).stalkIdeal p).map (taylorHom E ψ e hpe he)) := by
  obtain ⟨c, -, hcp, hk, hs⟩ := exists_regularCoords_stalk E ψ e he hpe (dim_stalk_eq E ψ)
  have hMC : (RegularCoords.stdMvPowerSeries 𝕜 n).MC
      ((I.stalkIdeal p).map (taylorHom E ψ e hpe he)) m =
      ((I.iteratedDeriv (m - 1)).stalkIdeal p).map (taylorHom E ψ e hpe he) := by
    rw [MC_map_taylorHom E ψ e he hpe c hcp, RegularCoords.MC,
      IdealSheaf.stalkIdeal_iteratedDeriv_eq_Dpow (J := I) c hk hs]
  have hB := map_taylorHom_MC_le_maximalIdeal E ψ I e he hpe hm hp
  rw [← hMC] at hB ⊢
  exact (isMCInvariant_iff_isInvariantOnePlus _ m hB).mp
    (isMCInvariant_map_taylorHom E ψ I e he hpe hI)

end Prop94

end Hironaka.Manifold

end
