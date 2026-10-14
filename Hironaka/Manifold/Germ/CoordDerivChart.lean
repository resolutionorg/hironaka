/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Germ.CoordDeriv
public import Mathlib.RingTheory.MvPowerSeries.Derivative
import Hironaka.Manifold.Germ.PDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Partial derivatives in a chart: coordinates, restriction, germs, the Taylor homomorphism

Properties of the partial derivative `coordDeriv` in the chart `(φ, ψ)` on the sections over
`V ⊆ φ.source` and of its stalk version `coordDerivStalk`
(`Hironaka/Manifold/Germ/CoordDeriv.lean`), the operators `∂/∂x_i` of Bierstone–Milman's
regular coordinate charts [BM97, (0.3)] and of Kollár's derivative ideals [Kol07, Definition 73]:

* `coordDeriv_coordSection`: `∂_i x_j = δ_ij` — near `φ(x)` the function `x_j ∘ φ⁻¹` is the linear
  form `ψ_j`, whose derivative along `ψ⁻¹ e_i` is `e_i(j)`;
* `coordDeriv_map`: `∂_i` commutes with restriction to a smaller open `W ⊆ V` — the derivative at
  `φ(x)`, `x ∈ W`, sees only the germ of `f ∘ φ⁻¹` at `φ(x)` (`Filter.EventuallyEq.fderiv_eq`);
* `coordDerivStalk_germ`: the stalk operator is the germ of the section operator,
  `∂_i (germ f) = germ (∂_i f)` — both sides transport to the germ of `y ↦ D(f ∘ φ⁻¹)(y)(ψ⁻¹ e_i)`
  at `φ(a)`; `coordDerivStalk_coord`: `∂_i x_j = δ_ij` on the coordinate germs;
* `IsTaylorHom.pderiv`: `T_a (∂_i s) = ∂_{X_i} (T_a s)` for any `T_a` satisfying the specification
  `IsTaylorHom` — Bierstone–Milman's "`T_a` commutes with differentiation" [BM97, (0.3)], from
  `IsTaylorHom.pderiv'` of `Hironaka/Manifold/Germ/PDeriv.lean` read through the chart
  transport.

These are the facts used to compute orders and derivative ideals in a chart
(`Hironaka/Manifold/Chart/`, `Hironaka/Manifold/BlowUp/Transform/`).
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

section Sections

variable (V : Opens M) (hV : (V : Set M) ⊆ φ.source)

/-- `∂_i x_j = δ_ij` [BM97, (0.3)]: the partial derivative of the coordinate `x_j = ψ_j ∘ φ` is the
constant `δ_ij`. -/
theorem coordDeriv_coordSection (i j : Fin n) :
    coordDeriv E ψ φ hφ V hV i (coordSection E ψ φ hφ V hV j) =
      algebraMap 𝕜 ((structureSheaf 𝕜 E M).presheaf.obj (op V)) (if i = j then 1 else 0) := by
  refine Subtype.ext (funext fun x => ?_)
  have hx : (x : M) ∈ φ.source := hV x.2
  change fderiv 𝕜 (extendSection 𝕜 E (coordSection E ψ φ hφ V hV j) ∘ φ.symm) (φ x)
    (ψ.symm (Pi.single i 1)) = if i = j then 1 else 0
  have h1 : (extendSection 𝕜 E (coordSection E ψ φ hφ V hV j) ∘ φ.symm) =ᶠ[𝓝 (φ x)]
      fun y => ψ y j := by
    filter_upwards [(φ.tendsto_symm hx).eventually (V.2.mem_nhds x.2),
      φ.eventually_right_inverse' hx] with y hy hy'
    change extendSection 𝕜 E (coordSection E ψ φ hφ V hV j) (φ.symm y) = ψ y j
    rw [extendSection_of_mem 𝕜 E _ hy, coordSection_apply, hy']
  have h2 : (fun y => ψ y j) =
      ⇑((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) j).comp
        (ψ : E →L[𝕜] (Fin n → 𝕜))) := rfl
  rw [h1.fderiv_eq, h2, ContinuousLinearMap.fderiv]
  change ψ (ψ.symm (Pi.single i 1)) j = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, ite_eq_left rfl]
  · rw [Pi.single_eq_of_ne (Ne.symm h), ite_eq_right h]

/-- `∂_i` commutes with restriction to a smaller open `W ⊆ V`: the derivative at `φ(x)` only sees
the germ of `f ∘ φ⁻¹` at `φ(x)`. -/
theorem coordDeriv_map (W : Opens M) (hW : (W : Set M) ⊆ φ.source) (hWV : W ≤ V) (i : Fin n)
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    coordDeriv E ψ φ hφ W hW i ((structureSheaf 𝕜 E M).presheaf.map (homOfLE hWV).op f) =
      (structureSheaf 𝕜 E M).presheaf.map (homOfLE hWV).op (coordDeriv E ψ φ hφ V hV i f) := by
  refine Subtype.ext (funext fun x => ?_)
  have hx : (x : M) ∈ φ.source := hW x.2
  change fderiv 𝕜 (extendSection 𝕜 E ((structureSheaf 𝕜 E M).presheaf.map (homOfLE hWV).op f) ∘
    φ.symm) (φ x) (ψ.symm (Pi.single i 1)) =
      fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1))
  have h1 : (extendSection 𝕜 E ((structureSheaf 𝕜 E M).presheaf.map (homOfLE hWV).op f) ∘ φ.symm)
      =ᶠ[𝓝 (φ x)] (extendSection 𝕜 E f ∘ φ.symm) := by
    filter_upwards [(φ.tendsto_symm hx).eventually (W.2.mem_nhds x.2)] with y hy
    change extendSection 𝕜 E ((structureSheaf 𝕜 E M).presheaf.map (homOfLE hWV).op f) (φ.symm y) =
      extendSection 𝕜 E f (φ.symm y)
    rw [extendSection_of_mem 𝕜 E _ hy, extendSection_of_mem 𝕜 E f (hWV hy)]
    rfl
  rw [h1.fderiv_eq]

variable {a : M} (ha : a ∈ φ.source)

/-- The germ at `a ∈ V` of the coordinate section `x_j` over `V` is the coordinate germ `coord`. -/
theorem germ_coordSection (haV : a ∈ V) (j : Fin n) :
    (structureSheaf 𝕜 E M).presheaf.germ V a haV (coordSection E ψ φ hφ V hV j) =
      coord E ψ φ hφ ha j :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- The germ of the constant section `c` is the constant `c` of the stalk (`const`,
`algebraMap 𝕜 𝒪_{M,a}`). -/
theorem germ_algebraMap (haV : a ∈ V) (c : 𝕜) :
    (structureSheaf 𝕜 E M).presheaf.germ V a haV
        (algebraMap 𝕜 ((structureSheaf 𝕜 E M).presheaf.obj (op V)) c) =
      const 𝕜 E M a c := by
  rw [const_apply]
  have h1 : algebraMap 𝕜 ((structureSheaf 𝕜 E M).presheaf.obj (op V)) c =
      (structureSheaf 𝕜 E M).presheaf.map (homOfLE le_top).op (constSection 𝕜 E M c) := rfl
  rw [h1]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

end Sections

section Stalk

variable {a : M} (ha : a ∈ φ.source)

/-- At the stalk: `∂_i (germ f) = germ (∂_i f)` — both sides transport to the germ of
`y ↦ D(f ∘ φ⁻¹)(y)(ψ⁻¹ e_i)` at `φ(a)`. -/
theorem coordDerivStalk_germ (V : Opens M) (hV : (V : Set M) ⊆ φ.source) (haV : a ∈ V) (i : Fin n)
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    coordDerivStalk E ψ φ hφ ha i ((structureSheaf 𝕜 E M).presheaf.germ V a haV f) =
      (structureSheaf 𝕜 E M).presheaf.germ V a haV (coordDeriv E ψ φ hφ V hV i f) := by
  rw [coordDerivStalk_apply, RingEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [isChartTransport_chartTransport E φ ha hφ V haV (coordDeriv E ψ φ hφ V hV i f),
    pderivGerm_coe' E ψ i (isChartTransport_chartTransport E φ ha hφ V haV f)]
  refine Germ.coe_eq.mpr ?_
  filter_upwards [(φ.tendsto_symm ha).eventually (V.2.mem_nhds haV),
    φ.eventually_right_inverse' ha] with y hy hy'
  change fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) y (ψ.symm (Pi.single i 1)) =
    extendSection 𝕜 E (coordDeriv E ψ φ hφ V hV i f) (φ.symm y)
  rw [extendSection_of_mem 𝕜 E _ hy, coordDeriv_apply, hy']

/-- At the stalk: `∂_i x_j = δ_ij` on the coordinate germs ([BM97, (0.3)];
[Kol07, Definition 73]). -/
theorem coordDerivStalk_coord (i j : Fin n) :
    coordDerivStalk E ψ φ hφ ha i (coord E ψ φ hφ ha j) =
      const 𝕜 E M a (if i = j then 1 else 0) := by
  rw [← germ_coordSection E ψ φ hφ ⟨φ.source, φ.open_source⟩ subset_rfl ha ha j,
    coordDerivStalk_germ E ψ φ hφ ha _ subset_rfl ha, coordDeriv_coordSection, germ_algebraMap]

/-- At the stalk: `∂_i (x_j − x_j(a)) = δ_ij` on the centred coordinate germs — the axiom
`pderiv_x` of the `Hironaka` library's regular coordinates (`IsLocalRing.RegularCoords`). -/
theorem coordDerivStalk_coord_sub_const (i j : Fin n) :
    coordDerivStalk E ψ φ hφ ha i
        (coord E ψ φ hφ ha j - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha j))) =
      if i = j then 1 else 0 := by
  rw [map_sub, coordDerivStalk_coord, coordDerivStalk_const, sub_zero]
  split_ifs <;> simp only [map_one, map_zero]

/-- "`T_a` commutes with differentiation" [BM97, (0.3)]: for any `T` satisfying the specification
`IsTaylorHom`, `T (∂_i s) = ∂_{X_i} (T s)` — `IsTaylorHom.pderiv'` read through the chart
transport. -/
theorem IsTaylorHom.pderiv
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) (i : Fin n) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    T (coordDerivStalk E ψ φ hφ ha i s) = MvPowerSeries.pderiv (R := 𝕜) i (T s) := by
  have h := IsTaylorHom.pderiv' E ψ φ ha hφ hT (isChartTransport_chartTransport E φ ha hφ) i
    (chartTransport E φ ha hφ s)
  rwa [RingEquiv.symm_apply_apply] at h

end Stalk

end Manifold

end
