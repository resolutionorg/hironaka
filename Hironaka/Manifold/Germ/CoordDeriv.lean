/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Hironaka.Manifold.Germ.ChartTransport
import Hironaka.Manifold.Germ.StalkMap
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Partial derivatives in a chart as operators on the structure sheaf

A manifold of Bierstone–Milman's category is covered by regular coordinate charts `U` with
coordinates `x = (x_1, …, x_n)`, `x_i ∈ 𝒪_M(U)`, on which "the partial derivatives `∂^{|α|}/∂x^α`
make sense as transformations `𝒪_M(U) → 𝒪_M(U)`" [BM97, (0.3)]; Kollár's derivative of an ideal
sheaf is formed with the derivations `∂/∂x_1, …, ∂/∂x_n` of local coordinates
[Kol07, Definition 73]. For a chart `φ` of the maximal atlas with coordinates
`ψ : E ≃L[𝕜] (Fin n → 𝕜)` (the coordinate functions `x_i = ψ_i ∘ φ`) and an open `V ⊆ φ.source`,
the **`i`-th partial derivative in the chart** of a section `f` of `𝒪_M` over `V` is the section

  `(∂_i f)(x) = D(f ∘ φ⁻¹)(φ x)(ψ⁻¹ e_i)`,

the derivative at `φ(x)` of the analytic function `f ∘ φ⁻¹` on the model space along the `i`-th
coordinate vector. It is analytic (an analytic function has analytic derivative, Mathlib's
`AnalyticAt.fderiv`, composed with the analytic chart), so `∂_i` is an operator on `𝒪_M(V)`; it is
additive, `𝕜`-linear and satisfies the Leibniz rule (`fderiv_add`, `fderiv_const_smul`,
`fderiv_mul`), so it is a `𝕜`-derivation `coordDeriv E ψ φ hφ V hV i : Derivation 𝕜 𝒪_M(V) 𝒪_M(V)`.

At the stalk `𝒪_{M,a}` the same operator is
`coordDerivStalk E ψ φ hφ ha i : Derivation 𝕜 𝒪_{M,a} 𝒪_{M,a}`, defined through the chart transport
`𝒪_{M,a} ≃+* 𝒪_{E, φ(a)}` as the partial derivative `pderivGerm` of analytic germs (that the germ of
`∂_i f` is `∂_i` of the germ of `f` is `coordDerivStalk_germ` in
`Hironaka/Manifold/Germ/CoordDerivChart.lean`). The `𝕜`-algebra structures used are the
pointwise one on the sections (Mathlib's `ContMDiffMap.algebra`) and the constants
`const 𝕜 E M a : 𝕜 →+* 𝒪_{M,a}` on the stalk, with the `ℚ`-algebra structure through `ℚ → 𝕜` that
the regular coordinates of the `Hironaka` library (`IsLocalRing.RegularCoords`) require.

These derivations make the analytic stalk an instance of the `Hironaka` library's regular
coordinates (`Hironaka/Manifold/Germ/CoordDerivCoords.lean`) and enter the derivative ideal
sheaves of the maximal-contact construction (`Hironaka/Manifold/IdealSheaf/Deriv.lean`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Algebra

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- The `𝕜`-algebra structure of the sections `𝒪_M(V)`: pointwise scalars, Mathlib's
`ContMDiffMap.algebra` (the scalar `c` acts as the constant section `c`). -/
instance instAlgebraSections (V : Opens M) :
    Algebra 𝕜 ((structureSheaf 𝕜 E M).presheaf.obj (op V)) :=
  inferInstanceAs (Algebra 𝕜 C^ω⟮𝓘(𝕜, E), (V : Opens M); 𝓘(𝕜), 𝕜⟯)

theorem algebraMap_sections_apply (V : Opens M) (c : 𝕜) (x : V) :
    algebraMap 𝕜 ((structureSheaf 𝕜 E M).presheaf.obj (op V)) c x = c := rfl

/-- The `𝕜`-algebra structure of the stalk `𝒪_{M,a}` through the constants
`const 𝕜 E M a : 𝕜 →+* 𝒪_{M,a}`. -/
instance instAlgebraStalk (a : M) : Algebra 𝕜 ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  (const 𝕜 E M a).toAlgebra

theorem algebraMap_stalk_eq (a : M) :
    algebraMap 𝕜 ((structureSheaf 𝕜 E M).presheaf.stalk a) = const 𝕜 E M a := rfl

variable [CharZero 𝕜]

/-- The `ℚ`-algebra structure of the stalk `𝒪_{M,a}`, `ℚ → 𝕜 → 𝒪_{M,a}`, as the regular coordinates
of the `Hironaka` library require (`RegularCoords` takes `[Algebra ℚ R]`). -/
instance instAlgebraRatStalk (a : M) : Algebra ℚ ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  ((const 𝕜 E M a).comp (algebraMap ℚ 𝕜)).toAlgebra

theorem algebraMap_rat_stalk_eq (a : M) :
    algebraMap ℚ ((structureSheaf 𝕜 E M).presheaf.stalk a) =
      (const 𝕜 E M a).comp (algebraMap ℚ 𝕜) := rfl

instance instIsScalarTowerRatStalk (a : M) :
    IsScalarTower ℚ 𝕜 ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end Algebra

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

section ExtendSection

variable {V : Opens M}

theorem extendSection_add (f g : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    extendSection 𝕜 E (f + g) = extendSection 𝕜 E f + extendSection 𝕜 E g := by
  funext y
  by_cases hy : y ∈ V
  · rw [Pi.add_apply, extendSection_of_mem 𝕜 E _ hy, extendSection_of_mem 𝕜 E f hy,
      extendSection_of_mem 𝕜 E g hy]
    rfl
  · simp only [Pi.add_apply, extendSection, extendBy0, dite_eq_right hy, add_zero]

theorem extendSection_mul (f g : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    extendSection 𝕜 E (f * g) = extendSection 𝕜 E f * extendSection 𝕜 E g := by
  funext y
  by_cases hy : y ∈ V
  · rw [Pi.mul_apply, extendSection_of_mem 𝕜 E _ hy, extendSection_of_mem 𝕜 E f hy,
      extendSection_of_mem 𝕜 E g hy]
    rfl
  · simp only [Pi.mul_apply, extendSection, extendBy0, dite_eq_right hy, mul_zero]

theorem extendSection_smul (c : 𝕜) (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    extendSection 𝕜 E (c • f) = c • extendSection 𝕜 E f := by
  funext y
  by_cases hy : y ∈ V
  · rw [Pi.smul_apply, extendSection_of_mem 𝕜 E _ hy, extendSection_of_mem 𝕜 E f hy]
    rfl
  · simp only [Pi.smul_apply, extendSection, extendBy0, dite_eq_right hy, smul_zero]

end ExtendSection

section Sections

variable {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (φ : OpenPartialHomeomorph M E)
  (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (V : Opens M) (hV : (V : Set M) ⊆ φ.source)

include hφ hV in
/-- A section `f` of `𝒪_M` over `V ⊆ φ.source`, read in the chart, is analytic at `φ(x)` for every
`x ∈ V`. -/
theorem analyticAt_extendSection_comp_symm (f : (structureSheaf 𝕜 E M).presheaf.obj (op V))
    (x : V) : AnalyticAt 𝕜 (extendSection 𝕜 E f ∘ φ.symm) (φ x) := by
  have hx : (x : M) ∈ φ.source := hV x.2
  have h1 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (extendSection 𝕜 E f) x :=
    (contMDiffOn_extendSection f).contMDiffAt (V.2.mem_nhds x.2)
  have h2 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (extendSection 𝕜 E f ∘ φ.symm) (φ x) :=
    ContMDiffAt.comp_of_eq h1 (contMDiffAt_chart_symm E φ hx hφ) (φ.left_inv hx)
  exact (contMDiffAt_iff_contDiffAt.mp h2).analyticAt

/-- The `i`-th partial derivative in the chart of a section `f` over `V`, as a function on `V`:
`x ↦ D(f ∘ φ⁻¹)(φ x)(ψ⁻¹ e_i)`. -/
def coordDerivFun (i : Fin n) (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) : V → 𝕜 :=
  fun x => fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1))

include hφ hV in
/-- Analytic functions have analytic partial derivatives: the partial derivative in the chart of an
analytic section is analytic — `AnalyticAt.fderiv` on the model space, composed with the analytic
chart `φ`. -/
theorem contMDiff_coordDerivFun (i : Fin n) (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜) ω (coordDerivFun E ψ φ V i f) := by
  intro x
  have h4 : AnalyticAt 𝕜
      (fun y => fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) y (ψ.symm (Pi.single i 1))) (φ x) :=
    ((ContinuousLinearMap.apply 𝕜 𝕜 (ψ.symm (Pi.single i 1))).analyticAt _).comp
      (analyticAt_extendSection_comp_symm E φ hφ V hV f x).fderiv
  have h5 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω
      (fun y => fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) y (ψ.symm (Pi.single i 1))) (φ x) :=
    contMDiffAt_iff_contDiffAt.mpr h4.contDiffAt
  have h6 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (fun x : V => φ x) x :=
    ((contMDiffOn_of_mem_maximalAtlas (n := ω) hφ).comp_contMDiff contMDiff_subtype_val
      fun x => hV x.2) x
  exact h5.comp x h6

/-- The partial derivative `∂_i f` as a section of `𝒪_M` over `V`. -/
def coordDerivSection (i : Fin n) (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    (structureSheaf 𝕜 E M).presheaf.obj (op V) :=
  ⟨coordDerivFun E ψ φ V i f, contMDiff_coordDerivFun E ψ φ hφ V hV i f⟩

theorem coordDerivSection_apply (i : Fin n) (f : (structureSheaf 𝕜 E M).presheaf.obj (op V))
    (x : V) :
    coordDerivSection E ψ φ hφ V hV i f x =
      fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1)) := rfl

theorem coordDerivSection_add (i : Fin n) (f g : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    coordDerivSection E ψ φ hφ V hV i (f + g) =
      coordDerivSection E ψ φ hφ V hV i f + coordDerivSection E ψ φ hφ V hV i g := by
  refine Subtype.ext (funext fun x => ?_)
  have hf := (analyticAt_extendSection_comp_symm E φ hφ V hV f x).differentiableAt
  have hg := (analyticAt_extendSection_comp_symm E φ hφ V hV g x).differentiableAt
  change fderiv 𝕜 (extendSection 𝕜 E (f + g) ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1)) =
    fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1)) +
      fderiv 𝕜 (extendSection 𝕜 E g ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1))
  rw [extendSection_add, ← _root_.add_apply, ← fderiv_add hf hg]
  rfl

theorem coordDerivSection_smul (i : Fin n) (c : 𝕜)
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    coordDerivSection E ψ φ hφ V hV i (c • f) = c • coordDerivSection E ψ φ hφ V hV i f := by
  refine Subtype.ext (funext fun x => ?_)
  have hf := (analyticAt_extendSection_comp_symm E φ hφ V hV f x).differentiableAt
  change fderiv 𝕜 (extendSection 𝕜 E (c • f) ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1)) =
    c • fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1))
  rw [extendSection_smul, ← _root_.smul_apply, ← fderiv_const_smul hf]
  rfl

/-- The Leibniz rule: `∂_i (f g) = f ∂_i g + g ∂_i f`. -/
theorem coordDerivSection_mul (i : Fin n) (f g : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    coordDerivSection E ψ φ hφ V hV i (f * g) =
      f * coordDerivSection E ψ φ hφ V hV i g + g * coordDerivSection E ψ φ hφ V hV i f := by
  refine Subtype.ext (funext fun x => ?_)
  have hf := (analyticAt_extendSection_comp_symm E φ hφ V hV f x).differentiableAt
  have hg := (analyticAt_extendSection_comp_symm E φ hφ V hV g x).differentiableAt
  have hx : (x : M) ∈ φ.source := hV x.2
  change fderiv 𝕜 (extendSection 𝕜 E (f * g) ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1)) =
    f x * fderiv 𝕜 (extendSection 𝕜 E g ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1)) +
      g x * fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1))
  rw [extendSection_mul]
  change fderiv 𝕜 ((extendSection 𝕜 E f ∘ φ.symm) * (extendSection 𝕜 E g ∘ φ.symm)) (φ x)
    (ψ.symm (Pi.single i 1)) = _
  rw [fderiv_mul hf hg, _root_.add_apply, _root_.smul_apply,
    _root_.smul_apply, smul_eq_mul, smul_eq_mul, Function.comp_apply,
    Function.comp_apply, φ.left_inv hx, extendSection_of_mem 𝕜 E f x.2,
    extendSection_of_mem 𝕜 E g x.2]

/-- **The `i`-th partial derivative in the chart** `∂_i : 𝒪_M(V) → 𝒪_M(V)`, for `V ⊆ φ.source`, as
a `𝕜`-derivation of the sections [BM97, (0.3)]. -/
def coordDeriv (i : Fin n) :
    Derivation 𝕜 ((structureSheaf 𝕜 E M).presheaf.obj (op V))
      ((structureSheaf 𝕜 E M).presheaf.obj (op V)) :=
  Derivation.mk'
    { toFun := coordDerivSection E ψ φ hφ V hV i
      map_add' := coordDerivSection_add E ψ φ hφ V hV i
      map_smul' := coordDerivSection_smul E ψ φ hφ V hV i }
    (coordDerivSection_mul E ψ φ hφ V hV i)

theorem coordDeriv_apply (i : Fin n) (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) (x : V) :
    coordDeriv E ψ φ hφ V hV i f x =
      fderiv 𝕜 (extendSection 𝕜 E f ∘ φ.symm) (φ x) (ψ.symm (Pi.single i 1)) := rfl

/-- The coordinate `x_j = ψ_j ∘ φ` as a section of `𝒪_M` over `V ⊆ φ.source` (`chartSection`
restricted to `V`). -/
def coordSection (j : Fin n) : (structureSheaf 𝕜 E M).presheaf.obj (op V) :=
  (structureSheaf 𝕜 E M).presheaf.map
    (homOfLE (show V ≤ ⟨φ.source, φ.open_source⟩ from hV)).op (chartSection E ψ φ hφ j)

theorem coordSection_apply (j : Fin n) (x : V) : coordSection E ψ φ hφ V hV j x = ψ (φ x) j := rfl

end Sections

section Stalk

variable {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

theorem pderivGerm_coe' (i : Fin n) {b : E} {g : analyticGermsAt 𝕜 E b} {F : E → 𝕜}
    (hF : (g : (𝓝 b).Germ 𝕜) = ↑F) :
    (pderivGerm E ψ i b g : (𝓝 b).Germ 𝕜) =
      ↑(fun y => fderiv 𝕜 F y (ψ.symm (Pi.single i 1))) := by
  obtain ⟨g, hg⟩ := g
  change g = ↑F at hF
  subst hF
  rfl

/-- At the level of germs: `∂_i` (`pderivGerm`) is additive. -/
theorem pderivGerm_add (i : Fin n) (b : E) (g h : analyticGermsAt 𝕜 E b) :
    pderivGerm E ψ i b (g + h) = pderivGerm E ψ i b g + pderivGerm E ψ i b h := by
  obtain ⟨g, f, rfl, hf⟩ := g
  obtain ⟨h, f', rfl, hf'⟩ := h
  refine Subtype.ext ?_
  rw [Subring.coe_add, pderivGerm_coe' E ψ i (F := f + f') rfl, pderivGerm_coe' E ψ i (F := f) rfl,
    pderivGerm_coe' E ψ i (F := f') rfl, ← Germ.coe_add]
  refine Germ.coe_eq.mpr ?_
  filter_upwards [hf.eventually_analyticAt, hf'.eventually_analyticAt] with y hy hy'
  change fderiv 𝕜 (f + f') y _ = fderiv 𝕜 f y _ + fderiv 𝕜 f' y _
  rw [fderiv_add hy.differentiableAt hy'.differentiableAt, _root_.add_apply]

/-- At the level of germs: the Leibniz rule for `∂_i` (`pderivGerm`). -/
theorem pderivGerm_mul (i : Fin n) (b : E) (g h : analyticGermsAt 𝕜 E b) :
    pderivGerm E ψ i b (g * h) = g * pderivGerm E ψ i b h + h * pderivGerm E ψ i b g := by
  obtain ⟨g, f, rfl, hf⟩ := g
  obtain ⟨h, f', rfl, hf'⟩ := h
  refine Subtype.ext ?_
  rw [pderivGerm_coe' E ψ i (F := f * f') rfl, Subring.coe_add, Subring.coe_mul, Subring.coe_mul,
    pderivGerm_coe' E ψ i (F := f') rfl, pderivGerm_coe' E ψ i (F := f) rfl, ← Germ.coe_mul,
    ← Germ.coe_mul, ← Germ.coe_add]
  refine Germ.coe_eq.mpr ?_
  filter_upwards [hf.eventually_analyticAt, hf'.eventually_analyticAt] with y hy hy'
  change fderiv 𝕜 (f * f') y _ = f y * fderiv 𝕜 f' y _ + f' y * fderiv 𝕜 f y _
  rw [fderiv_mul hy.differentiableAt hy'.differentiableAt, _root_.add_apply,
    _root_.smul_apply, _root_.smul_apply, smul_eq_mul, smul_eq_mul]

variable (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M}
  (ha : a ∈ φ.source)

/-- The partial derivative `∂_i` on `𝒪_{M,a}`, as a function: `pderivGerm` on analytic germs,
transported by the chart transport. -/
def coordDerivStalkFun (i : Fin n) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    (structureSheaf 𝕜 E M).presheaf.stalk a :=
  (chartTransport E φ ha hφ).symm (pderivGerm E ψ i (φ a) (chartTransport E φ ha hφ s))

theorem coordDerivStalkFun_add (i : Fin n) (s t : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    coordDerivStalkFun E ψ φ hφ ha i (s + t) =
      coordDerivStalkFun E ψ φ hφ ha i s + coordDerivStalkFun E ψ φ hφ ha i t := by
  unfold coordDerivStalkFun
  rw [map_add, pderivGerm_add, map_add]

theorem coordDerivStalkFun_mul (i : Fin n) (s t : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    coordDerivStalkFun E ψ φ hφ ha i (s * t) =
      s * coordDerivStalkFun E ψ φ hφ ha i t + t * coordDerivStalkFun E ψ φ hφ ha i s := by
  unfold coordDerivStalkFun
  rw [map_mul, pderivGerm_mul, map_add, map_mul, map_mul, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply]

/-- The chart transport of a constant germ is the constant germ. -/
theorem chartTransport_const (c : 𝕜) :
    (chartTransport E φ ha hφ (const 𝕜 E M a c) : (𝓝 (φ a)).Germ 𝕜) = ↑(fun _ : E => c) := by
  rw [const_apply, isChartTransport_chartTransport E φ ha hφ ⊤ trivial (constSection 𝕜 E M c)]
  refine congrArg _ (funext fun y => ?_)
  exact extendSection_of_mem 𝕜 E (constSection 𝕜 E M c) trivial

/-- `∂_i` kills the constants. -/
theorem coordDerivStalkFun_const (i : Fin n) (c : 𝕜) :
    coordDerivStalkFun E ψ φ hφ ha i (const 𝕜 E M a c) = 0 := by
  unfold coordDerivStalkFun
  rw [← map_zero (chartTransport E φ ha hφ).symm]
  refine congrArg _ (Subtype.ext ?_)
  rw [pderivGerm_coe' E ψ i (chartTransport_const E φ hφ ha c), Subring.coe_zero]
  refine congrArg _ (funext fun y => ?_)
  rw [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply]

/-- **The partial derivative `∂_i` on `𝒪_{M,a}`** as a `𝕜`-derivation, for a chart `φ` of the
maximal atlas containing `a` with coordinates `ψ` ([BM97, (0.3)]; the derivations
`∂/∂x_1, …, ∂/∂x_n` of [Kol07, Definition 73]). -/
def coordDerivStalk (i : Fin n) :
    Derivation 𝕜 ((structureSheaf 𝕜 E M).presheaf.stalk a)
      ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  Derivation.mk'
    { toFun := coordDerivStalkFun E ψ φ hφ ha i
      map_add' := coordDerivStalkFun_add E ψ φ hφ ha i
      map_smul' := fun c s => by
        change coordDerivStalkFun E ψ φ hφ ha i (c • s) = c • coordDerivStalkFun E ψ φ hφ ha i s
        rw [Algebra.smul_def, Algebra.smul_def, algebraMap_stalk_eq, coordDerivStalkFun_mul,
          coordDerivStalkFun_const, mul_zero, add_zero] }
    (coordDerivStalkFun_mul E ψ φ hφ ha i)

theorem coordDerivStalk_apply (i : Fin n) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    coordDerivStalk E ψ φ hφ ha i s =
      (chartTransport E φ ha hφ).symm (pderivGerm E ψ i (φ a) (chartTransport E φ ha hφ s)) :=
  rfl

theorem coordDerivStalk_const (i : Fin n) (c : 𝕜) :
    coordDerivStalk E ψ φ hφ ha i (const 𝕜 E M a c) = 0 :=
  coordDerivStalkFun_const E ψ φ hφ ha i c

end Stalk

end Manifold

end
