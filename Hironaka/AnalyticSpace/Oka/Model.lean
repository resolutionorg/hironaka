/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Germ.StalkNoetherian
public import Hironaka.AnalyticSpace.Defs
public import Hironaka.Analytic.Weierstrass.Basic
public import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Analytic.Weierstrass.FunctionLevel
import Hironaka.Analytic.Weierstrass.Tail
import Hironaka.Manifold.Germ.ResidueCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The Taylor isomorphism on the model space `Kⁿ` and the projection to the base

The analogue over `K` of the third step of the proof of Oka's coherence theorem [Fre17, Ch. I,
10.3], which Freitag carries out over `ℂ`, works at every point `a` of a product `U = V × D ⊆ Kⁿ`
with the power series expansions at `a` and the projection `U → V`. On the model `Kⁿ = Kn K n` (the
type `ULift (Fin n → K)`, a manifold over itself, with `sheafKn K n = 𝒜_{Kⁿ}` its sheaf of analytic
functions) this module fixes:

* `taylorKn ψ a : 𝒜_{Kⁿ,a} ≃+* Conv K n`, the Taylor isomorphism onto the convergent power series
  (`taylorEquivConv`) in the linear coordinates `ψ` and the identity chart, and `TKn ψ a` its
  underlying ring homomorphism into the formal power series (the Taylor homomorphism, characterised
  by `IsTaylorHom`); `ψ = knCoord K n` are the `ULift` coordinates, and `ψ = L ∘ knCoord` a linear
  change of coordinates;
* the projection `projKn ψ : Kn K (m + 1) →L[K] Kn K m` forgetting the distinguished coordinate
  `x_0 = ψ_0` (`Fin.tail` in coordinates; analytic as a continuous linear map);
* the Taylor series of the constants (`TKn_const`), of the centred coordinates
  (`TKn_coord_sub_const`: `x_i − x_i(a) ↦ X_i`), and of a section pulled back from the base along
  the projection (`TKn_germ_comapSection`: `T_a (g ∘ π) = liftTail (T_{π a} g)`, by the uniqueness
  of the power series of a germ, `eq_of_evalSeries_sub_eventuallyEq`, and `evalSeries_liftTail`).

Every statement here is bookkeeping for the induction of `Hironaka.AnalyticSpace.Oka.Main`.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Manifold
open Analytic
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace AnalyticSpace

variable (K : Type) [RCLike K]

/-- The coordinates of `Kⁿ = ULift (Fin n → K)`: the forgetful linear isometry. -/
abbrev knCoord (n : ℕ) : Kn.{u} K n ≃L[K] (Fin n → K) := ContinuousLinearEquiv.ulift

/-- `𝒜_{Kⁿ}`, the sheaf of analytic functions of `Kⁿ` as a manifold over itself (the structure sheaf
of the affine space `affine K n`). -/
abbrev sheafKn (n : ℕ) : TopCat.Sheaf CommRingCat.{u} (TopCat.of (Kn.{u} K n)) :=
  structureSheaf K (Kn.{u} K n) (Kn.{u} K n)

variable {K} {n : ℕ} (ψ : Kn.{u} K n ≃L[K] (Fin n → K))

/-- The Taylor homomorphism at `a ∈ Kⁿ` in the linear coordinates `ψ` and the identity chart
(`taylorHom`); `ψ = knCoord K n` are the `ULift` coordinates, `ψ = L ∘ knCoord` a linear change of
coordinates ("after a suitable linear coordinate transformation", [Fre17, Ch. I, 10.3]). -/
def TKn (a : Kn.{u} K n) : (sheafKn K n).presheaf.stalk a →+* MvPowerSeries (Fin n) K :=
  taylorHom (Kn.{u} K n) ψ (chartAt (Kn.{u} K n) a) (mem_chart_source _ a)
    (IsManifold.chart_mem_maximalAtlas a)

theorem isTaylorHom_TKn (a : Kn.{u} K n) :
    IsTaylorHom (Kn.{u} K n) ψ (chartAt (Kn.{u} K n) a) a (TKn ψ a) :=
  isTaylorHom_taylorHom _ _ _ _ _

theorem TKn_mem_conv (a : Kn.{u} K n) (s : (sheafKn K n).presheaf.stalk a) :
    TKn ψ a s ∈ Analytic.Conv K n :=
  taylorHom_mem_conv _ _ _ _ _ s

/-- The Taylor isomorphism `𝒜_{Kⁿ,a} ≃+* Conv K n` in the coordinates `ψ` (`taylorEquivConv` on the
model `Kⁿ`). -/
def taylorKn (a : Kn.{u} K n) : (sheafKn K n).presheaf.stalk a ≃+* Analytic.Conv K n :=
  taylorEquivConv (Kn.{u} K n) ψ (chartAt (Kn.{u} K n) a) (mem_chart_source _ a)
    (IsManifold.chart_mem_maximalAtlas a)

theorem taylorKn_apply_coe (a : Kn.{u} K n) (s : (sheafKn K n).presheaf.stalk a) :
    (taylorKn ψ a s : MvPowerSeries (Fin n) K) = TKn ψ a s := rfl

theorem TKn_injective (a : Kn.{u} K n) : Function.Injective (TKn ψ a) := fun _ _ h =>
  (taylorKn ψ a).injective (Subtype.ext h)

/-- Every convergent series is the Taylor series of a germ. -/
theorem exists_TKn_eq (a : Kn.{u} K n) {c : MvPowerSeries (Fin n) K} (hc : c ∈ Analytic.Conv K n) :
    ∃ s : (sheafKn K n).presheaf.stalk a, TKn ψ a s = c :=
  ⟨(taylorKn ψ a).symm ⟨c, hc⟩, by
    rw [← taylorKn_apply_coe, RingEquiv.apply_symm_apply]⟩

/-- The Taylor series of a constant is the constant series. -/
theorem TKn_const (a : Kn.{u} K n) (c : K) :
    TKn ψ a (const K (Kn.{u} K n) (Kn.{u} K n) a c) = MvPowerSeries.C c :=
  IsTaylorHom.map_const _ _ _ (IsManifold.chart_mem_maximalAtlas a) (mem_chart_source _ a)
    (isTaylorHom_TKn ψ a) c

/-- The coordinate germ `x_i = ψ_i` at `a` (`coord` in the coordinates `ψ`). -/
def coordKn (a : Kn.{u} K n) (i : Fin n) : (sheafKn K n).presheaf.stalk a :=
  coord (Kn.{u} K n) ψ (chartAt (Kn.{u} K n) a) (IsManifold.chart_mem_maximalAtlas a)
    (mem_chart_source _ a) i

theorem eval_coordKn (a : Kn.{u} K n) (i : Fin n) :
    Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) a (coordKn ψ a i) = ψ a i := by
  unfold coordKn
  rw [eval_coord, chartAt_self_eq]
  rfl

/-- The Taylor series of the centred coordinate `x_i − a_i` is `X_i`. -/
theorem TKn_coord_sub_const (a : Kn.{u} K n) (i : Fin n) :
    TKn ψ a (coordKn ψ a i - const K (Kn.{u} K n) (Kn.{u} K n) a (ψ a i)) =
      MvPowerSeries.X i := by
  rw [← eval_coordKn ψ a i]
  exact IsTaylorHom.map_coord_sub_const _ _ _ (IsManifold.chart_mem_maximalAtlas a)
    (mem_chart_source _ a) (isTaylorHom_TKn ψ a) i

section Projection

variable (K) (m : ℕ)

/-- Forgetting the first coordinate, `Fin.tail`, as a continuous linear map over `K`. -/
def tailProjCLM : (Fin (m + 1) → K) →L[K] (Fin m → K) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

theorem tailProjCLM_apply (y : Fin (m + 1) → K) : tailProjCLM K m y = Fin.tail y := rfl

variable {K m} (ψ : Kn.{u} K (m + 1) ≃L[K] (Fin (m + 1) → K))

/-- The projection `Kᵐ⁺¹ → Kᵐ` forgetting the distinguished coordinate `x_0 = ψ_0`, as a continuous
linear map (the projection `V × (−r, r) → V` of [Fre17, Ch. I, 10.3]); the base carries the `ULift`
coordinates. -/
def projKn : Kn.{u} K (m + 1) →L[K] Kn.{u} K m :=
  ((knCoord K m).symm : (Fin m → K) →L[K] Kn.{u} K m).comp
    ((tailProjCLM K m).comp (ψ : Kn.{u} K (m + 1) →L[K] (Fin (m + 1) → K)))

theorem projKn_apply (y : Kn.{u} K (m + 1)) : projKn ψ y = ULift.up (Fin.tail (ψ y)) := rfl

theorem down_projKn (y : Kn.{u} K (m + 1)) : (projKn ψ y).down = Fin.tail (ψ y) := rfl

theorem contMDiff_projKn :
    ContMDiff 𝓘(K, Kn.{u} K (m + 1)) 𝓘(K, Kn.{u} K m) ω (projKn ψ) :=
  (projKn ψ).contMDiff

/-- The extension by zero of a pulled-back section is the pulled-back extension. -/
theorem extendSection_comapSection {U : Opens (Kn.{u} K m)}
    (g : (sheafKn K m).presheaf.obj (op U)) (x : Kn.{u} K (m + 1)) :
    extendSection K (Kn.{u} K (m + 1)) (comapSection (projKn ψ) (contMDiff_projKn ψ) g) x =
      extendSection K (Kn.{u} K m) g (projKn ψ x) := by
  by_cases hx : projKn ψ x ∈ U
  · rw [extendSection_of_mem _ _ g hx,
      extendSection_of_mem _ _ _ ((mem_preimageOpens _ _).mpr hx : x ∈ preimageOpens _ _ U),
      comapSection_apply]
  · simp only [extendSection, extendBy0, dite_eq_right hx]
    rw [dite_eq_right]
    exact fun h => hx ((mem_preimageOpens _ _).mp h)

/-- The Taylor series at `a` (coordinates `ψ`) of a section pulled back from the base along the
projection is the lift of its Taylor series at `π a` (coefficients "independent of `z_n`", [Fre17,
Ch. I, 10.3]). -/
theorem TKn_germ_comapSection (a : Kn.{u} K (m + 1)) {U : Opens (Kn.{u} K m)}
    (hU : projKn ψ a ∈ U) (g : (sheafKn K m).presheaf.obj (op U)) :
    TKn ψ a ((sheafKn K (m + 1)).presheaf.germ (preimageOpens (projKn ψ) (contMDiff_projKn ψ) U) a
        ((mem_preimageOpens _ _).mpr hU) (comapSection (projKn ψ) (contMDiff_projKn ψ) g)) =
      liftTail (TKn (knCoord K m) (projKn ψ a)
        ((sheafKn K m).presheaf.germ U (projKn ψ a) hU g)) := by
  -- both sides are convergent series with the same germ of evaluations at `a`
  have h1 := (isTaylorHom_TKn ψ a).2 (preimageOpens (projKn ψ) (contMDiff_projKn ψ) U)
    ((mem_preimageOpens _ _).mpr hU) (comapSection (projKn ψ) (contMDiff_projKn ψ) g)
  have h2 := (isTaylorHom_TKn (knCoord K m) (projKn ψ a)).2 U hU g
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply]
    at h1 h2
  refine eq_of_evalSeries_sub_eventuallyEq ψ a (TKn_mem_conv ψ a _)
    (liftTail_mem_conv (TKn_mem_conv _ _ _)) ?_
  refine h1.symm.trans ?_
  -- `extendSection (g ∘ π) ∘ ψ⁻¹ = extendSection g ∘ up ∘ tail`
  have hcomp : ∀ y : Fin (m + 1) → K,
      (extendSection K (Kn.{u} K (m + 1)) (comapSection (projKn ψ) (contMDiff_projKn ψ) g) ∘
        id ∘ ψ.symm) y =
      (extendSection K (Kn.{u} K m) g ∘ id ∘ (knCoord K m).symm) (Fin.tail y) := by
    intro y
    simp only [Function.comp_apply, id]
    rw [extendSection_comapSection, projKn_apply, ψ.apply_symm_apply]
    rfl
  have htail :
      Tendsto Fin.tail (𝓝 (ψ a)) (𝓝 ((knCoord K m) (projKn ψ a))) := by
    have hfun : (⇑(tailProjCLM K m) : (Fin (m + 1) → K) → Fin m → K) = Fin.tail :=
      funext (tailProjCLM_apply K m)
    rw [← hfun]
    exact (tailProjCLM K m).continuous.tendsto (ψ a)
  have h3 := h2.comp_tendsto htail
  refine (Filter.EventuallyEq.of_eq (funext hcomp)).trans (h3.trans ?_)
  refine Filter.Eventually.of_forall fun y => ?_
  simp only [Function.comp_apply, evalSeries_liftTail]
  rfl

end Projection

end AnalyticSpace
