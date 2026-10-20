/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.GluedOffCenter
public import Hironaka.AnalyticSpace.Model
public import Hironaka.AnalyticSpace.Oka.Model
public import Mathlib.Analysis.InnerProductSpace.Basic
import Hironaka.AnalyticSpace.ModelSupport
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transition
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The standard blow-up chart map on the model space

In a blow-up chart (condition (2) of [BM88, Definition 4.1], `IsBlowUpChart`) the blowing-up
reads as the polynomial map `π_i = blowUpChartMap σ i` of `𝕜ⁿ` (`x_{σ i} ↦ x_{σ i}`,
`x_{σ k} ↦ x_{σ i} x_{σ k}`, the other coordinates fixed), and the exceptional divisor as the
coordinate hyperplane `{x_{σ i} = 0}`. This file sets up that model on the affine space `Kn 𝕜 n`
(the universe-lifted `𝕜ⁿ`, an analytic manifold over itself):

* `stdBlowUpMap 𝕜 σ i : Kn 𝕜 n → Kn 𝕜 n`, analytic (`contMDiff_stdBlowUpMap`);
* off the hyperplane it is the partial diffeomorphism `blowUpChartMapDiffeo`, so its germ maps
  there are bijective (`germMap_stdBlowUpMap_bijective`);
* `stdExceptional 𝕜 σ i`, the principal ideal sheaf of the coordinate `x_{σ i}`, the exceptional
  ideal sheaf of the model (`stalkIdeal_stdExceptional`).

The model serves the statement that reduction commutes with the strict transform
([BM97, Remark 3.14]); the model statement over `ℂ` (Rückert) is
`Hironaka.Manifold.BlowUp.Transform.Reduced.ModelComplex`.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped Manifold ContDiff
open AnalyticSpace

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n c : ℕ} (σ : Fin c ↪ Fin n) (i : Fin c)

variable (𝕜) in
/-- The standard blow-up chart map `π_i` on the model `Kn 𝕜 n`. -/
def stdBlowUpMap : Kn.{u} 𝕜 n → Kn.{u} 𝕜 n := fun x => ⟨blowUpChartMap σ i x.down⟩

/-- The model map in coordinates. -/
@[simp] theorem stdBlowUpMap_down (x : Kn.{u} 𝕜 n) :
    (stdBlowUpMap 𝕜 σ i x).down = blowUpChartMap σ i x.down := rfl

/-- The model map is the chart diffeomorphism `blowUpChartMapDiffeo` read on `Kⁿ`. -/
theorem stdBlowUpMap_eq_diffeo (x : Kn.{u} 𝕜 n) :
    stdBlowUpMap 𝕜 σ i x = BlowUpGlue.blowUpChartMapDiffeo (knCoord.{u} 𝕜 n) σ i
        x := rfl

/-- The model map is analytic (polynomial). -/
theorem contMDiff_stdBlowUpMap :
    ContMDiff 𝓘(𝕜, Kn.{u} 𝕜 n) 𝓘(𝕜, Kn.{u} 𝕜 n) ω (stdBlowUpMap 𝕜 σ i) := by
  rw [contMDiff_iff_contDiff]
  have h1 : ContDiff 𝕜 ω (blowUpChartMap (𝕜 := 𝕜) σ i) := contDiff_blowUpChartMap (𝕜 := 𝕜) σ
  exact (knCoord.{u} 𝕜 n).symm.contDiff.comp
      (h1.comp (knCoord.{u} 𝕜 n).contDiff)

/-- The scaling coordinate is preserved by the model map. -/
theorem stdBlowUpMap_down_scaling (x : Kn.{u} 𝕜 n) :
    (stdBlowUpMap 𝕜 σ i x).down (σ i) = x.down (σ i) := by
  rw [stdBlowUpMap_down, blowUpChartMap_apply_scaling]

/-- Off the exceptional hyperplane `{x_{σ i} = 0}` the germ maps of the model map are bijective (it
is the partial diffeomorphism `blowUpChartMapDiffeo` there). -/
theorem germMap_stdBlowUpMap_bijective {q : Kn.{u} 𝕜 n} (hq : q.down (σ i) ≠ 0) :
    Function.Bijective (germMap (stdBlowUpMap 𝕜 σ i) (contMDiff_stdBlowUpMap σ i) q) := by
  set Φ := BlowUpGlue.blowUpChartMapDiffeo (knCoord.{u} 𝕜 n) σ i with hΦ
  have hΦq : q ∈ Φ.source := hq
  have hbij : ∀ (b : Kn.{u} 𝕜 n) (hb : Φ q = b), Function.Bijective
      (germMapOn (Φ : Kn.{u} 𝕜 n → Kn.{u} 𝕜 n) (V := ⟨Φ.source, Φ.open_source⟩)
        Φ.contMDiffOn_toFun hΦq hb) := by
    rintro b rfl
    exact germMapOn_partialDiffeomorph_bijective Φ hΦq
  have hΦeq : (Φ : Kn.{u} 𝕜 n → Kn.{u} 𝕜 n) q = stdBlowUpMap 𝕜 σ i q :=
    (stdBlowUpMap_eq_diffeo σ i q).symm
  have heq : germMap (stdBlowUpMap 𝕜 σ i) (contMDiff_stdBlowUpMap σ i) q =
      germMapOn (Φ : Kn.{u} 𝕜 n → Kn.{u} 𝕜 n) (V := ⟨Φ.source, Φ.open_source⟩)
        Φ.contMDiffOn_toFun hΦq hΦeq := by
    refine RingHom.ext fun s => ?_
    apply stalkToGerm_injective 𝓘(𝕜, Kn.{u} 𝕜 n) ω (Kn.{u} 𝕜 n) q
    rw [stalkToGerm_germMap, stalkToGerm_germMapOn]
    induction stalkToGerm 𝓘(𝕜, Kn.{u} 𝕜 n) ω (Kn.{u} 𝕜 n) (stdBlowUpMap 𝕜 σ i q) s
      using Filter.Germ.inductionOn with
    | h f =>
      rw [Filter.Germ.coe_compTendsto, Filter.Germ.coe_compTendsto]
      rfl
  rw [heq]
  exact hbij _ hΦeq

/-! ## The exceptional ideal sheaf of the model -/

/-- A single global section generates an ideal sheaf (its principal ideal sheaf). -/
theorem hasLocalGenerators_span_germ_top {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {N : Type u} [TopologicalSpace N] [ChartedSpace E N]
    (t : (structureSheaf 𝕜 E N).presheaf.obj (op ⊤)) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N)
      fun x => Ideal.span {(structureSheaf 𝕜 E N).presheaf.germ ⊤ x trivial t} :=
  fun a => ⟨⊤, trivial, Unit, inferInstance, fun _ => t, fun b _ => by rw [Set.range_const]⟩

variable (𝕜) in
/-- The exceptional ideal sheaf of the model, the principal
ideal sheaf of the scaling coordinate `x_{σ i}`. -/
def stdExceptional : IdealSheaf (structureSheaf 𝕜 (Kn.{u} 𝕜 n) (Kn.{u} 𝕜 n)) :=
  IdealSheaf.ofStalks _ _ (hasLocalGenerators_span_germ_top (E := Kn.{u} 𝕜 n) (N := Kn.{u} 𝕜 n)
    (AnalyticSpace.coordSection 𝕜 n (σ i)))

/-- The stalks of the model's exceptional ideal sheaf are the principal
ideals of the coordinate germ `x_{σ i}`. -/
theorem stalkIdeal_stdExceptional (x : Kn.{u} 𝕜 n) :
    (stdExceptional 𝕜 σ i).stalkIdeal x =
      Ideal.span
        {(structureSheaf 𝕜 (Kn.{u} 𝕜 n) (Kn.{u} 𝕜 n)).presheaf.germ ⊤ x trivial
          (AnalyticSpace.coordSection 𝕜 n (σ i))} := by
  rw [stdExceptional, IdealSheaf.stalkIdeal_ofStalks]

/-- The cosupport of the model's exceptional ideal sheaf is the
coordinate hyperplane `{x_{σ i} = 0}`. -/
theorem mem_cosupport_stdExceptional (x : Kn.{u} 𝕜 n) :
    x ∈ (stdExceptional 𝕜 σ i).support ↔ x.down (σ i) = 0 := by
  rw [IdealSheaf.mem_support, stalkIdeal_stdExceptional, Ne, Ideal.span_singleton_eq_top]
  have h := isUnit_germ_affine_iff 𝕜 n ⊤ ⟨x, trivial⟩ (AnalyticSpace.coordSection 𝕜 n (σ i))
  exact ⟨fun hn => not_not.mp (mt h.mpr hn), fun h0 hu => (h.mp hu) h0⟩

end Manifold
