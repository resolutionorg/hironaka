/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.LogDeriv
public import Hironaka.Manifold.FiniteSuccession.Restrict.Restrict
public import Hironaka.Manifold.Germ.StalkMap
public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.Germ.CoordDerivChart
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Logarithmic derivatives commute with restriction to the hypersurface

Kollár's (87.1) [Kol07, 87]: the derivative in the direction normal to `S` does not restrict to
`S`, but the logarithmic derivatives do, "`(D^r(−log S)(I))|_S = D^r(I|_S)`".

The content is the descent of the tangential coordinate derivations along the restriction of
germs `ρ : 𝒪_{M,x} → 𝒪_{S,x}` (the stalk map of the inclusion `S ↪ M`): in a chart `φ` adapted to
`S` with `S = (x_h = 0)`, the hypersurface carries the induced chart `φ_S = projCompl ∘ ψ ∘ φ`
(`IsAdaptedChart.chartOn`, the coordinates other than `x_h`), whose inverse is
`φ⁻¹ ∘ ψ⁻¹ ∘ embedCompl` — the adapted chart's inverse after a continuous linear embedding. The
chain rule therefore identifies the `j`-th partial derivative of `f|_S` in `φ_S` with the
restriction of the partial derivative of `f` in the direction of the `j`-th complementary
coordinate (`comapSection_coordDeriv_inclusionMap`, then at the germ level
`germMap_inclusionMap_coordDerivStalk`). Hence, since `ρ(x_h) = 0` kills the `x_h ∂_h` generators
and the `∂_j` (`j ≠ h`) descend to the coordinate derivations of `S`, the image of
`D(−log S)(I)_x = ⟨I, x_h ∂_h I, ∂_j I⟩` under `ρ` is `D(ρ I)`
(`map_germMap_logDerivative_eq_derivative`), and (87.1) follows by induction on `r`
(`logDerivIter_pullback_inclusionMap`). This is the step by which order reduction on the
hypersurface of maximal contact controls the logarithmic derivatives on the ambient manifold
(`Hironaka/Manifold/BlowUp/Transform/LogDerivTransform.lean`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Set Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### The complementary embedding as a continuous linear map -/

section Compl

variable {n c : ℕ} (σ : Fin c ↪ Fin n)

/-- `embedCompl σ` is `𝕜`-linear. -/
def embedComplₗ : (Fin (n - c) → 𝕜) →ₗ[𝕜] (Fin n → 𝕜) where
  toFun := embedCompl σ
  map_add' w w' := by
    funext j
    simp only [embedCompl, Pi.add_apply]
    split_ifs <;> simp
  map_smul' a w := by
    funext j
    simp only [embedCompl, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

/-- `embedCompl σ` as a continuous linear map. -/
def embedComplL : (Fin (n - c) → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
  LinearMap.toContinuousLinearMap (embedComplₗ σ)

@[simp] theorem embedComplL_apply (w : Fin (n - c) → 𝕜) : embedComplL σ w = embedCompl σ w := rfl

/-- `embedCompl σ` sends the `j`-th basis vector of `𝕜^{n−c}` to the basis vector of `𝕜^n` at
the `j`-th complementary index. -/
theorem embedCompl_single (j : Fin (n - c)) :
    embedCompl σ (Pi.single j (1 : 𝕜)) = Pi.single ((complEquiv σ).symm j).1 1 := by
  funext i
  by_cases h : i ∈ Set.range σ
  · rw [embedCompl, dite_eq_left h, Pi.single_apply, ite_eq_right]
    rintro rfl
    exact ((complEquiv σ).symm j).2 h
  · rw [embedCompl, dite_eq_right h]
    by_cases hk : complEquiv σ ⟨i, h⟩ = j
    · have hi : i = ((complEquiv σ).symm j).1 := by rw [← hk, Equiv.symm_apply_apply]
      rw [Pi.single_apply, ite_eq_left hk, Pi.single_apply, ite_eq_left hi]
    · have hi : i ≠ ((complEquiv σ).symm j).1 := fun hi =>
        hk ((Equiv.eq_symm_apply (complEquiv σ)).mp (Subtype.ext hi))
      rw [Pi.single_apply, ite_eq_right hk, Pi.single_apply, ite_eq_right hi]

end Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M] [T2Space M]
  [SecondCountableTopology M] {S : Set M} (hS : IsClosedSubmanifold ψ S 1)
    (p : hS.toAnalyticManifold)

/-! ### The descent of the tangential coordinate derivations

Conventions: the point of `S` is `p : hS.toAnalyticManifold`; its image in `M` is written
`hS.inclusionMap p` throughout (the chart lemmas of closed submanifolds are instantiated at that
point through their implicit argument, so that rewriting matches syntactically), and the ambient
adapted chart at `p` is taken at `hS.subOf p`, the same point read in the subtype `↥S` — the
carrier of the bundled manifold unfolds to `↥S` only definitionally, and `rw`'s motive check needs
the syntactic type. -/

/-- The point `p` of the bundled hypersurface read in the subtype `↥S` (an identity cast). -/
def IsClosedSubmanifold.subOf (hS : IsClosedSubmanifold ψ S 1) (p : hS.toAnalyticManifold) : S := p

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.inclusionMap_eq_val_subOf (hS : IsClosedSubmanifold ψ S 1)
    (p : hS.toAnalyticManifold) : hS.inclusionMap p = (hS.subOf p : M) := rfl

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The chart of the bundled hypersurface at `p` is the chart induced by the adapted chart at `p`
(`IsClosedSubmanifold.chartedSpace`, definitionally). -/
theorem chartAt_toAnalyticManifold_eq :
    chartAt (Fin (n - 1) → 𝕜) p = (hS.isAdaptedChart_adaptedChartAt (hS.subOf p)).chartOn
      (hS.subOf p).2 := rfl

/-- The complementary index of the `j`-th coordinate of the induced chart at `p`. -/
abbrev complIdx (j : Fin (n - 1)) : Fin n := ((complEquiv (hS.adaptedIdx (hS.subOf p))).symm j).1

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem complIdx_notMem_range (j : Fin (n - 1)) :
    complIdx hS p j ∉ Set.range (hS.adaptedIdx (hS.subOf p)) := ((complEquiv (hS.adaptedIdx
      (hS.subOf p))).symm j).2

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The image of `p` in `M` lies in the source of the adapted chart at `p`. -/
theorem inclusionMap_mem_source_adaptedChartAt :
    hS.inclusionMap p ∈ (hS.adaptedChartAt (hS.subOf p)).source := hS.mem_source_adaptedChartAt
      (hS.subOf p)

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem inclusionMap_mem (q : hS.toAnalyticManifold) : hS.inclusionMap q ∈ S := q.2

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Kollár's "`∂f/∂x_i |_S = ∂(f|_S)/∂x_i` for `i > 1`" [Kol07, 87], at the level of sections: for
`f` on an open `V` inside the adapted chart at `p`, the `j`-th partial derivative of `f|_S` in the
induced chart is the restriction of the partial derivative of `f` in the direction of the `j`-th
complementary coordinate. -/
theorem comapSection_coordDeriv_inclusionMap (V : Opens M)
    (hV : (V : Set M) ⊆ (hS.adaptedChartAt (hS.subOf p)).source)
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) (j : Fin (n - 1)) :
    comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff
        (coordDeriv E ψ (hS.adaptedChartAt (hS.subOf p)) (hS.isAdaptedChart_adaptedChartAt
          (hS.subOf p)).1 V hV
          (complIdx hS p j) f) =
      coordDeriv (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 _) (chartAt (Fin (n - 1) → 𝕜) p)
        (IsManifold.chart_mem_maximalAtlas p)
        (preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff V) (fun _ hq => hV hq) j
        (comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff f) := by
  have hφ : IsAdaptedChart ψ S (hS.adaptedChartAt (hS.subOf p)) (hS.adaptedIdx (hS.subOf p)) :=
    hS.isAdaptedChart_adaptedChartAt (hS.subOf p)
  refine Subtype.ext (funext fun q => ?_)
  have hqV : hS.inclusionMap q ∈ V := q.2
  have hqφ : hS.inclusionMap q ∈ (hS.adaptedChartAt (hS.subOf p)).source := hV hqV
  -- the left side, as the partial derivative of `f` at the image of `q`
  have e1 : comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff
      (coordDeriv E ψ (hS.adaptedChartAt (hS.subOf p)) hφ.1 V hV (complIdx hS p j) f) q =
      coordDeriv E ψ (hS.adaptedChartAt (hS.subOf p)) hφ.1 V hV (complIdx hS p j) f
        ⟨hS.inclusionMap q, hqV⟩ :=
    comapSection_apply _ _ _ q
  rw [e1, coordDeriv_apply]
  refine Eq.trans ?_ (coordDeriv_apply (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 _)
    (chartAt (Fin (n - 1) → 𝕜) p) (IsManifold.chart_mem_maximalAtlas p)
    (preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff V) (fun _ hq => hV hq) j
    (comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff f) q).symm
  have hcoord : ∀ i, ψ (hS.adaptedChartAt (hS.subOf p) (hS.inclusionMap q)) (hS.adaptedIdx
    (hS.subOf p) i) = 0 :=
    (hφ.2 _ hqφ).mp (inclusionMap_mem hS q)
  -- the linear embedding of the induced chart's model into `E`
  set L : (Fin (n - 1) → 𝕜) →L[𝕜] E :=
    (ψ.symm : (Fin n → 𝕜) →L[𝕜] E).comp (embedComplL (hS.adaptedIdx (hS.subOf p))) with hL
  have hLapply : ∀ w, L w = ψ.symm (embedCompl (hS.adaptedIdx (hS.subOf p)) w) := fun w => rfl
  have hw₀ : chartAt (Fin (n - 1) → 𝕜) p q =
      projCompl (hS.adaptedIdx (hS.subOf p)) (ψ (hS.adaptedChartAt (hS.subOf p)
        (hS.inclusionMap q))) := rfl
  have hLw : L (chartAt (Fin (n - 1) → 𝕜) p q) = hS.adaptedChartAt (hS.subOf p)
    (hS.inclusionMap q) := by
    rw [hLapply, hw₀, embedCompl_projCompl _ hcoord, ContinuousLinearEquiv.symm_apply_apply]
  -- near `w₀` the function read in the induced chart is `F ∘ L`
  have hev : (extendSection 𝕜 (Fin (n - 1) → 𝕜)
      (comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff f) ∘
        (chartAt (Fin (n - 1) → 𝕜) p).symm) =ᶠ[𝓝 (chartAt (Fin (n - 1) → 𝕜) p q)]
        (extendSection 𝕜 E f ∘ (hS.adaptedChartAt (hS.subOf p)).symm) ∘ L := by
    have hopen : IsOpen (L ⁻¹' ((hS.adaptedChartAt (hS.subOf p)).target ∩ (hS.adaptedChartAt
      (hS.subOf p)).symm ⁻¹' V)) :=
      ((hS.adaptedChartAt (hS.subOf p)).symm.isOpen_inter_preimage V.2).preimage L.continuous
    have hmem : chartAt (Fin (n - 1) → 𝕜) p q ∈
        L ⁻¹' ((hS.adaptedChartAt (hS.subOf p)).target ∩ (hS.adaptedChartAt
          (hS.subOf p)).symm ⁻¹' V) := by
      rw [Set.mem_preimage, hLw]
      exact ⟨(hS.adaptedChartAt (hS.subOf p)).map_source hqφ,
        by rw [Set.mem_preimage, (hS.adaptedChartAt (hS.subOf p)).left_inv hqφ]; exact q.2⟩
    filter_upwards [hopen.mem_nhds hmem] with w hw
    obtain ⟨hw1, hw2⟩ := hw
    rw [hLapply] at hw1 hw2
    have hsymm : hS.inclusionMap ((chartAt (Fin (n - 1) → 𝕜) p).symm w) =
        (hS.adaptedChartAt (hS.subOf p)).symm
          (ψ.symm (embedCompl (hS.adaptedIdx (hS.subOf p)) w)) :=
      hφ.coe_symmAux (hS.subOf p).2 hw1
    have hwV : hS.inclusionMap ((chartAt (Fin (n - 1) → 𝕜) p).symm w) ∈ V := by
      rw [hsymm]; exact hw2
    simp only [Function.comp_apply, hLapply]
    have hwV' : (chartAt (Fin (n - 1) → 𝕜) p).symm w ∈
        preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff V := hwV
    rw [extendSection_of_mem 𝕜 (Fin (n - 1) → 𝕜) _ hwV', comapSection_apply, ← hsymm]
    exact (extendSection_of_mem 𝕜 E f hwV).symm
  have hFd : DifferentiableAt 𝕜 (extendSection 𝕜 E f ∘ (hS.adaptedChartAt (hS.subOf p)).symm)
      (L (chartAt (Fin (n - 1) → 𝕜) p q)) := by
    rw [hLw]
    exact (analyticAt_extendSection_comp_symm E (hS.adaptedChartAt (hS.subOf p)) hφ.1 V hV f
      ⟨_, q.2⟩).differentiableAt
  rw [hev.fderiv_eq, fderiv_comp _ hFd L.differentiableAt, L.fderiv,
    ContinuousLinearMap.comp_apply, hLw]
  congr 1
  rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl', id_eq, hLapply,
    embedCompl_single]

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Kollár's "`∂f/∂x_i |_S = ∂(f|_S)/∂x_i`" [Kol07, 87] at the germ level: the restriction of
germs carries the tangential coordinate derivation `∂_{complIdx j}` of the adapted chart at `p` to
the `j`-th coordinate derivation of the induced chart of `S`. -/
theorem germMap_inclusionMap_coordDerivStalk (j : Fin (n - 1))
    (s : (structureSheaf 𝕜 E M).presheaf.stalk (hS.inclusionMap p)) :
    germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p
        (coordDerivStalk E ψ (hS.adaptedChartAt (hS.subOf p)) (hS.isAdaptedChart_adaptedChartAt
          (hS.subOf p)).1
          (inclusionMap_mem_source_adaptedChartAt hS p) (complIdx hS p j) s) =
      coordDerivStalk (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 _)
        (chartAt (Fin (n - 1) → 𝕜) p) (IsManifold.chart_mem_maximalAtlas p) (mem_chart_source _ p) j
        (germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p s) := by
  obtain ⟨U, hxU, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  let V : Opens M := U ⊓ ⟨(hS.adaptedChartAt (hS.subOf p)).source, (hS.adaptedChartAt
    (hS.subOf p)).open_source⟩
  have hV : (V : Set M) ⊆ (hS.adaptedChartAt (hS.subOf p)).source := fun y hy => hy.2
  have hxV : hS.inclusionMap p ∈ V := ⟨hxU, inclusionMap_mem_source_adaptedChartAt hS p⟩
  have hres : (structureSheaf 𝕜 E M).presheaf.germ U (hS.inclusionMap p) hxU f =
      (structureSheaf 𝕜 E M).presheaf.germ V (hS.inclusionMap p) hxV
        ((structureSheaf 𝕜 E M).presheaf.map (homOfLE (inf_le_left : V ≤ U)).op f) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  rw [hres, coordDerivStalk_germ E ψ (hS.adaptedChartAt (hS.subOf p)) _ _ V hV hxV,
    germMap_germ _ _ hxV, germMap_germ _ _ hxV,
    coordDerivStalk_germ (Fin (n - 1) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 _)
      (chartAt (Fin (n - 1) → 𝕜) p) (IsManifold.chart_mem_maximalAtlas p) (mem_chart_source _ p)
      (preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff V) (fun _ hq => hV hq)
      ((mem_preimageOpens _ _).mpr hxV) j,
    comapSection_coordDeriv_inclusionMap hS p V hV]

/-! ### `ρ(D(−log S)(I)) = D(ρ I)` and (87.1) -/

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The stalk of the ideal sheaf of `S` at `p`, in the adapted chart at `p`: `(x_h)`. -/
theorem stalkIdeal_idealSheaf_inclusionMap :
    hS.idealSheaf.stalkIdeal (hS.inclusionMap p) =
      Ideal.span {coord E ψ (hS.adaptedChartAt (hS.subOf p)) (hS.isAdaptedChart_adaptedChartAt
        (hS.subOf p)).1
        (inclusionMap_mem_source_adaptedChartAt hS p) (hS.adaptedIdx (hS.subOf p) 0)} := by
  rw [hS.isIdealSheafOf_idealSheaf.2 _ _ (hS.isAdaptedChart_adaptedChartAt (hS.subOf p))
    (hS.inclusionMap p)
    (inclusionMap_mem_source_adaptedChartAt hS p) (inclusionMap_mem hS p), Set.range_unique]
  rfl

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The equation `x_h` of `S` in the adapted chart at `p` restricts to `0`. -/
theorem germMap_inclusionMap_coord_adaptedIdx :
    germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p
      (coord E ψ (hS.adaptedChartAt (hS.subOf p)) (hS.isAdaptedChart_adaptedChartAt (hS.subOf p)).1
        (inclusionMap_mem_source_adaptedChartAt hS p) (hS.adaptedIdx (hS.subOf p) 0)) = 0 := by
  have hmem : coord E ψ (hS.adaptedChartAt (hS.subOf p)) (hS.isAdaptedChart_adaptedChartAt
    (hS.subOf p)).1
      (inclusionMap_mem_source_adaptedChartAt hS p) (hS.adaptedIdx (hS.subOf p) 0) ∈
        hS.idealSheaf.stalkIdeal (hS.inclusionMap p) := by
    rw [stalkIdeal_idealSheaf_inclusionMap]
    exact Ideal.mem_span_singleton_self _
  have hker := hS.stalkIdeal_idealSheaf_of_mem (a := hS.inclusionMap p) (inclusionMap_mem hS p)
  rw [hker] at hmem
  exact (hS.germMap_inclusionMap_eq_restrictStalk p _).trans (RingHom.mem_ker.mp hmem)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Kollár's (87.1) at a stalk [Kol07, 87]: for `x ∈ S` and an ideal `I` of `𝒪_{M,x}`, the image
under the restriction of germs of `D(−log S)(I)` is the derivative of the image of `I`: `x_h ∂_h`
dies (`ρ x_h = 0`) and the `∂_j`, `j ≠ h`, descend to the coordinate derivations of `S`. -/
theorem map_germMap_logDerivative_eq_derivative
    (I : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk (hS.inclusionMap p))) :
    Ideal.map (germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p)
        (Ideal.logDerivative 𝕜 (hS.idealSheaf.stalkIdeal (hS.inclusionMap p)) I) =
      Ideal.derivative 𝕜 (Ideal.map (germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p) I) := by
  have hφ : IsAdaptedChart ψ S (hS.adaptedChartAt (hS.subOf p)) (hS.adaptedIdx (hS.subOf p)) :=
    hS.isAdaptedChart_adaptedChartAt (hS.subOf p)
  have hx : hS.inclusionMap p ∈ (hS.adaptedChartAt (hS.subOf p)).source :=
    inclusionMap_mem_source_adaptedChartAt hS p
  rw [stalkIdeal_idealSheaf_inclusionMap, ← Ideal.span_eq I,
    logDerivative_span_coord_eq E ψ (hS.adaptedChartAt (hS.subOf p)) hφ.1 hx, Ideal.map_span,
      Ideal.map_span,
    Ideal.derivative_span_eq_of_span _ (coordDerivStalk_mem_span (ContinuousLinearEquiv.refl 𝕜 _)
      (chartAt (Fin (n - 1) → 𝕜) p) (IsManifold.chart_mem_maximalAtlas p) (mem_chart_source _ p))]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨t, ht | ht, rfl⟩
    · exact Ideal.subset_span (Or.inl ⟨t, ht, rfl⟩)
    · obtain ⟨i, u, hu, rfl⟩ := Set.mem_iUnion.mp ht
      by_cases hi : i = hS.adaptedIdx (hS.subOf p) 0
      · subst hi
        rw [logCoordDerivStalk_self, Derivation.smul_apply, smul_eq_mul, map_mul,
          germMap_inclusionMap_coord_adaptedIdx, zero_mul]
        exact Ideal.zero_mem _
      · have hi' : i ∉ Set.range (hS.adaptedIdx (hS.subOf p)) := fun ⟨k, hk⟩ =>
          hi (by rw [← hk, Subsingleton.elim k 0])
        have hij : complIdx hS p (complEquiv (hS.adaptedIdx (hS.subOf p)) ⟨i, hi'⟩) = i := by
          simp only [complIdx, Equiv.symm_apply_apply]
        rw [logCoordDerivStalk_of_ne E ψ (hS.adaptedChartAt (hS.subOf p)) hφ.1 hx hi, ← hij,
          germMap_inclusionMap_coordDerivStalk hS p]
        exact Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr
          ⟨complEquiv (hS.adaptedIdx (hS.subOf p)) ⟨i, hi'⟩, ⟨_, ⟨u, hu, rfl⟩, rfl⟩⟩))
  · rintro _ (⟨t, ht, rfl⟩ | ht)
    · exact Ideal.subset_span ⟨t, Or.inl ht, rfl⟩
    · obtain ⟨j, _, ⟨u, hu, rfl⟩, rfl⟩ := Set.mem_iUnion.mp ht
      rw [← germMap_inclusionMap_coordDerivStalk hS p j u]
      refine Ideal.subset_span ⟨_, Or.inr (Set.mem_iUnion.mpr ⟨complIdx hS p j, ⟨u, hu, ?_⟩⟩), rfl⟩
      rw [logCoordDerivStalk_of_ne E ψ (hS.adaptedChartAt (hS.subOf p)) hφ.1 hx]
      intro h0
      exact complIdx_notMem_range hS p j ⟨0, h0.symm⟩

/-- **Kollár's (87.1)** [Kol07, 87]: on the bundled hypersurface, the restriction of
`D^r(−log S)(J)` along `S ↪ M` is the `r`-th derivative of the restriction of `J`. Induction on
`r` through the stalk identity `ρ(D(−log S)(I)) = D(ρ I)`. -/
theorem logDerivIter_pullback_inclusionMap (r : ℕ)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) :
    (IdealSheaf.logDerivIter E ψ hS r J).pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff =
      (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).iteratedDeriv r := by
  refine IdealSheaf.ext fun (p : hS.toAnalyticManifold) => ?_
  induction r with
  | zero => rw [IdealSheaf.logDerivIter_zero, IdealSheaf.iteratedDeriv_zero]
  | succ r ih =>
    rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.logDerivIter_succ,
      IdealSheaf.stalkIdeal_logDeriv,
      map_germMap_logDerivative_eq_derivative hS p, IdealSheaf.iteratedDeriv_succ,
      IdealSheaf.stalkIdeal_deriv, ← ih, IdealSheaf.stalkIdeal_pullback]

end Manifold

end
