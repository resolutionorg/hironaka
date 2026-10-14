/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Glued
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The glued space as an analytic manifold

The inclusion `toGlued j` of a piece into the glued space `Glued ψ Y c` is an open embedding; its
inverse, read through `ψ⁻¹`, is a chart `gluedChart j` of the glued space with source the image
of the piece and target `ψ⁻¹(S_j)`. These charts, one for each nonempty piece, form an atlas
(`ChartedSpace E (Glued ψ Y c)`), and the chart changes are the transition maps of
`Hironaka.Manifold.BlowUp.Glue` read through `ψ`, which are analytic; so the glued space is an
analytic manifold (`IsManifold 𝓘(𝕜, E) ω`) and every glued chart lies in its maximal atlas.

This gives the blowing-up of `M` with centre `Y` [BM88, Definition 4.1] its structure of analytic
manifold. The analyticity of the blow-down is proved in `Hironaka.Manifold.BlowUp.GluedBlowDown`
and its properness in `Hironaka.Manifold.BlowUp.GluedTopology`.
-/

@[expose] public section

open TopologicalSpace Topology
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

namespace BlowUpGlue

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ}

/-! ### The charts of the glued space -/

section Chart

variable (j : PieceIdx ψ Y c) (hj : (pieceSet j).Nonempty)

/-- The inclusion of a (nonempty) piece as an open partial homeomorphism. -/
def pieceEmbChart : OpenPartialHomeomorph (pieceSet j) (Glued ψ Y c) :=
  haveI : Nonempty (pieceSet j) := hj.to_subtype
  (isOpenEmbedding_toGlued j).toOpenPartialHomeomorph (toGlued j)

/-- The inverse of the embedding chart of a piece undoes the inclusion. -/
theorem pieceEmbChart_symm_toGlued (u : pieceSet j) :
    (pieceEmbChart j hj).symm (toGlued j u) = u :=
  haveI : Nonempty (pieceSet j) := hj.to_subtype
  IsOpenEmbedding.toOpenPartialHomeomorph_left_inv (toGlued j) (isOpenEmbedding_toGlued j)

/-- The target of the embedding chart of a piece is the image of the inclusion. -/
theorem pieceEmbChart_target : (pieceEmbChart j hj).target = Set.range (toGlued j) :=
  haveI : Nonempty (pieceSet j) := hj.to_subtype
  IsOpenEmbedding.toOpenPartialHomeomorph_target (toGlued j) (isOpenEmbedding_toGlued j)

open scoped Classical in
/-- The chart of the glued space over a nonempty piece: the inverse of the inclusion of the
piece, followed by `ψ⁻¹`; source the image of the piece, target `ψ⁻¹(S_j)`. -/
def gluedChart : OpenPartialHomeomorph (Glued ψ Y c) E where
  toFun p := ψ.symm ((pieceEmbChart j hj).symm p).1
  invFun v :=
    if h : ψ v ∈ pieceSet j then toGlued j ⟨ψ v, h⟩ else toGlued j ⟨hj.some, hj.some_mem⟩
  source := Set.range (toGlued j)
  target := ψ ⁻¹' pieceSet j
  map_source' := by
    rintro _ ⟨u, rfl⟩
    rw [Set.mem_preimage, pieceEmbChart_symm_toGlued, ψ.apply_symm_apply]
    exact u.2
  map_target' v hv := by
    rw [Set.mem_preimage] at hv
    simp only [dite_eq_left hv]
    exact ⟨_, rfl⟩
  left_inv' := by
    rintro _ ⟨u, rfl⟩
    simp only [pieceEmbChart_symm_toGlued, ψ.apply_symm_apply]
    rw [dite_eq_left u.2]
  right_inv' v hv := by
    rw [Set.mem_preimage] at hv
    simp only [dite_eq_left hv, pieceEmbChart_symm_toGlued, ψ.symm_apply_apply]
  open_source := (isOpenEmbedding_toGlued j).isOpen_range
  open_target := (isOpen_pieceSet j).preimage ψ.continuous
  continuousOn_toFun := by
    have h := (pieceEmbChart j hj).continuousOn_symm
    rw [pieceEmbChart_target] at h
    exact ψ.symm.continuous.comp_continuousOn (continuous_subtype_val.comp_continuousOn h)
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : Continuous fun v : ψ ⁻¹' pieceSet j => toGlued j ⟨ψ v.1, v.2⟩ :=
      (continuous_toGlued j).comp ((ψ.continuous.comp continuous_subtype_val).subtype_mk _)
    refine h.congr fun v => ?_
    rw [Set.domRestrict_apply, dite_eq_left (Set.mem_preimage.mp v.2)]

/-- The source of a glued chart is the image of its piece. -/
theorem gluedChart_source : (gluedChart j hj).source = Set.range (toGlued j) := rfl

/-- The target of a glued chart is the piece set read in `E`. -/
theorem gluedChart_target : (gluedChart j hj).target = ψ ⁻¹' pieceSet j := rfl

/-- A glued chart reads the coordinates of a point of its piece. -/
theorem gluedChart_toGlued (u : pieceSet j) : gluedChart j hj (toGlued j u) = ψ.symm u := by
  change ψ.symm ((pieceEmbChart j hj).symm (toGlued j u)).1 = ψ.symm u
  rw [pieceEmbChart_symm_toGlued]

open scoped Classical in
/-- The inverse of a glued chart is the inclusion of the piece. -/
theorem gluedChart_symm_apply {v : E} (hv : ψ v ∈ pieceSet j) :
    (gluedChart j hj).symm v = toGlued j ⟨ψ v, hv⟩ := by
  change (if h : ψ v ∈ pieceSet j then toGlued j ⟨ψ v, h⟩
    else toGlued j ⟨hj.some, hj.some_mem⟩) = _
  rw [dite_eq_left hv]

/-- Points of a piece lie in the source of its glued chart. -/
theorem toGlued_mem_gluedChart_source (u : pieceSet j) :
    toGlued j u ∈ (gluedChart j hj).source := ⟨u, rfl⟩

end Chart

/-! ### The charted space and manifold structure -/

theorem pieceSet_pieceOf_nonempty (p : Glued ψ Y c) : (pieceSet (pieceOf p)).Nonempty :=
  ⟨_, (pieceElt p).2⟩

/-- The charted-space structure of the glued space: the glued charts of the nonempty pieces (a piece
with empty coordinate set has no chart). -/
instance gluedChartedSpace : ChartedSpace E (Glued ψ Y c) where
  atlas := {Φ | ∃ (j : PieceIdx ψ Y c) (hj : (pieceSet j).Nonempty), Φ = gluedChart j hj}
  chartAt p := gluedChart (pieceOf p) (pieceSet_pieceOf_nonempty p)
  mem_chart_source p := ⟨pieceElt p, toGlued_pieceElt p⟩
  chart_mem_atlas p := ⟨pieceOf p, pieceSet_pieceOf_nonempty p, rfl⟩

/-- The atlas of the glued space consists of the glued charts of the nonempty pieces. -/
theorem mem_atlas_iff {Φ : OpenPartialHomeomorph (Glued ψ Y c) E} :
    Φ ∈ atlas E (Glued ψ Y c) ↔
      ∃ (j : PieceIdx ψ Y c) (hj : (pieceSet j).Nonempty), Φ = gluedChart j hj := Iff.rfl

/-- Each glued chart of a nonempty piece lies in the atlas. -/
theorem gluedChart_mem_atlas (j : PieceIdx ψ Y c) (hj : (pieceSet j).Nonempty) :
    gluedChart j hj ∈ atlas E (Glued ψ Y c) := ⟨j, hj, rfl⟩

/-- The chart change between the charts of two pieces is the transition map read through `ψ`. -/
theorem gluedChart_transition {j j' : PieceIdx ψ Y c} (hj : (pieceSet j).Nonempty)
    (hj' : (pieceSet j').Nonempty) {v : E}
    (hv : v ∈ (gluedChart j hj).target ∩ (gluedChart j hj).symm ⁻¹' (gluedChart j' hj').source) :
    ψ v ∈ transDom j j' ∧
      gluedChart j' hj' ((gluedChart j hj).symm v) = ψ.symm (transMap j j' (ψ v)) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [gluedChart_target, Set.mem_preimage] at hv1
  rw [Set.mem_preimage, gluedChart_symm_apply j hj hv1, gluedChart_source,
    toGlued_mem_range_iff] at hv2
  refine ⟨hv2, ?_⟩
  rw [gluedChart_symm_apply j hj hv1, ← toGlued_transMap hv2, gluedChart_toGlued]

/-- The glued space is an analytic manifold: its chart changes are the transition maps, analytic on
their open domains. -/
instance gluedIsManifold : IsManifold 𝓘(𝕜, E) ω (Glued ψ Y c) := by
  refine isManifold_of_contDiffOn 𝓘(𝕜, E) ω (Glued ψ Y c) ?_
  rintro _ _ ⟨j, hj, rfl⟩ ⟨j', hj', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source]
  have hT : IsOpen (⇑ψ ⁻¹' transDom j j') := (isOpen_transDom j j').preimage ψ.continuous
  have han : AnalyticOnNhd 𝕜 (⇑ψ.symm ∘ transMap j j' ∘ ⇑ψ) (⇑ψ ⁻¹' transDom j j') :=
    fun v hv => (ψ.symm.toContinuousLinearMap.analyticAt _).comp
      (((analyticOnNhd_transMap j j') _ hv).comp (ψ.toContinuousLinearMap.analyticAt v))
  refine (han.contDiffOn hT.uniqueDiffOn).congr_mono (fun v hv => ?_)
    fun v hv => (gluedChart_transition hj hj' hv).1
  exact (gluedChart_transition hj hj' hv).2

/-- Every chart of a piece lies in the maximal atlas. -/
theorem gluedChart_mem_maximalAtlas (j : PieceIdx ψ Y c) (hj : (pieceSet j).Nonempty) :
    gluedChart j hj ∈ maximalAtlas 𝓘(𝕜, E) ω (Glued ψ Y c) :=
  IsManifold.subset_maximalAtlas (gluedChart_mem_atlas j hj)

end

end BlowUpGlue

end Manifold
