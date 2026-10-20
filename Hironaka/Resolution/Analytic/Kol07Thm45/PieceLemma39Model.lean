/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39
public import Hironaka.AnalyticSpace.HomExt
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.Manifold.ClosedSub
import Hironaka.AnalyticSpace.Manifold.FullyFaithful
import Hironaka.AnalyticSpace.MonoidalUnique
import Hironaka.AnalyticSpace.QuotientLift
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc
import Hironaka.Manifold.SigmaManifold
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The model stalk map of a piece embedding and the local lifts

Kollár's Lemma 39 works in coordinates: the two embeddings `i₁ : Y → 𝕜ⁿ`, `i₂ : Y → 𝕜ᵐ` of one
piece are compared through local analytic maps `j₂ : 𝕜ⁿ ⇀ 𝕜ᵐ`, `j₁ : 𝕜ᵐ ⇀ 𝕜ⁿ` with `j₂ ∘ i₁ = i₂`
and `j₁ ∘ i₂ = i₁` near a point — the coordinate functions of one embedding, pulled back to `Y`,
extend to analytic functions on the other ambient [Kol07, Lemma 39, proof]; a morphism of analytic
spaces is described locally by its coordinate functions (Hironaka's local `K`-coordinations,
[Hir64, Ch. 0, §1, p. 120]). This module provides that step:

* the **coordinate map** `pieceCoord G : Sp(G) → 𝕜ⁿ` of a one-piece ambient and its chart
  (`pieceAmbientChart`, the chart of `Sp(G)` at any point as a partial analytic isomorphism onto its
  target — the sources are the whole ambient);
* the **model coordinate germs** `modelCoordGerm v k` of `𝕜ⁿ` at `v` and the **model germs**
  `modelGerm f hf hv` of functions analytic on an open `O ∋ v`, with their germs of functions;
* the **model stalk map** `E.modelStalkMap y : 𝒪_{𝕜ⁿ, i(y)} →+* 𝒪_{X|V, y}` of a piece embedding
  `E` at `y` — the stalk map of the `K`-morphism `X|V → Sp(G) → Sp(𝕜ⁿ)`, which is `pieceStalkMap`
  after the coordinate germ map; it is local and carries constants to constants;
* **the local lift** (`exists_modelLift`): for two embeddings `E`, `F` of one piece and a point `x`
  there is an open `O ∋ i_E(x)` of `𝕜ⁿ` and `j : 𝕜ⁿ → 𝕜ᵐ` analytic on `O` whose components,
  pulled back through `E`, are the coordinates of `F` at every `y` over `O` — from the local
  description of the sections of `Sp(G)/𝓘` (`exists_local_rep`) applied to the coordinate
  functions of `F` pulled back to `Sp(G)/𝓘` along `E⁻¹ ∘ F`, read through the chart;
* **the residues** (`modelPoint_eq_of_coord_eq`): such a lift takes `i_E(y)` to `i_F(y)` (a germ
  congruent to two constants modulo the maximal ideal has equal constants);
* **the uniqueness** (`modelStalkMap_eq_of_lift`): a lift with the coordinate identities gives
  `ε_F = ε_E ∘ j^*` on every germ (`stalkMap_eq_of_coord`, the stalks being Noetherian).

Not in the sources beyond Kollár's proof; bookkeeping on the local description of sections of a
closed subspace (`Hironaka/AnalyticSpace/Manifold/ClosedSub.lean`) and the uniqueness of local
homomorphisms determined by coordinates (`Hironaka/AnalyticSpace/MonoidalUnique.lean`).
-/

@[expose] public section

open TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Manifold ContDiff Topology

universe u v

noncomputable section

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### The coordinate map and the chart of a one-piece ambient -/

section Coord

variable {n : ℕ} (G : Opens (Fin n → 𝕜))

/-- The coordinate map `⟨(), z⟩ ↦ z` of the one-piece ambient `Sp(G) = ⊔_{PUnit} G`. -/
def pieceCoord : pieceAmbient.{u} 𝕜 G → (Fin n → 𝕜) := fun w => (w.2 : Fin n → 𝕜)

theorem pieceCoord_apply (w : pieceAmbient.{u} 𝕜 G) : pieceCoord G w = (w.2 : Fin n → 𝕜) := rfl

theorem pieceCoord_mem (w : pieceAmbient.{u} 𝕜 G) : pieceCoord G w ∈ G := w.2.2

theorem pieceCoord_injective : Function.Injective (pieceCoord.{u} G) := by
  intro w w' h
  exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (Subtype.ext h))

theorem contMDiff_pieceCoord :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (pieceCoord.{u} G) :=
  ContMDiff.sigmaDesc (M := fun _ : PUnit.{u + 1} => (G : Type)) (P := Fin n → 𝕜)
    (f := fun _ => Subtype.val) fun _ => contMDiff_subtype_val

/-- The chart of the one-piece ambient at any point is the coordinate map (the lifted chart of the
open `G ⊆ 𝕜ⁿ`; `PadIdeal.lean`'s `chartAt_pieceAmbient_apply` for an arbitrary open). -/
theorem chartAt_pieceAmbient_apply_eq_pieceCoord (x y : pieceAmbient.{u} 𝕜 G) :
    chartAt (Fin n → 𝕜) x y = pieceCoord G y := by
  have e := ChartedSpace.sigma_chartAt (H := Fin n → 𝕜)
    (M := fun _ : PUnit.{u + 1} => (G : Type)) (⟨x.1, x.2⟩ : Σ _ : PUnit.{u + 1}, (G : Type))
  change chartAt (Fin n → 𝕜) (⟨x.1, x.2⟩ : Σ _ : PUnit.{u + 1}, (G : Type))
    (⟨x.1, y.2⟩ : Σ _ : PUnit.{u + 1}, (G : Type)) = (y.2 : Fin n → 𝕜)
  rw [e]
  exact (OpenPartialHomeomorph.lift_openEmbedding_apply _ _).trans rfl

/-- The source of the chart of the one-piece ambient at any point is the whole ambient. -/
theorem mem_chart_source_pieceAmbient (x y : pieceAmbient.{u} 𝕜 G) :
    y ∈ (chartAt (Fin n → 𝕜) x).source := by
  have e := ChartedSpace.sigma_chartAt (H := Fin n → 𝕜)
    (M := fun _ : PUnit.{u + 1} => (G : Type)) (⟨x.1, x.2⟩ : Σ _ : PUnit.{u + 1}, (G : Type))
  change (⟨x.1, y.2⟩ : Σ _ : PUnit.{u + 1}, (G : Type)) ∈
    (chartAt (Fin n → 𝕜) (⟨x.1, x.2⟩ : Σ _ : PUnit.{u + 1}, (G : Type))).source
  rw [e, OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨y.2, ?_, rfl⟩
  simp only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
    chartAt_self_eq, OpenPartialHomeomorph.refl_source, Set.preimage_univ, Set.mem_univ]

/-- The chart of the one-piece ambient at `x`, as a partial analytic isomorphism `Sp(G) ⇀ 𝕜ⁿ`
(source the whole ambient, target the chart's target). -/
def pieceAmbientChart (x : pieceAmbient.{u} 𝕜 G) :
    PartialDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) (pieceAmbient.{u} 𝕜 G) (Fin n → 𝕜) ω where
  toPartialEquiv := (chartAt (Fin n → 𝕜) x).toPartialEquiv
  open_source := (chartAt (Fin n → 𝕜) x).open_source
  open_target := (chartAt (Fin n → 𝕜) x).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

theorem pieceAmbientChart_apply (x y : pieceAmbient.{u} 𝕜 G) :
    pieceAmbientChart G x y = pieceCoord G y :=
  chartAt_pieceAmbient_apply_eq_pieceCoord G x y

theorem mem_pieceAmbientChart_source (x y : pieceAmbient.{u} 𝕜 G) :
    y ∈ (pieceAmbientChart G x).source :=
  mem_chart_source_pieceAmbient G x y

theorem pieceCoord_mem_pieceAmbientChart_target (x y : pieceAmbient.{u} 𝕜 G) :
    pieceCoord G y ∈ (pieceAmbientChart G x).target := by
  rw [← pieceAmbientChart_apply]
  exact (pieceAmbientChart G x).toPartialEquiv.map_source (mem_pieceAmbientChart_source G x y)

theorem pieceAmbientChart_symm_pieceCoord (x y : pieceAmbient.{u} 𝕜 G) :
    (pieceAmbientChart G x).symm (pieceCoord G y) = y := by
  rw [← pieceAmbientChart_apply]
  exact (pieceAmbientChart G x).toPartialEquiv.left_inv (mem_pieceAmbientChart_source G x y)

theorem pieceCoord_pieceAmbientChart_symm (x : pieceAmbient.{u} 𝕜 G) {v : Fin n → 𝕜}
    (hv : v ∈ (pieceAmbientChart G x).target) :
    pieceCoord G ((pieceAmbientChart G x).symm v) = v := by
  rw [← pieceAmbientChart_apply]
  exact (pieceAmbientChart G x).toPartialEquiv.right_inv hv

end Coord

/-! ### The stalks of a one-piece ambient are the stalks of the model space -/

section Coord

variable {n : ℕ} (G : Opens (Fin n → 𝕜))

theorem pieceCoord_eq_chartAt (x : pieceAmbient.{u} 𝕜 G) :
    pieceCoord G = ⇑(chartAt (Fin n → 𝕜) x) :=
  funext fun y => (chartAt_pieceAmbient_apply_eq_pieceCoord G x y).symm

theorem map_nhds_pieceCoord (w : pieceAmbient.{u} 𝕜 G) :
    Filter.map (pieceCoord G) (𝓝 w) = 𝓝 (pieceCoord G w) := by
  rw [pieceCoord_eq_chartAt G w]
  exact (chartAt (Fin n → 𝕜) w).map_nhds_eq (mem_chart_source _ w)

/-- The germ map of the coordinate map is injective (the argument for a local analytic
isomorphism, `GermIso.lean`, for the coordinate map of a one-piece ambient). -/
theorem germMap_pieceCoord_injective (q : pieceAmbient.{u} 𝕜 G) :
    Function.Injective (germMap (pieceCoord G) (contMDiff_pieceCoord G) q) := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs => ?_
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) (pieceCoord G q)
  have := congrArg (stalkToGerm 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbient.{u} 𝕜 G) q) hs
  rw [stalkToGerm_germMap, map_zero] at this
  rw [map_zero]
  revert this
  induction stalkToGerm 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) (pieceCoord G q) s
    using Filter.Germ.inductionOn with
  | h f =>
    intro this
    rw [Filter.Germ.coe_compTendsto, ← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at this
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
    have h1 : ∀ᶠ v in Filter.map (pieceCoord G) (𝓝 q), f v = 0 :=
      Filter.eventually_map.mpr (this.mono fun _ hx => hx)
    rwa [map_nhds_pieceCoord] at h1

/-- The germ map of the coordinate map is surjective: a representative near `q` composed with the
inverse chart represents a germ at the coordinates of `q`. -/
theorem germMap_pieceCoord_surjective (q : pieceAmbient.{u} 𝕜 G) :
    Function.Surjective (germMap (pieceCoord G) (contMDiff_pieceCoord G) q) := by
  intro t
  obtain ⟨h, ht, W, hqW, hW⟩ :=
    (mem_range_stalkToGerm_iff 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbient.{u} 𝕜 G) q
      (stalkToGerm 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbient.{u} 𝕜 G) q t)).mp ⟨t, rfl⟩
  set ch := pieceAmbientChart G q with hch
  have hWo : IsOpen (ch.target ∩ ch.symm ⁻¹' (W : Set (pieceAmbient.{u} 𝕜 G))) :=
    ch.toOpenPartialHomeomorph.isOpen_inter_preimage_symm W.2
  have hsm : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) ω (h ∘ ch.symm)
      (ch.target ∩ ch.symm ⁻¹' (W : Set (pieceAmbient.{u} 𝕜 G))) :=
    hW.comp (ch.contMDiffOn_invFun.mono Set.inter_subset_left) fun _ hy => hy.2
  have hqx : pieceCoord G q ∈ ch.target ∩ ch.symm ⁻¹' (W : Set (pieceAmbient.{u} 𝕜 G)) :=
    ⟨pieceCoord_mem_pieceAmbientChart_target G q q, by
      rw [Set.mem_preimage, pieceAmbientChart_symm_pieceCoord]
      exact hqW⟩
  obtain ⟨s, hs⟩ := (mem_range_stalkToGerm_iff 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) (pieceCoord G q)
    (↑(h ∘ ch.symm))).mpr ⟨_, rfl, ⟨_, hWo⟩, hqx, hsm⟩
  refine ⟨s, stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbient.{u} 𝕜 G) q ?_⟩
  rw [stalkToGerm_germMap, hs, Filter.Germ.coe_compTendsto, ht, Filter.Germ.coe_eq]
  refine Filter.Eventually.of_forall fun w => ?_
  change h (ch.symm (pieceCoord G w)) = h w
  rw [pieceAmbientChart_symm_pieceCoord]

/-- **The stalk of a one-piece ambient at `q` is the stalk of the model space at its coordinates**:
the germ map of the coordinate map, as a ring isomorphism `𝒪_{𝕜ⁿ, z} ≃+* 𝒪_{Sp(G), ⟨(), z⟩}`. -/
def modelStalkEquiv (q : pieceAmbient.{u} 𝕜 G) :
    (structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.stalk (pieceCoord G q) ≃+*
      (structureSheaf 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 G)).presheaf.stalk q :=
  RingEquiv.ofBijective (germMap (pieceCoord G) (contMDiff_pieceCoord G) q)
    ⟨germMap_pieceCoord_injective G q, germMap_pieceCoord_surjective G q⟩

theorem modelStalkEquiv_apply (q : pieceAmbient.{u} 𝕜 G)
    (s : (structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.stalk (pieceCoord G q)) :
    modelStalkEquiv G q s = germMap (pieceCoord G) (contMDiff_pieceCoord G) q s := rfl

end Coord

/-! ### The coordinate germs and the germs of functions of the model space -/

section Model

variable {n : ℕ}

/-- The germ map of a partial analytic map carries the constants to the constants
(`germMap_const` for maps between manifolds of different models and universes). -/
theorem germMapOn_const' {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type v} [TopologicalSpace N] [ChartedSpace E' N] (φ : N → M) {V : Opens N}
    (hφ : ContMDiffOn 𝓘(𝕜, E') 𝓘(𝕜, E) ω φ V) {b : N} (hb : b ∈ V) {c : M} (hc : φ b = c)
    (a : 𝕜) : germMapOn φ hφ hb hc (const 𝕜 E M c a) = const 𝕜 E' N b a := by
  apply stalkToGerm_injective 𝓘(𝕜, E') ω N b
  rw [stalkToGerm_germMapOn, stalkToGerm_const, stalkToGerm_const, Filter.Germ.coe_compTendsto]
  rfl

/-- The coordinate germ `u_k` of the model space `𝕜ⁿ` at `v` (`coord` for the identity chart). -/
def modelCoordGerm (v : Fin n → 𝕜) (k : Fin n) :
    (structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.stalk v :=
  coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (chartAt (Fin n → 𝕜) v)
    (IsManifold.chart_mem_maximalAtlas v) (mem_chart_source _ v) k

theorem stalkToGerm_modelCoordGerm (v : Fin n → 𝕜) (k : Fin n) :
    stalkToGerm 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) v (modelCoordGerm v k) =
      ↑(fun w : Fin n → 𝕜 => w k) := by
  rw [modelCoordGerm, stalkToGerm_coord]
  refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun w => ?_)
  have hw : w ∈ (chartAt (Fin n → 𝕜) v).source := by
    rw [chartAt_self_eq]
    exact Set.mem_univ w
  rw [extendSection_of_mem 𝕜 (Fin n → 𝕜) _ hw]
  change (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (chartAt (Fin n → 𝕜) v w) k = w k
  rw [chartAt_self_eq]
  rfl

/-- The coordinate germ of a chart of a one-piece ambient is the model coordinate germ,
transported along the coordinate map. -/
theorem coord_pieceAmbient_eq {G : Opens (Fin n → 𝕜)} (q : pieceAmbient.{u} 𝕜 G) (k : Fin n) :
    coord (Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (chartAt (Fin n → 𝕜) q)
        (IsManifold.chart_mem_maximalAtlas q) (mem_chart_source _ q) k =
      germMap (pieceCoord G) (contMDiff_pieceCoord G) q (modelCoordGerm (pieceCoord G q) k) := by
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbient.{u} 𝕜 G) q
  rw [stalkToGerm_coord, stalkToGerm_germMap, stalkToGerm_modelCoordGerm,
    Filter.Germ.coe_compTendsto]
  refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun w => ?_)
  rw [extendSection_of_mem 𝕜 (Fin n → 𝕜) _ (mem_chart_source_pieceAmbient G q w)]
  change (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (chartAt (Fin n → 𝕜) q w) k = pieceCoord G w k
  rw [chartAt_pieceAmbient_apply_eq_pieceCoord]
  rfl

/-- The `k`-th coordinate function of a one-piece ambient as a global section. -/
def pieceCoordSection (G : Opens (Fin n → 𝕜)) (k : Fin n) :
    (structureSheaf 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 G)).presheaf.obj (op ⊤) :=
  sectionOfContMDiffOn (fun w => pieceCoord G w k) ⊤
    ((contMDiff_iff_contDiff.mpr (contDiff_apply 𝕜 (fun _ => 𝕜) k)).comp
      (contMDiff_pieceCoord G)).contMDiffOn

theorem germ_pieceCoordSection {G : Opens (Fin n → 𝕜)} (q : pieceAmbient.{u} 𝕜 G) (k : Fin n) :
    (structureSheaf 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 G)).presheaf.germ ⊤ q (Opens.mem_top q)
        (pieceCoordSection G k) =
      germMap (pieceCoord G) (contMDiff_pieceCoord G) q (modelCoordGerm (pieceCoord G q) k) := by
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbient.{u} 𝕜 G) q
  rw [pieceCoordSection, stalkToGerm_germ_sectionOfContMDiffOn, stalkToGerm_germMap,
    stalkToGerm_modelCoordGerm, Filter.Germ.coe_compTendsto]
  rfl

/-- The germ at `v ∈ O` of a function analytic on the open `O ⊆ 𝕜ⁿ`. -/
def modelGerm {O : Opens (Fin n → 𝕜)} (f : (Fin n → 𝕜) → 𝕜) (hf : ContDiffOn 𝕜 ω f O)
    {v : Fin n → 𝕜} (hv : v ∈ O) : (structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.stalk v :=
  (structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.germ O v hv
    (sectionOfContMDiffOn f O (contMDiffOn_iff_contDiffOn.mpr hf))

theorem stalkToGerm_modelGerm {O : Opens (Fin n → 𝕜)} (f : (Fin n → 𝕜) → 𝕜)
    (hf : ContDiffOn 𝕜 ω f O) {v : Fin n → 𝕜} (hv : v ∈ O) :
    stalkToGerm 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) v (modelGerm f hf hv) = ↑f :=
  stalkToGerm_germ_sectionOfContMDiffOn f O _ hv

theorem eval_modelGerm {O : Opens (Fin n → 𝕜)} (f : (Fin n → 𝕜) → 𝕜)
    (hf : ContDiffOn 𝕜 ω f O) {v : Fin n → 𝕜} (hv : v ∈ O) :
    Manifold.eval 𝕜 (Fin n → 𝕜) (Fin n → 𝕜) v (modelGerm f hf hv) = f v :=
  contMDiffSheafCommRing.eval_germ 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) ω (Fin n → 𝕜) 𝕜 O v hv _

theorem eval_modelCoordGerm (v : Fin n → 𝕜) (k : Fin n) :
    Manifold.eval 𝕜 (Fin n → 𝕜) (Fin n → 𝕜) v (modelCoordGerm v k) = v k := by
  rw [modelCoordGerm, eval_coord]
  change (chartAt (Fin n → 𝕜) v v) k = v k
  rw [chartAt_self_eq]
  rfl

/-- The model germ of `f` at `v` is congruent to the constant `f v` modulo the maximal ideal. -/
theorem modelGerm_sub_const_mem {O : Opens (Fin n → 𝕜)} (f : (Fin n → 𝕜) → 𝕜)
    (hf : ContDiffOn 𝕜 ω f O) {v : Fin n → 𝕜} (hv : v ∈ O) :
    modelGerm f hf hv - const 𝕜 (Fin n → 𝕜) (Fin n → 𝕜) v (f v) ∈
      IsLocalRing.maximalIdeal ((structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.stalk v) :=
  (mem_maximalIdeal_iff_eval (Fin n → 𝕜) _).mpr (by
    rw [map_sub, eval_modelGerm, eval_const, sub_self])

theorem modelCoordGerm_sub_const_mem (v : Fin n → 𝕜) (k : Fin n) :
    modelCoordGerm v k - const 𝕜 (Fin n → 𝕜) (Fin n → 𝕜) v (v k) ∈
      IsLocalRing.maximalIdeal ((structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.stalk v) :=
  (mem_maximalIdeal_iff_eval (Fin n → 𝕜) _).mpr (by
    rw [map_sub, eval_modelCoordGerm, eval_const, sub_self])

/-- The germ map of a partial analytic map `j` carries the coordinate germ `u_k` to the germ of the
component `j_k`. -/
theorem germMapOn_modelCoordGerm {m : ℕ} {j : (Fin n → 𝕜) → (Fin m → 𝕜)} {O : Opens (Fin n → 𝕜)}
    (hj : ContDiffOn 𝕜 ω j O) {v : Fin n → 𝕜} (hv : v ∈ O) {w : Fin m → 𝕜} (hjv : j v = w)
    (k : Fin m) :
    germMapOn j (contMDiffOn_iff_contDiffOn.mpr hj) hv hjv (modelCoordGerm w k) =
      modelGerm (fun v => j v k) (contDiffOn_pi.mp hj k) hv := by
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) v
  rw [stalkToGerm_germMapOn, stalkToGerm_modelCoordGerm, stalkToGerm_modelGerm,
    Filter.Germ.coe_compTendsto]
  rfl

/-- The stalk isomorphism of a one-piece ambient carries the constants to the constants. -/
theorem modelStalkEquiv_const {G : Opens (Fin n → 𝕜)} (q : pieceAmbient.{u} 𝕜 G) (c : 𝕜) :
    modelStalkEquiv G q (const 𝕜 (Fin n → 𝕜) (Fin n → 𝕜) (pieceCoord G q) c) =
      const 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 G) q c :=
  germMapOn_const' (pieceCoord G) (contMDiff_pieceCoord G).contMDiffOn (Opens.mem_top q) rfl c

theorem modelStalkEquiv_symm_const {G : Opens (Fin n → 𝕜)} (q : pieceAmbient.{u} 𝕜 G) (c : 𝕜) :
    (modelStalkEquiv G q).symm (const 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 G) q c) =
      const 𝕜 (Fin n → 𝕜) (Fin n → 𝕜) (pieceCoord G q) c := by
  rw [RingEquiv.symm_apply_eq, modelStalkEquiv_const]

end Model

/-! ### The model stalk map of a piece embedding -/

namespace PieceEmbedding

open _root_.Manifold

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- The coordinates `i(y) ∈ 𝕜ⁿ` of the ambient point of `y`. -/
abbrev modelPoint (y : X.restrictSet V) : Fin n → 𝕜 := pieceCoord E.G (E.ambientPoint y)

theorem modelPoint_mem (y : X.restrictSet V) : E.modelPoint y ∈ E.G := pieceCoord_mem _ _

instance isLocalHom_pieceStalkMap (y : X.restrictSet V) : IsLocalHom (E.pieceStalkMap y) :=
  (E.emb ≫ E.ideal.toAnalyticSpaceι).1.prop y

/-- The stalk map of a piece embedding carries the constants to the constants. -/
theorem pieceStalkMap_const (y : X.restrictSet V) (c : 𝕜) :
    E.pieceStalkMap y (const 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G) (E.ambientPoint y) c) =
      AnalyticSpace.KLocallyRingedSpace.constAt
        (AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V)) y c :=
  AnalyticSpace.KLocallyRingedSpace.Hom.algebraMap_stalk
    (E.emb ≫ E.ideal.toAnalyticSpaceι :
      AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V) ⟶
        AnalyticSpace.KLocallyRingedSpace.ofManifold 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G))
    y c

/-- **The model stalk map** `ε_y : 𝒪_{𝕜ⁿ, i(y)} →+* 𝒪_{X|V, y}` of a piece embedding at `y`: the
stalk map of the piece after the coordinate germ map (the description of a morphism by its
coordinate functions, Hironaka's local `K`-coordinations [Hir64, Ch. 0, §1, p. 120]). -/
def modelStalkMap (y : X.restrictSet V) :
    (structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.stalk (E.modelPoint y) →+*
      (X.restrictSet V).toLocallyRingedSpace.presheaf.stalk y :=
  (E.pieceStalkMap y).comp (germMap (pieceCoord E.G) (contMDiff_pieceCoord E.G) (E.ambientPoint y))

theorem modelStalkMap_apply (y : X.restrictSet V)
    (s : (structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.stalk (E.modelPoint y)) :
    E.modelStalkMap y s =
      E.pieceStalkMap y
        (germMap (pieceCoord E.G) (contMDiff_pieceCoord E.G) (E.ambientPoint y) s) :=
  rfl

theorem modelStalkMap_modelStalkEquiv (y : X.restrictSet V)
    (s : (structureSheaf 𝕜 (Fin n → 𝕜) (Fin n → 𝕜)).presheaf.stalk (E.modelPoint y)) :
    E.pieceStalkMap y (modelStalkEquiv E.G (E.ambientPoint y) s) = E.modelStalkMap y s :=
  rfl

theorem modelStalkMap_modelStalkEquiv_symm (y : X.restrictSet V)
    (s : (structureSheaf 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G)).presheaf.stalk
      (E.ambientPoint y)) :
    E.modelStalkMap y ((modelStalkEquiv E.G (E.ambientPoint y)).symm s) = E.pieceStalkMap y s :=
  congrArg (E.pieceStalkMap y) ((modelStalkEquiv E.G (E.ambientPoint y)).apply_symm_apply s)

instance isLocalHom_modelStalkMap (y : X.restrictSet V) : IsLocalHom (E.modelStalkMap y) :=
  @RingHom.isLocalHom_comp _ _ _ _ _ _ (E.pieceStalkMap y)
    (germMap (pieceCoord E.G) (contMDiff_pieceCoord E.G) (E.ambientPoint y))
    (E.isLocalHom_pieceStalkMap y)
    (isLocalHom_germMapOn (pieceCoord E.G) (contMDiff_pieceCoord E.G).contMDiffOn
      (Opens.mem_top _) rfl)

/-- The model stalk map carries the constants to the constants. -/
theorem modelStalkMap_const (y : X.restrictSet V) (c : 𝕜) :
    E.modelStalkMap y (const 𝕜 (Fin n → 𝕜) (Fin n → 𝕜) (E.modelPoint y) c) =
      AnalyticSpace.KLocallyRingedSpace.constAt
        (AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V)) y c :=
  (congrArg (E.pieceStalkMap y) (modelStalkEquiv_const (E.ambientPoint y) c)).trans
    (E.pieceStalkMap_const y c)

/-! ### The local lifts -/

/-- A local homomorphism carrying the constants to the constants carries a germ congruent to the
constant `c` to a germ congruent to the constant `c` (the maximal ideal goes into the maximal
ideal). -/
theorem sub_constAt_mem_of_isLocalHom {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {M : Type v} [TopologicalSpace M] [ChartedSpace E' M] {a : M}
    {Z : AnalyticSpace.KLocallyRingedSpace.{u} 𝕜} {z : Z}
    (θ : (structureSheaf 𝕜 E' M).presheaf.stalk a →+* Z.toLocallyRingedSpace.presheaf.stalk z)
    [IsLocalHom θ]
    (hθ : ∀ c, θ (const 𝕜 E' M a c) = AnalyticSpace.KLocallyRingedSpace.constAt Z z c)
    {s : (structureSheaf 𝕜 E' M).presheaf.stalk a} {c : 𝕜}
    (hs : s - const 𝕜 E' M a c ∈
      IsLocalRing.maximalIdeal ((structureSheaf 𝕜 E' M).presheaf.stalk a)) :
    θ s - AnalyticSpace.KLocallyRingedSpace.constAt Z z c ∈
      IsLocalRing.maximalIdeal (Z.toLocallyRingedSpace.presheaf.stalk z) := by
  rw [← hθ c, ← map_sub]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
  exact fun hu => hs (isUnit_of_map_unit _ _ hu)

/-- **Residues of a lift**: if the `k`-th coordinate of `F` at `y` is the germ of `f` pulled back
through `E`, then `i_F(y)_k = f (i_E(y))` (a germ congruent to two constants modulo the maximal
ideal has equal constants). -/
theorem modelPoint_eq_of_coord_eq {m : ℕ} (F : PieceEmbedding 𝕜 m X V) (y : X.restrictSet V)
    {O : Opens (Fin n → 𝕜)} {f : (Fin n → 𝕜) → 𝕜} (hf : ContDiffOn 𝕜 ω f O)
    (hy : E.modelPoint y ∈ O) (k : Fin m)
    (h : F.modelStalkMap y (modelCoordGerm (F.modelPoint y) k) =
      E.modelStalkMap y (modelGerm f hf hy)) :
    F.modelPoint y k = f (E.modelPoint y) :=
  AnalyticSpace.KLocallyRingedSpace.eq_of_sub_constAt_mem
    (X := AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V))
    (sub_constAt_mem_of_isLocalHom (F.modelStalkMap y) (F.modelStalkMap_const y)
      (modelCoordGerm_sub_const_mem _ k))
    (h ▸ sub_constAt_mem_of_isLocalHom (E.modelStalkMap y) (E.modelStalkMap_const y)
      (modelGerm_sub_const_mem f hf hy))

/-- **The stalk maps of a lift agree everywhere** (`ringHom_ext_of_coord'`, the stalks of `X|V`
being Noetherian): if the coordinates of `F` at `y` are the components of `j` pulled back through
`E`, and `j` carries `i_E(y)` to `i_F(y)`, then `ε_F y = ε_E y ∘ j^*` on every germ. -/
theorem modelStalkMap_eq_of_lift {m : ℕ} (F : PieceEmbedding 𝕜 m X V) (y : X.restrictSet V)
    {O : Opens (Fin n → 𝕜)} {j : (Fin n → 𝕜) → (Fin m → 𝕜)} (hj : ContDiffOn 𝕜 ω j O)
    (hy : E.modelPoint y ∈ O) (hjy : j (E.modelPoint y) = F.modelPoint y)
    (hcoord : ∀ k, F.modelStalkMap y (modelCoordGerm (F.modelPoint y) k) =
      E.modelStalkMap y (modelGerm (fun v => j v k) (contDiffOn_pi.mp hj k) hy))
    (s : (structureSheaf 𝕜 (Fin m → 𝕜) (Fin m → 𝕜)).presheaf.stalk (F.modelPoint y)) :
    F.modelStalkMap y s =
      E.modelStalkMap y (germMapOn j (contMDiffOn_iff_contDiffOn.mpr hj) hy hjy s) := by
  let e := modelStalkEquiv F.G (F.ambientPoint y)
  let θ := (E.modelStalkMap y).comp (germMapOn j (contMDiffOn_iff_contDiffOn.mpr hj) hy hjy)
  let β := θ.comp e.symm.toRingHom
  have hloc : IsLocalHom e.symm.toRingHom := ⟨fun a ha => by simpa using ha.map e⟩
  have hθ : IsLocalHom θ := RingHom.isLocalHom_comp _ _
  have hβ : IsLocalHom β := @RingHom.isLocalHom_comp _ _ _ _ _ _ θ e.symm.toRingHom hθ hloc
  have key : F.pieceStalkMap y = β :=
    @AnalyticSpace.KLocallyRingedSpace.ringHom_ext_of_coord' 𝕜 _ _ _ _ _ _ _ _
      ((X.restrictSet V).toLocallyRingedSpace.presheaf.stalk y) _
      ((X.restrictSet V).toLocallyRingedSpace.isLocalRing y)
      (AnalyticSpace.isNoetherianRing_stalk (X.restrictSet V) y)
      (ContinuousLinearEquiv.refl 𝕜 (Fin m → 𝕜)) _
      (IsManifold.chart_mem_maximalAtlas (F.ambientPoint y)) _ (mem_chart_source _ _)
      (F.pieceStalkMap y) β (F.isLocalHom_pieceStalkMap y) hβ
      (fun c => (F.pieceStalkMap_const y c).trans
        ((congrArg (fun t => E.modelStalkMap y
            (germMapOn j (contMDiffOn_iff_contDiffOn.mpr hj) hy hjy t))
          (modelStalkEquiv_symm_const (F.ambientPoint y) c)).trans
          ((congrArg (E.modelStalkMap y) (germMapOn_const' j _ hy hjy c)).trans
            (E.modelStalkMap_const y c))).symm)
      (fun i => ((congrArg (F.pieceStalkMap y) (coord_pieceAmbient_eq (F.ambientPoint y) i)).trans
        (hcoord i)).trans
        (congrArg (E.modelStalkMap y) ((germMapOn_modelCoordGerm hj hy hjy i).symm.trans
          (congrArg (germMapOn j (contMDiffOn_iff_contDiffOn.mpr hj) hy hjy)
            ((e.symm_apply_apply (modelCoordGerm (F.modelPoint y) i)).symm.trans
              (congrArg e.symm (coord_pieceAmbient_eq (F.ambientPoint y) i).symm))))))
  exact (congrArg (fun φ => φ (e s)) key).trans
    (congrArg (fun t => E.modelStalkMap y
      (germMapOn j (contMDiffOn_iff_contDiffOn.mpr hj) hy hjy t)) (e.symm_apply_apply s))

/-- **The local lift** (the extension `j` of one embedding's coordinates to the other ambient in
[Kol07, Lemma 39, proof]): for two embeddings `E : X|V ↪ 𝕜ⁿ`, `F : X|V ↪ 𝕜ᵐ` of one piece and a
point `x`, there is an open `O ∋ i_E(x)` of `𝕜ⁿ` and a map `j : 𝕜ⁿ → 𝕜ᵐ` analytic on `O` whose
components, pulled back through `E`, are the coordinates of `F` at every `y` over `O` — the local
description of the sections of `Sp(G)/𝓘` (`exists_local_rep`) applied to the coordinate functions
of `Sp(G')` pulled back along `E⁻¹ ∘ F`, and read in the chart of `Sp(G)`. -/
theorem exists_modelLift {m : ℕ} (F : PieceEmbedding 𝕜 m X V) (x : X.restrictSet V) :
    ∃ (O : Opens (Fin n → 𝕜)) (_ : E.modelPoint x ∈ O) (j : (Fin n → 𝕜) → (Fin m → 𝕜))
      (hj : ContDiffOn 𝕜 ω j O),
      ∀ (y : X.restrictSet V) (hy : E.modelPoint y ∈ O) (k : Fin m),
        F.modelStalkMap y (modelCoordGerm (F.modelPoint y) k) =
          E.modelStalkMap y (modelGerm (fun v => j v k) (contDiffOn_pi.mp hj k) hy) := by
  classical
  -- the coordinate functions of `Sp(G')`, read on `Sp(G)/𝓘` through `E⁻¹ ∘ F`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : AnalyticSpace.toKLocallyRingedSpace
        E.ideal.toAnalyticSpace ⟶
      AnalyticSpace.KLocallyRingedSpace.ofManifold 𝕜 (Fin m → 𝕜) (pieceAmbient.{u} 𝕜 F.G),
      (E.emb : AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V) ⟶
        AnalyticSpace.toKLocallyRingedSpace E.ideal.toAnalyticSpace) ≫ Φ =
        (CategoryStruct.comp (obj := AnalyticSpace _) F.emb F.ideal.toAnalyticSpaceι :
          AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V) ⟶
            AnalyticSpace.KLocallyRingedSpace.ofManifold 𝕜 (Fin m → 𝕜)
              (pieceAmbient.{u} 𝕜 F.G)) := by
    have hE : IsIso E.emb := E.emb_isIso
    refine ⟨(@inv (AnalyticSpace.{u} 𝕜) _ _ _ E.emb hE :
      AnalyticSpace.toKLocallyRingedSpace E.ideal.toAnalyticSpace ⟶
        AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V)) ≫
      (CategoryStruct.comp (obj := AnalyticSpace _) F.emb F.ideal.toAnalyticSpaceι :
        AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V) ⟶
          AnalyticSpace.KLocallyRingedSpace.ofManifold 𝕜 (Fin m → 𝕜)
            (pieceAmbient.{u} 𝕜 F.G)), ?_⟩
    have h1 : (E.emb : AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V) ⟶
        AnalyticSpace.toKLocallyRingedSpace E.ideal.toAnalyticSpace) ≫
        (@inv (AnalyticSpace.{u} 𝕜) _ _ _ E.emb hE :
          AnalyticSpace.toKLocallyRingedSpace E.ideal.toAnalyticSpace ⟶
            AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V)) = 𝟙 _ :=
      @IsIso.hom_inv_id (AnalyticSpace.{u} 𝕜) _ _ _ E.emb hE
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫
      (CategoryStruct.comp (obj := AnalyticSpace _) F.emb F.ideal.toAnalyticSpaceι :
        AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V) ⟶
          AnalyticSpace.KLocallyRingedSpace.ofManifold 𝕜 (Fin m → 𝕜)
            (pieceAmbient.{u} 𝕜 F.G))) h1).trans (Category.id_comp _))
  -- the local representatives of the pulled-back coordinate functions near `E x`
  choose U₁ hxU₁ W₁ a ha using fun k : Fin m =>
    AnalyticSpace.KLocallyRingedSpace.exists_local_rep E.ideal
      ((Opens.map Φ.1.base).obj ⊤) (Φ.1.c.app (op ⊤) (pieceCoordSection F.G k))
      ⟨E.emb x, Opens.mem_top _⟩
  choose O' hO' using fun k =>
    AnalyticSpace.QuotientSpace.exists_opens_eq_preimage
      (AnalyticSpace.KLocallyRingedSpace.ofManifold 𝕜 (Fin n → 𝕜)
        (pieceAmbient.{u} 𝕜 E.G)).toLocallyRingedSpace E.ideal (U₁ k)
  -- the germ identity at the points of the support over `O' k ⊓ W₁ k`
  have hgerm : ∀ (k : Fin m) (z : E.ideal.toAnalyticSpace) (hzO : z.1 ∈ O' k) (hzW : z.1 ∈ W₁ k),
      (Φ.1.stalkMap z).hom ((structureSheaf 𝕜 (Fin m → 𝕜) (pieceAmbient.{u} 𝕜 F.G)).presheaf.germ ⊤
          (Φ.1.base z) (Opens.mem_top _) (pieceCoordSection F.G k)) =
        (E.ideal.toAnalyticSpaceι.1.stalkMap z).hom
          ((structureSheaf 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G)).presheaf.germ (W₁ k) z.1 hzW
            (a k)) := by
    intro k z hzO hzW
    have hloc := fun (w : E.ideal.toAnalyticSpace) (hw : w.1 ∈ O' k) => ha k w (by
      rw [hO' k]
      exact (AnalyticSpace.QuotientSpace.mem_preimage _ _).mpr hw)
    obtain ⟨_, e⟩ := AnalyticSpace.QuotientSpace.germ_eq_stalkMap_ι_germ
      (AnalyticSpace.KLocallyRingedSpace.ofManifold 𝕜 (Fin n → 𝕜)
        (pieceAmbient.{u} 𝕜 E.G)).toLocallyRingedSpace E.ideal
      (Φ.1.c.app (op ⊤) (pieceCoordSection F.G k)) (Opens.mem_top z) (a k) hzO hloc
    exact (LocallyRingedSpace.stalkMap_germ_apply Φ.1 ⊤ z (Opens.mem_top _)
      (pieceCoordSection F.G k)).trans e
  -- through the isomorphism `E`: the coordinates of `F` at `y` are the germs of `a k` through `E`
  have hgerm' : ∀ (k : Fin m) (y : X.restrictSet V) (hyO : E.ambientPoint y ∈ O' k)
      (hyW : E.ambientPoint y ∈ W₁ k),
      F.modelStalkMap y (modelCoordGerm (F.modelPoint y) k) =
        E.pieceStalkMap y ((structureSheaf 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G)).presheaf.germ
          (W₁ k) (E.ambientPoint y) hyW (a k)) := by
    intro k y hyO hyW
    have h := congrArg (E.emb.1.stalkMap y).hom (hgerm k (E.emb.1.base y) hyO hyW)
    have hL : (E.emb.1.stalkMap y).hom ((Φ.1.stalkMap (E.emb.1.base y)).hom
          ((structureSheaf 𝕜 (Fin m → 𝕜) (pieceAmbient.{u} 𝕜 F.G)).presheaf.germ ⊤
            (Φ.1.base (E.emb.1.base y)) (Opens.mem_top _) (pieceCoordSection F.G k))) =
        F.pieceStalkMap y ((structureSheaf 𝕜 (Fin m → 𝕜) (pieceAmbient.{u} 𝕜 F.G)).presheaf.germ ⊤
          (F.ambientPoint y) (Opens.mem_top _) (pieceCoordSection F.G k)) := by
      have h1 := congrArg (fun φ => φ.hom
        ((structureSheaf 𝕜 (Fin m → 𝕜) (pieceAmbient.{u} 𝕜 F.G)).presheaf.germ ⊤
          (Φ.1.base (E.emb.1.base y)) (Opens.mem_top _) (pieceCoordSection F.G k)))
        (LocallyRingedSpace.stalkMap_comp E.emb.1 Φ.1 y)
      have h2 := congrArg (fun ψ : AnalyticSpace.toKLocallyRingedSpace
          (X.restrictSet V) ⟶ AnalyticSpace.KLocallyRingedSpace.ofManifold 𝕜 (Fin m → 𝕜)
            (pieceAmbient.{u} 𝕜 F.G) =>
          (ψ.1.stalkMap y).hom
            ((structureSheaf 𝕜 (Fin m → 𝕜) (pieceAmbient.{u} 𝕜 F.G)).presheaf.germ ⊤ (ψ.1.base y)
              (Opens.mem_top _) (pieceCoordSection F.G k))) hΦ
      exact h1.symm.trans h2
    have hR : (E.emb.1.stalkMap y).hom ((E.ideal.toAnalyticSpaceι.1.stalkMap (E.emb.1.base y)).hom
          ((structureSheaf 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G)).presheaf.germ (W₁ k)
            (E.ambientPoint y) hyW (a k))) =
        E.pieceStalkMap y ((structureSheaf 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G)).presheaf.germ
          (W₁ k) (E.ambientPoint y) hyW (a k)) :=
      (congrArg (fun φ => φ.hom
        ((structureSheaf 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G)).presheaf.germ (W₁ k)
          (E.ambientPoint y) hyW (a k)))
        (LocallyRingedSpace.stalkMap_comp E.emb.1 E.ideal.toAnalyticSpaceι.1 y)).symm
    exact ((congrArg (F.pieceStalkMap y) (germ_pieceCoordSection (F.ambientPoint y) k)).symm.trans
      (hL.symm.trans h)).trans hR
  -- the model open and the lift, through the chart at `i(x)`
  set ch := pieceAmbientChart E.G (E.ambientPoint x) with hch
  have hsymm : ∀ y, ch.symm (pieceCoord E.G y) = y := fun y =>
    pieceAmbientChart_symm_pieceCoord E.G (E.ambientPoint x) y
  have htgt : ∀ y, pieceCoord E.G y ∈ ch.target := fun y =>
    pieceCoord_mem_pieceAmbientChart_target E.G (E.ambientPoint x) y
  let Ok : Fin m → Opens (Fin n → 𝕜) := fun k =>
    ⟨ch.target ∩ ch.symm ⁻¹' ((O' k ⊓ W₁ k : Opens (pieceAmbient.{u} 𝕜 E.G)) : Set _),
      ch.toOpenPartialHomeomorph.isOpen_inter_preimage_symm (O' k ⊓ W₁ k).2⟩
  have hxO' : ∀ k, E.ambientPoint x ∈ O' k := fun k => by
    have := hxU₁ k
    rw [hO' k] at this
    exact (AnalyticSpace.QuotientSpace.mem_preimage _ _).mp this
  have hxW : ∀ k, E.ambientPoint x ∈ W₁ k := fun k => by
    obtain ⟨_, hzW, _⟩ := ha k _ (hxU₁ k)
    exact hzW
  have hmem : ∀ k v, v ∈ Ok k → ch.symm v ∈ O' k ∧ ch.symm v ∈ W₁ k := fun k v hv => hv.2
  refine ⟨⟨⋂ k, (Ok k : Set (Fin n → 𝕜)), isOpen_iInter_of_finite fun k => (Ok k).2⟩,
    Set.mem_iInter.mpr fun k => ⟨htgt _, ?_⟩,
    fun v k => extendSection 𝕜 (Fin n → 𝕜) (a k) (ch.symm v), ?_, ?_⟩
  · change ch.symm (pieceCoord E.G (E.ambientPoint x)) ∈
      ((O' k ⊓ W₁ k : Opens (pieceAmbient.{u} 𝕜 E.G)) : Set (pieceAmbient.{u} 𝕜 E.G))
    rw [hsymm]
    exact ⟨hxO' k, hxW k⟩
  · refine contDiffOn_pi.mpr fun k => contMDiffOn_iff_contDiffOn.mp ?_
    exact (contMDiffOn_extendSection (a k)).comp
      (ch.contMDiffOn_invFun.mono fun v hv => (Set.mem_iInter.mp hv k).1)
      fun v hv => (hmem k v (Set.mem_iInter.mp hv k)).2
  · intro y hy k
    have hyk := hmem k _ (Set.mem_iInter.mp hy k)
    rw [hsymm] at hyk
    refine (hgerm' k y hyk.1 hyk.2).trans (congrArg (E.pieceStalkMap y) ?_)
    apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbient.{u} 𝕜 E.G) (E.ambientPoint y)
    rw [stalkToGerm_germMap, stalkToGerm_modelGerm, stalkToGerm_structureSheaf_germ,
      Filter.Germ.coe_compTendsto]
    refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun w => ?_)
    change extendSection 𝕜 (Fin n → 𝕜) (a k) w =
      extendSection 𝕜 (Fin n → 𝕜) (a k) (ch.symm (pieceCoord E.G w))
    rw [hsymm]

end PieceEmbedding

end Hironaka.Manifold
