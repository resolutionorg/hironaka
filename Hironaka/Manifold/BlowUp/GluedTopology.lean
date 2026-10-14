/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.GluedBlowDown
import Hironaka.Manifold.BlowUp.Transition
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# The glued space is Hausdorff and second countable, and the blow-down is proper

A blowing-up `M'` is required to be an analytic manifold, here Hausdorff and second countable,
and `π` to be proper [BM88, Definition 4.1]. For the glued space:

* **Hausdorff**: two points over distinct points of `M` are separated by the preimages of
  separating open sets; two points over the same point `a` lie in pieces over one adapted chart at
  `a`; in the same piece they are separated inside it, and in the pieces `i ≠ k` with neither
  point in the other's chart, the open sets `{|u_k| < 1}` and `{|u'_i| < 1}` are disjoint since
  the transition `T_ik` has `u'_i = 1/u_k`;
* **second countable**: countably many adapted charts cover `M` (second countable), and the
  images of countable bases of the corresponding pieces form a countable basis of the glued
  space;
* **proper**: the preimage of a compact set is covered by finitely many compact boxes
  `{π_k u ∈ closedBall, |u_l| ≤ 1 (l ≠ k)}` (the boxes are compact, and every point of a piece is
  carried into a box by some `T_ik`, `Hironaka.Manifold.BlowUp.Transition`), and it is closed.

These are the remaining clauses showing that the glued space is a blowing-up
(`Hironaka.Manifold.BlowUp.Exists`). The arguments are not in the source.
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

/-- Two distinct points of a piece are separated in the glued space. -/
theorem exists_disjoint_open_of_ne_same_piece (j : PieceIdx ψ Y c) {u u' : pieceSet j}
    (h : u ≠ u') :
    ∃ U V : Set (Glued ψ Y c), IsOpen U ∧ IsOpen V ∧ toGlued j u ∈ U ∧ toGlued j u' ∈ V ∧
      Disjoint U V := by
  obtain ⟨U, V, hU, hV, hu, hu', hUV⟩ := t2_separation h
  exact ⟨toGlued j '' U, toGlued j '' V, (isOpenEmbedding_toGlued j).isOpenMap _ hU,
    (isOpenEmbedding_toGlued j).isOpenMap _ hV, ⟨u, hu, rfl⟩, ⟨u', hu', rfl⟩,
    (Set.disjoint_image_iff (toGlued_injective j)).mpr hUV⟩

/-- Two distinct points of the glued space in pieces over one chart are separated. -/
theorem exists_disjoint_open_same_chart (s : Shrink.{u} (AdaptedChart ψ Y c)) (k k' : Fin c)
    (w : pieceSet (s, k)) (w' : pieceSet (s, k')) (hne : toGlued (s, k) w ≠ toGlued (s, k') w') :
    ∃ U V : Set (Glued ψ Y c), IsOpen U ∧ IsOpen V ∧ toGlued (s, k) w ∈ U ∧
      toGlued (s, k') w' ∈ V ∧ Disjoint U V := by
  by_cases hw : (w : Fin n → 𝕜) ∈ transDom (s, k) (s, k')
  · have h := toGlued_transMap hw
    rw [← h] at hne ⊢
    exact exists_disjoint_open_of_ne_same_piece (s, k') fun h' => hne (congrArg _ h')
  by_cases hw' : (w' : Fin n → 𝕜) ∈ transDom (s, k') (s, k)
  · have h := toGlued_transMap hw'
    rw [← h] at hne ⊢
    exact exists_disjoint_open_of_ne_same_piece (s, k) fun h' => hne (congrArg _ h')
  have hkk' : k ≠ k' := by
    rintro rfl
    exact hw (by rw [transDom_self]; exact w.2)
  rw [mem_transDom_same s k k' (Ne.symm hkk')] at hw
  rw [mem_transDom_same s k' k hkk'] at hw'
  push Not at hw hw'
  have h1 : (w : Fin n → 𝕜) (pieceEmb (s, k) k') = 0 := hw w.2
  have h2 : (w' : Fin n → 𝕜) (pieceEmb (s, k') k) = 0 := hw' w'.2
  refine ⟨toGlued (s, k) '' {v | ‖(v : Fin n → 𝕜) (pieceEmb (s, k) k')‖ < 1},
    toGlued (s, k') '' {v | ‖(v : Fin n → 𝕜) (pieceEmb (s, k') k)‖ < 1}, ?_, ?_,
    ⟨w, by change ‖_‖ < 1; rw [h1, norm_zero]; exact zero_lt_one, rfl⟩,
    ⟨w', by change ‖_‖ < 1; rw [h2, norm_zero]; exact zero_lt_one, rfl⟩, ?_⟩
  · exact (isOpenEmbedding_toGlued _).isOpenMap _
      (isOpen_lt ((continuous_apply _).comp continuous_subtype_val).norm continuous_const)
  · exact (isOpenEmbedding_toGlued _).isOpenMap _
      (isOpen_lt ((continuous_apply _).comp continuous_subtype_val).norm continuous_const)
  · rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain ⟨hdom, hb'⟩ := toGlued_eq_iff.mp hab.symm
    have hdom' := hdom
    rw [mem_transDom_same s k k' (Ne.symm hkk')] at hdom'
    have hbk : (b : Fin n → 𝕜) (pieceEmb (s, k) k) = ((a : Fin n → 𝕜) (pieceEmb (s, k) k'))⁻¹ := by
      rw [← hb', transMap_same s k k' hdom, blowUpTransition_apply_i _ _ hkk']
    have ha1 : ‖(a : Fin n → 𝕜) (pieceEmb (s, k) k')‖ < 1 := ha
    have hb1 : ‖(b : Fin n → 𝕜) (pieceEmb (s, k) k)‖ < 1 := hb
    rw [hbk, norm_inv] at hb1
    have hpos : 0 < ‖(a : Fin n → 𝕜) (pieceEmb (s, k) k')‖ := norm_pos_iff.mpr hdom'.2
    have hlt := (mul_le_of_le_one_right (norm_nonneg _) hb1.le).trans_lt ha1
    rw [mul_inv_cancel₀ hpos.ne'] at hlt
    exact lt_irrefl _ hlt

section Global

variable [IsManifold 𝓘(𝕜, E) ω M] (hY : IsClosedSubmanifold ψ Y c) (σ₀ : Fin c ↪ Fin n)
  (i₀ : Fin c)

/-- A chart (shrunk index) at each point of `M`. -/
def chartIdxAt (a : M) : Shrink.{u} (AdaptedChart ψ Y c) :=
  (exists_piece_mem_source hY σ₀ i₀ a).choose

/-- The chosen adapted chart at `a` contains `a` in its source. -/
theorem mem_source_chartIdxAt (a : M) : a ∈ (pieceChart (chartIdxAt hY σ₀ i₀ a, i₀)).source :=
  (exists_piece_mem_source hY σ₀ i₀ a).choose_spec

include hY σ₀ i₀

/-- The glued space is Hausdorff. -/
theorem t2Space_glued [T2Space M] : T2Space (Glued ψ Y c) := by
  refine ⟨fun p q hpq => ?_⟩
  by_cases hproj : gluedProj p = gluedProj q
  · obtain ⟨s, hs⟩ := exists_piece_mem_source hY σ₀ i₀ (gluedProj p)
    obtain ⟨k, w, rfl⟩ := exists_toGlued_eq p s hs
    have hs' : gluedProj q ∈ (pieceChart (s, i₀)).source := by rw [← hproj]; exact hs
    obtain ⟨k', w', rfl⟩ := exists_toGlued_eq q s hs'
    exact exists_disjoint_open_same_chart s k k' w w' hpq
  · obtain ⟨U, V, hU, hV, hp, hq, hUV⟩ := t2_separation hproj
    exact ⟨gluedProj ⁻¹' U, gluedProj ⁻¹' V, hU.preimage continuous_gluedProj,
      hV.preimage continuous_gluedProj, hp, hq, hUV.preimage _⟩

/-- The glued space is second countable. -/
theorem secondCountableTopology_glued [SecondCountableTopology M] :
    SecondCountableTopology (Glued ψ Y c) := by
  have : ProperSpace (Fin n → 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  obtain ⟨S, hS, hcover⟩ := countable_cover_nhds
    (f := fun a : M => (pieceChart (chartIdxAt hY σ₀ i₀ a, i₀)).source)
    fun a => (pieceChart _).open_source.mem_nhds (mem_source_chartIdxAt hY σ₀ i₀ a)
  have hb : ∀ j : PieceIdx ψ Y c,
      ∃ b : Set (Set (pieceSet j)), b.Countable ∧ IsTopologicalBasis b := fun j => by
    obtain ⟨b, hb1, -, hb3⟩ := exists_countable_basis (α := pieceSet j)
    exact ⟨b, hb1, hb3⟩
  choose b hbc hbb using hb
  let B : Set (Set (Glued ψ Y c)) := ⋃ a ∈ S, ⋃ k : Fin c,
    (fun v => toGlued (chartIdxAt hY σ₀ i₀ a, k) '' v) '' b (chartIdxAt hY σ₀ i₀ a, k)
  have hBc : B.Countable :=
    hS.biUnion fun a _ => Set.countable_iUnion fun k => (hbc _).image _
  refine (isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).secondCountableTopology hBc
  · intro U hU
    obtain ⟨a, -, hU⟩ := Set.mem_iUnion₂.mp hU
    obtain ⟨k, hU⟩ := Set.mem_iUnion.mp hU
    obtain ⟨v, hv, rfl⟩ := hU
    exact (isOpenEmbedding_toGlued _).isOpenMap _ ((hbb _).isOpen hv)
  · intro p U hpU hU
    have hmem : gluedProj p ∈ ⋃ a ∈ S, (pieceChart (chartIdxAt hY σ₀ i₀ a, i₀)).source := by
      rw [hcover]
      exact Set.mem_univ _
    obtain ⟨a, haS, ha⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨k, w, rfl⟩ := exists_toGlued_eq p (chartIdxAt hY σ₀ i₀ a) ha
    obtain ⟨v, hvb, hwv, hvU⟩ := (hbb (chartIdxAt hY σ₀ i₀ a, k)).exists_subset_of_mem_open
      (show w ∈ toGlued (chartIdxAt hY σ₀ i₀ a, k) ⁻¹' U from hpU)
      (hU.preimage (continuous_toGlued _))
    refine ⟨toGlued (chartIdxAt hY σ₀ i₀ a, k) '' v, ?_, ⟨w, hwv, rfl⟩, ?_⟩
    · exact Set.mem_iUnion₂.mpr ⟨a, haS, Set.mem_iUnion.mpr ⟨k, v, hvb, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hvU hx

/-- The blow-down is proper, as [BM88, Definition 4.1] requires. -/
theorem isProperMap_gluedProj [T2Space M] : IsProperMap (gluedProj : Glued ψ Y c → M) := by
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  have : ProperSpace (Fin n → 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_gluedProj, fun K hK => ?_⟩
  set s : M → Shrink.{u} (AdaptedChart ψ Y c) := chartIdxAt hY σ₀ i₀ with hs_def
  have hs : ∀ a, a ∈ (pieceChart (s a, i₀)).source := mem_source_chartIdxAt hY σ₀ i₀
  -- a closed ball around the image of each point inside the image of its chart
  have hball : ∀ a : M, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (ψ (pieceChart (s a, i₀) a)) r ⊆ ψ '' (pieceChart (s a, i₀)).target := by
    intro a
    have hopen : IsOpen (ψ '' (pieceChart (s a, i₀)).target) :=
      ψ.toHomeomorph.isOpenMap _ (pieceChart _).open_target
    have hmem : ψ (pieceChart (s a, i₀) a) ∈ ψ '' (pieceChart (s a, i₀)).target :=
      ⟨_, (pieceChart _).map_source (hs a), rfl⟩
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hopen _ hmem
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub⟩
  choose r hr hrsub using hball
  -- the open cover of `K`
  let O : M → Set M := fun a => (pieceChart (s a, i₀)).source ∩
    pieceChart (s a, i₀) ⁻¹' (ψ ⁻¹' Metric.ball (ψ (pieceChart (s a, i₀) a)) (r a))
  have hO : ∀ a, IsOpen (O a) := fun a =>
    (pieceChart _).isOpen_inter_preimage (Metric.isOpen_ball.preimage ψ.continuous)
  have hKO : K ⊆ ⋃ a, O a := fun a _ =>
    Set.mem_iUnion.mpr ⟨a, hs a, Metric.mem_ball_self (hr a)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hO hKO
  -- the compact boxes
  let Box : M → Fin c → Set (Glued ψ Y c) := fun a k => toGlued (s a, k) ''
    (Subtype.val ⁻¹' {u : Fin n → 𝕜 |
      blowUpChartMap (pieceEmb (s a, k)) k u ∈
        Metric.closedBall (ψ (pieceChart (s a, i₀) a)) (r a) ∧
      ∀ l, l ≠ k → ‖u (pieceEmb (s a, k) l)‖ ≤ 1})
  have hBox : ∀ a k, IsCompact (Box a k) := by
    intro a k
    have hC := isCompact_blowUpChartMap_preimage_inter_box (pieceEmb (s a, k)) (i := k)
      (isCompact_closedBall (ψ (pieceChart (s a, i₀) a)) (r a))
    have hind := (isOpen_pieceSet (s a, k)).isOpenEmbedding_subtypeVal.isInducing
    refine ((hind.isCompact_preimage_iff ?_).mpr hC).image (continuous_toGlued _)
    rintro u ⟨hu1, -⟩
    rw [Subtype.range_val]
    exact hrsub a hu1
  refine IsCompact.of_isClosed_subset
    (t.finite_toSet.isCompact_biUnion fun a _ => isCompact_iUnion (hBox a))
    (hK.isClosed.preimage continuous_gluedProj) ?_
  intro p hp
  obtain ⟨a, hat, has, hpb⟩ := Set.mem_iUnion₂.mp (ht hp)
  obtain ⟨k', w, rfl⟩ := exists_toGlued_eq p (s a) has
  obtain ⟨k, hkdom, hkbox⟩ :=
    exists_blowUpTransition_mem_box (pieceEmb (s a, k')) (i := k') (w : Fin n → 𝕜)
  have hw' : (w : Fin n → 𝕜) ∈ transDom (s a, k') (s a, k) := by
    by_cases hkk : k' = k
    · subst hkk
      rw [transDom_self]
      exact w.2
    · rw [mem_transDom_same (s a) k' k (Ne.symm hkk)]
      exact ⟨w.2, (mem_blowUpTransitionDomain _ _ hkk).mp hkdom⟩
  have hπ : pieceMap (s a, k') w = ψ (pieceChart (s a, i₀) (gluedProj (toGlued (s a, k') w))) := by
    rw [gluedProj_toGlued, pieceChart_mk (s a) i₀ k', apply_blowDown w.2]
  refine Set.mem_iUnion₂.mpr ⟨a, hat, Set.mem_iUnion.mpr ⟨k,
    ⟨transMap (s a, k') (s a, k) w, transMap_mem_pieceSet hw'⟩, ⟨?_, ?_⟩, toGlued_transMap hw'⟩⟩
  · change blowUpChartMap (pieceEmb (s a, k)) k (transMap (s a, k') (s a, k) w) ∈ _
    rw [transMap_same _ _ _ hw', pieceEmb_mk (s a) k k',
      blowUpChartMap_blowUpTransition _ _ hkdom]
    change pieceMap (s a, k') w ∈ _
    rw [hπ]
    exact Metric.ball_subset_closedBall hpb
  · intro l hl
    change ‖transMap (s a, k') (s a, k) w (pieceEmb (s a, k) l)‖ ≤ 1
    rw [transMap_same _ _ _ hw']
    exact hkbox l hl

end Global

end

end BlowUpGlue

end Manifold
