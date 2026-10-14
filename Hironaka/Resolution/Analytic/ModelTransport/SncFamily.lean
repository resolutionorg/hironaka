/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.ModelTransport.SquareChart
public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.ModelTransport.Square
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Simple normal crossings families and the boundary predicates along an analytic isomorphism

The simple-normal-crossings vocabulary of `Hironaka/Manifold/Snc/Defs.lean` — a family
`G : HypersurfaceFamily M` being simple normal crossings in a chart isomorphism
`ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)` (`IsSnc`), a set having simple normal crossings with it (`HasSncWith`),
its reduced ideal sheaf (`idealSheaf`) — and the boundary predicates of the analytic main theorems
in their family form (`AnalyticManifold.IdealSheaf.IsSncBoundary`, `IsSncBoundaryWith`;
[Kol07, Definition 24], [Wlo09, Definition 3.2.4]) transport along an analytic isomorphism
`g : N ≃ M` across the models (`Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N M ω`), the family being pulled back
as `G.comap g`.

* `IsSnc` and `HasSncWith` transport in one direction for any two chart isomorphisms
  `ψ₀ : E ≃L (Fin n → 𝕜)`, `ψ₁ : E' ≃L (Fin n → 𝕜)`: the model isomorphism `ψ₀.trans ψ₁.symm` and
  the chart device of `Hironaka/Resolution/Analytic/ModelTransport/SquareChart.lean` read an snc
  chart of `G` at `g a` as an snc chart of `G.comap g` at `a` (`IsSncChartAt.of_square`), the closed
  hypersurfaces pull back (`IsClosedSubmanifold.preimage_of_square`, re-read through
  `IsClosedSubmanifold.congr_cle`), local finiteness by Mathlib's
  `LocallyFinite.preimage_continuous`; the converse is the same direction along `g⁻¹`, with
  `(G.comap g).comap g⁻¹ = G`.
* The reduced ideal sheaf: both branches of the definition correspond — the vanishing stalks of
  `g⁻¹(|G|)` are the images of those of `|G|` under the stalk isomorphism of `g` and local
  generators are carried both ways (`Hironaka/Resolution/Analytic/ModelTransport/Square.lean`).
* The boundary predicates are existential in the chart isomorphism, so their transport takes the
  model isomorphism `ψ : E ≃L[𝕜] E'`: the witness on the other model is `ψ.trans ψ₁'` towards `M`,
  `ψ.symm.trans ψ₀` towards `N`, and the family is `G.comap g⁻¹`, `G.comap g`. In the main
  theorems `ψ` is the transport's `ContinuousLinearEquiv.ofFinrankEq`.
* The two predicates of Włodarczyk's embedded desingularization, the transversal boundary
  predicate `IsSncBoundaryTransversalTo` and the factorization predicate `IsMulBoundaryMonomial`
  ([Wlo09, Theorem 2.0.2 (3) and (6)]), pull back along `g` in the same way
  (`IsSncBoundaryTransversalTo.pullbackDiffeomorph`, `IsMulBoundaryMonomial.pullbackDiffeomorph`).
* `isSnc_congr_chart`: the corollary at `g := Diffeomorph.refl` — `IsSnc` does not depend on the
  chart isomorphism.
-/

public section

noncomputable section

open AnalyticManifold TopologicalSpace Set Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
  {N : AnalyticManifold.{u} 𝕜 E'} (g : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N M ω) {n : ℕ}
  (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) (ψ₁ : E' ≃L[𝕜] (Fin n → 𝕜))

/-! ### Bookkeeping: pull-backs of families, the two chart isomorphisms -/

/-- Pulling a family back along the identity is the identity. -/
@[simp]
theorem HypersurfaceFamily.comap_id {X : Type u} (G : HypersurfaceFamily X) : G.comap id = G := rfl

/-- Pulling back along `g` and then along `g⁻¹` is the identity. -/
theorem HypersurfaceFamily.comap_symm_comap (G : HypersurfaceFamily M) :
    (G.comap ⇑g).comap ⇑g.symm = G := by
  rw [HypersurfaceFamily.comap_comap, show ⇑g ∘ ⇑g.symm = id from funext g.apply_symm_apply,
    HypersurfaceFamily.comap_id]

/-- `g⁻¹ ⁻¹' (g ⁻¹' S) = S`. -/
theorem _root_.Hironaka.Manifold.Diffeomorph.symm_preimage_preimage (S : Set M) : ⇑g.symm ⁻¹'
    (⇑g ⁻¹' S) = S := by
  ext y; simp [g.apply_symm_apply]

/-- Through the model isomorphism `ψ₁⁻¹ ∘ ψ₀ : E ≃ E'`, the chart isomorphism `ψ₀` of `E` re-reads
as `ψ₁` on `E'` (pointwise). -/
theorem _root_.Hironaka.Manifold.trans_symm_symm_trans_apply (v : E') :
    ((ψ₀.trans ψ₁.symm).symm.trans ψ₀) v = ψ₁ v := by
  simp

/-- The closed-submanifold predicate depends on the chart isomorphism only pointwise. -/
theorem IsClosedSubmanifold.congr_cle {ψ ψ' : E ≃L[𝕜] (Fin n → 𝕜)} (h : ∀ v, ψ v = ψ' v)
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c) : IsClosedSubmanifold ψ' Y c where
  isClosed := hY.isClosed
  exists_adaptedChart a ha := by
    obtain ⟨φ, σ, hφa, hφ⟩ := hY.exists_adaptedChart a ha
    exact ⟨φ, σ, hφa, hφ.congr_cle h⟩

/-! ### Simple normal crossings along `g` -/

/-- An snc chart of `G` at `g a` in the chart isomorphism `ψ₀` reads, through `g` and the model
isomorphism `ψ₁⁻¹ ∘ ψ₀`, as an snc chart of `G.comap g` at `a` in `ψ₁`, with the same coordinate
indices. -/
theorem HypersurfaceFamily.IsSncChartAt.of_square (G : HypersurfaceFamily M)
    {φ : OpenPartialHomeomorph M E} {a : N} {c : {j // g a ∈ G.hyp j} → Fin n}
    (h : G.IsSncChartAt ψ₀ φ (g a) c) :
    (G.comap ⇑g).IsSncChartAt ψ₁ (chartOfSquare g (ψ₀.trans ψ₁.symm) φ) a c := by
  refine ⟨chartOfSquare_mem_maximalAtlas g _ h.1, ?_, fun j x hx => ?_, h.2.2.2⟩
  · rw [chartOfSquare_source]; exact h.2.1
  · rw [chartOfSquare_source] at hx
    have := h.2.2.1 j (g x) hx
    rw [chartOfSquare_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    exact this

/-- The forward direction, for any two chart isomorphisms: an snc family pulled back along `g` is
snc — the hypersurfaces by `IsClosedSubmanifold.preimage_of_square` re-read in `ψ₁`, local
finiteness by `LocallyFinite.preimage_continuous`, the snc charts by `IsSncChartAt.of_square`. -/
theorem HypersurfaceFamily.isSnc_comap_diffeomorph (G : HypersurfaceFamily M) (hG : G.IsSnc ψ₀) :
    (G.comap ⇑g).IsSnc ψ₁ := by
  refine ⟨fun j => ?_, hG.2.1.preimage_continuous g.continuous, fun a => ?_⟩
  · exact ((hG.1 j).preimage_of_square g (ψ₀.trans ψ₁.symm) ψ₀).congr_cle
      (trans_symm_symm_trans_apply ψ₀ ψ₁)
  · obtain ⟨φ, c, hc⟩ := hG.2.2 (g a)
    exact ⟨chartOfSquare g (ψ₀.trans ψ₁.symm) φ, c, hc.of_square g ψ₀ ψ₁⟩

/-- **An snc family pulled back along an analytic isomorphism across the models is snc, in any
chart isomorphism of the target model, and conversely**: the converse is the forward direction
along `g⁻¹`. -/
theorem HypersurfaceFamily.isSnc_comap_diffeomorph_iff (G : HypersurfaceFamily M) :
    (G.comap ⇑g).IsSnc ψ₁ ↔ G.IsSnc ψ₀ := by
  refine ⟨fun h => ?_, HypersurfaceFamily.isSnc_comap_diffeomorph g ψ₀ ψ₁ G⟩
  have := HypersurfaceFamily.isSnc_comap_diffeomorph g.symm ψ₁ ψ₀ (G.comap ⇑g) h
  rwa [HypersurfaceFamily.comap_symm_comap] at this

/-- The forward direction: `HasSncWith` along `g` — the adapted snc chart at `g a` reads as an
adapted snc chart at `a`. -/
theorem HypersurfaceFamily.hasSncWith_comap_diffeomorph (G : HypersurfaceFamily M) {Y : Set M}
    {c : ℕ} (hG : G.HasSncWith ψ₀ Y c) : (G.comap ⇑g).HasSncWith ψ₁ (⇑g ⁻¹' Y) c := by
  intro a ha
  obtain ⟨φ, σ, cidx, hφ, hc⟩ := hG (g a) ha
  exact ⟨chartOfSquare g (ψ₀.trans ψ₁.symm) φ, σ, cidx,
    (hφ.of_square g (ψ₀.trans ψ₁.symm) ψ₀).congr_cle (trans_symm_symm_trans_apply ψ₀ ψ₁),
    hc.of_square g ψ₀ ψ₁⟩

/-- **`HasSncWith` along an analytic isomorphism across the models**: `g⁻¹(Y)` has simple normal
crossings with `G.comap g` in `ψ₁` iff `Y` has with `G` in `ψ₀`. -/
theorem HypersurfaceFamily.hasSncWith_comap_diffeomorph_iff (G : HypersurfaceFamily M) (Y : Set M)
    (c : ℕ) : (G.comap ⇑g).HasSncWith ψ₁ (⇑g ⁻¹' Y) c ↔ G.HasSncWith ψ₀ Y c := by
  refine ⟨fun h => ?_, HypersurfaceFamily.hasSncWith_comap_diffeomorph g ψ₀ ψ₁ G⟩
  have := HypersurfaceFamily.hasSncWith_comap_diffeomorph g.symm ψ₁ ψ₀ (G.comap ⇑g) h
  rwa [HypersurfaceFamily.comap_symm_comap, Diffeomorph.symm_preimage_preimage] at this

/-- **The reduced ideal sheaf of a family along an analytic isomorphism across the models** is the
pull-back of the reduced ideal sheaf: both branches of the definition correspond — the vanishing
stalks of `g⁻¹(|G|)` are the images of those of `|G|` under the stalk isomorphism of `g`, and local
generators are carried both ways. -/
theorem HypersurfaceFamily.idealSheaf_comap_diffeomorph (G : HypersurfaceFamily M) :
    (G.comap ⇑g).idealSheaf =
        IdealSheaf.pullbackDiffeomorph g G.idealSheaf := by
  unfold HypersurfaceFamily.idealSheaf
  rw [HypersurfaceFamily.support_comap]
  by_cases h₂ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M) fun x : M =>
      vanishingStalk (𝕜 := 𝕜) (E := E) G.support x
  · have h₁ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E' N) fun x : N =>
        vanishingStalk (𝕜 := 𝕜) (E := E') (⇑g ⁻¹' G.support) x :=
      hasLocalGenerators_vanishingStalk_preimage_diffeomorph g _ h₂
    rw [dite_eq_left h₂, dite_eq_left h₁]
    refine IdealSheaf.ext fun x => ?_
    rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph, IdealSheaf.stalkIdeal_ofStalks,
      IdealSheaf.stalkIdeal_ofStalks, vanishingStalk_preimage_pullbackDiffeomorph]
  · have h₁ : ¬ IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E' N) fun x : N =>
        vanishingStalk (𝕜 := 𝕜) (E := E') (⇑g ⁻¹' G.support) x :=
      fun hg => h₂ ((hasLocalGenerators_vanishingStalk_preimage_diffeomorph_iff g _).mp hg)
    rw [dite_eq_right h₂, dite_eq_right h₁]
    exact (IdealSheaf.pullbackDiffeomorph_top g).symm

/-- **`IsSnc` does not depend on the chart isomorphism**: the corollary of
`isSnc_comap_diffeomorph_iff` at `g := Diffeomorph.refl`. -/
theorem HypersurfaceFamily.isSnc_congr_chart (ψ₀' : E ≃L[𝕜] (Fin n → 𝕜))
    (G : HypersurfaceFamily M) : G.IsSnc ψ₀' ↔ G.IsSnc ψ₀ := by
  have := HypersurfaceFamily.isSnc_comap_diffeomorph_iff (Diffeomorph.refl 𝓘(𝕜, E) M ω) ψ₀ ψ₀' G
  rwa [Diffeomorph.coe_refl, HypersurfaceFamily.comap_id] at this

/-! ### The boundary predicates of the main theorems along `g`, with the model isomorphism -/

variable (ψ : E ≃L[𝕜] E')

include ψ in
/-- **The boundary predicate `IsSncBoundary` of the main theorems along an analytic isomorphism
across the models**, with the model isomorphism `ψ`: the snc family and its chart isomorphism are
carried by `isSnc_comap_diffeomorph` and `idealSheaf_comap_diffeomorph` (`ψ.trans ψ₁'` towards `M`,
`ψ.symm.trans ψ₀` towards `N`). -/
theorem _root_.AnalyticManifold.IdealSheaf.isSncBoundary_pullbackDiffeomorph_iff
    (B : AnalyticManifold.IdealSheaf M) :
    IdealSheaf.IsSncBoundary
        (IdealSheaf.pullbackDiffeomorph g B) ↔
      IdealSheaf.IsSncBoundary B := by
  constructor
  · rintro ⟨n, ψ₁', G', hG', hB⟩
    refine ⟨n, ψ.trans ψ₁', G'.comap ⇑g.symm,
      HypersurfaceFamily.isSnc_comap_diffeomorph g.symm ψ₁' (ψ.trans ψ₁') G' hG', ?_⟩
    rw [HypersurfaceFamily.idealSheaf_comap_diffeomorph, hB,
      IdealSheaf.pullbackDiffeomorph_symm_pullbackDiffeomorph]
  · rintro ⟨n, ψ₀, G, hG, hB⟩
    exact ⟨n, ψ.symm.trans ψ₀, G.comap ⇑g,
      HypersurfaceFamily.isSnc_comap_diffeomorph g ψ₀ (ψ.symm.trans ψ₀) G hG,
      by rw [HypersurfaceFamily.idealSheaf_comap_diffeomorph, hB]⟩

include ψ in
/-- **The boundary-with-centre predicate `IsSncBoundaryWith` of the main theorems along an analytic
isomorphism across the models**, with the model isomorphism `ψ`: `isSnc_comap_diffeomorph`,
`hasSncWith_comap_diffeomorph` (on `(D.pullbackDiffeomorph g).support = g⁻¹(D.support)`) and
`idealSheaf_comap_diffeomorph`. -/
theorem _root_.AnalyticManifold.IdealSheaf.isSncBoundaryWith_pullbackDiffeomorph_iff
    (B D : AnalyticManifold.IdealSheaf M) :
    IdealSheaf.IsSncBoundaryWith
        (IdealSheaf.pullbackDiffeomorph g B)
        (IdealSheaf.pullbackDiffeomorph g D) ↔
      IdealSheaf.IsSncBoundaryWith B D := by
  constructor
  · rintro ⟨n, ψ₁', G', c, hG', hB, hD⟩
    refine ⟨n, ψ.trans ψ₁', G'.comap ⇑g.symm, c,
      HypersurfaceFamily.isSnc_comap_diffeomorph g.symm ψ₁' (ψ.trans ψ₁') G' hG', ?_, ?_⟩
    · rw [HypersurfaceFamily.idealSheaf_comap_diffeomorph, hB,
        IdealSheaf.pullbackDiffeomorph_symm_pullbackDiffeomorph]
    · have := HypersurfaceFamily.hasSncWith_comap_diffeomorph g.symm ψ₁' (ψ.trans ψ₁') G' hD
      rwa [IdealSheaf.support_pullbackDiffeomorph,
        Diffeomorph.symm_preimage_preimage] at this
  · rintro ⟨n, ψ₀, G, c, hG, hB, hD⟩
    refine ⟨n, ψ.symm.trans ψ₀, G.comap ⇑g, c,
      HypersurfaceFamily.isSnc_comap_diffeomorph g ψ₀ (ψ.symm.trans ψ₀) G hG,
      by rw [HypersurfaceFamily.idealSheaf_comap_diffeomorph, hB], ?_⟩
    rw [IdealSheaf.support_pullbackDiffeomorph]
    exact HypersurfaceFamily.hasSncWith_comap_diffeomorph g ψ₀ (ψ.symm.trans ψ₀) G hD

include ψ in
/-- **The transversal boundary predicate `IsSncBoundaryTransversalTo` of Włodarczyk's embedded
desingularization along an analytic isomorphism across the models**, with the model isomorphism
`ψ`: the family is `G.comap g` (`isSnc_comap_diffeomorph`, `idealSheaf_comap_diffeomorph`), and at
a point `a` of `g⁻¹(Y)` the adapted snc chart of `G` at `g a` is read through `g`
(`chartOfSquare`, `IsAdaptedChart.of_square`, `IsSncChartAt.of_square`), the coordinate indices,
hence the transversality, unchanged. -/
theorem _root_.AnalyticManifold.IdealSheaf.IsSncBoundaryTransversalTo.pullbackDiffeomorph
    {B Y : AnalyticManifold.IdealSheaf M} (h : B.IsSncBoundaryTransversalTo Y) :
    (IdealSheaf.pullbackDiffeomorph g B).IsSncBoundaryTransversalTo
      (IdealSheaf.pullbackDiffeomorph g Y) := by
  obtain ⟨n, ψ₀, G, hG, hB, hY⟩ := h
  refine ⟨n, ψ.symm.trans ψ₀, G.comap ⇑g,
    HypersurfaceFamily.isSnc_comap_diffeomorph g ψ₀ (ψ.symm.trans ψ₀) G hG,
    by rw [HypersurfaceFamily.idealSheaf_comap_diffeomorph, hB], fun a ha => ?_⟩
  rw [IdealSheaf.support_pullbackDiffeomorph] at ha
  obtain ⟨c, φ, σ, cidx, hφ, hc, hpr⟩ := hY (g a) ha
  refine ⟨c, chartOfSquare g (ψ₀.trans (ψ.symm.trans ψ₀).symm) φ, σ, cidx, ?_,
    hc.of_square g ψ₀ (ψ.symm.trans ψ₀), hpr⟩
  rw [IdealSheaf.support_pullbackDiffeomorph]
  exact (hφ.of_square g (ψ₀.trans (ψ.symm.trans ψ₀).symm) ψ₀).congr_cle
    (trans_symm_symm_trans_apply ψ₀ (ψ.symm.trans ψ₀))

include ψ in
/-- **The factorization predicate `IsMulBoundaryMonomial` of Włodarczyk's embedded
desingularization along an analytic isomorphism across the models**, with the model isomorphism
`ψ`: the family is `G.comap g`, and at every point `x` the stalk identity at `g x` is carried by
the stalk isomorphism of `g`, which maps products, powers and the vanishing ideals of the
components of `G` to those of the components of `G.comap g`
(`vanishingStalk_preimage_pullbackDiffeomorph`). -/
theorem _root_.AnalyticManifold.IdealSheaf.IsMulBoundaryMonomial.pullbackDiffeomorph
    {J Y B : AnalyticManifold.IdealSheaf M} (h : J.IsMulBoundaryMonomial Y B) :
    (IdealSheaf.pullbackDiffeomorph g J).IsMulBoundaryMonomial
      (IdealSheaf.pullbackDiffeomorph g Y) (IdealSheaf.pullbackDiffeomorph g B) := by
  obtain ⟨n, ψ₀, G, hG, hB, h6⟩ := h
  refine ⟨n, ψ.symm.trans ψ₀, G.comap ⇑g,
    HypersurfaceFamily.isSnc_comap_diffeomorph g ψ₀ (ψ.symm.trans ψ₀) G hG,
    by rw [HypersurfaceFamily.idealSheaf_comap_diffeomorph, hB], fun x => ?_⟩
  obtain ⟨s, α, hs, heq⟩ := h6 (g x)
  refine ⟨s, α, hs, ?_⟩
  rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph, IdealSheaf.stalkIdeal_pullbackDiffeomorph, heq,
    Ideal.map_mul]
  congr 1
  rw [show Ideal.map (g.stalkRingEquiv x) (∏ j ∈ s, vanishingStalk (G.hyp j) (g x) ^ α j) =
      Ideal.mapHom (g.stalkRingEquiv x) (∏ j ∈ s, vanishingStalk (G.hyp j) (g x) ^ α j) from rfl,
    map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Ideal.mapHom_apply, Ideal.map_pow]
  congr 1
  exact (vanishingStalk_preimage_pullbackDiffeomorph g (G.hyp j) x).symm

end Manifold

end
