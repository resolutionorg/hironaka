/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Defs
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The vanishing stalk of a preimage along a local analytic isomorphism, for charted types

`vanishingStalk_preimage_of_isLocalDiffeomorphAt` of
`Hironaka/Resolution/Analytic/Functor/PullbackTransport.lean` is stated for bundled analytic
manifolds and an `AnalyticMap`; here the same statements are proved for a bare analytic map
between charted types (`[IsManifold 𝓘(𝕜, E) ω M]` alone, no Hausdorff or second-countability
assumptions): a germ vanishes on `h⁻¹(Z)` at `b` iff its push-forward along the local inverse
vanishes on `Z` at `h b` (`Germ.vanishesOn_compTendsto_of_isLocalDiffeomorphAt'`), and
`vanishingStalk (h ⁻¹' Z) b = Ideal.map (germMap h hh b) (vanishingStalk Z (h b))`
(`vanishingStalk_preimage_of_isLocalDiffeomorphAt'`, through the bijective germ map
`germMap_bijective_of_isLocalDiffeomorphAt`). The proofs are those of the bundled lemmas. Off the
centre of a blowing-up the map is a local analytic isomorphism (condition (1) of
[BM88, Definition 4.1]) and the strict transforms are the preimages of the components, so the
vanishing stalks upstairs are transports of the vanishing stalks downstairs; this is used in the
Jacobian bookkeeping of the `Hironaka` library (`Hironaka/Resolution/Analytic/BM97/LedgerStep.lean`,
`Hironaka/Resolution/Analytic/ModelTransport/Square.lean`).
-/

public section

open Filter Topology Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {N : Type u} [TopologicalSpace N]
  [ChartedSpace E N]

/-- A germ at `h b` vanishes on `Z` iff its pull-back along the local analytic isomorphism `h`
vanishes on `h⁻¹(Z)` at `b` (the charted-type form of
`Germ.vanishesOn_compTendsto_of_isLocalDiffeomorphAt`): near `b` the map `h` agrees with a partial
diffeomorphism `Φ`, which carries `𝓝[h ⁻¹' Z] b` onto `𝓝[Z] (h b)`. -/
theorem Germ.vanishesOn_compTendsto_of_isLocalDiffeomorphAt' {h : N → M}
    (hh : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {b : N} (hb : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω h b)
    (Z : Set M) (k : (𝓝 (h b)).Germ 𝕜) :
    Germ.VanishesOn (h ⁻¹' Z) b (k.compTendsto h (hh.continuous.tendsto b)) ↔
      Germ.VanishesOn Z (h b) k := by
  obtain ⟨Φ, hbΦ, heq⟩ := hb.exists_partialDiffeomorph
  induction k using Germ.inductionOn with
  | h f =>
    rw [Germ.coe_compTendsto, Germ.vanishesOn_coe, Germ.vanishesOn_coe]
    have hev : ∀ᶠ y in 𝓝 b, y ∈ Φ.source := Φ.open_source.mem_nhds hbΦ
    have hmap : Filter.map h (𝓝[h ⁻¹' Z] b) = 𝓝[Z] (h b) := by
      have e1 : Filter.map h (𝓝[h ⁻¹' Z] b) = Filter.map ⇑Φ (𝓝[h ⁻¹' Z] b) :=
        Filter.map_congr ((hev.mono fun y hy => heq hy).filter_mono nhdsWithin_le_nhds)
      have hset : (h ⁻¹' Z : Set N) =ᶠ[𝓝 b] (⇑Φ ⁻¹' Z) :=
        Filter.eventuallyEqSet_iff.mpr (hev.mono fun y hy => by
          rw [Set.mem_preimage, Set.mem_preimage, heq hy])
      rw [e1, nhdsWithin_eq_iff_eventuallyEqSet.mpr hset, heq hbΦ]
      exact Φ.toOpenPartialHomeomorph.map_nhdsWithin_preimage_eq hbΦ Z
    rw [← hmap, Filter.eventually_map]
    exact Iff.rfl

/-- **The vanishing stalk of `h⁻¹(Z)` at `b` is the image of the vanishing stalk of `Z` at `h b`
under the germ map of the local analytic isomorphism `h` at `b`** (the charted-type form of
`vanishingStalk_preimage_of_isLocalDiffeomorphAt`, for a bare analytic map between charted types):
the comap of the vanishing stalk of the preimage is the vanishing stalk of `Z` (the germ identity
above), and `Ideal.map` of a comap along a surjection is the ideal itself
(`germMap_bijective_of_isLocalDiffeomorphAt`). -/
theorem vanishingStalk_preimage_of_isLocalDiffeomorphAt' {h : N → M}
    (hh : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {b : N} (hb : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω h b)
    (Z : Set M) :
    vanishingStalk (𝕜 := 𝕜) (E := E) (h ⁻¹' Z) b =
      Ideal.map (germMap h hh b) (vanishingStalk (𝕜 := 𝕜) (E := E) Z (h b)) := by
  have hcomap : (vanishingStalk (𝕜 := 𝕜) (E := E) (h ⁻¹' Z) b).comap (germMap h hh b) =
      vanishingStalk (𝕜 := 𝕜) (E := E) Z (h b) := by
    ext s
    rw [Ideal.mem_comap, mem_vanishingStalk_iff, mem_vanishingStalk_iff, stalkToGerm_germMap]
    exact Germ.vanishesOn_compTendsto_of_isLocalDiffeomorphAt' hh hb Z _
  rw [← hcomap]
  exact (Ideal.map_comap_of_surjective _
    (germMap_bijective_of_isLocalDiffeomorphAt h hh hb).2 _).symm

end Hironaka.Manifold
