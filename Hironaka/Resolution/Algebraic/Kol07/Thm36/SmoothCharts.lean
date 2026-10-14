/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.Smooth.SmoothAmbientLift
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SigmaCharts  -- shake: keep (used only by `example`s)

/-!
# The charts of Lemma 41, shrunk to basic opens

For a smooth `h : Y ⟶ X` of relative dimension `d` between schemes with closed immersions
`embX : X ⟶ AX` and `embY : Y ⟶ AY` into ambients (`AY` affine), every point `y ∈ Y` lies in a
**chart** (`Chart h embX embY d`): an affine open `W` of `Y`, given as a scheme with its open
immersion `e : W ⟶ Y`, together with

* the fibre square of [Kol07, Lemma 41] (`exists_smooth_ambient_lift'`), restricted to `W`: an
  affine `B` smooth of relative dimension `d` over `AX` and a closed immersion `j : W ⟶ B` with
  `IsPullback j (e ≫ h) q embX`;
* the square on the side of `Y`: a global section `G` of `AY` with `W = embY ⁻¹ᵁ D(G)`, so that `W`
  is the fibre product of `Y` and the basic open `D(G)` over `AY`, `IsPullback jY e (D(G)).ι embY`.

These are exactly the squares that `admissibleEmbedding_sigma`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.SigmaCharts`) takes for the coproduct `Z := ∐ Wᵢ` of
finitely many charts covering `Y`, on both sides: the ambient `∐ D(Gᵢ)` over `AY` (relative
dimension `0`) and the ambient `∐ Bᵢ` over `AX` (relative dimension `d`). This is how "(34.1) is a
local property" is used in the proof of [Kol07, Theorem 36] to derive the functoriality of the
resolution of an affine scheme under smooth morphisms from that of the principalization sequence
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineFunctoriality`).

## The construction

Lemma 41 at `y` gives an open `V ∋ y` of `Y`, an affine `AY₁` smooth of some relative dimension
`d'` over an affine open `UA` of `AX`, a closed immersion `j₁ : V ⟶ AY₁` and the fibre square over
`UA`. Since `embY` is an embedding, `V` is the preimage of an open of `AY`, which contains a basic
open `D(G) ∋ embY y` (`isBasis_basicOpen`); `W := embY ⁻¹ᵁ D(G) = D(g)` for `g := embY^♯ G` is an
affine open of `Y` inside `V`. On `V` it is the basic open `D(t)` of `t := g|_V`; lifting `t` along
the surjection `Γ(AY₁) → Γ(V)` of the closed immersion `j₁` (`Scheme.Hom.app_surjective`) to `t̃`
gives the affine basic open `B := D(t̃) ⊆ AY₁` with `j₁ ⁻¹ᵁ B = D(t)`, so `W` is also an open of `V`
and `j := j₁|_W : W ⟶ B` is the restriction of a closed immersion. The square over `AX` is the
square of Lemma 41 pasted with the restriction squares of `embX` to `UA` and of `j₁` to `B`
(`isPullback_morphismRestrict`, `IsPullback.paste_vert`); the square over `AY` is Mathlib's
`IsOpenImmersion.isPullback` on `embY ⁻¹ᵁ D(G) = W`. Finally `d' = d`: the map `V → X ∩ UA` is both
the base change of `AY₁ → UA` (relative dimension `d'`) and a restriction of `h` (relative
dimension `d`), and `V ∋ y` is nonempty (`SmoothOfRelativeDimension.eq_of_nonempty`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  Hironaka.Sequence

namespace Hironaka.Resolution

/-- A chart of the smooth `h : Y ⟶ X` over the closed immersions `embX`, `embY` (the fibre square
of [Kol07, Lemma 41], shrunk to a basic open of `Y`): an affine open `W` of `Y` (a scheme with its
open immersion `e`), a fibre square over `embX` with an affine `B` smooth of relative dimension `d`
over `AX`, and the basic open `D(G)` of `AY` cutting `W` out of `Y`, with its fibre square over
`embY`. -/
structure Chart {X Y AX AY : Scheme.{u}} (h : Y ⟶ X) (embX : X ⟶ AX) (embY : Y ⟶ AY) (d : ℕ)
    where
  /-- The chart, an affine open of `Y`. -/
  W : Scheme.{u}
  /-- The open immersion of the chart into `Y`. -/
  e : W ⟶ Y
  [isOpenImmersion_e : IsOpenImmersion e]
  [isAffine_W : IsAffine W]
  /-- The affine ambient of the chart over `AX`. -/
  B : Scheme.{u}
  [isAffine_B : IsAffine B]
  /-- The smooth map of ambients, of relative dimension `d`. -/
  q : B ⟶ AX
  [smoothOfRelativeDimension_q : SmoothOfRelativeDimension d q]
  /-- The closed immersion of the chart into its ambient. -/
  j : W ⟶ B
  [isClosedImmersion_j : IsClosedImmersion j]
  /-- The fibre square of [Kol07, Lemma 41]: `W = X ×_{AX} B`. -/
  sqX : IsPullback j (e ≫ h) q embX
  /-- The global section of `AY` whose basic open cuts `W` out of `Y`. -/
  G : Γ(AY, ⊤)
  /-- The closed immersion of the chart into the basic open `D(G)`. -/
  jY : W ⟶ (AY.basicOpen G : Scheme.{u})
  [isClosedImmersion_jY : IsClosedImmersion jY]
  /-- The Y-side fibre square: `W = Y ×_{AY} D(G)`. -/
  sqY : IsPullback jY e (AY.basicOpen G).ι embY

attribute [instance] Chart.isOpenImmersion_e Chart.isAffine_W Chart.isAffine_B
  Chart.smoothOfRelativeDimension_q Chart.isClosedImmersion_j Chart.isClosedImmersion_jY

/-- Every point of `Y` lies in a chart ("(34.1) is a local property", [Kol07, Theorem 36, proof],
with the fibre square of [Kol07, Lemma 41] shrunk to a basic open); the relative dimension of the
chart is that of `h` by `SmoothOfRelativeDimension.eq_of_nonempty`. -/
theorem exists_chart_mem {X Y AX AY : Scheme.{u}} (h : Y ⟶ X) (d : ℕ)
    [SmoothOfRelativeDimension d h] (embX : X ⟶ AX) [IsClosedImmersion embX] (embY : Y ⟶ AY)
    [IsClosedImmersion embY] [IsAffine AY] (y : Y) :
    ∃ c : Chart h embX embY d, y ∈ Set.range c.e := by
  have := SmoothOfRelativeDimension.smooth d h
  obtain ⟨UA, V, hyV, hV, AYc, hAYc, hA, hsm, ⟨d', hd'⟩, -, j, hj, sq⟩ :=
    exists_smooth_ambient_lift' h y embX
  -- Step A: a basic open `D(G)` of `AY` with `embY y ∈ D(G)` and `embY ⁻¹ᵁ D(G) ≤ V`
  obtain ⟨O, hO, hOV⟩ := embY.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  have hyO : embY y ∈ (⟨O, hO⟩ : AY.Opens) := by
    change embY y ∈ O
    have : y ∈ embY ⁻¹' O := by rw [hOV]; exact hyV
    exact this
  obtain ⟨_, ⟨G, rfl⟩, hyG, hGO⟩ := (Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen AY)) hyO
  have hpre : embY ⁻¹ᵁ AY.basicOpen G ≤ V := by
    intro z hz
    have hz' : embY z ∈ O := hGO hz
    have : z ∈ embY ⁻¹' O := hz'
    rw [hOV] at this
    exact this
  -- Step B: the matching basic open of `AYc`
  have hsurj : Function.Surjective (j.app ⊤) :=
    Scheme.Hom.app_surjective j ⊤ (isAffineOpen_top AYc)
  obtain ⟨t', ht'⟩ := hsurj (V.ι.appTop (embY.appTop G))
  have hAff : IsAffine (AYc.basicOpen t' : Scheme.{u}) := (isAffineOpen_top AYc).basicOpen t'
  have hWaff : IsAffine (j ⁻¹ᵁ AYc.basicOpen t' : Scheme.{u}) :=
    ((isAffineOpen_top AYc).basicOpen t').preimage j
  -- the chart `W := j ⁻¹ᵁ D(t')`, an open of `V`, is `D(g)` read in `V`
  have hWv : j ⁻¹ᵁ AYc.basicOpen t' =
      (V : Scheme.{u}).basicOpen (V.ι.appTop (embY.appTop G)) := by
    rw [Scheme.preimage_basicOpen_top]
    exact congrArg _ ht'
  have hWY : (V : Scheme.{u}).basicOpen (V.ι.appTop (embY.appTop G)) =
      V.ι ⁻¹ᵁ (Y.basicOpen (embY.appTop G)) := by
    rw [Scheme.preimage_basicOpen_top]
  have hYG : Y.basicOpen (embY.appTop G) = embY ⁻¹ᵁ AY.basicOpen G := by
    rw [Scheme.preimage_basicOpen_top]
  have hWv' : j ⁻¹ᵁ AYc.basicOpen t' = V.ι ⁻¹ᵁ (Y.basicOpen (embY.appTop G)) := hWv.trans hWY
  have hle : Y.basicOpen (embY.appTop G) ≤ V := hYG ▸ hpre
  -- the chart's open immersion into `Y` has range `D(g)`
  have hrange : ((j ⁻¹ᵁ AYc.basicOpen t').ι ≫ V.ι).opensRange =
      Y.basicOpen (embY.appTop G) := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hWv',
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hle
  -- Y-side: the chart maps into `D(G)`
  have hrangeY : Set.range (((j ⁻¹ᵁ AYc.basicOpen t').ι ≫ V.ι) ≫ embY) ⊆
      Set.range (AY.basicOpen G).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    have hw : ((j ⁻¹ᵁ AYc.basicOpen t').ι ≫ V.ι) w ∈ Y.basicOpen (embY.appTop G) := by
      rw [← hrange]
      exact Scheme.Hom.mem_opensRange.mpr ⟨w, rfl⟩
    rw [hYG] at hw
    exact hw
  have hjY : IsOpenImmersion.lift (AY.basicOpen G).ι _ hrangeY ≫ (AY.basicOpen G).ι =
      ((j ⁻¹ᵁ AYc.basicOpen t').ι ≫ V.ι) ≫ embY := IsOpenImmersion.lift_fac _ _ _
  have sqY : IsPullback (IsOpenImmersion.lift (AY.basicOpen G).ι _ hrangeY)
      ((j ⁻¹ᵁ AYc.basicOpen t').ι ≫ V.ι) (AY.basicOpen G).ι embY :=
    IsOpenImmersion.isPullback _ _ _ _ hjY.symm
      (by rw [Scheme.Opens.opensRange_ι, hrange, hYG])
  have hjYcl : IsClosedImmersion (IsOpenImmersion.lift (AY.basicOpen G).ι _ hrangeY) :=
    IsZariskiLocalAtTarget.of_isPullback (P := @IsClosedImmersion) sqY.flip ‹_›
  -- X-side: Lemma 41's square, globalised and restricted to the chart
  have hres : IsPullback (embX.resLE UA (embX ⁻¹ᵁ UA) le_rfl) (embX ⁻¹ᵁ UA).ι UA.ι embX := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact isPullback_morphismRestrict embX UA
  have sq' : IsPullback j (V.ι ≫ h) (hA ≫ UA.ι) embX := by
    have := sq.paste_vert hres
    rwa [Scheme.Hom.resLE_comp_ι] at this
  have hjW : IsClosedImmersion (j ∣_ AYc.basicOpen t') := IsZariskiLocalAtTarget.restrict hj _
  have sqX : IsPullback (j ∣_ AYc.basicOpen t') (((j ⁻¹ᵁ AYc.basicOpen t').ι ≫ V.ι) ≫ h)
      ((AYc.basicOpen t').ι ≫ hA ≫ UA.ι) embX := by
    rw [Category.assoc]
    exact (isPullback_morphismRestrict j (AYc.basicOpen t')).paste_vert sq'
  -- the relative dimension of the chart is that of `h`
  have hlocS : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} d) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have hlocT : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} d) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ inferInstance
  have hr1 : SmoothOfRelativeDimension d' (h.resLE (embX ⁻¹ᵁ UA) V hV) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange d'
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @SmoothOfRelativeDimension d') sq hd'
  have hr2 : SmoothOfRelativeDimension d (h.resLE (embX ⁻¹ᵁ UA) V hV) :=
    IsZariskiLocalAtSource.resLE (P := @SmoothOfRelativeDimension d) hV ‹_›
  have hne : Nonempty (V : Scheme.{u}) := ⟨⟨y, hyV⟩⟩
  have hdd : d' = d :=
    SmoothOfRelativeDimension.eq_of_nonempty (h.resLE (embX ⁻¹ᵁ UA) V hV) (n := d') (m := d)
  have hq0 : SmoothOfRelativeDimension (0 + (d' + 0)) ((AYc.basicOpen t').ι ≫ hA ≫ UA.ι) :=
    smoothOfRelativeDimension_comp 0 (d' + 0) _ _
  have hq : SmoothOfRelativeDimension d ((AYc.basicOpen t').ι ≫ hA ≫ UA.ι) := by
    have e0 : 0 + (d' + 0) = d := by omega
    rw [e0] at hq0
    exact hq0
  -- the chart, and the point lies in it
  refine ⟨⟨(j ⁻¹ᵁ AYc.basicOpen t' : Scheme.{u}), (j ⁻¹ᵁ AYc.basicOpen t').ι ≫ V.ι,
    (AYc.basicOpen t' : Scheme.{u}), (AYc.basicOpen t').ι ≫ hA ≫ UA.ι, j ∣_ AYc.basicOpen t', sqX,
    G, IsOpenImmersion.lift (AY.basicOpen G).ι _ hrangeY, sqY⟩, ?_⟩
  have hyW : (⟨y, hyV⟩ : (V : Scheme.{u})) ∈ j ⁻¹ᵁ AYc.basicOpen t' := by
    rw [hWv']
    change V.ι ⟨y, hyV⟩ ∈ Y.basicOpen (embY.appTop G)
    rw [hYG]
    exact hyG
  exact ⟨⟨⟨y, hyV⟩, hyW⟩, rfl⟩

end Hironaka.Resolution
