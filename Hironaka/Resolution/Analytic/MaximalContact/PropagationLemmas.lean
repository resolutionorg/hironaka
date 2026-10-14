/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.MaximalContact.OneStepDescentLemmas
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Tools for the propagation step

Kollár's propagation step ("(91.1′–4′) also hold in an open neighbourhood `U(p)` of `p`",
[Kol07, 95]) moves stalk-level facts at one point to a neighbourhood
(`Hironaka/Resolution/Analytic/MaximalContact/Propagation.lean`). This module holds the general
tools it uses:

* `IdealSheaf.eventually_germ_mem_stalkIdeal`: a section whose germ at `a` lies in the stalk ideal
  `J_a` has its germs in `J` at every point near `a` — the witness `g' ∈ J(V)` with `g'_a = g_a`
  agrees with `g` on a neighbourhood, on which `J` is a sheaf of ideals;
* `germMap_germ_eq_germMap_germ_of_eventuallyEq`: the pull-backs along two maps `f, g` of the
  germs of two sections agree when the composites `s₁ ∘ f`, `s₂ ∘ g` agree near the point;
* `map_stalkCast_stalkIdeal`: transport of a stalk ideal along an equality of points;
* `contMDiffOn_subtypeVal_comp_iff`: analyticity of a map into an open subset is analyticity of
  its composite with the inclusion (Mathlib's `ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff`,
  at `C^ω`);
* `PartialDiffeomorph.isLocalDiffeomorph_comp_subtype_val`: a partial analytic isomorphism `Φ`
  composed with the inclusion of an open `U ⊆ Φ.source`, as a map out of the open submanifold `U`,
  is a local analytic isomorphism — Kollár's `Φ : U(p) → M`.
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section Generic

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} X}

/-- A germ in the stalk ideal at `a` stays in the stalk ideals nearby: if the germ at `a` of a
section `g` lies in `J_a`, the germs of `g` at all points near `a` lie in `J` (the witness
`g' ∈ J(V)` with `g'_a = g_a` agrees with `g` on a neighbourhood). -/
theorem _root_.Manifold.IdealSheaf.eventually_germ_mem_stalkIdeal (J : IdealSheaf 𝒪) {W : Opens X}
    {a : X}
    (ha : a ∈ W) (g : 𝒪.presheaf.obj (op W)) (h : 𝒪.presheaf.germ W a ha g ∈ J.stalkIdeal a) :
    ∀ᶠ b in 𝓝 a, ∀ hb : b ∈ W, 𝒪.presheaf.germ W b hb g ∈ J.stalkIdeal b := by
  obtain ⟨V, haV, g', hg', hgg'⟩ := J.mem_stalkIdeal_iff.mp h
  obtain ⟨W', haW', iV, iW, hres⟩ := 𝒪.presheaf.germ_eq a haV ha g' g hgg'
  filter_upwards [W'.2.mem_nhds haW'] with b hb hbW
  rw [← 𝒪.presheaf.germ_res_apply iW b hb g, ← hres, 𝒪.presheaf.germ_res_apply iV b hb g']
  exact J.germ_mem_stalkIdeal (iV.le hb) hg'

end Generic

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section Germs

variable {U M : AnalyticManifold.{u} 𝕜 E}

/-- Two pull-backs of germs of sections agree when the composites agree near the point. -/
theorem germMap_germ_eq_germMap_germ_of_eventuallyEq (f g : AnalyticMap U M)
    (u : U)
    {W₁ W₂ : Opens M} (h₁ : f u ∈ W₁) (h₂ : g u ∈ W₂)
    (s₁ : (structureSheaf 𝕜 E M).presheaf.obj (op W₁))
    (s₂ : (structureSheaf 𝕜 E M).presheaf.obj (op W₂))
    (hev : ∀ᶠ x in 𝓝 u, extendSection 𝕜 E s₁ (f x) = extendSection 𝕜 E s₂ (g x)) :
    germMap (⇑f) f.contMDiff u ((structureSheaf 𝕜 E M).presheaf.germ W₁ (f u) h₁ s₁) =
      germMap (⇑g) g.contMDiff u ((structureSheaf 𝕜 E M).presheaf.germ W₂ (g u) h₂ s₂) := by
  apply stalkToGerm_injective
  rw [stalkToGerm_germMap, stalkToGerm_germMap, stalkToGerm_structureSheaf_germ,
    stalkToGerm_structureSheaf_germ, Germ.coe_compTendsto, Germ.coe_compTendsto]
  exact Germ.coe_eq.mpr hev

/-- Transport of a stalk ideal along an equality of points. -/
theorem map_stalkCast_stalkIdeal (J : AnalyticManifold.IdealSheaf M) {x y : M} (h : x = y) :
    Ideal.map (stalkCast (𝕜 := 𝕜) (E := E) h) (J.stalkIdeal x) = J.stalkIdeal y := by
  subst h
  exact Ideal.map_id _

end Germs

section Subtype

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace E N]

/-- Analyticity of a map into an open subset `U` is analyticity of its composite with the
inclusion (Mathlib's `ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff` at `C^ω`). -/
theorem contMDiffOn_subtypeVal_comp_iff {U : Opens N} (f : M → U) (s : Set M) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Subtype.val ∘ f) s ↔ ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω f s :=
  forall₂_congr fun x _ => ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f s x

/-- Kollár's `Φ : U(p) → M` [Kol07, 95]: a partial analytic isomorphism `Φ` composed with the
inclusion of an open `U ⊆ Φ.source`, as a map out of the open submanifold `U`, is a local analytic
isomorphism — its inverse `Φ⁻¹ : Φ(U) → U` is analytic into the open subset. -/
theorem PartialDiffeomorph.isLocalDiffeomorph_comp_subtype_val
    (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (U : Opens M) (hU : (U : Set M) ⊆ Φ.source) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (fun x : U => Φ x.1) := by
  intro x₀
  classical
  have hleft : ∀ x : U, Φ.toPartialEquiv.invFun (Φ x.1) ∈ U := fun x => by
    have h := Φ.toPartialEquiv.left_inv' (hU x.2)
    change Φ.toPartialEquiv.invFun (Φ.toPartialEquiv.toFun x.1) ∈ U
    rw [h]
    exact x.2
  let Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) U N ω :=
    { toFun := fun x => Φ x.1
      invFun := fun y =>
        if h : Φ.toPartialEquiv.invFun y ∈ U then ⟨Φ.toPartialEquiv.invFun y, h⟩ else x₀
      source := univ
      target := Φ '' (U : Set M)
      map_source' := fun x _ => ⟨x.1, x.2, rfl⟩
      map_target' := fun _ _ => mem_univ _
      left_inv' := by
        intro x _
        rw [dite_eq_left (hleft x)]
        exact Subtype.ext (Φ.toPartialEquiv.left_inv' (hU x.2))
      right_inv' := by
        rintro _ ⟨x, hxU, rfl⟩
        rw [dite_eq_left (hleft ⟨x, hxU⟩)]
        exact Φ.toPartialEquiv.right_inv' (Φ.toPartialEquiv.map_source' (hU hxU))
      open_source := isOpen_univ
      open_target := (Φ.toOpenPartialHomeomorph.isOpen_image_iff_of_subset_source hU).mpr U.2
      contMDiffOn_toFun :=
        (Φ.contMDiffOn_toFun.comp_contMDiff contMDiff_subtype_val fun x => hU x.2).contMDiffOn
      contMDiffOn_invFun := by
        refine (contMDiffOn_subtypeVal_comp_iff _ _).mp ?_
        refine (Φ.contMDiffOn_invFun.mono ?_).congr ?_
        · rintro _ ⟨x, hxU, rfl⟩
          exact Φ.toPartialEquiv.map_source' (hU hxU)
        · rintro _ ⟨x, hxU, rfl⟩
          have h := hleft ⟨x, hxU⟩
          simp only [Function.comp_apply, dite_eq_left h] }
  exact Ψ.isLocalDiffeomorphAt _ _ _ (mem_univ x₀)

end Subtype

end Hironaka.Manifold

end
