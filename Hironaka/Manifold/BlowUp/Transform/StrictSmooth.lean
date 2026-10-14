/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.StrictSubspace
public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.CoordGerm
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.BlowUp.Transform.StrictCharts
import Hironaka.Manifold.BlowUp.Transform.StrictFlag
import Hironaka.Manifold.BlowUp.Transform.StrictIdeal
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Strict transforms of closed subspaces: the smooth case

The strict transform `X'` of a closed subspace `X ⊆ M` under the blowing-up `π : M' → M` along a
closed submanifold `Y` is defined ideal-theoretically (`strictTransformSubspace`: the saturation
`⋃_k (π⁻¹(I_X) : I_F^k)` of the total transform with respect to the exceptional divisor `F`,
[BM97, Proposition 3.13]), and the geometric strict transform `X''` as the smallest closed
subspace of `π⁻¹(X)` containing `|π⁻¹(X)| ∖ |F|` (`geometricStrictTransform`). This file proves
that in the smooth case these agree with the geometric constructions on the manifold:

* for closed submanifolds `Y ⊆ S` the strict transform of `S` is the ideal sheaf
  (`IsClosedSubmanifold.idealSheaf`) of the closed submanifold
  `strictTransformSet π Y S = closure (π⁻¹(S ∖ Y))`, and `X' = X''` (the identification of the
  blow-up of `S` with the birational transform of `S` in [Kol07, Definition 30, 30.2]);
* for `S = Y` the strict transform is empty, the total transform is the exceptional divisor, and
  its ideal `π^*I_Y = I_F` is locally principal (blowing up a smooth variety along itself, as in
  the proof of [Kol07, Corollary 22]; [Wlo09, Lemma 5.3.7]);
* for a smooth hypersurface `H` having simple normal crossings with `Y` (in coordinates: at every
  point of `H ∩ Y` a chart adapted to `Y` in which `H` is a coordinate hyperplane), the strict
  transform of `H` is the ideal sheaf of the smooth hypersurface `strictTransformSet π Y H`; for
  `Y ⊆ H` it is the birational transform `π^{-1}_*(I_H, 1)` [BM97, §3, "The strict transform"].

## The argument

Everything reduces to a stalkwise identity `saturation = I_{S'}` for the closed submanifold
`S' = strictTransformSet π Y S`, then `IdealSheaf.ext` (the saturation stalks have local
generators because `I_{S'}` does, so `strictTransformSubspace` is the sheaf with those stalks;
the finite-type clause holds outright here).

* `saturation ⊆ I_{S'}` is chart-free (`saturationStalk_le_idealSheaf_strictTransform`): pulled
  back germs of `I_S` vanish on `π⁻¹(S) ⊇ S'` (`totalTransform_stalkIdeal_le_idealSheaf_of_subset`,
  from the vanishing characterisation `germ_mem_stalkIdeal_idealSheaf_iff`); a germ `t` with
  `u^k t ∈ π⁻¹(I_S)`, `u` the exceptional coordinate, vanishes on `S' ∖ F ⊇ π⁻¹(S ∖ Y)`, which is
  dense in `S'`, so `t` vanishes on `S'` (`eq_zero_on_closure_of_pow_mul_eq_zero`).
* `I_{S'} ⊆ saturation` is the chart computation. For `Y ⊆ S` it uses the flag chart
  (`exists_adaptedChart_flag`: `Y = {z_σ = 0}`, `S = {z_{σ(τ j)} = 0}`) and the blow-up chart
  formulas `u_i u_{σ k} = π^* z_{σ k}` (`IsBlowUpChart.germMap_coord_of_ne`): on the charts
  `i ∉ range τ`, `S' = {u_{σ(τ j)} = 0}` and each `u_{σ(τ j)} ∈ (π⁻¹(I_S) : I_F)`; on the charts
  `i ∈ range τ`, `S'` is absent and the saturation is `⊤`. For a hypersurface it uses the three
  chart lemmas of `Hironaka.Manifold.BlowUp.Transform.Strict`
  (`strictTransform_inter_source_self/_of_ne/_off`) for `H = {z_k = 0}` with `k` the blow-up
  index, another centre index, or an off-centre index. Off the centre the saturation is the total
  transform (`saturationStalk_of_notMem_cosupport`) and the transported chart gives the
  generators.
* `X' = X''`: every candidate vanishes on `π⁻¹(S ∖ Y)` (its stalks at those points lie in the
  maximal ideal), hence on the closure `S'`, so lies in `I_{S'}`
  (`geometricCandidates_le_idealSheaf_strictTransform`); with
  `strictTransform_mem_geometricCandidates_of_hasLocalGenerators` this makes `I_{S'}` the greatest
  candidate, and `geometricStrictTransform` (a classical choice of the greatest element) equals
  it.
* The case `S = Y` is immediate: `I_F = π⁻¹(I_Y)` by definition (both are the pullback of `I_Y`),
  so `1` lies in the saturation; the principal stalks are
  `stalkIdeal_exceptionalIdealSheaf_eq_span_coord`.

Conventions: ideal sheaves are ordered by inclusion of stalks, `⊤` is the empty subspace; the
strict transform set is Kollár's birational transform of a subvariety. The statements quantify
over closed-submanifold witnesses `hS'`/`hH'` of the strict transform set where they name its
ideal sheaf; the witnesses are supplied by `IsClosedSubmanifold.strictTransform` and
`isClosedSubmanifold_strictTransform_of_charts`. The topological lemmas and the vanishing
characterisation are routine (the sources' "dense in the strict transform").
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### Two topological lemmas: vanishing on a dense subset -/

/-- A continuous function vanishing on `A ∩ W` vanishes on `closure A ∩ W` (`W` open). -/
theorem eq_zero_on_closure_of_eq_zero_on {X' : Type*} [TopologicalSpace X'] {A W : Set X'}
    (hW : IsOpen W) {G : X' → 𝕜} (hG : ContinuousOn G W) (hA0 : ∀ z ∈ A ∩ W, G z = 0) :
    ∀ y ∈ closure A ∩ W, G y = 0 := by
  rintro y ⟨hyA, hyW⟩
  have hne : (𝓝[A] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hyA
  have hW' : W ∈ 𝓝[A] y := mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hyW)
  have heq : 𝓝[A ∩ W] y = 𝓝[A] y := nhdsWithin_inter_of_mem' hW'
  have ht : Tendsto G (𝓝[A] y) (𝓝 (G y)) := by
    rw [← heq]
    exact (hG.continuousWithinAt hyW).mono_left (nhdsWithin_mono y inter_subset_right)
  have h0 : Tendsto G (𝓝[A] y) (𝓝 (0 : 𝕜)) := by
    rw [← heq]
    exact tendsto_const_nhds.congr'
      (eventually_of_mem self_mem_nhdsWithin fun z hz => (hA0 z hz).symm)
  exact tendsto_nhds_unique ht h0

/-- A continuous function vanishing, up to a factor nonzero on `A`, on the closure of `A`,
vanishes on that closure. -/
theorem eq_zero_on_closure_of_pow_mul_eq_zero {X' : Type*} [TopologicalSpace X'] {A W : Set X'}
    (hW : IsOpen W) {G v : X' → 𝕜} (hG : ContinuousOn G W) {k : ℕ}
    (hv : ∀ z ∈ A ∩ W, v z ≠ 0) (hvan : ∀ y ∈ closure A ∩ W, v y ^ k * G y = 0) :
    ∀ y ∈ closure A ∩ W, G y = 0 := by
  rintro y ⟨hyA, hyW⟩
  have hA0 : ∀ z ∈ A ∩ W, G z = 0 := fun z hz =>
    (mul_eq_zero.mp (hvan z ⟨subset_closure hz.1, hz.2⟩)).resolve_left (pow_ne_zero k (hv z hz))
  have hne : (𝓝[A] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hyA
  have hW' : W ∈ 𝓝[A] y := mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hyW)
  have heq : 𝓝[A ∩ W] y = 𝓝[A] y := nhdsWithin_inter_of_mem' hW'
  have ht : Tendsto G (𝓝[A] y) (𝓝 (G y)) := by
    rw [← heq]
    exact (hG.continuousWithinAt hyW).mono_left (nhdsWithin_mono y inter_subset_right)
  have h0 : Tendsto G (𝓝[A] y) (𝓝 (0 : 𝕜)) := by
    rw [← heq]
    exact tendsto_const_nhds.congr'
      (eventually_of_mem self_mem_nhdsWithin fun z hz => (hA0 z hz).symm)
  exact tendsto_nhds_unique ht h0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-! ### The vanishing characterisation of the ideal of a closed submanifold -/

/-- A germ at a point of a closed submanifold lies in its ideal iff a representing function
vanishes on the submanifold near the point (`germ_mem_stalkIdeal_idealSheaf_iff`, read
through `stalkToGerm`). -/
theorem IsClosedSubmanifold.mem_stalkIdeal_idealSheaf_iff_eventually {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) {p : M} (hp : p ∈ Y)
    (s : (structureSheaf 𝕜 E M).presheaf.stalk p) {f : M → 𝕜}
    (hf : stalkToGerm 𝓘(𝕜, E) ω M p s = ↑f) :
    s ∈ hY.idealSheaf.stalkIdeal p ↔ ∀ᶠ y : Y in 𝓝 (⟨p, hp⟩ : Y), f (y : M) = 0 := by
  obtain ⟨V, hpV, g, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  rw [hY.germ_mem_stalkIdeal_idealSheaf_iff V hp hpV]
  rw [stalkToGerm_structureSheaf_germ] at hf
  have hef : ∀ᶠ x in 𝓝 p, extendSection 𝕜 E g x = f x := Germ.coe_eq.mp hf
  have hef' : ∀ᶠ y : Y in 𝓝 (⟨p, hp⟩ : Y), extendSection 𝕜 E g (y : M) = f (y : M) :=
    (continuous_subtype_val.tendsto (⟨p, hp⟩ : Y)).eventually hef
  exact eventually_congr (hef'.mono fun y hy => by rw [hy])

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-! ### Stalkwise lemmas on the saturation (no chart on `M` needed) -/

/-- The total transform of the ideal of a closed submanifold `S` lies in the
ideal of any closed submanifold `S' ⊆ π⁻¹(S)` — pulled-back germs of functions vanishing on `S`
vanish on `π⁻¹(S)`. -/
theorem totalTransform_stalkIdeal_le_idealSheaf_of_subset {Y : Set M} {c : ℕ}
    (h : IsBlowUp ψ Y c π) {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S s)
    {S' : Set M'} {s' : ℕ} (hS' : IsClosedSubmanifold ψ S' s') (hsub : S' ⊆ π ⁻¹' S) (p : M') :
    (hS.idealSheaf.pullback π h.contMDiff).stalkIdeal p ≤ hS'.idealSheaf.stalkIdeal p := by
  by_cases hp : p ∈ S'
  · rw [IdealSheaf.stalkIdeal_pullback, Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap]
    have hpS : π p ∈ S := hsub hp
    obtain ⟨U, hU, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq t
    rw [hS.germ_mem_stalkIdeal_idealSheaf_iff U hpS hU] at ht
    rw [hS'.mem_stalkIdeal_idealSheaf_iff_eventually hp _
      (f := extendSection 𝕜 E f ∘ π) (by
        rw [stalkToGerm_germMap, stalkToGerm_structureSheaf_germ, Germ.coe_compTendsto])]
    have hmap : Continuous (fun y : S' => (⟨π y, hsub y.2⟩ : S)) :=
      (h.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _
    exact (hmap.tendsto ⟨p, hp⟩).eventually ht
  · rw [hS'.stalkIdeal_idealSheaf_of_notMem hp]
    exact le_top

/-- Off `π⁻¹(S)` the saturation of the total transform of `I_S` is the unit ideal (the stalk of
`I_S` at `π p ∉ S` is `⊤`). -/
theorem saturationStalk_eq_top_of_notMem_preimage {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) {S : Set M} {s : ℕ}
    (hS : IsClosedSubmanifold ψ S s) {p : M'} (hpS : π p ∉ S) :
    saturationStalk hY h hS.idealSheaf p = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  refine Submodule.mem_iSup_of_mem 0 (Submodule.mem_colon.mpr fun q _ => ?_)
  rw [IdealSheaf.stalkIdeal_pullback, hS.stalkIdeal_idealSheaf_of_notMem hpS, Ideal.map_top]
  exact Submodule.mem_top

/-- If a generator `u` of the exceptional ideal at `p` lies in the total transform, the saturation
is the unit ideal (`1 ∈ (π⁻¹(I) : I_F)`). -/
theorem saturationStalk_eq_top_of_mem {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) {I : IdealSheaf (structureSheaf 𝕜 E M)} {p : M'}
    {u : (structureSheaf 𝕜 E M').presheaf.stalk p}
    (hIF : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p = Ideal.span {u})
    (hu : u ∈ (I.pullback π h.contMDiff).stalkIdeal p) : saturationStalk hY h I p = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  refine Submodule.mem_iSup_of_mem 1 (Submodule.mem_colon.mpr fun q hq => ?_)
  rw [SetLike.mem_coe, pow_one, hIF, Ideal.mem_span_singleton'] at hq
  obtain ⟨a, rfl⟩ := hq
  rw [smul_eq_mul, one_mul]
  exact Ideal.mul_mem_left _ a hu

/-- `v` lies in the saturation `(π⁻¹(I) : I_F)` as soon as `u v` lies in the total transform, `u`
a generator of the exceptional ideal at `p` — BM97's `f' = y_exc^{-1} (f ∘ σ)` ([BM97, §3, "The
strict transform"]) read as a membership. -/
theorem mem_saturationStalk_of_mul_mem {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) {I : IdealSheaf (structureSheaf 𝕜 E M)} {p : M'}
    {u v : (structureSheaf 𝕜 E M').presheaf.stalk p}
    (hIF : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p = Ideal.span {u})
    (huv : u * v ∈ (I.pullback π h.contMDiff).stalkIdeal p) :
    v ∈ saturationStalk hY h I p := by
  refine Submodule.mem_iSup_of_mem 1 (Submodule.mem_colon.mpr fun q hq => ?_)
  rw [SetLike.mem_coe, pow_one, hIF, Ideal.mem_span_singleton'] at hq
  obtain ⟨a, rfl⟩ := hq
  rw [smul_eq_mul, mul_left_comm]
  refine Ideal.mul_mem_left _ a ?_
  rw [mul_comm]
  exact huv

/-- Every
candidate `J` (an ideal sheaf `≥ π⁻¹(I_S)` whose cosupport contains
`|π⁻¹(S)| ∖ |F| = π⁻¹(S ∖ Y)`) lies in the ideal of the submanifold strict transform `S'`: a
section of `J` vanishes at every point of the cosupport of `J` (the stalk ideal lies in the maximal
ideal there), hence on `π⁻¹(S ∖ Y)`, hence — by continuity — on its closure `S'`. -/
theorem geometricCandidates_le_idealSheaf_strictTransform {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) {S : Set M} {s : ℕ}
    (hS : IsClosedSubmanifold ψ S s) (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s)
    {J : IdealSheaf (structureSheaf 𝕜 E M')}
    (hJ : J ∈ geometricCandidates hY h hS.idealSheaf) : J ≤ hS'.idealSheaf := by
  rw [IdealSheaf.le_def]
  intro p
  by_cases hp : p ∈ strictTransformSet π Y S
  swap
  · rw [hS'.stalkIdeal_idealSheaf_of_notMem hp]
    exact le_top
  intro t ht
  obtain ⟨V, hpV, g, hg, rfl⟩ := (IdealSheaf.mem_stalkIdeal_iff _).mp ht
  rw [hS'.germ_mem_stalkIdeal_idealSheaf_iff V hp hpV]
  have hvan : ∀ z ∈ π ⁻¹' (S \ Y) ∩ (V : Set M'), extendSection 𝕜 E g z = 0 := by
    intro z hz
    have hzJ : z ∈ J.support := by
      refine hJ.2 z ⟨?_, ?_⟩
      · rw [IdealSheaf.support_pullback, hS.cosupport_idealSheaf]
        exact hz.1.1
      · rw [(isIdealSheafOf_exceptionalIdealSheaf hY h).1]
        exact hz.1.2
    have hmem : (structureSheaf 𝕜 E M').presheaf.germ V z hz.2 g ∈ J.stalkIdeal z :=
      J.germ_mem_stalkIdeal hz.2 hg
    have hle : J.stalkIdeal z ≤ IsLocalRing.maximalIdeal _ :=
      IsLocalRing.le_maximalIdeal ((IdealSheaf.mem_support _).mp hzJ)
    rw [← eval_germ' _ hz.2 g]
    exact (mem_maximalIdeal_iff_eval _ _).mp (hle hmem)
  refine (mem_nhds_subtype _ _ _).mpr ⟨V, V.2.mem_nhds hpV, fun y hy => ?_⟩
  exact eq_zero_on_closure_of_eq_zero_on (A := π ⁻¹' (S \ Y)) V.2
    (contMDiffOn_extendSection g).continuousOn hvan (y : M') ⟨y.2, hy⟩

/-! ### Blowing up a smooth `X` along itself -/

section

variable {X : Set M} {c : ℕ} (hX : IsClosedSubmanifold ψ X c) (h : IsBlowUp ψ X c π)

/-- The saturation of the total
transform of the centre's own ideal is the unit ideal at every point — `I_F = π⁻¹(I_X)`, so
`1 ∈ (π⁻¹(I_X) : I_F)`. -/
theorem saturationStalk_self_eq_top (a' : M') : saturationStalk hX h hX.idealSheaf a' = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  refine Submodule.mem_iSup_of_mem 1 (Submodule.mem_colon.mpr fun p hp => ?_)
  rw [SetLike.mem_coe, pow_one] at hp
  rw [one_smul]
  exact hp

/-- The strict transform of the
centre is empty — the unit ideal sheaf (`IdealSheaf.ext` from `saturationStalk_self_eq_top`; the
constant family `⊤` has local generators). -/
theorem strictTransform_self_eq_empty : strictTransformSubspace hX h hX.idealSheaf = ⊤ := by
  have hsat : saturationStalk hX h hX.idealSheaf = fun _ => ⊤ :=
    funext (saturationStalk_self_eq_top hX h)
  have hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M')
      (saturationStalk hX h hX.idealSheaf) := by
    rw [hsat]
    exact IdealSheaf.hasLocalGenerators_top
  refine IdealSheaf.ext fun a' => ?_
  rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hX h _ hex,
    saturationStalk_self_eq_top, IdealSheaf.stalkIdeal_top]

/-- The total transform of the centre is the exceptional divisor,
`π⁻¹(X) = F` — as closed subspaces, both being the pullback of `I_X` along `π`; the two
readings coincide by `rfl`. -/
theorem totalTransform_self_eq_exceptional :
    hX.idealSheaf.pullback π h.contMDiff = hX.idealSheaf.pullback π h.contMDiff := rfl

/-- The points of `π⁻¹(X)` are `π⁻¹(X) = |F|`
(`IdealSheaf.support_pullback`, `cosupport_idealSheaf`). -/
theorem cosupport_totalTransform_self :
    (hX.idealSheaf.pullback π h.contMDiff).support = π ⁻¹' X := by
  rw [IdealSheaf.support_pullback, hX.cosupport_idealSheaf]

/-- The
stalks of the total transform of the centre are principal — spanned by the scaling coordinate `u_i`
in the blow-up chart `i` (`stalkIdeal_exceptionalIdealSheaf_eq_span_coord`), by `1` off
the exceptional divisor. -/
theorem exists_stalkIdeal_totalTransform_self_eq_span_singleton (a' : M') :
    ∃ y : (structureSheaf 𝕜 E M').presheaf.stalk a',
      (hX.idealSheaf.pullback π h.contMDiff).stalkIdeal a' = Ideal.span {y} := by
  by_cases ha : π a' ∈ X
  · obtain ⟨φ, σ, haφ, hφ⟩ := hX.exists_adaptedChart (π a') ha
    obtain ⟨i, Φ, hΦ, haΦ⟩ := h.cover φ σ hφ a' haφ
    exact ⟨_, stalkIdeal_exceptionalIdealSheaf_eq_span_coord hX h hφ hΦ haΦ⟩
  · refine ⟨1, ?_⟩
    rw [Ideal.span_singleton_one]
    exact stalkIdeal_exceptionalIdealSheaf_of_notMem hX h ha

end

/-! ### The saturation lies in the ideal of the submanifold strict transform -/

/-- Inclusion "saturation `⊆ I_{S'}`" ([BM97, Proposition 3.13] read
in the smooth case): a germ `t` at `p` in the saturation `(π⁻¹(I_S) : I_F^k)` has `u^k t` in
`π⁻¹(I_S) ⊆ I_{S'}` for the exceptional coordinate `u = u_i` of the blow-up chart, so `t` vanishes
on `S' ∖ F ⊇ π⁻¹(S ∖ Y)`, which is dense in `S' = closure (π⁻¹(S ∖ Y))`; hence `t ∈ I_{S'}`
(`mem_stalkIdeal_idealSheaf_iff_eventually`). `S'` is any closed-submanifold witness of the strict
transform set; no containment `Y ⊆ S` is needed. -/
theorem saturationStalk_le_idealSheaf_strictTransform {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) {S : Set M} {s : ℕ}
    (hS : IsClosedSubmanifold ψ S s) (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s)
    (p : M') : saturationStalk hY h hS.idealSheaf p ≤ hS'.idealSheaf.stalkIdeal p := by
  have hsub : strictTransformSet π Y S ⊆ π ⁻¹' S :=
    strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed
  by_cases hp : p ∈ strictTransformSet π Y S
  swap
  · rw [hS'.stalkIdeal_idealSheaf_of_notMem hp]
    exact le_top
  by_cases hpY : π p ∈ Y
  swap
  · have hnot : p ∉ (hY.idealSheaf.pullback π h.contMDiff).support := by
      rw [(isIdealSheafOf_exceptionalIdealSheaf hY h).1]
      exact hpY
    rw [saturationStalk_of_notMem_cosupport hY h _ hnot]
    exact totalTransform_stalkIdeal_le_idealSheaf_of_subset h hS hS' hsub p
  obtain ⟨φ, σ, hpφ, hφ⟩ := hY.exists_adaptedChart (π p) hpY
  obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hpφ
  have hIF : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p =
      Ideal.span {coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i)} :=
    stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hpΦ
  intro t ht
  have hdir : Directed (· ≤ ·) fun k : ℕ =>
      Submodule.colon ((hS.idealSheaf.pullback π h.contMDiff).stalkIdeal p)
        (SetLike.coe ((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p ^ k)) := by
    refine Monotone.directed_le fun a b hab => Submodule.colon_mono le_rfl ?_
    exact SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right hab)
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp ht
  have huk : coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i) ^ k ∈
      (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p ^ k :=
    Ideal.pow_mem_pow (by rw [hIF]; exact Ideal.mem_span_singleton_self _) k
  have hmem : coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i) ^ k * t ∈ hS'.idealSheaf.stalkIdeal p := by
    refine totalTransform_stalkIdeal_le_idealSheaf_of_subset h hS hS' hsub p ?_
    have := Submodule.mem_colon.mp hk _ huk
    rwa [smul_eq_mul, mul_comm] at this
  obtain ⟨V, hpV, g, rfl⟩ := (structureSheaf 𝕜 E M').presheaf.exists_germ_eq t
  have hrep : stalkToGerm 𝓘(𝕜, E) ω M' p
      (coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i) ^ k *
        (structureSheaf 𝕜 E M').presheaf.germ V p hpV g) =
      ↑(extendSection 𝕜 E (chartSection E ψ Φ hΦ.mem_maximalAtlas (σ i)) ^ k *
        extendSection 𝕜 E g) := by
    rw [map_mul, map_pow, stalkToGerm_coord, stalkToGerm_structureSheaf_germ, ← Germ.coe_pow,
      ← Germ.coe_mul]
  rw [hS'.mem_stalkIdeal_idealSheaf_iff_eventually hp _ hrep] at hmem
  rw [hS'.mem_stalkIdeal_idealSheaf_iff_eventually hp _ (stalkToGerm_structureSheaf_germ _ _ _ _)]
  obtain ⟨O, hO, hOsub⟩ := (mem_nhds_subtype _ _ _).mp hmem
  obtain ⟨W, hWO, hWopen, hpW⟩ := mem_nhds_iff.mp hO
  have hW'open : IsOpen (W ∩ Φ.source ∩ (V : Set M')) := (hWopen.inter Φ.open_source).inter V.2
  have hpW' : p ∈ W ∩ Φ.source ∩ (V : Set M') := ⟨⟨hpW, hpΦ⟩, hpV⟩
  refine (mem_nhds_subtype _ _ _).mpr ⟨_, hW'open.mem_nhds hpW', fun y hy => ?_⟩
  refine eq_zero_on_closure_of_pow_mul_eq_zero (A := π ⁻¹' (S \ Y)) hW'open
    (G := extendSection 𝕜 E g)
    (v := extendSection 𝕜 E (chartSection E ψ Φ hΦ.mem_maximalAtlas (σ i))) (k := k)
    ((contMDiffOn_extendSection g).continuousOn.mono fun x hx => hx.2) ?_ ?_ (y : M') ⟨y.2, hy⟩
  · intro z hz
    have hzΦ : z ∈ Φ.source := hz.2.1.2
    rw [extendSection_of_mem 𝕜 E _ hzΦ]
    change ψ (Φ z) (σ i) ≠ 0
    exact fun h0 => hz.1.2 ((IsBlowUpChart.mem_preimage_iff hφ hΦ hzΦ).mpr h0)
  · intro y' hy'
    exact hOsub (show (⟨y', hy'.1⟩ : strictTransformSet π Y S) ∈ Subtype.val ⁻¹' O from
      hWO hy'.2.1.1)

variable [IsManifold 𝓘(𝕜, E) ω M]

/-! ### A closed submanifold containing the centre -/

section

variable {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
  {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S s) (hYS : Y ⊆ S)

include hYS in
/-- Off the strict
transform set the saturation is the unit ideal — either `π p ∉ S` (the total transform is `⊤`
there), or `p` lies over the centre in a blow-up chart `Φ` of index `i` in which some `S`-coordinate
`u_{σ (τ j)}` is a unit at `p`, so `u_i = u_i u_{σ(τ j)} / u_{σ(τ j)} = π^*z_{σ(τ j)} / u_{σ(τ j)}`
lies in `π⁻¹(I_S)` and `1 ∈ (π⁻¹(I_S) : I_F)`. -/
theorem saturationStalk_eq_top_of_notMem_strictTransform {p : M'}
    (hp : p ∉ strictTransformSet π Y S) : saturationStalk hY h hS.idealSheaf p = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  by_cases hpS : π p ∈ S
  swap
  · refine Submodule.mem_iSup_of_mem 0 (Submodule.mem_colon.mpr fun q _ => ?_)
    rw [IdealSheaf.stalkIdeal_pullback, hS.stalkIdeal_idealSheaf_of_notMem hpS, Ideal.map_top]
    exact Submodule.mem_top
  have hpY : π p ∈ Y := by
    by_contra hpY
    exact hp ((preimage_subset_strictTransform_union (π := π) (Y := Y) (H := S)
      (show p ∈ π ⁻¹' S from hpS)).resolve_right hpY)
  obtain ⟨φ, σ, τ, hpφ, hφ, hSflag⟩ := exists_adaptedChart_flag hY hS hYS hpY
  obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hpφ
  have hφS : IsAdaptedChart ψ S φ (τ.trans σ) := ⟨hφ.1, hSflag⟩
  -- the scaling coordinate lies in the total transform
  have hu : coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i) ∈
      (hS.idealSheaf.pullback π h.contMDiff).stalkIdeal p := by
    rw [IdealSheaf.stalkIdeal_pullback, hS.stalkIdeal_idealSheaf_eq_span hpS hφS hpφ]
    by_cases hi : i ∈ Set.range τ
    · obtain ⟨j, hj⟩ := hi
      rw [← IsBlowUpChart.germMap_coord_self h.contMDiff hφ.1 hΦ hpΦ]
      refine Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, ?_⟩)
      simp only [Function.Embedding.trans_apply, hj]
    · -- some `S`-coordinate `u_{σ(τ j)}` is a unit at `p`, and `u_i u_{σ(τ j)} = π^* z_{σ(τ j)}`
      have hE := strictTransform_inter_source_of_not_mem_range hφ hΦ hSflag hi
      have hnot : ¬ ∀ j, ψ (Φ p) (σ (τ j)) = 0 := fun hall =>
        hp ((Set.ext_iff.mp hE p).mpr ⟨hpΦ, hall⟩).1
      obtain ⟨j, hj⟩ := not_forall.mp hnot
      have hunit : IsUnit (coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ (τ j))) := by
        rw [← IsLocalRing.notMem_maximalIdeal, mem_maximalIdeal_iff_eval, eval_coord]
        exact hj
      have hne : τ j ≠ i := fun hji => hi ⟨j, hji⟩
      have hmul : coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i) *
          coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ (τ j)) ∈
          Ideal.map (germMap π h.contMDiff p)
            (Ideal.span (Set.range fun j => coord E ψ φ hφ.1 hpφ ((τ.trans σ) j))) := by
        rw [← IsBlowUpChart.germMap_coord_of_ne h.contMDiff hφ.1 hΦ hpΦ hne]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
      exact (Ideal.mul_unit_mem_iff_mem _ hunit).mp hmul
  refine Submodule.mem_iSup_of_mem 1 (Submodule.mem_colon.mpr fun q hq => ?_)
  rw [SetLike.mem_coe, pow_one, stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hpΦ,
    Ideal.mem_span_singleton'] at hq
  obtain ⟨a, rfl⟩ := hq
  rw [smul_eq_mul, one_mul]
  exact Ideal.mul_mem_left _ a hu

include hYS in
/-- The inclusion
"`I_{S'} ⊆` saturation": over the centre, in the flag chart, `S'` is `{u_{σ(τ j)} = 0}`
on the blow-up charts of index `i ∉ range τ` (`strictTransform_inter_source_of_not_mem_range`) and
`u_i u_{σ(τ j)} = π^* z_{σ(τ j)} ∈ π⁻¹(I_S)`, so each generator `u_{σ(τ j)}` lies in
`(π⁻¹(I_S) : I_F)`; off the centre `π` is a local isomorphism and the saturation is the total
transform (`saturationStalk_of_notMem_cosupport`), whose generators `z_{σ₁ j} ∘ π` are
the coordinates of the transported chart (`exists_adaptedChart_strictTransform_off'`). -/
theorem idealSheaf_strictTransform_stalkIdeal_le_saturationStalk
    (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s) (p : M') :
    hS'.idealSheaf.stalkIdeal p ≤ saturationStalk hY h hS.idealSheaf p := by
  have hπc : Continuous π := h.contMDiff.continuous
  by_cases hp : p ∈ strictTransformSet π Y S
  swap
  · rw [saturationStalk_eq_top_of_notMem_strictTransform hY h hS hYS hp]
    exact le_top
  by_cases hpY : π p ∈ Y
  · obtain ⟨φ, σ, τ, hpφ, hφ, hSflag⟩ := exists_adaptedChart_flag hY hS hYS hpY
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hpφ
    have hi : i ∉ Set.range τ := fun hi =>
      Set.eq_empty_iff_forall_notMem.mp (strictTransform_inter_source_of_mem_range hφ hΦ hSflag hi)
        p ⟨hp, hpΦ⟩
    have hΦS' : IsAdaptedChart ψ (strictTransformSet π Y S) Φ (τ.trans σ) :=
      isAdaptedChart_strictTransform_of_not_mem_range hφ hΦ hSflag hi
    have hφS : IsAdaptedChart ψ S φ (τ.trans σ) := ⟨hφ.1, hSflag⟩
    rw [hS'.stalkIdeal_idealSheaf_eq_span hp hΦS' hpΦ, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.mem_iSup_of_mem 1 (Submodule.mem_colon.mpr fun q hq => ?_)
    rw [SetLike.mem_coe, pow_one, stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hpΦ,
      Ideal.mem_span_singleton'] at hq
    obtain ⟨a, rfl⟩ := hq
    rw [smul_eq_mul, mul_left_comm]
    refine Ideal.mul_mem_left _ a ?_
    have hne : τ j ≠ i := fun hji => hi ⟨j, hji⟩
    rw [mul_comm]
    change coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i) *
      coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ (τ j)) ∈ _
    rw [← IsBlowUpChart.germMap_coord_of_ne h.contMDiff hφ.1 hΦ hpΦ hne,
      IdealSheaf.stalkIdeal_pullback]
    refine Ideal.mem_map_of_mem _ ?_
    rw [hS.stalkIdeal_idealSheaf_eq_span (hYS hpY) hφS hpφ]
    exact Ideal.subset_span ⟨j, rfl⟩
  · have hnot : p ∉ (hY.idealSheaf.pullback π h.contMDiff).support := by
      rw [(isIdealSheafOf_exceptionalIdealSheaf hY h).1]
      exact hpY
    rw [saturationStalk_of_notMem_cosupport hY h _ hnot]
    have hpS : π p ∈ S := strictTransform_subset_preimage hπc hS.isClosed hp
    obtain ⟨φ, σ₁, e, hpφ, hφ, hpe, he, hcoord⟩ :=
      exists_adaptedChart_strictTransform_off' hY h hS hpS hpY
    rw [hS'.stalkIdeal_idealSheaf_eq_span hp he hpe, IdealSheaf.stalkIdeal_pullback,
      hS.stalkIdeal_idealSheaf_eq_span hpS hφ hpφ, Ideal.map_span, ← Set.range_comp]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine Ideal.subset_span ⟨j, ?_⟩
    apply stalkToGerm_injective 𝓘(𝕜, E) ω M' p
    rw [Function.comp_apply, stalkToGerm_germMap, stalkToGerm_coord, stalkToGerm_coord,
      Germ.coe_compTendsto, Germ.coe_eq]
    filter_upwards [e.open_source.mem_nhds hpe,
      (hπc.isOpen_preimage _ φ.open_source).mem_nhds hpφ] with x hx hx'
    rw [Function.comp_apply, extendSection_of_mem 𝕜 E _ hx', extendSection_of_mem 𝕜 E _ hx]
    change ψ (φ (π x)) (σ₁ j) = ψ (e x) (σ₁ j)
    exact (hcoord x hx j).symm

include hYS in
/-- Stalkwise, the saturation of the total transform of `I_S` by the exceptional
divisor is the ideal of the submanifold strict transform `S'` (both inclusions above). -/
theorem saturationStalk_eq_idealSheaf_strictTransform
    (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s) :
    saturationStalk hY h hS.idealSheaf = fun p => hS'.idealSheaf.stalkIdeal p :=
  funext fun p => le_antisymm (saturationStalk_le_idealSheaf_strictTransform hY h hS hS' p)
    (idealSheaf_strictTransform_stalkIdeal_le_saturationStalk hY h hS hYS hS' p)

include hYS in
/-- The saturation stalks have local generators (they are the stalks of the ideal sheaf
`idealSheaf` of the submanifold `S'`, which is locally finitely generated) — the finite-type clause
holds outright in the smooth case, without any Noetherian hypothesis. -/
theorem hasLocalGenerators_saturationStalk_of_subset :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M')
      (saturationStalk hY h hS.idealSheaf) := by
  have hS' := hS.strictTransform hY h hYS
  rw [saturationStalk_eq_idealSheaf_strictTransform hY h hS hYS hS']
  intro a
  obtain ⟨U, ha, k, f, -, hf⟩ := hS'.idealSheaf.locallyFG a
  exact ⟨U, ha, Fin k, inferInstance, f, hf⟩

include hYS in
/-- A restatement: the strict
transform `X'` of a closed submanifold `S ⊇ Y` IS the closed submanifold `Bl_Y S ⊆ Bl_Y M` — its
ideal sheaf is `idealSheaf` of the strict transform set, for any closed-submanifold
witness `hS'` of that set. -/
theorem strictTransform_submanifold_eq_blowUp
    (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s) :
    strictTransformSubspace hY h hS.idealSheaf = hS'.idealSheaf := by
  have hex := hasLocalGenerators_saturationStalk_of_subset hY h hS hYS
  refine IdealSheaf.ext fun p => ?_
  rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h _ hex]
  exact congrFun (saturationStalk_eq_idealSheaf_strictTransform hY h hS hYS hS') p

include hYS in
/-- The strict transform of a closed
submanifold `S ⊇ Y` is the ideal sheaf (`IsIdealSheafOf`) of the closed
submanifold `strictTransformSet π Y S` of `M'`, of the codimension of `S`
(`IsClosedSubmanifold.strictTransform` supplies the witness). -/
theorem isIdealSheafOf_strictTransformSubspace_of_subset :
    IsIdealSheafOf ψ (strictTransformSet π Y S) s (strictTransformSubspace hY h hS.idealSheaf) := by
  have hS' := hS.strictTransform hY h hYS
  rw [strictTransform_submanifold_eq_blowUp hY h hS hYS hS']
  exact hS'.isIdealSheafOf_idealSheaf

include hYS in
/-- The points of `X'` are the strict transform set `closure (π⁻¹(S ∖ Y))`. -/
theorem cosupport_strictTransformSubspace_of_subset :
    (strictTransformSubspace hY h hS.idealSheaf).support = strictTransformSet π Y S :=
  (isIdealSheafOf_strictTransformSubspace_of_subset hY h hS hYS).1

include hYS in
/-- The ideal
sheaf of `X'` is the greatest of candidates — it is a candidate because its stalks are
the saturation (`strictTransform_mem_geometricCandidates_of_hasLocalGenerators`), and
every candidate lies in it (`geometricCandidates_le_idealSheaf_strictTransform`). The geometric
strict transform exists here without local Noetherianity. -/
theorem isGreatest_geometricCandidates_strictTransform_of_subset :
    IsGreatest (geometricCandidates hY h hS.idealSheaf)
      (strictTransformSubspace hY h hS.idealSheaf) := by
  have hS' := hS.strictTransform hY h hYS
  have hex := hasLocalGenerators_saturationStalk_of_subset hY h hS hYS
  refine ⟨strictTransform_mem_geometricCandidates_of_hasLocalGenerators hY h _ hex, fun J hJ => ?_⟩
  rw [strictTransform_submanifold_eq_blowUp hY h hS hYS hS']
  exact geometricCandidates_le_idealSheaf_strictTransform hY h hS hS' hJ

include hYS in
/-- The geometric strict transform of a closed submanifold `S ⊇ Y`
is its strict transform — `geometricStrictTransform` is the `Classical.choice` of the
greatest candidate, which `isGreatest_geometricCandidates_strictTransform_of_subset` exhibits. -/
theorem geometricStrictTransform_eq_strictTransform_of_subset :
    geometricStrictTransform hY h hS.idealSheaf = strictTransformSubspace hY h hS.idealSheaf := by
  have hg := isGreatest_geometricCandidates_strictTransform_of_subset hY h hS hYS
  have hex : ∃ J, IsGreatest (geometricCandidates hY h hS.idealSheaf) J := ⟨_, hg⟩
  rw [geometricStrictTransform, dite_eq_left hex]
  exact (Classical.choose_spec hex).unique hg

end

/-! ### A smooth hypersurface with simple normal crossings with the centre -/

section

variable {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
  {H : Set M} (hH : IsClosedSubmanifold ψ H 1)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The inclusion
"`I_{H'} ⊆` saturation" for a smooth hypersurface `H` with snc charts along the centre: at a point
over `H ∩ Y` take the chart `φ` of `hchart` (`H = {z_k = 0}`) and a blow-up chart `Φ` of index `i`;
if `k = σ i`, `H'` misses the chart and `u_i = π^*z_k ∈ π⁻¹(I_H)` makes the saturation `⊤`; if
`k = σ k'` with `k' ≠ i`, `H' = {u_{σ k'} = 0}` on the chart and `u_i u_{σ k'} = π^* z_k`, so the
generator `u_{σ k'}` lies in `(π⁻¹(I_H) : I_F)` (and the saturation is `⊤` where `u_{σ k'}` is a
unit); if `k` is off the centre, `H' = {u_k = 0}` and `u_k = π^* z_k ∈ π⁻¹(I_H)`. Off the centre
the saturation is the total transform and the transported chart gives the generator.
Off `π⁻¹(H)` both sides are `⊤`. -/
theorem idealSheaf_strictTransform_hypersurface_le_saturationStalk
    (hchart : ∀ a ∈ H ∩ Y, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (k : Fin n),
      a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ ∧ ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) k = 0)
    (hH' : IsClosedSubmanifold ψ (strictTransformSet π Y H) 1) (p : M') :
    hH'.idealSheaf.stalkIdeal p ≤ saturationStalk hY h hH.idealSheaf p := by
  have hπc : Continuous π := h.contMDiff.continuous
  by_cases hpH : π p ∈ H
  swap
  · rw [saturationStalk_eq_top_of_notMem_preimage hY h hH hpH]
    exact le_top
  by_cases hpY : π p ∈ Y
  · obtain ⟨φ, σ, k, hpφ, hφ, hHk⟩ := hchart (π p) ⟨hpH, hpY⟩
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hpφ
    have hφH : IsAdaptedChart ψ H φ (singleEmb k) := isAdaptedChart_singleIdx hφ.1 hHk
    have htot : (hH.idealSheaf.pullback π h.contMDiff).stalkIdeal p =
        Ideal.span {germMap π h.contMDiff p (coord E ψ φ hφ.1 hpφ k)} := by
      rw [IdealSheaf.stalkIdeal_pullback, hH.stalkIdeal_idealSheaf_eq_span hpH hφH hpφ,
        range_singleIdx_coord, Ideal.map_span, Set.image_singleton]
    have hIF := stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hpΦ
    by_cases hkr : ∃ k', σ k' = k
    · obtain ⟨k', rfl⟩ := hkr
      by_cases hki : k' = i
      · subst hki
        have hp' : p ∉ strictTransformSet π Y H := fun hp =>
          Set.eq_empty_iff_forall_notMem.mp (strictTransform_inter_source_self hφ hΦ hHk) p
            ⟨hp, hpΦ⟩
        rw [hH'.stalkIdeal_idealSheaf_of_notMem hp', top_le_iff]
        refine saturationStalk_eq_top_of_mem hY h hIF ?_
        rw [htot, ← IsBlowUpChart.germMap_coord_self h.contMDiff hφ.1 hΦ hpΦ]
        exact Ideal.mem_span_singleton_self _
      · have hE := strictTransform_inter_source_of_ne hφ hΦ hHk (Ne.symm hki)
        have huv : coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i) *
            coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ k') ∈
            (hH.idealSheaf.pullback π h.contMDiff).stalkIdeal p := by
          rw [htot, ← IsBlowUpChart.germMap_coord_of_ne h.contMDiff hφ.1 hΦ hpΦ hki]
          exact Ideal.mem_span_singleton_self _
        by_cases hp' : p ∈ strictTransformSet π Y H
        · have hΦH' : IsAdaptedChart ψ (strictTransformSet π Y H) Φ (singleEmb (σ k')) :=
            isAdaptedChart_singleIdx hΦ.mem_maximalAtlas fun x hx =>
              ⟨fun hxH => ((Set.ext_iff.mp hE x).mp ⟨hxH, hx⟩).2,
                fun h0 => ((Set.ext_iff.mp hE x).mpr ⟨hx, h0⟩).1⟩
          rw [hH'.stalkIdeal_idealSheaf_eq_span hp' hΦH' hpΦ, range_singleIdx_coord, Ideal.span_le,
            Set.singleton_subset_iff, SetLike.mem_coe]
          exact mem_saturationStalk_of_mul_mem hY h hIF huv
        · rw [hH'.stalkIdeal_idealSheaf_of_notMem hp', top_le_iff]
          have hne : ψ (Φ p) (σ k') ≠ 0 := fun h0 => hp' ((Set.ext_iff.mp hE p).mpr ⟨hpΦ, h0⟩).1
          have hu : IsUnit (coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ k')) := by
            rw [← IsLocalRing.notMem_maximalIdeal, mem_maximalIdeal_iff_eval, eval_coord]
            exact hne
          exact saturationStalk_eq_top_of_mem hY h hIF ((Ideal.mul_unit_mem_iff_mem _ hu).mp huv)
    · have hkr' : ∀ k', σ k' ≠ k := fun k' hk' => hkr ⟨k', hk'⟩
      have hE := strictTransform_inter_source_off hφ hΦ hkr' hHk
      have hk : coord E ψ Φ hΦ.mem_maximalAtlas hpΦ k ∈
          (hH.idealSheaf.pullback π h.contMDiff).stalkIdeal p := by
        rw [htot, ← IsBlowUpChart.germMap_coord_off h.contMDiff hφ.1 hΦ hpΦ hkr']
        exact Ideal.mem_span_singleton_self _
      by_cases hp' : p ∈ strictTransformSet π Y H
      · have hΦH' : IsAdaptedChart ψ (strictTransformSet π Y H) Φ (singleEmb k) :=
          isAdaptedChart_singleIdx hΦ.mem_maximalAtlas fun x hx =>
            ⟨fun hxH => ((Set.ext_iff.mp hE x).mp ⟨hxH, hx⟩).2,
              fun h0 => ((Set.ext_iff.mp hE x).mpr ⟨hx, h0⟩).1⟩
        rw [hH'.stalkIdeal_idealSheaf_eq_span hp' hΦH' hpΦ, range_singleIdx_coord, Ideal.span_le,
          Set.singleton_subset_iff, SetLike.mem_coe]
        exact totalTransform_stalkIdeal_le_saturationStalk hY h _ p hk
      · rw [hH'.stalkIdeal_idealSheaf_of_notMem hp', top_le_iff, Ideal.eq_top_iff_one]
        have hne : ψ (Φ p) k ≠ 0 := fun h0 => hp' ((Set.ext_iff.mp hE p).mpr ⟨hpΦ, h0⟩).1
        have hu : IsUnit (coord E ψ Φ hΦ.mem_maximalAtlas hpΦ k) := by
          rw [← IsLocalRing.notMem_maximalIdeal, mem_maximalIdeal_iff_eval, eval_coord]
          exact hne
        refine totalTransform_stalkIdeal_le_saturationStalk hY h _ p ?_
        exact (Ideal.eq_top_iff_one _).mp (Ideal.eq_top_of_isUnit_mem _ hk hu)
  · have hnot : p ∉ (hY.idealSheaf.pullback π h.contMDiff).support := by
      rw [(isIdealSheafOf_exceptionalIdealSheaf hY h).1]
      exact hpY
    rw [saturationStalk_of_notMem_cosupport hY h _ hnot]
    have hp : p ∈ strictTransformSet π Y H :=
      (preimage_subset_strictTransform_union (π := π) (Y := Y)
        (show p ∈ π ⁻¹' H from hpH)).resolve_right hpY
    obtain ⟨φ, σ₁, e, hpφ, hφ, hpe, he, hcoord⟩ :=
      exists_adaptedChart_strictTransform_off' hY h hH hpH hpY
    rw [hH'.stalkIdeal_idealSheaf_eq_span hp he hpe, IdealSheaf.stalkIdeal_pullback,
      hH.stalkIdeal_idealSheaf_eq_span hpH hφ hpφ, Ideal.map_span, ← Set.range_comp]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine Ideal.subset_span ⟨j, ?_⟩
    apply stalkToGerm_injective 𝓘(𝕜, E) ω M' p
    rw [Function.comp_apply, stalkToGerm_germMap, stalkToGerm_coord, stalkToGerm_coord,
      Germ.coe_compTendsto, Germ.coe_eq]
    filter_upwards [e.open_source.mem_nhds hpe,
      (hπc.isOpen_preimage _ φ.open_source).mem_nhds hpφ] with x hx hx'
    rw [Function.comp_apply, extendSection_of_mem 𝕜 E _ hx', extendSection_of_mem 𝕜 E _ hx]
    change ψ (φ (π x)) (σ₁ j) = ψ (e x) (σ₁ j)
    exact (hcoord x hx j).symm

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Stalkwise, the saturation of the total transform of `I_H` is the
ideal of the hypersurface strict transform `H'`, for any codimension-one witness `hH'`. -/
theorem saturationStalk_eq_idealSheaf_strictTransform_hypersurface
    (hchart : ∀ a ∈ H ∩ Y, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (k : Fin n),
      a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ ∧ ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) k = 0)
    (hH' : IsClosedSubmanifold ψ (strictTransformSet π Y H) 1) :
    saturationStalk hY h hH.idealSheaf = fun p => hH'.idealSheaf.stalkIdeal p :=
  funext fun p => le_antisymm (saturationStalk_le_idealSheaf_strictTransform hY h hH hH' p)
    (idealSheaf_strictTransform_hypersurface_le_saturationStalk hY h hH hchart hH' p)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The saturation stalks have local generators — they are the stalks of the ideal
sheaf of the smooth hypersurface `H'`
(`isClosedSubmanifold_strictTransform_of_charts`). -/
theorem hasLocalGenerators_saturationStalk_hypersurface
    (hchart : ∀ a ∈ H ∩ Y, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (k : Fin n),
      a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ ∧ ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) k = 0) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M')
      (saturationStalk hY h hH.idealSheaf) := by
  have hH' := isClosedSubmanifold_strictTransform_of_charts hY h hH hchart
  rw [saturationStalk_eq_idealSheaf_strictTransform_hypersurface hY h hH hchart hH']
  intro a
  obtain ⟨U, ha, k, f, -, hf⟩ := hH'.idealSheaf.locallyFG a
  exact ⟨U, ha, Fin k, inferInstance, f, hf⟩

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- A restatement: the strict transform of a smooth hypersurface
`H` with snc charts along the centre is `idealSheaf` of the strict transform set, for any
codimension-one witness `hH'` of that set. -/
theorem strictTransform_hypersurface_eq
    (hchart : ∀ a ∈ H ∩ Y, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (k : Fin n),
      a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ ∧ ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) k = 0)
    (hH' : IsClosedSubmanifold ψ (strictTransformSet π Y H) 1) :
    strictTransformSubspace hY h hH.idealSheaf = hH'.idealSheaf := by
  have hex := hasLocalGenerators_saturationStalk_hypersurface hY h hH hchart
  refine IdealSheaf.ext fun p => ?_
  rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h _ hex]
  exact congrFun (saturationStalk_eq_idealSheaf_strictTransform_hypersurface hY h hH hchart hH') p

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The strict transform of a smooth hypersurface `H` with snc charts
along the centre is the ideal sheaf of the smooth hypersurface `strictTransformSet π Y H`
(`isClosedSubmanifold_strictTransform_of_charts`). -/
theorem isIdealSheafOf_strictTransformSubspace_hypersurface
    (hchart : ∀ a ∈ H ∩ Y, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (k : Fin n),
      a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ ∧ ∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) k = 0) :
    IsIdealSheafOf ψ (strictTransformSet π Y H) 1 (strictTransformSubspace hY h hH.idealSheaf) := by
  have hH' := isClosedSubmanifold_strictTransform_of_charts hY h hH hchart
  rw [strictTransform_hypersurface_eq hY h hH hchart hH']
  exact hH'.isIdealSheafOf_idealSheaf

/-- For a smooth
hypersurface `H ⊇ Y`, the strict transform of `H` is the marked transform
`π^{-1}_*(I_H, 1)` — both are the ideal sheaf of the strict transform set
(`isIdealSheafOf_strictTransform`, `strictTransform_submanifold_eq_blowUp` with `s = 1`). -/
theorem strictTransform_hypersurface_eq_birationalTransform (hYH : Y ⊆ H) :
    strictTransformSubspace hY h hH.idealSheaf =
      (MarkedIdealSheaf.birationalTransform hY h ⟨hH.idealSheaf, 1⟩).I := by
  have hH' := isClosedSubmanifold_strictTransform hY h hH hYH
  rw [strictTransform_submanifold_eq_blowUp hY h hH hYH hH']
  exact ((isIdealSheafOf_strictTransform hY h hH hYH).eq_idealSheaf hH').symm

end

end Manifold
