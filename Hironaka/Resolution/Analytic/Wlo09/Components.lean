/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.ModifiedMarkedFam
public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeq
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.StrictSubspace
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceBasic
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The controlled transform inside the saturation chain, and the exceptional set

Tools for identifying the final support of Włodarczyk's modified marked resolution with the strict
transform of `Y` (the proof of [Wlo09, Theorem 7.4.1]), stated for any finite blow-up sequence of
order `≥ 1` [Kol07, Definition 66]. The ideal-theoretic strict transform of a closed subspace
along a blowing-up is described by its saturation, the colon of the total transform by the powers
of the exceptional ideal [BM97, Proposition 3.13]; where a lemma needs the saturation to be finitely
generated (proved for every `RCLike` field in `BlowUp/Transform/SaturationFiniteType.lean`), it
takes that as an explicit hypothesis.

* The saturation is monotone in the ideal (`saturationStalk_mono`); the controlled transform of
  `(I, m)` lies in the saturation of `I` when `I` has order `≥ m` along the centre (the colon
  description `isDivExceptional_birationalTransform`); and the saturation lies in the stalk of the
  strict transform in both branches of its definition.
* Hence, along a sequence of order `≥ 1`, the marked chain at mark `1` lies in the saturation
  chain stage by stage (`markedTransformSeq_le_strictTransformSubspaceSeq`), and the cosupport of
  the final strict transform lies in the final support
  (`cosupport_strictTransformSubspaceSeq_subset`), unconditionally.
* The support of the family of exceptional divisors at stage `i + 1` is the preimage of the
  support at stage `i` together with the exceptional divisor of the `i`-th blow-up
  (`support_totalTransformSeq_succ`, the recursion of [Hir64, Main Theorem II′(N), p. 156] read on
  supports), so a point off the final exceptional set lies over no centre at any stage; off the
  exceptional set the two chains agree
  (`stalkIdeal_markedTransformSeq_eq_strictTransformSubspaceSeq_of_notMem_support`).
* The density step: at a point of the support of `J` where `J` is locally the ideal of a
  coordinate subspace transversal to the members of a simple normal crossing family, the support
  off the family is dense (`mem_closure_cosupport_diff_support_of_isSmoothTransversalIdealAt`).
* The identity itself (`cosupport_markedTransformSeq_eq_cosupport_strictTransformSubspaceSeq`):
  for a sequence of order `≥ 1` whose exceptional families are simple normal crossing families,
  whose saturations are finitely generated and whose final controlled transform is at every
  support point locally the ideal of a coordinate subspace transversal to the exceptional
  divisors, the final support is the cosupport of the final strict transform.

These lemmas are applied to the embedded desingularization functor in
`Hironaka/Resolution/Analytic/Wlo09/StrictTransformClauses.lean`.
-/

public section

open Set Topology TopologicalSpace AnalyticManifold Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section Saturation

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}
  (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)

/-- The saturation is monotone in the ideal sheaf. -/
theorem saturationStalk_mono {I J : Manifold.IdealSheaf (structureSheaf 𝕜 E M)} (hIJ : I ≤ J)
    (a' : M') :
    saturationStalk hY h I a' ≤ saturationStalk hY h J a' := by
  refine iSup_mono fun k => Submodule.colon_mono ?_ le_rfl
  rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback]
  exact Ideal.map_mono (hIJ _)

/-- The controlled transform of `(I, m)` lies in the saturation of `I` when `I` has order `≥ m`
along the centre: its stalk is the colon by the `m`-th power of the exceptional ideal
(`isDivExceptional_birationalTransform`), one term of the saturation's supremum. -/
theorem birationalTransform_stalkIdeal_le_saturationStalk (I : Manifold.IdealSheaf
    (structureSheaf 𝕜 E M))
    {m : ℕ} (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) (a' : M') :
    (MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I.stalkIdeal a' ≤
      saturationStalk hY h I a' := by
  have hcol := isDivExceptional_birationalTransform hY h ⟨I, m⟩ hm a'
  dsimp only at hcol
  rw [hcol]
  exact le_iSup (fun k : ℕ => Submodule.colon ((I.pullback π h.contMDiff).stalkIdeal a')
    (SetLike.coe ((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ^ k))) m

/-- The saturation lies in the stalk of the strict transform `strictTransformSubspace`, in both
branches of its definition (the stalks agree when the saturation has local generators; otherwise
the strict transform is the unit ideal sheaf). -/
theorem saturationStalk_le_stalkIdeal_strictTransformSubspace
    (I : Manifold.IdealSheaf (structureSheaf 𝕜 E M)) (a' : M') :
    saturationStalk hY h I a' ≤ (strictTransformSubspace hY h I).stalkIdeal a' := by
  by_cases hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I)
  · rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex]
  · rw [strictTransformSubspace_of_not_hasLocalGenerators hY h I hex, IdealSheaf.stalkIdeal_top]
    exact le_top

end Saturation

section Chain

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- Along a sequence of order `≥ 1` for `(J, 1, E₀)` [Kol07, Definition 66], the marked chain at
mark `1` lies in the saturation chain (`strictTransformSubspaceSeq`) stage by stage: at each step
the controlled transform lies in the saturation of the previous controlled transform
(`birationalTransform_stalkIdeal_le_saturationStalk`, the order clause (4′) supplying the order
`≥ 1` along the centre), which lies in the saturation of the previous strict transform
(`saturationStalk_mono`, the induction hypothesis), which lies in the strict transform
(`saturationStalk_le_stalkIdeal_strictTransformSubspace`). -/
theorem markedTransformSeq_le_strictTransformSubspaceSeq (J E₀ : AnalyticManifold.IdealSheaf M)
    (hge : S.IsOfOrderGe J 1 E₀) (i : Fin (S.length + 1)) :
    S.markedTransformSeq J 1 i ≤ S.strictTransformSubspaceSeq J i := by
  induction i using Fin.induction with
  | zero => exact le_rfl
  | succ i ih =>
    rw [FiniteSuccession.markedTransformSeq_succ, FiniteSuccession.strictTransformSubspaceSeq_succ,
      IdealSheaf.le_def]
    intro a'
    have hm : ∀ a ∈ (S.center i).support, ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (S.isClosedSubmanifold_center i).idealSheaf (S.markedTransformSeq J 1 i.castSucc) a := by
      intro a ha
      rw [S.idealSheaf_center i, Nat.cast_one]
      exact (hge i).2 a ha
    calc (MarkedIdealSheaf.birationalTransform (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
          ⟨S.markedTransformSeq J 1 i.castSucc, 1⟩).I.stalkIdeal a'
        ≤ saturationStalk (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
            (S.markedTransformSeq J 1 i.castSucc) a' :=
          birationalTransform_stalkIdeal_le_saturationStalk _ _ _ hm a'
      _ ≤ saturationStalk (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
            (S.strictTransformSubspaceSeq J i.castSucc) a' :=
          saturationStalk_mono _ _ ih a'
      _ ≤ (strictTransformSubspace (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
            (S.strictTransformSubspaceSeq J i.castSucc)).stalkIdeal a' :=
          saturationStalk_le_stalkIdeal_strictTransformSubspace _ _ _ a'

/-- One inclusion of the identity between the final support and the final strict transform, from
the order hypothesis alone and with no finite-type input: the cosupport of the final strict
transform lies in the final support `supp(𝓘_r, 1)` (a larger ideal sheaf has a smaller
cosupport). -/
theorem cosupport_strictTransformSubspaceSeq_subset (J E₀ : AnalyticManifold.IdealSheaf M)
    (hge : S.IsOfOrderGe J 1 E₀) (i : Fin (S.length + 1)) :
    (S.strictTransformSubspaceSeq J i).support ⊆ (S.markedTransformSeq J 1 i).support := by
  intro x hx htop
  exact hx (top_le_iff.mp
    (htop ▸ markedTransformSeq_le_strictTransformSubspaceSeq S J E₀ hge i x))

/-- The support of the exceptional family at stage `i + 1` is the preimage of the support at stage
`i` together with the exceptional divisor of the `i`-th blow-up (the recursion
`E_{i+1} = red(π_i⁻¹(E_i) ∪ π_i⁻¹(Z_i))` of [Hir64, Main Theorem II′(N), p. 156] read on
supports). The components at stage `i` are assumed closed (they are, for a sequence of order
`≥ 1`: `isSnc_totalTransformSeq`). -/
theorem support_totalTransformSeq_succ (i : Fin S.length)
    (hcl : ∀ j, IsClosed ((S.totalTransformSeq i.castSucc).hyp j)) :
    (S.totalTransformSeq i.succ).support =
      S.map i ⁻¹' (S.totalTransformSeq i.castSucc).support ∪ S.exceptionalAt i := by
  rw [FiniteSuccession.totalTransformSeq_succ]
  exact HypersurfaceFamily.support_totalTransform _ _ _ (S.map i).2.continuous hcl

/-- A point of stage `i + 1` off the exceptional family lies off the `i`-th exceptional divisor and
maps to a point off the exceptional family of stage `i`. -/
theorem notMem_exceptionalAt_and_map_notMem_of_notMem_support (i : Fin S.length)
    (hcl : ∀ j, IsClosed ((S.totalTransformSeq i.castSucc).hyp j)) {x : S.stage i.succ}
    (hx : x ∉ (S.totalTransformSeq i.succ).support) :
    x ∉ S.exceptionalAt i ∧ S.map i x ∉ (S.totalTransformSeq i.castSucc).support := by
  rw [support_totalTransformSeq_succ S i hcl, Set.mem_union, not_or] at hx
  exact ⟨hx.2, hx.1⟩

end Chain

section OffExceptional

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- Off the exceptional family the two chains agree, given that each saturation is finitely
generated (the hypothesis under which the strict transform is the saturation,
[BM97, Proposition 3.13]): at a point of stage `i` lying on no exceptional divisor, the stalk of
the marked chain at mark `1` equals the stalk of the saturation chain. Both are the pullback of
the previous stalks along the blow-up (`birationalTransform_stalkIdeal_of_notMem`,
`saturationStalk_of_notMem_cosupport`), and the previous stalks agree by induction, the point lying
over a point off the previous exceptional family (`support_totalTransformSeq_succ`). -/
theorem stalkIdeal_markedTransformSeq_eq_strictTransformSubspaceSeq_of_notMem_support
    (J E₀ : AnalyticManifold.IdealSheaf M) (hge : S.IsOfOrderGe J 1 E₀)
    (hcl : ∀ (i : Fin (S.length + 1)) (j), IsClosed ((S.totalTransformSeq i).hyp j))
    (hsat : ∀ i : Fin S.length,
      IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E (S.stage i.succ))
        (saturationStalk (π := ⇑(S.map i)) (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
          (S.strictTransformSubspaceSeq J i.castSucc)))
    (i : Fin (S.length + 1)) (x : S.stage i) (hx : x ∉ (S.totalTransformSeq i).support) :
    (S.markedTransformSeq J 1 i).stalkIdeal x =
      (S.strictTransformSubspaceSeq J i).stalkIdeal x := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    obtain ⟨hxe, hxm⟩ :=
      notMem_exceptionalAt_and_map_notMem_of_notMem_support S i (hcl i.castSucc) hx
    have hm : ∀ a ∈ (S.center i).support, ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (S.isClosedSubmanifold_center i).idealSheaf (S.markedTransformSeq J 1 i.castSucc) a := by
      intro a ha
      rw [S.idealSheaf_center i, Nat.cast_one]
      exact (hge i).2 a ha
    have hxc : x ∉ ((S.isClosedSubmanifold_center i).idealSheaf.pullback _ (S.isBlowUp_map
        i).contMDiff).support := by
      rw [IsBlowUp.cosupport_exceptionalIdealSheaf (S.isClosedSubmanifold_center i)
        (S.isBlowUp_map i)]
      exact hxe
    rw [FiniteSuccession.markedTransformSeq_succ, FiniteSuccession.strictTransformSubspaceSeq_succ,
      birationalTransform_stalkIdeal_of_notMem (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
        hm hxe,
      stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _ (hsat i) x,
      saturationStalk_of_notMem_cosupport _ _ _ hxc,
      IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback, ih (S.map i x) hxm]

end OffExceptional

section Density

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- A coordinate ideal `(z_σ)` at `a` is proper iff every `z_{σ i}` vanishes at `a` (a coordinate
not vanishing at `a` is a unit of the stalk, `isUnit_coord_of_ne_zero`; vanishing coordinates lie in
the maximal ideal, `coord_mem_maximalIdeal_of_eq_zero`). -/
theorem span_coord_ne_top_iff (φ : OpenPartialHomeomorph M E)
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M)
    {a : M} (ha : a ∈ φ.source) {c : ℕ} (σ : Fin c ↪ Fin n) :
    Ideal.span (Set.range fun i => coord E ψ φ hφ ha (σ i)) ≠ ⊤ ↔ ∀ i, ψ (φ a) (σ i) = 0 := by
  constructor
  · intro hne i
    by_contra h0
    exact hne (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩)
      (isUnit_coord_of_ne_zero φ hφ ha h0))
  · intro h0
    refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    exact coord_mem_maximalIdeal_of_eq_zero φ hφ ha (h0 i)

/-- The density step: at a point `x` of the support of `J` where `J` is locally the ideal of a
coordinate subspace transversal to the members of the simple normal crossing family `F` through
`x` (the predicate `IsSmoothTransversalIdealAt`, the shape of the final controlled transform of
the modified marked resolution), the support of `J` off the family is dense at `x`. In the chart,
move `x` off every member through it along the members' own coordinates (which are not
coordinates of the subspace) by an arbitrarily small nonzero amount; the members not through `x`
form a closed set missing `x` (the family is locally finite with closed members). -/
theorem mem_closure_cosupport_diff_support_of_isSmoothTransversalIdealAt (F : HypersurfaceFamily M)
    (hF : F.IsSnc ψ) (J : Manifold.IdealSheaf (structureSheaf 𝕜 E M)) {x : M} (hxJ : x ∈ J.support)
    (hx : F.IsSmoothTransversalIdealAt ψ J x) : x ∈ closure (J.support \ F.support) := by
  classical
  obtain ⟨c, φ, σ, cidx, hφ, hrest⟩ := hx
  obtain ⟨hJ, hne⟩ := hrest
  -- `hJ`'s type depends on `hφ`: project it instead of destructuring it
  have hatlas := hφ.1
  have hxs := hφ.2.1
  have hcoord := hφ.2.2.1
  -- the members not through `x` form a closed set missing `x`
  have hclosed : IsClosed (⋃ j : {j // x ∉ F.hyp j}, F.hyp j.1) :=
    (hF.2.1.comp_injective Subtype.val_injective).isClosed_iUnion fun j => (hF.1 j.1).isClosed
  have hxN : x ∉ ⋃ j : {j // x ∉ F.hyp j}, F.hyp j.1 := by
    simp only [Set.mem_iUnion, not_exists]
    exact fun j => j.2
  -- the coordinates of `x`: the subspace coordinates vanish (`x` is a support point)
  have hx0 : ∀ i, ψ (φ x) (σ i) = 0 := by
    have := (hJ x hxs) ▸ (IdealSheaf.mem_support J).mp hxJ
    exact (span_coord_ne_top_iff ψ φ hatlas hxs σ).mp this
  -- the perturbation direction: the indicator of the members' coordinates
  set v : Fin n → 𝕜 := fun k => if k ∈ Set.range cidx then 1 else 0 with hv
  have hvσ : ∀ i, v (σ i) = 0 := by
    intro i
    simp only [hv]
    rw [ite_eq_right]
    rintro ⟨j, hj⟩
    exact hne j i hj
  have hvc : ∀ j, v (cidx j) = 1 := by
    intro j
    simp only [hv]
    rw [ite_eq_left ⟨j, rfl⟩]
  set g : 𝕜 → E := fun t => ψ.symm (ψ (φ x) + t • v) with hg
  have hgc : Continuous g :=
    ψ.symm.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hg0 : g 0 = φ x := by simp [hg]
  rw [mem_closure_iff_nhds]
  intro U hU
  -- the open neighbourhood of `x` inside the chart and off the members not through `x`
  obtain ⟨W, hWU, hWo, hxW⟩ := mem_nhds_iff.mp hU
  set W' : Set M := W ∩ φ.source ∩ (⋃ j : {j // x ∉ F.hyp j}, F.hyp j.1)ᶜ with hW'
  have hW'o : IsOpen W' := (hWo.inter φ.open_source).inter hclosed.isOpen_compl
  have hxW' : x ∈ W' := ⟨⟨hxW, hxs⟩, hxN⟩
  -- the parameters `t` whose perturbation lands in `W'`, an open neighbourhood of `0`
  have hSo : IsOpen (g ⁻¹' (φ.target ∩ φ.symm ⁻¹' W')) :=
    (φ.isOpen_inter_preimage_symm hW'o).preimage hgc
  have h0S : (0 : 𝕜) ∈ g ⁻¹' (φ.target ∩ φ.symm ⁻¹' W') := by
    refine ⟨?_, ?_⟩
    · rw [hg0]; exact φ.map_source hxs
    · rw [Set.mem_preimage, hg0, φ.left_inv hxs]; exact hxW'
  have := NormedField.nhdsWithin_isUnit_neBot (α := 𝕜)
  obtain ⟨t, htS, htu⟩ := Filter.nonempty_of_mem (Filter.inter_mem
    (mem_nhdsWithin_of_mem_nhds (hSo.mem_nhds h0S)) (self_mem_nhdsWithin (s := {x : 𝕜 | IsUnit x})))
  have ht0 : t ≠ 0 := htu.ne_zero
  obtain ⟨hgt, haW'⟩ := htS
  -- the perturbed point
  set a : M := φ.symm (g t) with hadef
  have has : a ∈ φ.source := φ.map_target hgt
  have hφa : φ a = g t := φ.right_inv hgt
  have hψa : ψ (φ a) = ψ (φ x) + t • v := by rw [hφa, hg]; simp
  refine ⟨a, ?_, ?_, ?_⟩
  · exact hWU haW'.1.1
  · -- `a` is a support point: its subspace coordinates vanish
    rw [IdealSheaf.mem_support, hJ a has]
    refine (span_coord_ne_top_iff ψ φ hatlas has σ).mpr fun i => ?_
    rw [hψa]
    simp [hx0 i, hvσ i]
  · -- `a` lies on no member of the family
    intro hmem
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
    by_cases hxj : x ∈ F.hyp j
    · have h1 := (hcoord ⟨j, hxj⟩ a has).mp hj
      have h2 := (hcoord ⟨j, hxj⟩ x hxs).mp hxj
      rw [hψa] at h1
      exact ht0 (by simpa [h2, hvc ⟨j, hxj⟩] using h1)
    · exact haW'.2 (Set.mem_iUnion.mpr ⟨⟨j, hxj⟩, hj⟩)

end Density

section Assembly

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The final support is the cosupport of the final strict transform, for any finite blow-up
sequence of order `≥ 1` [Kol07, Definition 66] whose exceptional families are simple normal
crossing families, whose saturations have local generators, and whose final controlled transform is
at every support point locally the ideal of a coordinate subspace transversal to the exceptional
divisors (the shape of the output of Włodarczyk's modified algorithm, the proof of
[Wlo09, Theorem 7.4.1]). One inclusion is `cosupport_strictTransformSubspaceSeq_subset`; for the
other, a support point is a limit of support points off the exceptional divisors (the density
lemma), where the two chains agree
(`stalkIdeal_markedTransformSeq_eq_strictTransformSubspaceSeq_of_notMem_support`), and the
cosupport of the strict transform is closed. -/
theorem cosupport_markedTransformSeq_eq_cosupport_strictTransformSubspaceSeq
    (J E₀ : AnalyticManifold.IdealSheaf M) (hge : S.IsOfOrderGe J 1 E₀)
    (hsnc : ∀ i : Fin (S.length + 1), (S.totalTransformSeq i).IsSnc ψ)
    (hsat : ∀ i : Fin S.length,
      IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E (S.stage i.succ))
        (saturationStalk (π := ⇑(S.map i)) (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
          (S.strictTransformSubspaceSeq J i.castSucc)))
    (hc1 : ∀ x ∈ (S.markedTransformSeq J 1 (Fin.last _)).support,
      (S.totalTransformSeq (Fin.last _)).IsSmoothTransversalIdealAt ψ
        (S.markedTransformSeq J 1 (Fin.last _)) x) :
    (S.markedTransformSeq J 1 (Fin.last _)).support =
      (S.strictTransformSubspaceSeq J (Fin.last _)).support := by
  refine Set.Subset.antisymm ?_ (cosupport_strictTransformSubspaceSeq_subset S J E₀ hge _)
  intro x hx
  have hcl : ∀ (i : Fin (S.length + 1)) (j), IsClosed ((S.totalTransformSeq i).hyp j) :=
    fun i j => ((hsnc i).1 j).isClosed
  have hdense := mem_closure_cosupport_diff_support_of_isSmoothTransversalIdealAt ψ
    (S.totalTransformSeq (Fin.last _)) (hsnc _) (S.markedTransformSeq J 1 (Fin.last _)) hx
    (hc1 x hx)
  refine closure_minimal ?_ (IdealSheaf.isClosed_support _) hdense
  rintro y ⟨hyJ, hyE⟩
  rw [IdealSheaf.mem_support] at hyJ ⊢
  rwa [← stalkIdeal_markedTransformSeq_eq_strictTransformSubspaceSeq_of_notMem_support S J E₀ hge
    hcl hsat (Fin.last _) y hyE]

end Assembly

end Hironaka.Manifold
