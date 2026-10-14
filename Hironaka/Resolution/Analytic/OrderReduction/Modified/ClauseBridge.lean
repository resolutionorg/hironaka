/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseTools
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepCExit
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StopPersistence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.Module.PerfectSpace


/-!
# The two stop clauses across a change of boundary family

The output clause and the stopped clause of `ClauseTools.lean` (the fields
`output_isSmoothSubmanifoldIdeal` and `stopped_never_blownUp` of `BMOmodFam`) are stated against
the total boundary of the run; the pieces of the modified first step satisfy them against other
boundary families. The boundary of the triple of [Kol07, Theorem 103, Step 2.2] (the exceptional
divisors of Step 2.1 with the maximal-contact member `H_r` emptied) is a sub-family of the total
boundary at that stage, the members present before Step 2.1 being dropped; and the boundary of the
run one dimension down is identified with the trace of the ambient boundary on the strict transforms
of `H⁺` at the level of supports only (`support_traceFamilyFrom_eq_support_boundarySeq`,
`boundarySeq_pushforwardStageIso`, `isSnc_totalTransformSeqFrom_and_boundarySeq_eq`). This module
proves the generic bridges, for arbitrary boundary families:

* `HypersurfaceFamily.MembersSubset F' F`: every nonempty member of `F'` is a member of `F`. The
  relation is kept by inverse images, by the total transform under a blow-up (equal members have
  equal strict transforms, the exceptional member is shared) and hence along the boundary families
  of a succession (`membersSubset_totalTransformSeqFrom`); the exceptional divisors alone form a
  sub-family of every boundary family (`membersSubset_totalTransformSeq_totalTransformSeqFrom`).
* `IsSmoothTransversalIdealAt.of_membersSubset`: the predicate passes to a sub-family
  (`IsSmoothTransversalIdealAt.emptyMember` is the one-member case);
  `IsSmoothTransversalIdealAt.of_forall_mem`: and back when every member of the bigger family
  through the point is a member of the smaller one (the situation of the output clause, where the
  extra members miss the support of the transform).
* `IsSnc.exists_hyp_inter_eq_of_support_eq`, `IsSnc.exists_equiv_of_support_eq_nhds`,
  `IsSmoothTransversalIdealAt.of_support_eq_nhds`: two families with simple normal crossings and
  the same support near a point have the same members through it near it, so the predicate depends
  only on the support of the boundary near the point. On the open the member is a closed
  hypersurface having simple normal crossings with one family, hence, by the dictionary
  `hasOnlyNormalCrossingsWith_idealSheaf_iff` on the reduced ideal sheaves, which agree on the
  open, with the other; in a chart with simple normal crossings it is a coordinate hyperplane inside
  the finite union of the coordinate hyperplanes of the members through the point, hence one of
  them (`exists_mem_source_coord_eq_zero_ne`: a coordinate hyperplane is not contained in a finite
  union of other coordinate hyperplanes near a point; `IsSncChartAt.eq_of_hyp_inter_eq`,
  `IsSnc.hyp_injOn_nonempty`); then `IsSmoothTransversalIdealAt.congr_nhds`.
* `StoppedClause.of_membersSubset`, `OutputClause.of_forall_mem`: the same bridges for the two
  clauses.
* `notMem_center_of_ord_eq_zero`: a point of order `0` is never blown up. A centre point has order
  `≥ 1` ([Kol07, Definition 66 (4′)]), and the marked transform at a point over a point off the
  centre is the pull-back of the stalk below (`birationalTransform_stalkIdeal_of_notMem`); an
  induction on the first stage at which the fibre would meet a centre, from the order clause alone;
  the stop predicate does not enter.

The relation between the boundary of the run on a hypersurface and the trace of the ambient
boundary is the `E_i ∩ S_i` of [Kol07, Definition 30, 30.2]; the order of a centre is
[Kol07, Definition 66 (4′)]; simple normal crossings are [Kol07, Definition 24] and
[Wlo09, Theorem 2.0.3 (2)]. The statements themselves are not in the sources.
-/

@[expose] public section


noncomputable section

open Set Topology TopologicalSpace Hironaka.Manifold Manifold
open scoped Manifold ContDiff

universe u

namespace Manifold

namespace HypersurfaceFamily

variable {M : Type u}

/-- **The sub-family relation**: every nonempty member of `F'` is a member of `F` (as a set). This
is the relation between the boundary of the triple of [Kol07, Theorem 103, Step 2.2] (the
exceptional divisors of Step 2.1, `H_r` emptied) and the total boundary at that stage: the members
present before Step 2.1 are dropped, and `H_r` is a member of neither. -/
def MembersSubset (F' F : HypersurfaceFamily M) : Prop :=
  ∀ j', F'.hyp j' = ∅ ∨ ∃ j, F'.hyp j' = F.hyp j

/-- The support of a sub-family lies in the support. -/
theorem MembersSubset.support_subset {F' F : HypersurfaceFamily M} (h : F'.MembersSubset F) :
    F'.support ⊆ F.support := by
  intro x hx
  obtain ⟨j', hj'⟩ := Set.mem_iUnion.mp hx
  rcases h j' with h0 | ⟨j, hj⟩
  · rw [h0] at hj'
    exact absurd hj' (Set.notMem_empty x)
  · exact Set.mem_iUnion.mpr ⟨j, hj ▸ hj'⟩

/-- The empty family is a sub-family of every family. -/
theorem membersSubset_empty (F : HypersurfaceFamily M) :
    (HypersurfaceFamily.empty M).MembersSubset F := by
  intro j'
  exact j'.elim

/-- A family with one member emptied is a sub-family of the family. -/
theorem membersSubset_emptyMember (F : HypersurfaceFamily M) (j : F.ι) :
    (F.emptyMember j).MembersSubset F := by
  intro k
  by_cases hk : k = j
  · left
    simp only [HypersurfaceFamily.emptyMember]
    exact ite_eq_left hk
  · right
    refine ⟨k, ?_⟩
    simp only [HypersurfaceFamily.emptyMember]
    exact ite_eq_right hk

/-- The sub-family relation is kept by inverse images. -/
theorem MembersSubset.comap {N : Type u} {F' F : HypersurfaceFamily M} (h : F'.MembersSubset F)
    (g : N → M) : (F'.comap g).MembersSubset (F.comap g) := by
  intro j'
  rcases h j' with h0 | ⟨j, hj⟩
  · left
    change g ⁻¹' F'.hyp j' = ∅
    rw [h0, Set.preimage_empty]
  · right
    refine ⟨j, ?_⟩
    change g ⁻¹' F'.hyp j' = g ⁻¹' F.hyp j
    rw [hj]

/-- The sub-family relation is kept by the total transform under a blow-up: equal members have equal
strict transforms, the empty member an empty one, and the exceptional member is shared. -/
theorem MembersSubset.totalTransform {M' : Type u} [TopologicalSpace M']
    {F' F : HypersurfaceFamily M} (h : F'.MembersSubset F) (π : M' → M) (Y : Set M) :
    (F'.totalTransform π Y).MembersSubset (F.totalTransform π Y) := by
  intro k
  obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
  rcases k' with j' | u
  · rcases h j' with h0 | ⟨j, hj⟩
    · left
      change strictTransformSet π Y (F'.hyp j') = ∅
      rw [h0]
      unfold strictTransformSet
      rw [Set.empty_sdiff, Set.preimage_empty, closure_empty]
    · right
      refine ⟨toLex (Sum.inl j), ?_⟩
      change strictTransformSet π Y (F'.hyp j') = strictTransformSet π Y (F.hyp j)
      rw [hj]
  · right
    exact ⟨toLex (Sum.inr u), rfl⟩

end HypersurfaceFamily

end Manifold

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E}

/-- The sub-family relation is kept by the boundary families of a succession at every stage
(`MembersSubset.totalTransform` along the recursion of `totalTransformSeqFromAux`). -/
theorem membersSubset_totalTransformSeqFrom (S : FiniteSuccession M)
    {F' F : HypersurfaceFamily M} (h : F'.MembersSubset F) (i : Fin (S.length + 1)) :
    (S.totalTransformSeqFrom F' i).MembersSubset (S.totalTransformSeqFrom F i) := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact h
  | succ i ih => exact (ih (Nat.lt_of_succ_lt hi)).totalTransform _ _

/-- The exceptional divisors alone (the boundary family from the empty start) form a sub-family of
the boundary family from any start `F`. -/
theorem membersSubset_totalTransformSeq_totalTransformSeqFrom (S : FiniteSuccession M)
    (F : HypersurfaceFamily M) (i : Fin (S.length + 1)) :
    (S.totalTransformSeq i).MembersSubset (S.totalTransformSeqFrom F i) := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact HypersurfaceFamily.membersSubset_empty F
  | succ i ih => exact (ih (Nat.lt_of_succ_lt hi)).totalTransform _ _

end AnalyticManifold.FiniteSuccession

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **A coordinate hyperplane of a chart is not contained in a finite union of other coordinate
hyperplanes near a point**: in a chart `φ` at `a`, for finitely many indices `K` and an index
`k ∉ K` whose coordinates all vanish at `a`, every neighbourhood of `a` contains a point of the
source where the `k`-th coordinate vanishes and none of the `K`-coordinates does (the point
`ψ⁻¹(ψ (φ a) + ε · 1_K)` for a small `ε ≠ 0`). -/
theorem _root_.Hironaka.Manifold.exists_mem_source_coord_eq_zero_ne {M : Type u}
    [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source) (K : Finset (Fin n)) {k : Fin n}
    (hk : k ∉ K) (h0 : ψ (φ a) k = 0) (hK : ∀ c ∈ K, ψ (φ a) c = 0) {W : Set M} (hW : W ∈ 𝓝 a) :
    ∃ y ∈ φ.source ∩ W, ψ (φ y) k = 0 ∧ ∀ c ∈ K, ψ (φ y) c ≠ 0 := by
  classical
  set d : Fin n → 𝕜 := fun c => if c ∈ K then 1 else 0 with hd
  set v : 𝕜 → E := fun ε => ψ.symm (ψ (φ a) + ε • d) with hv
  have hv0 : v 0 = φ a := by
    simp only [hv, zero_smul, add_zero, ContinuousLinearEquiv.symm_apply_apply]
  have hvc : Continuous v :=
    ψ.symm.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨W', hW'W, hW'o, haW'⟩ := mem_nhds_iff.mp hW
  have hopen : IsOpen (φ.target ∩ φ.symm ⁻¹' W') := φ.isOpen_inter_preimage_symm hW'o
  have hmem : φ a ∈ φ.target ∩ φ.symm ⁻¹' W' :=
    ⟨φ.map_source ha, by rw [Set.mem_preimage, φ.left_inv ha]; exact haW'⟩
  have hev : ∀ᶠ ε in 𝓝 (0 : 𝕜), v ε ∈ φ.target ∩ φ.symm ⁻¹' W' := by
    have := hvc.continuousAt (x := (0 : 𝕜))
    rw [ContinuousAt, hv0] at this
    exact this.eventually_mem (hopen.mem_nhds hmem)
  obtain ⟨ε, hε, hε0⟩ := ((eventually_nhdsWithin_of_eventually_nhds hev).and
    (self_mem_nhdsWithin (s := ({(0 : 𝕜)}ᶜ : Set 𝕜)))).exists
  have hε0' : ε ≠ 0 := hε0
  have hεt : v ε ∈ φ.target := hε.1
  have hcoord : ψ (φ (φ.symm (v ε))) = ψ (φ a) + ε • d := by
    rw [φ.right_inv hεt]
    exact ψ.apply_symm_apply _
  refine ⟨φ.symm (v ε), ⟨φ.map_target hεt, hW'W hε.2⟩, ?_, ?_⟩
  · rw [hcoord, Pi.add_apply, Pi.smul_apply, hd]
    simp only [ite_eq_right hk, smul_zero, add_zero]
    exact h0
  · intro c hcK
    rw [hcoord, Pi.add_apply, Pi.smul_apply, hd]
    simp only [ite_eq_left hcK, smul_eq_mul, mul_one, hK c hcK, zero_add]
    exact hε0'

/-- Two members through `x` of a family with simple normal crossings that agree near `x` are the
same member: in the chart at `x` they are coordinate hyperplanes with the same trace near `x`, so
their indices agree (`exists_mem_source_coord_eq_zero_ne`), and `cidx` is injective. -/
theorem HypersurfaceFamily.IsSncChartAt.eq_of_hyp_inter_eq {F : HypersurfaceFamily M}
    {φ : OpenPartialHomeomorph M E} {x : M} {c : {j // x ∈ F.hyp j} → Fin n}
    (hc : F.IsSncChartAt ψ φ x c) {W : Set M} (hW : W ∈ 𝓝 x) {j₁ j₂ : {j // x ∈ F.hyp j}}
    (h : F.hyp j₁.1 ∩ W = F.hyp j₂.1 ∩ W) : j₁ = j₂ := by
  classical
  by_contra hne
  have hcne : c j₁ ≠ c j₂ := fun h' => hne (hc.injective h')
  have hxs := hc.mem_source
  have h1 : ψ (φ x) (c j₁) = 0 := (hc.mem_iff j₁ hxs).mp j₁.2
  have h2 : ∀ k ∈ ({c j₂} : Finset (Fin n)), ψ (φ x) k = 0 := by
    intro k hk
    rw [Finset.mem_singleton.mp hk]
    exact (hc.mem_iff j₂ hxs).mp j₂.2
  obtain ⟨y, ⟨hys, hyW⟩, hy1, hy2⟩ := exists_mem_source_coord_eq_zero_ne φ hxs {c j₂}
    (by simpa using hcne) h1 h2 hW
  have hy1' : y ∈ F.hyp j₁.1 := (hc.mem_iff j₁ hys).mpr hy1
  have hy2' : y ∉ F.hyp j₂.1 := fun hmem =>
    hy2 (c j₂) (Finset.mem_singleton_self _) ((hc.mem_iff j₂ hys).mp hmem)
  exact hy2' ((Set.ext_iff.mp h y).mp ⟨hy1', hyW⟩).1

/-- A family with simple normal crossings has no two indices with the same nonempty member
(`IsSncChartAt.eq_of_hyp_inter_eq` at a point of the member, with `W = univ`). -/
theorem HypersurfaceFamily.IsSnc.hyp_injOn_nonempty {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    {j₁ j₂ : F.ι} (h : F.hyp j₁ = F.hyp j₂) (hne : (F.hyp j₁).Nonempty) : j₁ = j₂ := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨φ, c, hc⟩ := hF.exists_isSncChartAt x
  have hx₂ : x ∈ F.hyp j₂ := h ▸ hx
  have := hc.eq_of_hyp_inter_eq (W := Set.univ) Filter.univ_mem (j₁ := ⟨j₁, hx⟩)
    (j₂ := ⟨j₂, hx₂⟩) (by rw [Set.inter_univ, Set.inter_univ]; exact h)
  exact congrArg Subtype.val this

/-- **The predicate passes to a sub-family** (the bigger boundary implies the smaller;
`IsSmoothTransversalIdealAt.emptyMember` is the one-member case): the members of `F'` through `x`
inject into those of `F` through `x` with the same sets, and the chart, the coordinates `σ` and the
ideal are unchanged. -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.of_membersSubset
    {F' F : HypersurfaceFamily M} (hF' : F'.IsSnc ψ) (hsub : F'.MembersSubset F)
    {J : AnalyticManifold.IdealSheaf M} {x : M} (h : F.IsSmoothTransversalIdealAt ψ J x) :
    F'.IsSmoothTransversalIdealAt ψ J x := by
  obtain ⟨c, φ, σ, cidx, hφ, hJ, hne⟩ := h
  have hex : ∀ j' : {j' // x ∈ F'.hyp j'}, ∃ j, F'.hyp j'.1 = F.hyp j := fun j' =>
    (hsub j'.1).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨x, j'.2⟩)
  let e : {j' // x ∈ F'.hyp j'} → {j // x ∈ F.hyp j} := fun j' =>
    ⟨Classical.choose (hex j'), by rw [← Classical.choose_spec (hex j')]; exact j'.2⟩
  have he : ∀ j', F'.hyp j'.1 = F.hyp (e j').1 := fun j' => Classical.choose_spec (hex j')
  have hinj : Function.Injective e := by
    intro j₁ j₂ h12
    apply Subtype.ext
    refine hF'.hyp_injOn_nonempty ?_ ⟨x, j₁.2⟩
    rw [he j₁, he j₂, h12]
  refine ⟨c, φ, σ, cidx ∘ e, ⟨hφ.1, hφ.2.1, fun j' y hy => ?_, hφ.2.2.2.comp hinj⟩, hJ,
    fun j' i => hne (e j') i⟩
  rw [he j']
  exact hφ.2.2.1 (e j') y hy

/-- **The predicate passes back from a sub-family** when every member of the bigger family through
the point is one of the sub-family (`IsSmoothTransversalIdealAt.congr_nhds` with an equivalence of
the members through `x`). This is the situation of the output clause, where the extra members miss
the support of the transform. -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.of_forall_mem
    {F' F : HypersurfaceFamily M} (hF : F.IsSnc ψ) {x : M}
    (hall : ∀ j, x ∈ F.hyp j → ∃ j', F'.hyp j' = F.hyp j) {J : AnalyticManifold.IdealSheaf M}
    (h : F'.IsSmoothTransversalIdealAt ψ J x) : F.IsSmoothTransversalIdealAt ψ J x := by
  obtain ⟨c, φ, σ, cidx, hφ, hJ, hne⟩ := h
  let e : {j // x ∈ F.hyp j} → {j' // x ∈ F'.hyp j'} := fun j =>
    ⟨Classical.choose (hall j.1 j.2), by rw [Classical.choose_spec (hall j.1 j.2)]; exact j.2⟩
  have he : ∀ j, F'.hyp (e j).1 = F.hyp j.1 := fun j => Classical.choose_spec (hall j.1 j.2)
  have hinj : Function.Injective e := by
    intro j₁ j₂ h12
    apply Subtype.ext
    refine hF.hyp_injOn_nonempty ?_ ⟨x, j₁.2⟩
    rw [← he j₁, ← he j₂, h12]
  refine ⟨c, φ, σ, cidx ∘ e, ⟨hφ.1, hφ.2.1, fun j y hy => ?_, hφ.2.2.2.comp hinj⟩, hJ,
    fun j i => hne (e j) i⟩
  rw [← he j]
  exact hφ.2.2.1 (e j) y hy

/-- **A member of `F₂` through `x` is, near `x`, a member of `F₁`**, for families with simple normal
crossings and the same support on an open `U ∋ x` (the `E_i ∩ S_i` of [Kol07, Definition 30, 30.2]
read member by member). On `U` the member is a closed hypersurface having simple normal crossings
with `F₂|U`, hence, by the dictionary `hasOnlyNormalCrossingsWith_idealSheaf_iff` on the reduced
ideal sheaves, which agree on `U` (`idealSheaf_congr_support`), with `F₁|U`; in the chart of `F₁`
at `x` it is a coordinate hyperplane inside the finite union of the coordinate hyperplanes of the
members of `F₁` through `x` (the other members miss a neighbourhood,
`LocallyFinite.iInter_compl_mem_nhds`), so by `exists_mem_source_coord_eq_zero_ne` it is one of
them. -/
theorem HypersurfaceFamily.IsSnc.exists_hyp_inter_eq_of_support_eq {F₁ F₂ : HypersurfaceFamily M}
    (hF₁ : F₁.IsSnc ψ) (hF₂ : F₂.IsSnc ψ) {U : Set M} (hU : IsOpen U) {x : M} (hxU : x ∈ U)
    (hsupp : F₁.support ∩ U = F₂.support ∩ U) (j₂ : {j // x ∈ F₂.hyp j}) :
    ∃ (j₁ : {j // x ∈ F₁.hyp j}) (V : Set M), IsOpen V ∧ x ∈ V ∧
      F₁.hyp j₁.1 ∩ V = F₂.hyp j₂.1 ∩ V := by
  classical
  set Uo : Opens M := ⟨U, hU⟩ with hUo
  set ι : AnalyticMap (M.restrict Uo) M := M.inclusion Uo with hιdef
  have hιd : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ι := isLocalDiffeomorph_inclusion M Uo
  have hιU : ∀ y : M.restrict Uo, ι y ∈ U := fun y => y.2
  have hF₁' : (F₁.comap ι).IsSnc ψ := HypersurfaceFamily.isSnc_comap hF₁ ι hιd
  have hF₂' : (F₂.comap ι).IsSnc ψ := HypersurfaceFamily.isSnc_comap hF₂ ι hιd
  set H' : Set (M.restrict Uo) := ⇑ι ⁻¹' F₂.hyp j₂.1 with hH'
  have hH'c : IsClosedSubmanifold ψ H' 1 :=
    (hF₂.isClosedSubmanifold j₂.1).preimage_of_isLocalDiffeomorph hιd
  -- the member has simple normal crossings with `F₂|U`
  have hsnc₂ : (F₂.comap ι).HasSncWith ψ H' 1 := by
    intro a ha
    obtain ⟨φ, cidx, hφ⟩ := hF₂'.exists_isSncChartAt a
    exact ⟨φ, singleEmb (cidx ⟨j₂.1, ha⟩), cidx,
      isAdaptedChart_singleIdx hφ.mem_maximalAtlas fun y hy => hφ.mem_iff ⟨j₂.1, ha⟩ hy, hφ⟩
  -- the two families have the same reduced ideal sheaf on `U`: hence with `F₁|U`
  have hsupp' : (F₂.comap ι).support = (F₁.comap ι).support := by
    rw [HypersurfaceFamily.support_comap, HypersurfaceFamily.support_comap]
    ext y
    simp only [Set.mem_preimage]
    exact ⟨fun h2 => ((Set.ext_iff.mp hsupp (ι y)).mpr ⟨h2, hιU y⟩).1,
      fun h1 => ((Set.ext_iff.mp hsupp (ι y)).mp ⟨h1, hιU y⟩).1⟩
  have hnc := (hasOnlyNormalCrossingsWith_idealSheaf_iff hF₂' hH'c).mpr hsnc₂
  rw [HypersurfaceFamily.idealSheaf_congr_support hsupp'] at hnc
  have hsnc₁ := (hasOnlyNormalCrossingsWith_idealSheaf_iff hF₁' hH'c).mp hnc
  -- the snc chart of `F₁|U` at `x` adapted to the member
  set x' : M.restrict Uo := ⟨x, hxU⟩ with hx'
  have hx'H : x' ∈ H' := j₂.2
  obtain ⟨φ, σ, cidx, hφ, hc⟩ := hsnc₁.exists_chart hx'H
  have hxs : x' ∈ φ.source := hc.mem_source
  -- finitely many members of `F₁|U` through `x'`; the other members miss a neighbourhood
  have : Finite {j // x' ∈ (F₁.comap ι).hyp j} :=
    (hF₁'.locallyFinite.point_finite x').to_subtype
  have := Fintype.ofFinite {j // x' ∈ (F₁.comap ι).hyp j}
  set K : Finset (Fin n) := Finset.univ.image cidx with hK
  have hW := hF₁'.locallyFinite.iInter_compl_mem_nhds
    (fun j => (hF₁'.isClosedSubmanifold j).isClosed) x'
  -- the coordinate of the member is the coordinate of a member of `F₁|U` through `x'`
  have hσK : σ 0 ∈ K := by
    by_contra hk
    have h0 : ψ (φ x') (σ 0) = 0 := (hφ.2 x' hxs).mp hx'H 0
    have hKz : ∀ k ∈ K, ψ (φ x') k = 0 := by
      intro k hkK
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hkK
      exact (hc.mem_iff j hxs).mp j.2
    obtain ⟨y, ⟨hys, hyW⟩, hy0, hyK⟩ := exists_mem_source_coord_eq_zero_ne φ hxs K hk h0 hKz hW
    have hyH : y ∈ H' := (hφ.2 y hys).mpr fun i => by rw [Subsingleton.elim i 0]; exact hy0
    have hy₁ : y ∈ (F₁.comap ι).support := by
      rw [← hsupp']
      exact Set.mem_iUnion.mpr ⟨j₂.1, hyH⟩
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy₁
    by_cases hxj : x' ∈ (F₁.comap ι).hyp j
    · exact hyK (cidx ⟨j, hxj⟩) (Finset.mem_image.mpr ⟨⟨j, hxj⟩, Finset.mem_univ _, rfl⟩)
        ((hc.mem_iff ⟨j, hxj⟩ hys).mp hyj)
    · exact (Set.mem_iInter₂.mp hyW j hxj) hyj
  obtain ⟨j₁, -, hj₁⟩ := Finset.mem_image.mp hσK
  -- back to `M`: on the image of the chart source the two members agree
  refine ⟨⟨j₁.1, j₁.2⟩, ⇑ι '' φ.source, hιd.isOpenMap _ φ.open_source, ⟨x', hxs, rfl⟩, ?_⟩
  ext z
  constructor
  · rintro ⟨hz1, y, hys, rfl⟩
    refine ⟨?_, y, hys, rfl⟩
    have hy1 : y ∈ (F₁.comap ι).hyp j₁.1 := hz1
    have h1 := (hc.mem_iff j₁ hys).mp hy1
    rw [hj₁] at h1
    exact (hφ.2 y hys).mpr fun i => by rw [Subsingleton.elim i 0]; exact h1
  · rintro ⟨hz2, y, hys, rfl⟩
    refine ⟨?_, y, hys, rfl⟩
    have hyH : y ∈ H' := hz2
    have h1 : ψ (φ y) (cidx j₁) = 0 := by
      rw [hj₁]
      exact (hφ.2 y hys).mp hyH 0
    exact (hc.mem_iff j₁ hys).mpr h1

/-- **Two families with simple normal crossings and the same support near `x` have the same members
through `x` near `x`**: `IsSnc.exists_hyp_inter_eq_of_support_eq` in both directions, the two maps
inverse to each other by `IsSncChartAt.eq_of_hyp_inter_eq`, on the finite intersection of the
neighbourhoods (finitely many members through `x`, `LocallyFinite.point_finite`). -/
theorem HypersurfaceFamily.IsSnc.exists_equiv_of_support_eq_nhds {F₁ F₂ : HypersurfaceFamily M}
    (hF₁ : F₁.IsSnc ψ) (hF₂ : F₂.IsSnc ψ) {U : Set M} (hU : IsOpen U) {x : M} (hxU : x ∈ U)
    (hsupp : F₁.support ∩ U = F₂.support ∩ U) :
    ∃ (e : {j // x ∈ F₁.hyp j} ≃ {j // x ∈ F₂.hyp j}) (V : Set M), IsOpen V ∧ x ∈ V ∧
      ∀ j, F₂.hyp (e j).1 ∩ V = F₁.hyp j.1 ∩ V := by
  classical
  have : Finite {j // x ∈ F₁.hyp j} := (hF₁.locallyFinite.point_finite x).to_subtype
  have hsupp' : F₂.support ∩ U = F₁.support ∩ U := hsupp.symm
  choose f Vf hVf hxVf hf using
    fun j₂ : {j // x ∈ F₂.hyp j} => hF₁.exists_hyp_inter_eq_of_support_eq hF₂ hU hxU hsupp j₂
  choose g Vg hVg hxVg hg using
    fun j₁ : {j // x ∈ F₁.hyp j} => hF₂.exists_hyp_inter_eq_of_support_eq hF₁ hU hxU hsupp' j₁
  obtain ⟨φ₁, c₁, hc₁⟩ := hF₁.exists_isSncChartAt x
  obtain ⟨φ₂, c₂, hc₂⟩ := hF₂.exists_isSncChartAt x
  have hfg : ∀ j₁, f (g j₁) = j₁ := by
    intro j₁
    refine hc₁.eq_of_hyp_inter_eq (W := Vf (g j₁) ∩ Vg j₁)
      (Filter.inter_mem ((hVf _).mem_nhds (hxVf _)) ((hVg _).mem_nhds (hxVg _))) ?_
    ext z
    constructor
    · rintro ⟨hz, hz1, hz2⟩
      refine ⟨?_, hz1, hz2⟩
      have h1 := ((Set.ext_iff.mp (hf (g j₁)) z).mp ⟨hz, hz1⟩).1
      exact ((Set.ext_iff.mp (hg j₁) z).mp ⟨h1, hz2⟩).1
    · rintro ⟨hz, hz1, hz2⟩
      refine ⟨?_, hz1, hz2⟩
      have h1 := ((Set.ext_iff.mp (hg j₁) z).mpr ⟨hz, hz2⟩).1
      exact ((Set.ext_iff.mp (hf (g j₁)) z).mpr ⟨h1, hz1⟩).1
  have hgf : ∀ j₂, g (f j₂) = j₂ := by
    intro j₂
    refine hc₂.eq_of_hyp_inter_eq (W := Vg (f j₂) ∩ Vf j₂)
      (Filter.inter_mem ((hVg _).mem_nhds (hxVg _)) ((hVf _).mem_nhds (hxVf _))) ?_
    ext z
    constructor
    · rintro ⟨hz, hz1, hz2⟩
      refine ⟨?_, hz1, hz2⟩
      have h1 := ((Set.ext_iff.mp (hg (f j₂)) z).mp ⟨hz, hz1⟩).1
      exact ((Set.ext_iff.mp (hf j₂) z).mp ⟨h1, hz2⟩).1
    · rintro ⟨hz, hz1, hz2⟩
      refine ⟨?_, hz1, hz2⟩
      have h1 := ((Set.ext_iff.mp (hf j₂) z).mpr ⟨hz, hz2⟩).1
      exact ((Set.ext_iff.mp (hg (f j₂)) z).mpr ⟨h1, hz1⟩).1
  refine ⟨⟨g, f, hfg, hgf⟩, ⋂ j₁, Vg j₁, isOpen_iInter_of_finite hVg, Set.mem_iInter.mpr hxVg, ?_⟩
  intro j₁
  change F₂.hyp (g j₁).1 ∩ ⋂ j, Vg j = F₁.hyp j₁.1 ∩ ⋂ j, Vg j
  ext z
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨((Set.ext_iff.mp (hg j₁) z).mp ⟨hz, Set.mem_iInter.mp hzV j₁⟩).1, hzV⟩
  · rintro ⟨hz, hzV⟩
    exact ⟨((Set.ext_iff.mp (hg j₁) z).mpr ⟨hz, Set.mem_iInter.mp hzV j₁⟩).1, hzV⟩

/-- **The predicate depends only on the support of the boundary near the point**, for families with
simple normal crossings: `IsSnc.exists_equiv_of_support_eq_nhds` and
`IsSmoothTransversalIdealAt.congr_nhds`. This is the bridge between the boundary of the run one
dimension down and the trace of the ambient boundary along a push-forward, which the library
identifies at the level of supports and reduced ideal sheaves only
(`support_traceFamilyFrom_eq_support_boundarySeq`, `boundarySeq_pushforwardStageIso`,
`isSnc_totalTransformSeqFrom_and_boundarySeq_eq`). -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.of_support_eq_nhds
    {F₁ F₂ : HypersurfaceFamily M} (hF₁ : F₁.IsSnc ψ) (hF₂ : F₂.IsSnc ψ) {U : Set M}
    (hU : IsOpen U) {x : M} (hxU : x ∈ U) (hsupp : F₁.support ∩ U = F₂.support ∩ U)
    {J : AnalyticManifold.IdealSheaf M} (h : F₁.IsSmoothTransversalIdealAt ψ J x) :
    F₂.IsSmoothTransversalIdealAt ψ J x := by
  obtain ⟨e, V, hV, hxV, he⟩ := hF₁.exists_equiv_of_support_eq_nhds hF₂ hU hxU hsupp
  exact HypersurfaceFamily.IsSmoothTransversalIdealAt.congr_nhds ψ hV hxV e he (fun _ _ => rfl) h

end Manifold

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- **The stopped clause passes from a sub-family boundary to the bigger boundary**: a predicate
point off the bigger boundary is a predicate point off the smaller one
(`IsSmoothTransversalIdealAt.of_membersSubset` at its stage, `membersSubset_totalTransformSeqFrom`,
`MembersSubset.support_subset`). -/
theorem StoppedClause.of_membersSubset (S : FiniteSuccession M) {I : IdealSheaf M}
    {F' F : HypersurfaceFamily M} (hsnc : ∀ i, (S.totalTransformSeqFrom F' i).IsSnc ψ₀)
    (hsub : F'.MembersSubset F) (h : S.StoppedClause ψ₀ I F') : S.StoppedClause ψ₀ I F := by
  intro i k hk x hP hx y hy
  refine h i k hk x (hP.of_membersSubset (hsnc _) (S.membersSubset_totalTransformSeqFrom hsub _))
    ?_ y hy
  intro j' hj'
  have hmem : x ∈ (S.totalTransformSeqFrom F' _).support := Set.mem_iUnion.mpr ⟨j', hj'⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
    ((S.membersSubset_totalTransformSeqFrom hsub _).support_subset hmem)
  exact hx j hj

/-- **The output clause passes from a sub-family boundary to the bigger boundary** when every member
of the bigger boundary through a support point of the last stage is a member of the smaller one
(`IsSmoothTransversalIdealAt.of_forall_mem` at the last stage). -/
theorem OutputClause.of_forall_mem (S : FiniteSuccession M) {I : IdealSheaf M}
    {F' F : HypersurfaceFamily M} (hsnc : (S.totalTransformSeqFrom F (Fin.last _)).IsSnc ψ₀)
    (hall : ∀ x : S.stage (Fin.last _), (1 : ℕ∞) ≤ (S.markedTransformSeq I 1 (Fin.last _)).ord x →
      ∀ j, x ∈ (S.totalTransformSeqFrom F (Fin.last _)).hyp j →
        ∃ j', (S.totalTransformSeqFrom F' (Fin.last _)).hyp j' =
          (S.totalTransformSeqFrom F (Fin.last _)).hyp j)
    (h : S.OutputClause ψ₀ I F') : S.OutputClause ψ₀ I F := by
  intro x hord
  exact (h x hord).of_forall_mem hsnc (hall x hord)

/-- **A point of order `0` is never blown up**, along a succession of order `≥ 1`: a centre point
has order `≥ 1` along the centre, hence order `≥ 1` ([Kol07, Definition 66 (4′)]), so a point of
order `0` is not in the centre, and the marked transform at a point over it is the pull-back of the
stalk below (`birationalTransform_stalkIdeal_of_notMem`, the blow-up being a local isomorphism
there), of order `0` again. The proof is an induction on the number of steps; no predicate is
involved. -/
theorem notMem_center_of_ord_eq_zero (S : FiniteSuccession M) {I E₀ : IdealSheaf M}
    (hge : S.IsOfOrderGe I 1 E₀) (i k : ℕ) (h : i + k < S.length)
    {x : S.stage ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩}
    (hx : (S.markedTransformSeq I 1
      ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩).ord x = 0)
    (y : S.stage ⟨i + k, Nat.lt_succ_of_lt h⟩)
    (hy : S.stageMapAdd i k (Nat.lt_succ_of_lt h) y = x) :
    y ∉ (S.center ⟨i + k, h⟩).support := by
  -- the order stays `0` along the fibre over `x`
  have key : ∀ (k : ℕ) (h : i + k < S.length + 1) (y : S.stage ⟨i + k, h⟩),
      S.stageMapAdd i k h y = x → (S.markedTransformSeq I 1 ⟨i + k, h⟩).ord y = 0 := by
    intro k
    induction k with
    | zero =>
      intro h y hy
      have hyx : y = x := hy
      subst hyx
      exact hx
    | succ k ih =>
      intro h y hy
      have hk : i + k < S.length + 1 := Nat.lt_of_succ_lt h
      have hk' : i + k < S.length := Nat.lt_of_succ_lt_succ h
      have hzx : S.stageMapAdd i k hk (S.map ⟨i + k, hk'⟩ y) = x := hy
      have hz := ih hk _ hzx
      -- the image of `y` is not in the centre: a centre point has order `≥ 1`
      have hzc : S.map ⟨i + k, hk'⟩ y ∉ (S.center ⟨i + k, hk'⟩).support := by
        intro hmem
        have h1 := (hge ⟨i + k, hk'⟩).2 _ hmem
        have h2 := BMOmod.ordAlongIdeal_le_ord_of_mem_support (S.center ⟨i + k, hk'⟩)
          (S.markedTransformSeq I 1 ⟨i + k, hk⟩) hmem
        rw [hz] at h2
        exact absurd (h1.trans h2) (by simp)
      have hJ : ∀ a ∈ (S.center ⟨i + k, hk'⟩).support,
          ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
            (S.isClosedSubmanifold_center ⟨i + k, hk'⟩).idealSheaf
            (S.markedTransformSeq I 1 ⟨i + k, hk⟩) a := by
        intro a ha
        rw [S.idealSheaf_center]
        exact (hge ⟨i + k, hk'⟩).2 a ha
      have hstalk := birationalTransform_stalkIdeal_of_notMem
        (S.isClosedSubmanifold_center ⟨i + k, hk'⟩) (S.isBlowUp_map ⟨i + k, hk'⟩) hJ hzc
      have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (S.map ⟨i + k, hk'⟩) y :=
        (S.isBlowUp_map ⟨i + k, hk'⟩).isLocalDiffeomorphOn_compl ⟨y, hzc⟩
      have e : S.markedTransformSeq I 1 ⟨i + (k + 1), h⟩ =
          (MarkedIdealSheaf.birationalTransform (S.isClosedSubmanifold_center ⟨i + k, hk'⟩)
            (S.isBlowUp_map ⟨i + k, hk'⟩) ⟨S.markedTransformSeq I 1 ⟨i + k, hk⟩, 1⟩).I :=
        S.markedTransformSeq_succ I 1 ⟨i + k, hk'⟩
      rw [e, BMOmod.ord_congr_stalk hstalk]
      exact (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ hloc).trans hz
  intro hmem
  have h0 := key k (Nat.lt_succ_of_lt h) y hy
  have h1 := (hge ⟨i + k, h⟩).2 y hmem
  have h2 := BMOmod.ordAlongIdeal_le_ord_of_mem_support (S.center ⟨i + k, h⟩)
    (S.markedTransformSeq I 1 ⟨i + k, Nat.lt_succ_of_lt h⟩) hmem
  rw [h0] at h2
  exact absurd (h1.trans h2) (by simp)

end AnalyticManifold.FiniteSuccession

end
