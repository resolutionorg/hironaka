/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Independence
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.ReducedComponents
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Functorial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SmoothPointTransport
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# All components of a reduced equidimensional scheme are absorbed at the same index

Kollár defines `BR` on "(possibly reducible) affine schemes" as in the proof of [Kol07, Corollary
22]: embed `X ↪ A`, run `BP(A, I_X, ∅)` and truncate at the first centre containing the strict
transform of `X` [Kol07, Theorem 36, proof]. For a reducible `X` this presupposes that the
irreducible components are absorbed together: the first blow-up along a centre containing the
strict transform of one component deletes that component. This module proves it for a reduced `X`
whose smooth locus over `k` is smooth of ONE relative dimension (all components of one dimension),
whether or not the components meet:

* `componentIndex`, the absorbing index of a component `C` in the run `BP TA` of an admissible
  embedding: the first centre containing the strict transform of the reduced closed subscheme of
  `C`, pushed to the ambient (`firstCenterIndex`);
* `componentIndex_eq`: any two components have the same absorbing index;
* `firstCenterIndex_eq_componentIndex`: the first centre containing the strict transform of the
  whole of `X`, the truncation index of `BR_affine`, is the common absorbing index.

**The argument** is Kollár's localisation [Kol07, 4.2; Theorem 27, proof] applied to two
components. Suppose `j := j(C') < j(C)`. The absorbing centre `Z_j` of `C'` has a point over every
point of `C'` (`exists_mem_strictTransformSeq_support_stageMap_eq`: the strict transform of `C'` at
stage `j` lies in `Z_j` and maps onto `C'`, the stage map being proper and the image containing the
generic point), in particular over a closed smooth point `x₀` of `C'` (the generic point of `C'` is
a smooth point, and the closed points of the Jacobson `X` meet every nonempty locally closed set).
No restricted centre `Z_i ∩ X̄_i` with `i ≤ j < j(C)` has a point over the generic point of `C`
(`notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex`), so none has one over a closed
smooth point `x₀'` of `C` outside the closed set of points over which some restricted centre has a
point. But two closed smooth points see the same restricted centres
(`restrictedCenterHasPointOver_iff_of_mem_smoothLocus`: the two-point étale pair and the
functoriality of `BP` under smooth surjections, [Kol07, Theorem 35 (4)]): contradiction. Nothing
about how the components meet is used; the equidimensionality enters only through the étale pair,
and the codimension of `X` in `A` plays no role (the common value may be the length of the run).

**The identification.** For any blow-up sequence `S` on `A` and a reduced closed subscheme
`X = V(I) ↪ A`, the centre `Z_i` contains the strict transform of `X` iff it contains the strict
transforms of all components of `X` (`centerContains_iff_forall_component`): one direction is the
monotonicity of the strict transform, the other is that the support of the strict transform of a
finite union is the union of the strict transforms' supports and that the strict transform of the
reduced `X` is reduced (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools`). Hence, when
all components have the absorbing index `j`, so has `X` (`firstCenterIndex_eq_of_forall`). Without
the equality the first centre containing the strict transform of `X` would be the one at which the
LAST component is absorbed, and the components absorbed earlier would be blown up along themselves.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence TopologicalSpace
  Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Def

variable (k) (X : Scheme.{u}) [IsNoetherian X] (TA : Triple k) (emb : X ⟶ TA.X.left)

/-- The absorbing index of the irreducible component `C` of `X` in the run `BP TA` along the closed
embedding `emb`: the first centre containing the strict transform of `C` (`firstCenterIndex`), taken
for the reduced closed subscheme `X.irreducibleComponentIdeal C hC` of the component, pushed to the
ambient. -/
@[expose] noncomputable def componentIndex (C : Set X) (hC : C ∈ irreducibleComponents X) : ℕ :=
  firstCenterIndex (Hironaka.Sequence.BP TA) ((X.irreducibleComponentIdeal C hC).map emb)

/-- The defining equation of `componentIndex`. -/
theorem componentIndex_def (C : Set X) (hC : C ∈ irreducibleComponents X) :
    componentIndex k X TA emb C hC =
      firstCenterIndex (Hironaka.Sequence.BP TA) ((X.irreducibleComponentIdeal C hC).map emb) :=
  rfl

end Def

/-! ### The absorbing centre lies over the whole component -/

/-- Before or at the first containing centre, the strict transform of an integral `V(I)` maps onto
`V(I)`: its generic point lies over the generic point `η` of `V(I)`, and the image of the strict
transform under the proper stage map is closed, so it contains the closure of `η`. -/
theorem exists_mem_strictTransformSeq_support_stageMap_eq {A : Scheme.{u}} [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) [IsIntegral I.subscheme] {η : A}
    (hη : IsGenericPoint η (I.support : Set A)) (i : Fin (S.length + 1))
    (hi : i.val ≤ firstCenterIndex S I) {x : A} (hx : x ∈ I.support) :
    ∃ p ∈ (S.strictTransformSeq I i).support, S.stageMap i p = x := by
  obtain ⟨η', hgen, hmap, -⟩ :=
    exists_isGenericPoint_strictTransformSeq_of_le_firstCenterIndex S I hη i hi
  have := isProper_stageMap S i
  have hT : IsClosed (S.stageMap i '' ((S.strictTransformSeq I i).support : Set (S.stage i))) :=
    (S.stageMap i).isClosedMap _ (S.strictTransformSeq I i).support.isClosed
  have hsub : (I.support : Set A) ⊆
      S.stageMap i '' ((S.strictTransformSeq I i).support : Set (S.stage i)) := by
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr ⟨η', hgen.mem, hmap⟩) hT
  obtain ⟨p, hp, hpx⟩ := hsub hx
  exact ⟨p, hp, hpx⟩

/-! ### The theorem -/

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsNoetherian X] [IsReduced X]

/-- One inequality of `componentIndex_eq`, by contradiction: if `C'` is absorbed strictly before
`C`, at index `j`, then the restricted centre `Z_j ∩ X̄_j` has a point over a closed smooth point
of `C'` and none over a closed smooth point of `C` outside the closed set of points over which some
restricted centre of index `≤ j` has a point, while the two closed smooth points see the same
restricted centres. -/
theorem componentIndex_le {d : ℕ}
    [SmoothOfRelativeDimension d
      ((X ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (X ↘ Spec (CommRingCat.of k)))]
    (TA : Triple k) (emb : X ⟶ TA.X.left) (hadm : AdmissibleEmbedding k X TA emb)
    (C C' : Set X) (hC : C ∈ irreducibleComponents X) (hC' : C' ∈ irreducibleComponents X) :
    componentIndex k X TA emb C hC ≤ componentIndex k X TA emb C' hC' := by
  classical
  obtain ⟨hcl, hover, -, hE, hI⟩ := hadm
  have hAln : IsLocallyNoetherian TA.X.left :=
    (TA.X.left ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of k))
  set S := Hironaka.Sequence.BP TA with hS
  by_contra hlt
  rw [not_le] at hlt
  -- `j`, the absorbing index of `C'`, is an index of the run
  set j := componentIndex k X TA emb C' hC' with hjdef
  have hjeq : j = firstCenterIndex S ((X.irreducibleComponentIdeal C' hC').map emb) := rfl
  have hjC : j < firstCenterIndex S ((X.irreducibleComponentIdeal C hC).map emb) := hlt
  have hjlen : j < S.length := lt_of_lt_of_le hlt (firstCenterIndex_le_length _ _)
  -- the two components' data
  have hIC : IsIntegral ((X.irreducibleComponentIdeal C hC).map emb).subscheme :=
    isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced C hC emb
  have hIC' : IsIntegral ((X.irreducibleComponentIdeal C' hC').map emb).subscheme :=
    isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced C' hC' emb
  obtain ⟨ηC, hηC, hηCs⟩ := exists_isGenericPoint_mem_smoothLocus (k := k) C hC
  obtain ⟨ηC', hηC', hηC's⟩ := exists_isGenericPoint_mem_smoothLocus (k := k) C' hC'
  have hηCA := isGenericPoint_map_irreducibleComponentIdeal C hC emb hηC
  have hηC'A := isGenericPoint_map_irreducibleComponentIdeal C' hC' emb hηC'
  have hle' : TA.I ≤ (X.irreducibleComponentIdeal C' hC').map emb := by
    rw [← hI, Scheme.irreducibleComponentIdeal_def, Scheme.IdealSheafData.map_ker]
    exact Scheme.Hom.le_ker_comp _ _
  -- the truncation at `j + 1`
  have hlen : (S.take (j + 1)).length = j + 1 := length_take_of_le S hjlen
  have hjT : j < (S.take (j + 1)).length := by omega
  -- (a) a closed smooth point `x₀` of `C'`, over which the restricted centre `Z_j ∩ X̄_j` has a
  -- point
  obtain ⟨x₀, ⟨hx₀C, hx₀s⟩, hx₀c⟩ := nonempty_inter_closedPoints (X := X)
    (Z := C' ∩ ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)) ⟨ηC', hηC'.mem, hηC's⟩
    ((isClosed_of_mem_irreducibleComponents C' hC').isLocallyClosed.inter
      (X ↘ Spec (CommRingCat.of k)).smoothLocus.isOpen.isLocallyClosed)
  have hex' : ∃ n, CenterContains S ((X.irreducibleComponentIdeal C' hC').map emb) n := by
    by_contra hno
    have h0 : firstCenterIndex S ((X.irreducibleComponentIdeal C' hC').map emb) = S.length := by
      unfold firstCenterIndex
      rw [dite_eq_right hno]
    omega
  obtain ⟨hj', hleZ⟩ := firstCenterIndex_of_exists hex'
  have hx₀A : emb x₀ ∈ ((X.irreducibleComponentIdeal C' hC').map emb).support := by
    rw [← SetLike.mem_coe, ← hηC'A.def]
    exact specializes_iff_mem_closure.mp ((hηC'.specializes hx₀C).map emb.continuous)
  obtain ⟨p, hp, hpx⟩ := exists_mem_strictTransformSeq_support_stageMap_eq S _ hηC'A
    ⟨j, Nat.lt_succ_of_lt hjlen⟩ le_rfl hx₀A
  have hPj : RestrictedCenterHasPointOver S TA.I ⟨j, hjlen⟩ (emb x₀) :=
    ⟨p, Scheme.IdealSheafData.support_antitone hleZ hp,
      Scheme.IdealSheafData.support_antitone (strictTransformSeq_mono S hle' _) hp, hpx⟩
  have hPjT : RestrictedCenterHasPointOver (S.take (j + 1)) TA.I ⟨j, hjT⟩ (emb x₀) :=
    (restrictedCenterHasPointOver_take_mk S TA.I (j + 1) j hjT hjlen (emb x₀)).2 hPj
  -- (b) a closed smooth point `x₀'` of `C` over which no restricted centre of index `≤ j` has a
  -- point: the generic point of `C` is one, and the set of points over which some has is closed
  have hB : IsClosed
      {x : X | ∃ i, RestrictedCenterHasPointOver (S.take (j + 1)) TA.I i (emb x)} := by
    have := isClosed_setOf_restrictedCenterHasPointOver (S.take (j + 1)) emb
    rwa [hI] at this
  have hηCB : ηC ∉
      {x : X | ∃ i, RestrictedCenterHasPointOver (S.take (j + 1)) TA.I i (emb x)} := by
    rintro ⟨i, hi⟩
    have hi' : i.val < S.length := lt_of_lt_of_le i.2 (by rw [length_take]; exact min_le_right _ _)
    rw [restrictedCenterHasPointOver_take_mk S TA.I (j + 1) i.val i.2 hi'] at hi
    obtain ⟨q, hqZ, -, hq⟩ := hi
    have hilt : i.val < firstCenterIndex S ((X.irreducibleComponentIdeal C hC).map emb) := by
      have : i.val < j + 1 := lt_of_lt_of_eq i.2 hlen
      omega
    exact notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex S _ hηCA ⟨i.val, hi'⟩ hilt
      q hq hqZ
  obtain ⟨x₀', ⟨⟨hx₀'C, hx₀'s⟩, hx₀'B⟩, hx₀'c⟩ := nonempty_inter_closedPoints (X := X)
    (Z := (C ∩ ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)) ∩
      {x : X | ∃ i, RestrictedCenterHasPointOver (S.take (j + 1)) TA.I i (emb x)}ᶜ)
    ⟨ηC, ⟨hηC.mem, hηCs⟩, hηCB⟩
    (((isClosed_of_mem_irreducibleComponents C hC).isLocallyClosed.inter
      (X ↘ Spec (CommRingCat.of k)).smoothLocus.isOpen.isLocallyClosed).inter
      hB.isOpen_compl.isLocallyClosed)
  -- (c) the two closed smooth points see the same restricted centres
  have key := restrictedCenterHasPointOver_iff_of_mem_smoothLocus TA emb hE hI (d := d)
    (fun T => Hironaka.Sequence.BP T)
    (fun T' g _ hs hp => Hironaka.Sequence.BP_pullback_of_surjective TA T' g hs hp)
    (j + 1) hx₀s hx₀'s hx₀c hx₀'c ⟨j, hjT⟩
  exact hx₀'B ⟨⟨j, hjT⟩, key.1 hPjT⟩

/-- **All irreducible components of a reduced equidimensional scheme are absorbed at the same
index.** For a reduced `X` whose smooth locus over `k` is smooth of one relative dimension, embedded
by an admissible embedding `X ↪ A`, any two irreducible components `C, C'` of `X` have the same
absorbing index in the run `BP(A, I_X, ∅)`, whether or not they meet (`componentIndex_le` both
ways). -/
theorem componentIndex_eq {d : ℕ}
    [SmoothOfRelativeDimension d
      ((X ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (X ↘ Spec (CommRingCat.of k)))]
    (TA : Triple k) (emb : X ⟶ TA.X.left) (hadm : AdmissibleEmbedding k X TA emb)
    (C C' : Set X) (hC : C ∈ irreducibleComponents X) (hC' : C' ∈ irreducibleComponents X) :
    componentIndex k X TA emb C hC = componentIndex k X TA emb C' hC' :=
  le_antisymm (componentIndex_le X (d := d) TA emb hadm C C' hC hC')
    (componentIndex_le X (d := d) TA emb hadm C' C hC' hC)

/-! ### The identification of the first containing centre -/

section Identification

variable {A : Scheme.{u}} [IsLocallyNoetherian A] (S : BlowUpSequence A) (emb : X ⟶ A)
  [IsClosedImmersion emb]

omit [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [IsReduced X] [IsLocallyNoetherian A] in
/-- The support of the ideal of `X` in the ambient is the union of the supports of the pushed
reduced ideals of its components. -/
theorem coe_support_ker_eq_iUnion :
    (emb.ker.support : Set A) =
      ⋃ C ∈ (Set.univ : Set {C : Set X // C ∈ irreducibleComponents X}),
        (((X.irreducibleComponentIdeal C.1 C.2).map emb).support : Set A) := by
  rw [Scheme.Hom.support_ker, emb.isClosedEmbedding.isClosed_range.closure_eq]
  ext a
  simp only [Set.mem_range, Set.mem_iUnion, Set.mem_univ, exists_true_left]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨_root_.irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
      ?_⟩
    rw [Scheme.IdealSheafData.support_map, Closeds.coe_closure]
    exact subset_closure ⟨x, mem_irreducibleComponent, rfl⟩
  · rintro ⟨C, hC⟩
    rw [Scheme.IdealSheafData.support_map, Closeds.coe_closure,
      support_irreducibleComponentIdeal'] at hC
    rw [(emb.isClosedEmbedding.isClosedMap _
      (isClosed_of_mem_irreducibleComponents C.1 C.2)).closure_eq] at hC
    obtain ⟨x, -, rfl⟩ := hC
    exact ⟨x, rfl⟩

omit [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] in
/-- A centre contains the strict transform of the reduced `X` iff it contains the strict transforms
of all its components: monotonicity of the strict transform one way; the finite-union formula for
the support of the strict transform and the reducedness of the strict transform of `X` the other.
-/
theorem centerContains_iff_forall_component (n : ℕ) (hn : n < S.length) :
    CenterContains S emb.ker n ↔
      ∀ (C : Set X) (hC : C ∈ irreducibleComponents X),
        CenterContains S ((X.irreducibleComponentIdeal C hC).map emb) n := by
  constructor
  · rintro ⟨hn, hle⟩ C hC
    refine ⟨hn, le_trans hle (strictTransformSeq_mono S ?_ _)⟩
    rw [Scheme.irreducibleComponentIdeal_def, Scheme.IdealSheafData.map_ker]
    exact Scheme.Hom.le_ker_comp _ _
  · intro h
    refine ⟨hn, ?_⟩
    have : IsReduced emb.ker.subscheme := isReduced_image emb
    have hred : IsReduced (S.strictTransformSeq emb.ker ⟨n, Nat.lt_succ_of_lt hn⟩).subscheme :=
      isReduced_strictTransformSeq_subscheme S emb.ker _
    refine le_of_support_subset _ _ ?_
    have : Finite {C : Set X // C ∈ irreducibleComponents X} :=
      NoetherianSpace.finite_irreducibleComponents.to_subtype
    rw [coe_support_strictTransformSeq_biUnion S Set.univ Set.finite_univ
      (fun C : {C : Set X // C ∈ irreducibleComponents X} =>
        (X.irreducibleComponentIdeal C.1 C.2).map emb) emb.ker (coe_support_ker_eq_iUnion X emb)
      ⟨n, Nat.lt_succ_of_lt hn⟩]
    refine Set.iUnion₂_subset fun C _ => ?_
    exact Scheme.IdealSheafData.support_antitone (h C.1 C.2).2

omit [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] in
/-- If all components of the reduced `X` have the same first containing centre, it is the first
containing centre of `X`. -/
theorem firstCenterIndex_eq_of_forall (C : Set X) (hC : C ∈ irreducibleComponents X)
    (h : ∀ (C' : Set X) (hC' : C' ∈ irreducibleComponents X),
      firstCenterIndex S ((X.irreducibleComponentIdeal C' hC').map emb) =
        firstCenterIndex S ((X.irreducibleComponentIdeal C hC).map emb)) :
    firstCenterIndex S emb.ker =
      firstCenterIndex S ((X.irreducibleComponentIdeal C hC).map emb) := by
  classical
  set j := firstCenterIndex S ((X.irreducibleComponentIdeal C hC).map emb) with hjdef
  have hjle : j ≤ S.length := firstCenterIndex_le_length _ _
  -- no centre before `j` contains the strict transform of `X`
  have hbefore : ∀ m, m < j → ¬ CenterContains S emb.ker m := by
    intro m hm hcc
    have hm' : m < S.length := lt_of_lt_of_le hm hjle
    exact not_centerContains_of_lt_firstCenterIndex' S _ hm
      (((centerContains_iff_forall_component X S emb m hm').1 hcc) C hC)
  apply le_antisymm
  · -- `firstCenterIndex ≤ j`: at `j` every component is contained, if `j` is an index
    rcases lt_or_eq_of_le hjle with hjlt | hjeq
    · have hcc : CenterContains S emb.ker j := by
        refine (centerContains_iff_forall_component X S emb j hjlt).2 fun C' hC' => ?_
        have hex : ∃ n, CenterContains S ((X.irreducibleComponentIdeal C' hC').map emb) n := by
          by_contra hno
          have h0 : firstCenterIndex S ((X.irreducibleComponentIdeal C' hC').map emb) =
            S.length := by
            unfold firstCenterIndex
            rw [dite_eq_right hno]
          rw [h C' hC'] at h0
          omega
        have := firstCenterIndex_of_exists hex
        rwa [h C' hC'] at this
      unfold firstCenterIndex
      rw [dite_eq_left ⟨j, hcc⟩]
      exact Nat.find_min' _ hcc
    · rw [hjeq]
      exact firstCenterIndex_le_length _ _
  · -- `j ≤ firstCenterIndex`
    by_cases hex : ∃ n, CenterContains S emb.ker n
    · by_contra hlt
      rw [not_le] at hlt
      exact hbefore _ hlt (firstCenterIndex_of_exists hex)
    · unfold firstCenterIndex
      rw [dite_eq_right hex]
      exact hjle

end Identification

/-- **The truncation index of `BR_affine` is the common absorbing index**: on a reduced `X` whose
smooth locus is smooth of one relative dimension, with an admissible embedding, the first centre of
`BP TA` containing the strict transform of `X` is the absorbing index of any one component
(`componentIndex_eq`, `firstCenterIndex_eq_of_forall`). -/
theorem firstCenterIndex_eq_componentIndex {d : ℕ}
    [SmoothOfRelativeDimension d
      ((X ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (X ↘ Spec (CommRingCat.of k)))]
    (TA : Triple k) (emb : X ⟶ TA.X.left) (hadm : AdmissibleEmbedding k X TA emb)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    firstCenterIndex (Hironaka.Sequence.BP TA) TA.I = componentIndex k X TA emb C hC := by
  have hcl : IsClosedImmersion emb := hadm.1
  have hAln : IsLocallyNoetherian TA.X.left :=
    (TA.X.left ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  rw [← hadm.2.2.2.2]
  exact firstCenterIndex_eq_of_forall X (Hironaka.Sequence.BP TA) emb C hC
    fun C' hC' => componentIndex_eq X (d := d) TA emb hadm C' C hC' hC

end Hironaka.Resolution
