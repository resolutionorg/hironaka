/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.EqualAbsorbingIndex
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36IsoSnc
import Hironaka.Resolution.Algebraic.Kol07.IsoRestrict
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformUnion
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Centers
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Functorial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Absorption
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersMiss
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersOverSupport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.Kol07.Thm36.IsoOverSmoothLocus
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SmoothPointTransport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clauses (1)–(3) of Theorem 36 for the affine resolution of a reduced equidimensional scheme

For the resolution `BR_affine TA emb` of a reduced affine scheme `X ↪ A` whose smooth locus over `k`
is smooth of one relative dimension (`Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine`: the
restriction to `X` of the principalization sequence `BP(A, I_X, ∅)` truncated at the first centre
containing the strict transform of `X`), the three geometric clauses of [Kol07, Theorem 36] — the
step by which Kollár's `BR` is "defined on (possibly reducible) affine schemes" in the proof of the
theorem. The irreducible components of `X` may meet. Throughout, `X` is nonempty (`hne`) and of
codimension `≥ 2` in `A` at every generic point (`hcodim`, the choice of the embedding in the proof
of [Kol07, Theorem 36]); the empty `X` is treated by the assembly.

By `Hironaka.Resolution.Algebraic.Kol07.Thm36.EqualAbsorbingIndex`, the truncation index
`j = firstCenterIndex (BP TA) TA.I` is the absorbing index of every component `C` of `X`, and it is
an index of the run: some centre has a point over the generic point of `C`, since `Π^* I_X` is
invertible and `I_X` is the maximal ideal of the regular local ring of `A` at that point
(`componentIndex_lt_length`, the argument of the proof of [Kol07, Corollary 22]). At stage `j`:

* **clause (1)** (`smooth_composite_BR_affine_of_class`): the strict transform `C̄_j` of each
  component is integral and is an irreducible component of the smooth centre `Z_j`, open in `Z_j`,
  because its generic point is the unique point of the stage over the generic point of `C`, which
  is a maximal point of `X` (`isOpenImmersion_inclusion_component`); the strict transform `X̄_j` of
  `X` is reduced with support the union of the `C̄_j`, so its inclusion into the reduced `Z_j` is a
  closed immersion with open range, hence an open immersion
  (`isOpenImmersion_inclusion_firstCenterIndex`), and `X̄_j`, the end result, is smooth over `k`;
* **clause (2)** (`isIso_composite_restrict_smoothLocus_BR_affine_of_class`): no restricted centre
  `Z_i ∩ X̄_i`, `i < j`, has a point over a smooth point of `X`
  (`not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus_of_class`): none has over the generic
  point of a component (`i < j` is the absorbing index of that component), and two closed smooth
  points see the same restricted centres
  (`not_restrictedCenterHasPointOver_of_mem_smoothLocus_of_exists`);
* **clause (3)** (`exists_snc_preimage_singularLocus_BR_affine_of_class`): the restriction to `X̄_j`
  of the exceptional divisors of `A_j → A` is a simple normal crossing family with support
  `Π⁻¹(Sing X)` (`exists_isSnc_comap_totalTransformSeq_take_of_forall`, through every point of
  `X̄_j` the strict transform of the component through its image, which no earlier centre
  contains).

The clauses are assembled on the whole affine `X` and on the class in
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36Assembly`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence TopologicalSpace
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] (TA : Triple k) {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [IsNoetherian X] [IsReduced X] (emb : X ⟶ TA.X.left) (hadm : AdmissibleEmbedding k X TA emb)

/-! ### The generic points of the components in the ambient -/

omit [AlgebraicGeometry.IsNoetherian X] [IsReduced X] in
/-- The generic point of a component `C` of `X`, pushed along the closed immersion `emb`, is a
maximal point of `emb(X) = V(ker emb)` (`Closeds.genericPoints`): a point of `emb(X)` generalising
it is the image of a point of `X` generalising the generic point of `C`, which is that generic
point (a closed embedding reflects specialisation). -/
theorem mem_genericPoints_support_ker {A : Scheme.{u}} (f : X ⟶ A) [IsClosedImmersion f]
    {C : Set X} (hC : C ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η C) :
    f η ∈ f.ker.support.genericPoints := by
  have hsupp : (f.ker.support : Set A) = Set.range f := by
    rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq]
  refine ⟨?_, fun ξ hξ hsp => ?_⟩
  · rw [← SetLike.mem_coe, hsupp]
    exact ⟨η, rfl⟩
  · have hξ' : ξ ∈ Set.range f := by rwa [← hsupp]
    obtain ⟨x, rfl⟩ := hξ'
    have hx : x ⤳ η := f.isClosedEmbedding.isInducing.specializes_iff.mp hsp
    rw [eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents hC hη hx]

omit [CharZero k] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsReduced X] in
include hadm in
/-- The ideal of `X` lies in the pushed reduced ideal of each component. -/
theorem le_map_irreducibleComponentIdeal (C : Set X) (hC : C ∈ irreducibleComponents X) :
    TA.I ≤ (X.irreducibleComponentIdeal C hC).map emb := by
  rw [← hadm.2.2.2.2, Scheme.irreducibleComponentIdeal_def, Scheme.IdealSheafData.map_ker]
  exact Scheme.Hom.le_ker_comp _ _

/-! ### The absorbing index is an index of the run -/

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] in
include hadm in
/-- Some centre of `BP TA` contains the strict transform of each component [Kol07, Corollary 22,
proof]: `I_X` is the maximal ideal of the regular local ring of `A` at the generic point `η_C` of
the component, of dimension `≥ 2` (`hcodim`), so it is not principal there, while `Π^* I_X` is
invertible (clause (2) of [Kol07, Theorem 35]); hence some centre has a point over `η_C`
(`exists_mem_center_support_of_isInvertible_comap_composite`), and the least such centre contains
the strict transform of `C` (`exists_centerContains_of_exists_mem_center_support`). -/
theorem componentIndex_lt_length
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η)))
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    componentIndex k X TA emb C hC < (BP TA).length := by
  have hcl : IsClosedImmersion emb := hadm.1
  have hAln : IsLocallyNoetherian TA.X.left :=
    (TA.X.left ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  have hIC : IsIntegral ((X.irreducibleComponentIdeal C hC).map emb).subscheme :=
    isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced C hC emb
  have hη : IsGenericPoint hC.1.genericPoint C :=
    hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  have hηgen : hC.1.genericPoint ∈ genericPoints X := by
    change closure {hC.1.genericPoint} ∈ irreducibleComponents X
    rw [hη.def]
    exact hC
  have hηA : emb hC.1.genericPoint ∈ TA.I.support.genericPoints := by
    rw [← hadm.2.2.2.2]
    exact mem_genericPoints_support_ker emb hC hη
  obtain ⟨i, y, hy, hmem⟩ := exists_mem_center_support_of_isInvertible_comap_composite (BP TA)
    TA.I hηA (hcodim _ hηgen) (isInvertible_comap_composite_BP TA)
  have hex : ∃ n, CenterContains (BP TA) ((X.irreducibleComponentIdeal C hC).map emb) n :=
    exists_centerContains_of_exists_mem_center_support (BP TA) _
      (isGenericPoint_map_irreducibleComponentIdeal C hC emb hη) ⟨i, y, hy, hmem⟩
  rw [componentIndex_def]
  exact firstCenterIndex_lt_length hex

/-! ### Two general lemmas on inclusions of closed subschemes -/

/-- The identification of `Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification` with the
centre lying over a closed set `K` in which the generic point `η` of `V(I)` is maximal (instead of
over `V(I)` itself): at the first centre `Z_j` containing the strict transform of the integral
`V(I)`, if `Z_j` is regular, lies over `K`, and `η ∈ K.genericPoints`, then `X̄_j` is an irreducible
component of `Z_j`, open in it. For the components of a reduced `X`, `K = emb(X)`. -/
theorem isOpenImmersion_inclusion_of_mem_genericPoints {A : Scheme.{u}} [IsNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) [IsIntegral I.subscheme] (j : Fin S.length)
    (hj : j.val = firstCenterIndex S I) (hle : S.center j ≤ S.strictTransformSeq I j.castSucc)
    (hZ : IsRegular (S.center j).subscheme) {K : Closeds A}
    (hcos : ∀ y ∈ (S.center j).support, S.stageMap j.castSucc y ∈ K) {η : A}
    (hη : IsGenericPoint η (I.support : Set A)) (hηK : η ∈ K.genericPoints) :
    IsOpenImmersion (IdealSheafData.inclusion hle) := by
  have hLN : IsLocallyNoetherian A := inferInstance
  have hst : IsNoetherian (S.stage j.castSucc) := isNoetherian_stage S j.castSucc
  obtain ⟨η', hgen, hmap, huniq⟩ :=
    exists_isGenericPoint_strictTransformSeq_of_le_firstCenterIndex S I hη j.castSucc (le_of_eq hj)
  have hmax : η' ∈ (S.center j).support.genericPoints := by
    refine ⟨IdealSheafData.support_antitone hle hgen.mem, fun ξ hξ hspec => ?_⟩
    have h1 : S.stageMap j.castSucc ξ ⤳ S.stageMap j.castSucc η' :=
      hspec.map (S.stageMap j.castSucc).continuous
    rw [hmap] at h1
    exact huniq ξ (hηK.2 (hcos ξ hξ) h1)
  exact isOpenImmersion_inclusion_of_isGenericPoint (S.center j) _ hle hZ hgen hmax

/-- The range of the inclusion `V(T) ⟶ V(Z)` of closed subschemes (`Z ≤ T`) is the preimage of
`V(T)` under the inclusion of `V(Z)`. -/
theorem range_inclusion {A : Scheme.{u}} {Z T : A.IdealSheafData} (hle : Z ≤ T) :
    Set.range (IdealSheafData.inclusion hle) = Z.subschemeι ⁻¹' (T.support : Set A) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    change Z.subschemeι (IdealSheafData.inclusion hle t) ∈ (T.support : Set A)
    rw [← Scheme.Hom.comp_apply, IdealSheafData.inclusion_subschemeι, ← T.range_subschemeι]
    exact ⟨t, rfl⟩
  · intro hz
    have hz' : Z.subschemeι z ∈ Set.range T.subschemeι := by rwa [T.range_subschemeι]
    obtain ⟨t, ht⟩ := hz'
    refine ⟨t, (Scheme.Hom.isClosedEmbedding Z.subschemeι).injective ?_⟩
    rw [← Scheme.Hom.comp_apply, IdealSheafData.inclusion_subschemeι, ht]

/-! ### The absorbing index on the class -/

variable {d : ℕ}
  [SmoothOfRelativeDimension d
    ((X ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (X ↘ Spec (CommRingCat.of k)))]
include d

include hadm in
/-- The truncation index of `BR_affine` is an index of the run `BP TA` (`X` nonempty). -/
theorem firstCenterIndex_lt_length_BP_of_class (hne : Nonempty X)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    firstCenterIndex (BP TA) TA.I < (BP TA).length := by
  obtain ⟨x⟩ := hne
  rw [firstCenterIndex_eq_componentIndex (d := d) X TA emb hadm (_root_.irreducibleComponent x)
    (irreducibleComponent_mem_irreducibleComponents x)]
  exact componentIndex_lt_length TA emb hadm hcodim _ _

include hadm in
/-- The centre at the truncation index contains the strict transform of `X`. -/
theorem centerContains_firstCenterIndex_BP_of_class (hne : Nonempty X)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    CenterContains (BP TA) TA.I (firstCenterIndex (BP TA) TA.I) := by
  classical
  have hlt := firstCenterIndex_lt_length_BP_of_class (d := d) TA emb hadm hne hcodim
  have hex : ∃ n, CenterContains (BP TA) TA.I n := by
    by_contra hno
    have h0 : firstCenterIndex (BP TA) TA.I = (BP TA).length := by
      unfold firstCenterIndex
      rw [dite_eq_right hno]
    omega
  exact firstCenterIndex_of_exists hex

include hadm in
/-- The centre at the truncation index contains the strict transform of every component. -/
theorem centerContains_component_firstCenterIndex
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η)))
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    CenterContains (BP TA) ((X.irreducibleComponentIdeal C hC).map emb)
      (firstCenterIndex (BP TA) TA.I) := by
  classical
  rw [firstCenterIndex_eq_componentIndex (d := d) X TA emb hadm C hC]
  have hlt := componentIndex_lt_length TA emb hadm hcodim C hC
  have hex : ∃ n, CenterContains (BP TA) ((X.irreducibleComponentIdeal C hC).map emb) n := by
    by_contra hno
    have h0 : firstCenterIndex (BP TA) ((X.irreducibleComponentIdeal C hC).map emb) =
        (BP TA).length := by
      unfold firstCenterIndex
      rw [dite_eq_right hno]
    change componentIndex k X TA emb C hC = (BP TA).length at h0
    omega
  exact firstCenterIndex_of_exists hex

/-! ### Clause (1): the end result is smooth -/

include hadm in
/-- At the truncation index `j`, the strict transform of each component `C` of `X` is an irreducible
component of the centre `Z_j`, open in it: `Z_j` is smooth, hence regular, and lies over `emb(X)`
(the centres of `BP(A, I_X, ∅)` lie over `V(I_X)`), in which the generic point of `C` is maximal. -/
theorem isOpenImmersion_inclusion_component (C : Set X) (hC : C ∈ irreducibleComponents X)
    (hj : firstCenterIndex (BP TA) TA.I < (BP TA).length)
    (hle : (BP TA).center ⟨_, hj⟩ ≤ (BP TA).strictTransformSeq
      ((X.irreducibleComponentIdeal C hC).map emb) ⟨_, Nat.lt_succ_of_lt hj⟩) :
    IsOpenImmersion (IdealSheafData.inclusion hle) := by
  have hcl : IsClosedImmersion emb := hadm.1
  have hE : IsEmpty TA.E.ι := hadm.2.2.2.1
  have : IsNoetherian TA.X.left := (TA.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hIC : IsIntegral ((X.irreducibleComponentIdeal C hC).map emb).subscheme :=
    isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced C hC emb
  have hη : IsGenericPoint hC.1.genericPoint C :=
    hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  have hsm : Smooth (((BP TA).center ⟨_, hj⟩).subschemeι ≫
      (BP TA).stageMap ⟨_, Nat.lt_succ_of_lt hj⟩ ≫ (TA.X.left ↘ Spec (CommRingCat.of k))) :=
    (BP_center_smooth_hasSncWith TA ⟨_, hj⟩).1
  have hZ : IsRegular ((BP TA).center ⟨_, hj⟩).subscheme :=
    isRegular_of_smooth (((BP TA).center ⟨_, hj⟩).subschemeι ≫
      (BP TA).stageMap ⟨_, Nat.lt_succ_of_lt hj⟩ ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))
  have hηA : emb hC.1.genericPoint ∈ TA.I.support.genericPoints := by
    rw [← hadm.2.2.2.2]
    exact mem_genericPoints_support_ker emb hC hη
  exact isOpenImmersion_inclusion_of_mem_genericPoints (BP TA) _ ⟨_, hj⟩
    (firstCenterIndex_eq_componentIndex (d := d) X TA emb hadm C hC) hle hZ
    (fun y hy => stageMap_mem_support_of_mem_center_BP TA hE ⟨_, hj⟩ hy)
    (isGenericPoint_map_irreducibleComponentIdeal C hC emb hη) hηA

include hadm in
/-- At the truncation index `j`, the strict transform `X̄_j` of `X` is an open subscheme of the
centre `Z_j`: its support is the union of the supports of the components' strict transforms, each
open in `Z_j` (`isOpenImmersion_inclusion_component`), and a closed immersion into the reduced
`Z_j` with open range is an open immersion. -/
theorem isOpenImmersion_inclusion_firstCenterIndex
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η)))
    (hj : firstCenterIndex (BP TA) TA.I < (BP TA).length)
    (hle : (BP TA).center ⟨_, hj⟩ ≤ (BP TA).strictTransformSeq TA.I ⟨_, Nat.lt_succ_of_lt hj⟩) :
    IsOpenImmersion (IdealSheafData.inclusion hle) := by
  have hcl : IsClosedImmersion emb := hadm.1
  have hI : emb.ker = TA.I := hadm.2.2.2.2
  have : IsNoetherian TA.X.left := (TA.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hAln : IsLocallyNoetherian TA.X.left := inferInstance
  set S := BP TA with hS
  set j := firstCenterIndex S TA.I with hjdef
  have hsm : Smooth ((S.center ⟨j, hj⟩).subschemeι ≫
      S.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ (TA.X.left ↘ Spec (CommRingCat.of k))) :=
    (BP_center_smooth_hasSncWith TA ⟨j, hj⟩).1
  have hZ : IsRegular (S.center ⟨j, hj⟩).subscheme :=
    isRegular_of_smooth ((S.center ⟨j, hj⟩).subschemeι ≫
      S.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))
  have hred : IsReduced (S.center ⟨j, hj⟩).subscheme := isReduced_of_isRegular hZ
  -- the components' inclusions are open immersions
  have hleC : ∀ (C : Set X) (hC : C ∈ irreducibleComponents X),
      S.center ⟨j, hj⟩ ≤ S.strictTransformSeq ((X.irreducibleComponentIdeal C hC).map emb)
        ⟨j, Nat.lt_succ_of_lt hj⟩ :=
    fun C hC => (centerContains_component_firstCenterIndex (d := d) TA emb hadm hcodim C hC).2
  have hopenC : ∀ (C : Set X) (hC : C ∈ irreducibleComponents X),
      IsOpen (Set.range (IdealSheafData.inclusion (hleC C hC))) := fun C hC =>
    have := isOpenImmersion_inclusion_component (d := d) TA emb hadm C hC hj (hleC C hC)
    (IdealSheafData.inclusion (hleC C hC)).isOpenEmbedding.isOpen_range
  -- the range of the inclusion of `X̄_j` is the union of the components' ranges
  have : Finite {C : Set X // C ∈ irreducibleComponents X} :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hsupp : ((S.strictTransformSeq TA.I ⟨j, Nat.lt_succ_of_lt hj⟩).support :
      Set (S.stage ⟨j, Nat.lt_succ_of_lt hj⟩)) =
      ⋃ C ∈ (Set.univ : Set {C : Set X // C ∈ irreducibleComponents X}),
        ((S.strictTransformSeq ((X.irreducibleComponentIdeal C.1 C.2).map emb)
          ⟨j, Nat.lt_succ_of_lt hj⟩).support : Set (S.stage ⟨j, Nat.lt_succ_of_lt hj⟩)) := by
    rw [← hI]
    exact coe_support_strictTransformSeq_biUnion S Set.univ Set.finite_univ
      (fun C : {C : Set X // C ∈ irreducibleComponents X} =>
        (X.irreducibleComponentIdeal C.1 C.2).map emb) emb.ker (coe_support_ker_eq_iUnion X emb) _
  have hopen : IsOpen (Set.range (IdealSheafData.inclusion hle)) := by
    rw [range_inclusion, hsupp, Set.preimage_iUnion₂]
    refine isOpen_biUnion fun C _ => ?_
    rw [← range_inclusion (hleC C.1 C.2)]
    exact hopenC C.1 C.2
  exact isOpenImmersion_of_isClosedImmersion_of_isOpen_range _ hopen

include hadm in
/-- **Clause (1) of [Kol07, Theorem 36] for the affine resolution of a reduced equidimensional
scheme**: the end result of `BR_affine TA emb` is smooth over `k`. It is the strict transform `X̄_j`
at the truncation index, an open subscheme of the smooth centre `Z_j`
(`isOpenImmersion_inclusion_firstCenterIndex`, `smooth_composite_pullback_take`). -/
theorem smooth_composite_BR_affine_of_class (hne : Nonempty X)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    Smooth ((BR_affine TA emb).composite ≫ (X ↘ Spec (CommRingCat.of k))) := by
  have hcl : IsClosedImmersion emb := hadm.1
  have hover : emb.IsOver (Spec (CommRingCat.of k)) := hadm.2.1
  obtain ⟨hj, hle⟩ := centerContains_firstCenterIndex_BP_of_class (d := d) TA emb hadm hne hcodim
  have : IsOpenImmersion (IdealSheafData.inclusion hle) :=
    isOpenImmersion_inclusion_firstCenterIndex (d := d) TA emb hadm hcodim hj hle
  have hsm : Smooth (((BP TA).center ⟨_, hj⟩).subschemeι ≫
      (BP TA).stageMap ⟨_, Nat.lt_succ_of_lt hj⟩ ≫ (TA.X.left ↘ Spec (CommRingCat.of k))) :=
    (BP_center_smooth_hasSncWith TA ⟨_, hj⟩).1
  have h := smooth_composite_pullback_take (BP TA) emb (TA.X.left ↘ Spec (CommRingCat.of k)) TA.I
    hadm.2.2.2.2 _ hj hle hsm
  rwa [comp_over] at h

/-! ### Clause (2): an isomorphism over the smooth locus -/

include hadm in
/-- Before the truncation index no restricted centre of `BP TA` has a point over the generic point
of a component of `X`: the truncation index is the absorbing index of the component
(`notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex`). -/
theorem not_restrictedCenterHasPointOver_BP_genericPoint_of_class (C : Set X)
    (hC : C ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η C)
    (i : Fin ((BP TA).take (firstCenterIndex (BP TA) TA.I)).length) :
    ¬ RestrictedCenterHasPointOver ((BP TA).take (firstCenterIndex (BP TA) TA.I)) TA.I i
      (emb η) := by
  have hcl : IsClosedImmersion emb := hadm.1
  have hAln : IsLocallyNoetherian TA.X.left :=
    (TA.X.left ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  have hIC : IsIntegral ((X.irreducibleComponentIdeal C hC).map emb).subscheme :=
    isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced C hC emb
  intro hi
  rw [restrictedCenterHasPointOver_take] at hi
  obtain ⟨p, hZ, -, hp⟩ := hi
  have hlt : i.val < firstCenterIndex (BP TA) ((X.irreducibleComponentIdeal C hC).map emb) := by
    have h1 : i.val < firstCenterIndex (BP TA) TA.I :=
      lt_of_lt_of_le i.2 (by rw [length_take]; exact min_le_left _ _)
    exact lt_of_lt_of_eq h1 ((firstCenterIndex_eq_componentIndex (d := d) X TA emb hadm C hC).trans
      (componentIndex_def k X TA emb C hC))
  exact notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex (BP TA) _
    (isGenericPoint_map_irreducibleComponentIdeal C hC emb hη) ⟨i.val, _⟩ hlt p hp hZ

include hadm in
/-- Kollár's localisation argument [Kol07, 4.2] on the truncation: no restricted centre of the
truncation of `BP TA` at the truncation index has a point over a smooth point of `X`
(`not_restrictedCenterHasPointOver_of_mem_smoothLocus_of_exists`, from the generic point of a
component, with the functoriality of the principalization sequence under smooth surjections). -/
theorem not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus_of_class (hne : Nonempty X) {x : X}
    (hx : x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus)
    (i : Fin ((BP TA).take (firstCenterIndex (BP TA) TA.I)).length) :
    ¬ RestrictedCenterHasPointOver ((BP TA).take (firstCenterIndex (BP TA) TA.I)) TA.I i
      (emb x) := by
  have hcl : IsClosedImmersion emb := hadm.1
  have hover : emb.IsOver (Spec (CommRingCat.of k)) := hadm.2.1
  obtain ⟨y⟩ := hne
  obtain ⟨η, hη, hηs⟩ := exists_isGenericPoint_mem_smoothLocus (k := k)
    (_root_.irreducibleComponent y) (irreducibleComponent_mem_irreducibleComponents y)
  exact not_restrictedCenterHasPointOver_of_mem_smoothLocus_of_exists TA emb hadm.2.2.2.1
    hadm.2.2.2.2 (d := d) (fun T => BP T)
    (fun T' g _ hs hp => BP_pullback_of_surjective TA T' g hs hp) (firstCenterIndex (BP TA) TA.I)
    ⟨η, hηs, fun i => not_restrictedCenterHasPointOver_BP_genericPoint_of_class (d := d) TA emb hadm
      (_root_.irreducibleComponent y) (irreducibleComponent_mem_irreducibleComponents y) hη i⟩
    hx i

include hadm in
/-- **Clause (2) of [Kol07, Theorem 36] for the affine resolution of a reduced equidimensional
scheme**: `Π : X_j → X` is an isomorphism over the smooth locus of `X`. The restricted centres avoid
`X^{ns}`, so `isIso_composite_restrict_of_centers_disjoint` applies to `BR_affine TA emb`. -/
theorem isIso_composite_restrict_smoothLocus_BR_affine_of_class (hne : Nonempty X) :
    IsIso ((BR_affine TA emb).composite ∣_ (X ↘ Spec (CommRingCat.of k)).smoothLocus) := by
  have hcl : IsClosedImmersion emb := hadm.1
  refine isIso_composite_restrict_of_centers_disjoint (BR_affine TA emb) _ fun i => ?_
  rw [Set.disjoint_left]
  intro p hp hpU
  let i' : Fin ((BP TA).take (firstCenterIndex (BP TA) TA.I)).length :=
    ⟨i.val, lt_of_lt_of_eq i.2 (length_pullback _ emb)⟩
  have hbr := (restrictedCenterHasPointOver_iff_of_isClosedImmersion
    ((BP TA).take (firstCenterIndex (BP TA) TA.I)) emb i'
    ((BR_affine TA emb).stageMap i.castSucc p)).1 ⟨p, hp, rfl⟩
  rw [hadm.2.2.2.2] at hbr
  exact not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus_of_class (d := d) TA emb hadm hne
    hpU i' hbr

/-! ### Clause (3): the preimage of the singular locus -/

include hadm in
/-- **Clause (3) of [Kol07, Theorem 36] for the affine resolution of a reduced equidimensional
scheme**: `Π⁻¹(Sing X)` is the support of a simple normal crossing family on the end result, the
restriction of the total exceptional divisor (`exists_isSnc_comap_totalTransformSeq_take_of_forall`:
through every point of `X̄_j` passes the strict transform of the component through its image, an
integral closed subscheme of `X` that no centre before `j` contains). -/
theorem exists_snc_preimage_singularLocus_BR_affine_of_class (hne : Nonempty X)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    ∃ F : DivisorFamily (BR_affine TA emb).last, F.IsSnc ∧
      (F.support : Set (BR_affine TA emb).last) =
        (BR_affine TA emb).composite ⁻¹'
          ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ := by
  have hcl : IsClosedImmersion emb := hadm.1
  have hover : emb.IsOver (Spec (CommRingCat.of k)) := hadm.2.1
  have hE : IsEmpty TA.E.ι := hadm.2.2.2.1
  have hI : emb.ker = TA.I := hadm.2.2.2.2
  have hsmA := TA.smooth
  have hAn : IsNoetherian TA.X.left := (TA.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have : Finite {C : Set X // C ∈ irreducibleComponents X} :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  set S := BP TA with hS
  set j := firstCenterIndex S TA.I with hjdef
  obtain ⟨hj, hle⟩ := centerContains_firstCenterIndex_BP_of_class (d := d) TA emb hadm hne hcodim
  have hopen : IsOpenImmersion (IdealSheafData.inclusion hle) :=
    isOpenImmersion_inclusion_firstCenterIndex (d := d) TA emb hadm hcodim hj hle
  obtain ⟨-, hsnc⟩ := BP_center_smooth_hasSncWith TA ⟨j, hj⟩
  -- through every point of `X̄_j` the strict transform of a component
  have hcomp : ∀ p ∈ ((S.take j).strictTransformSeq TA.I (Fin.last _)).support,
      ∃ J : TA.X.left.IdealSheafData, IsIntegral J.subscheme ∧ TA.I ≤ J ∧
        p ∈ ((S.take j).strictTransformSeq J (Fin.last _)).support ∧
        ∃ η : TA.X.left, IsGenericPoint η (J.support : Set TA.X.left) ∧
          ∀ m : Fin (S.take j).length,
            ¬ (S.take j).center m ≤ (S.take j).strictTransformSeq J m.castSucc := by
    intro p hp
    have hp' : p ∈ ⋃ C ∈ (Set.univ : Set {C : Set X // C ∈ irreducibleComponents X}),
        (((S.take j).strictTransformSeq ((X.irreducibleComponentIdeal C.1 C.2).map emb)
          (Fin.last _)).support : Set ((S.take j).stage (Fin.last _))) := by
      rw [← coe_support_strictTransformSeq_biUnion (S.take j) Set.univ Set.finite_univ
        (fun C : {C : Set X // C ∈ irreducibleComponents X} =>
          (X.irreducibleComponentIdeal C.1 C.2).map emb) emb.ker (coe_support_ker_eq_iUnion X emb)
        (Fin.last _), hI]
      exact hp
    obtain ⟨C, -, hpC⟩ := Set.mem_iUnion₂.mp hp'
    have hη : IsGenericPoint C.2.1.genericPoint C.1 :=
      C.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C.1 C.2)
    refine ⟨(X.irreducibleComponentIdeal C.1 C.2).map emb,
      isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced C.1 C.2 emb,
      le_map_irreducibleComponentIdeal TA emb hadm C.1 C.2, hpC, emb C.2.1.genericPoint,
      isGenericPoint_map_irreducibleComponentIdeal C.1 C.2 emb hη, fun m hm => ?_⟩
    have hmj : m.val < j := lt_of_lt_of_eq m.2 (length_take_of_le S hj.le)
    have hcc : CenterContains S ((X.irreducibleComponentIdeal C.1 C.2).map emb) m.val :=
      (centerContains_take_iff S _ j m.val hmj).1 ⟨m.2, hm⟩
    have hlt : m.val < firstCenterIndex S ((X.irreducibleComponentIdeal C.1 C.2).map emb) :=
      lt_of_lt_of_eq hmj ((firstCenterIndex_eq_componentIndex (d := d) X TA emb hadm C.1 C.2).trans
        (componentIndex_def k X TA emb C.1 C.2))
    exact not_centerContains_of_lt_firstCenterIndex' S _ hlt hcc
  exact exists_isSnc_comap_totalTransformSeq_take_of_forall (TA.X.left ↘ Spec (CommRingCat.of k)) S
    (BP_isOrderGeSeq_zero TA).1 TA.I TA.E hE emb hI hj hle hsnc hcomp
    (smooth_composite_BR_affine_of_class (d := d) TA emb hadm hne hcodim)
    fun x hx i =>
      not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus_of_class (d := d) TA emb hadm hne hx i

end Hironaka.Resolution
