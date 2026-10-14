/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Kol07.OffCenters
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersOverSupport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.TransformDerivative
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transport of the generic point before the first containing centre

In the proof of [Kol07, Corollary 22] there is a unique `j` such that `π_0 ⋯ π_{j−1}` is a local
isomorphism around `η_X` while the centre `Z_j` of `π_j` contains `η_X`.
`Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter`
proves that at a stage `i ≤ firstCenterIndex S I` the strict transform of the integral `V(I)` has a
generic point `η_i` which is the unique point over the generic point `η` of `V(I)`, and that no
earlier centre has a point over `η`; `Hironaka.Resolution.Algebraic.Kol07.OffCenters` proves the
pointwise transport along a sequence: at a point over no earlier centre the stage map is an
isomorphism on stalks and the stalk of the strict transform is the image of the stalk of the
subscheme. This file composes the two, in the form needed by Włodarczyk's embedded
desingularization, whose components are transported until the first stage at which a centre contains
them (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`).

* `le_firstCenterIndex_of_forall_lt_not`: if no centre before `n` contains the strict transform,
  then `n ≤ firstCenterIndex S I`;
* `stageMapBetween_notMem_center_support_of_le_firstCenterIndex`: the transports of a point over
  `η` avoid every earlier centre;
* `stalkIdeal_markedTransformSeq_of_forall_notMem`: over no earlier centre the stalk of the marked
  transform is the image of the stalk of the ideal (the exceptional stalks are the unit ideal
  there), the marked counterpart of `stalkIdeal_strictTransformSeq_of_forall_notMem`;
* `notMem_support_totalTransformSeq_of_forall_notMem`: such a point lies on no member of the total
  transform of a family it did not lie on [Kol07, Definition 25];
* `mem_genericPoints_markedTransformSeq_support_of_forall_notMem`: the unique point over a generic
  point of `V(I)` at which `I` agrees with an integral `J` is a generic point of the support of the
  marked transform (its stalk is the image of `J`'s, and any specialisation to it lies over `η`);
* `exists_isGenericPoint_strictTransformSeq_and_isIso_of_le_firstCenterIndex`: the packaged form
  at a stage `≤ firstCenterIndex`.

The results hold on any scheme, locally Noetherian where the integrality of the strict transforms
is needed.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {A : Scheme.{u}}

/-! ### The first containing centre -/

open Classical in
/-- If no centre before `n ≤ S.length` contains the strict transform of `V(I)`, then
`n ≤ firstCenterIndex S I` (when no centre contains it at all, `firstCenterIndex S I = S.length`).
This is how the minimal absorbing stage of the embedded desingularization loop is compared with
the first-centre index of each of its components. -/
theorem le_firstCenterIndex_of_forall_lt_not (S : BlowUpSequence A) (I : A.IdealSheafData) {n : ℕ}
    (hn : n ≤ S.length) (h : ∀ m < n, ¬ CenterContains S I m) : n ≤ firstCenterIndex S I := by
  by_cases hex : ∃ m, CenterContains S I m
  · by_contra hlt
    exact h _ (not_le.mp hlt) (firstCenterIndex_of_exists hex)
  · unfold firstCenterIndex
    rw [dite_eq_right hex]
    exact hn

/-- At a stage `i ≤ firstCenterIndex S I`, a point `y` over the generic point `η` of the integral
`V(I)` is carried by the intermediate stage maps to no earlier centre [Kol07, Corollary 22,
proof]: `notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex` and the cocycle identity
`Π_m ∘ Π_{im} = Π_i`. -/
theorem stageMapBetween_notMem_center_support_of_le_firstCenterIndex [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) [IsIntegral I.subscheme] {η : A}
    (hη : IsGenericPoint η (I.support : Set A)) (i : Fin (S.length + 1))
    (hi : i.val ≤ firstCenterIndex S I) {y : S.stage i} (hy : S.stageMap i y = η)
    (m : Fin S.length) (hmi : m.val < i.val) :
    S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) y ∉ (S.center m).support :=
  notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex S I hη m (lt_of_lt_of_le hmi hi) _
    (by rw [← Scheme.Hom.comp_apply, stageMapBetween_comp_stageMap]; exact hy)

/-! ### The marked transform off the centres -/

/-- The marked transform along a sequence [Kol07, Warning 63, (63.1)] at a point over no earlier
centre, in the `⟨j, hj⟩` form of the indices: the stalk of the marked transform of `(J, c)` at a
point of the `j`-th stage lying over no earlier centre is the image of the stalk of `J` under the
stalk map of the stage map, the exceptional stalk of each step being the unit ideal there
(`stalkIdeal_markedTransform_of_notMem`). The marked counterpart of
`isIso_stalkMap_stageMap_and_stalkIdeal_strictTransformSeq_mk`. -/
theorem stalkIdeal_markedTransformSeq_of_forall_notMem_mk :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (J : X.IdealSheafData) (c j : ℕ)
      (hj : j < S.length + 1) (p : S.stage ⟨j, hj⟩),
      (∀ (m : ℕ) (hm : m < S.length) (hmj : m < j),
        S.stageMapBetween ⟨j, hj⟩ ⟨m, Nat.lt_succ_of_lt hm⟩ (Nat.le_of_lt hmj) p ∉
          (S.center ⟨m, hm⟩).support) →
      (S.markedTransformSeq J c ⟨j, hj⟩).stalkIdeal p =
        (J.stalkIdeal (S.stageMap ⟨j, hj⟩ p)).map ((S.stageMap ⟨j, hj⟩).stalkMap p).hom
  | _, nil Y, J, c, j, hj, p, _ => by
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    exact (stalkIdeal_map_stalkMap_id J p).symm
  | _, cons Y D rest, J, c, 0, hj, p, _ => (stalkIdeal_map_stalkMap_id J p).symm
  | _, cons Y D rest, J, c, j + 1, hj, p, h => by
    revert p h
    change ∀ (p : rest.stage ⟨j, Nat.lt_of_succ_lt_succ hj⟩),
      (∀ (m : ℕ) (hm : m < rest.length + 1) (hmj : m < j + 1),
        (cons Y D rest).stageMapBetween ⟨j + 1, hj⟩ ⟨m, Nat.lt_succ_of_lt hm⟩ (Nat.le_of_lt hmj) p ∉
          ((cons Y D rest).center ⟨m, hm⟩).support) →
      (rest.markedTransformSeq (J.markedTransform D c) c ⟨j, _⟩).stalkIdeal p =
        (J.stalkIdeal (D.blowUpπ (rest.stageMap ⟨j, _⟩ p))).map
          ((rest.stageMap ⟨j, _⟩ ≫ D.blowUpπ).stalkMap p).hom
    intro p h
    have h0 : D.blowUpπ (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p) ∉ D.support :=
      h 0 (Nat.succ_pos _) (Nat.succ_pos _)
    have hy : rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p ∉
        (D.comap D.blowUpπ).support := by
      rw [mem_support_comap_iff_apply]
      exact h0
    have h' : ∀ (m : ℕ) (hm : m < rest.length) (hmj : m < j),
        rest.stageMapBetween ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ⟨m, Nat.lt_succ_of_lt hm⟩
          (Nat.le_of_lt hmj) p ∉ (rest.center ⟨m, hm⟩).support :=
      fun m hm hmj => h (m + 1) (Nat.succ_lt_succ hm) (Nat.succ_lt_succ hmj)
    rw [stalkIdeal_markedTransformSeq_of_forall_notMem_mk rest (J.markedTransform D c) c j
      (Nat.lt_of_succ_lt_succ hj) p h', stalkIdeal_markedTransform_of_notMem D J c hy,
      Ideal.map_map, Scheme.Hom.stalkMap_comp]
    rfl

/-- At a point over no earlier centre, the stalk of the marked transform of `(J, c)` is the image
of the stalk of `J` under the stalk map of the stage map [Kol07, Warning 63, (63.1)]. -/
theorem stalkIdeal_markedTransformSeq_of_forall_notMem (S : BlowUpSequence A)
    (J : A.IdealSheafData) (c : ℕ) (i : Fin (S.length + 1)) (p : S.stage i)
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) p ∉ (S.center m).support) :
    (S.markedTransformSeq J c i).stalkIdeal p =
      (J.stalkIdeal (S.stageMap i p)).map ((S.stageMap i).stalkMap p).hom := by
  obtain ⟨j, hj⟩ := i
  exact stalkIdeal_markedTransformSeq_of_forall_notMem_mk S J c j hj p fun m hm hmj => h ⟨m, hm⟩ hmj

/-! ### Off the boundary -/

/-- A point off the support of a family lies on none of its members. -/
theorem notMem_component_support_of_notMem_support {X : Scheme.{u}} (F : DivisorFamily X) {p : X}
    (hp : p ∉ F.support) (l : F.ι) : p ∉ (F.component l).support :=
  fun hl => hp (le_iSup (fun i => (F.component i).support) l hl)

/-- A point over no earlier centre whose image lies on no member of `E` lies on no member of the
total transform of `E` at its stage [Kol07, Definition 25] (`mem_support_totalTransformSeq_iff`). -/
theorem notMem_support_totalTransformSeq_of_forall_notMem [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (E : DivisorFamily A) (i : Fin (S.length + 1)) (p : S.stage i)
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) p ∉ (S.center m).support)
    (hE : S.stageMap i p ∉ E.support) : p ∉ (S.totalTransformSeq E i).support := by
  rw [mem_support_totalTransformSeq_iff]
  rintro (hp | ⟨m, hmi, hp⟩)
  · exact hE hp
  · exact h m hmi hp

/-! ### The generic point of the marked transform's support -/

/-- Let `η` be a generic point of `supp I` at which `I` agrees with an integral `J` whose support
has generic point `η`, and let `η'` be a point over `η` at stage `i` which lies over no earlier
centre and is the unique point over `η`. Then `η'` is a generic point of the support of the marked
transform of `(I, c)` at stage `i`: its stalk is the image of the proper stalk of `J` under an
isomorphism, and a point of that support specialising to `η'` lies over a point of `supp I`
specialising to `η`, hence over `η`, hence equals `η'`. (This carries along the sequence the
hypothesis "`I = I_{Y₁}` near a generic point of `Y₁`" of the Claim in the proof of
[Wlo05, Theorem 4.7.1].) -/
theorem mem_genericPoints_markedTransformSeq_support_of_forall_notMem (S : BlowUpSequence A)
    (I J : A.IdealSheafData) (c : ℕ) {η : A} (hη : IsGenericPoint η (J.support : Set A))
    (hηI : η ∈ I.support.genericPoints) (hIJ : I.stalkIdeal η = J.stalkIdeal η)
    (i : Fin (S.length + 1)) {η' : S.stage i} (hη' : S.stageMap i η' = η)
    (huniq : ∀ y, S.stageMap i y = η → y = η')
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) η' ∉ (S.center m).support) :
    η' ∈ (S.markedTransformSeq I c i).support.genericPoints := by
  have hiso : IsIso ((S.stageMap i).stalkMap η') :=
    isIso_stalkMap_stageMap_of_forall_notMem S i η' h
  have hIJ' : I.stalkIdeal (S.stageMap i η') = J.stalkIdeal (S.stageMap i η') := by
    rw [hη']
    exact hIJ
  have hstalk : (S.markedTransformSeq I c i).stalkIdeal η' =
      (J.stalkIdeal (S.stageMap i η')).map ((S.stageMap i).stalkMap η').hom := by
    rw [stalkIdeal_markedTransformSeq_of_forall_notMem S I c i η' h, hIJ']
  have hJ : J.stalkIdeal (S.stageMap i η') ≠ ⊤ := by
    rw [hη']
    intro hJtop
    have := (mem_support_iff_stalkIdeal_le_maximalIdeal J η).mp hη.mem
    rw [hJtop] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp this)
  refine ⟨?_, fun ζ hζ hspec => ?_⟩
  · -- the stalk is proper: the image of the proper stalk of `J` under an isomorphism
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal]
    apply IsLocalRing.le_maximalIdeal
    rw [hstalk]
    intro htop
    apply hJ
    have hbij : Function.Bijective ((S.stageMap i).stalkMap η').hom :=
      (asIso ((S.stageMap i).stalkMap η')).commRingCatIsoToRingEquiv.bijective
    have hc := congrArg (Ideal.comap ((S.stageMap i).stalkMap η').hom) htop
    rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_top] at hc
  · -- a specialization to `η'` in the support lies over `η`, hence is `η'`
    have hζI : S.stageMap i ζ ∈ I.support := by
      have hle : (S.markedTransformSeq I c i).support ≤ (I.comap (S.stageMap i)).support :=
        support_antitone (comap_stageMap_le_markedTransformSeq S I c i)
      exact (mem_support_comap_iff_apply I (S.stageMap i) ζ).mp (hle hζ)
    have hsp : S.stageMap i ζ ⤳ η := by
      rw [← hη']
      exact hspec.map (S.stageMap i).continuous
    exact huniq ζ (hηI.2 hζI hsp)

/-! ### The packaged form -/

/-- The transport of the generic point, packaged [Kol07, Corollary 22, proof]: at a stage
`i ≤ firstCenterIndex S J` the strict transform of the integral `V(J)` has a generic point `η'`, the
unique point over the generic point `η` of `V(J)`; its transports avoid every earlier centre and the
stage map is an isomorphism on stalks at it
(`exists_isGenericPoint_strictTransformSeq_of_le_firstCenterIndex` with
`isIso_stalkMap_stageMap_of_forall_notMem`). -/
theorem exists_isGenericPoint_strictTransformSeq_and_isIso_of_le_firstCenterIndex
    [IsLocallyNoetherian A] (S : BlowUpSequence A) (J : A.IdealSheafData) [IsIntegral J.subscheme]
    {η : A} (hη : IsGenericPoint η (J.support : Set A)) (i : Fin (S.length + 1))
    (hi : i.val ≤ firstCenterIndex S J) :
    ∃ η' : S.stage i, IsGenericPoint η' ((S.strictTransformSeq J i).support : Set (S.stage i)) ∧
      S.stageMap i η' = η ∧ (∀ y, S.stageMap i y = η → y = η') ∧
      (∀ (m : Fin S.length) (hmi : m.val < i.val),
        S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) η' ∉ (S.center m).support) ∧
      IsIso ((S.stageMap i).stalkMap η') := by
  obtain ⟨η', hgen, hmap, huniq⟩ :=
    exists_isGenericPoint_strictTransformSeq_of_le_firstCenterIndex S J hη i hi
  have havoid : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) η' ∉ (S.center m).support :=
    fun m hmi => stageMapBetween_notMem_center_support_of_le_firstCenterIndex S J hη i hi hmap m hmi
  exact ⟨η', hgen, hmap, huniq, havoid, isIso_stalkMap_stageMap_of_forall_notMem S i η' havoid⟩

end Hironaka.Resolution
