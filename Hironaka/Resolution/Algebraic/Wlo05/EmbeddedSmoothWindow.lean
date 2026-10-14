/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersMiss
public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCore
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCoreTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedOrderGe
import Hironaka.Scheme.BlowUpSequence.ColonComapOpenImmersion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.EmptyFamily
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The loop through a smooth window

Clause (b) of [Wlo05, Theorem 1.0.2] for the embedded desingularization sequence
(`Hironaka.Resolution.Algebraic.Wlo05.Embedded`): no centre of `BED(X, I_Y, ∅)` has a point over
`Reg(Y)`, the set of smooth points of `Y`. The proof ([Wlo05, 4.6]: at a smooth point of `Y` "the
generic points would be transformed isomorphically") runs the core lemma of the smooth case
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCore`) LOCALLY, on an open immersion `j : W ⟶ X`
through which `Y` is seen as ONE smooth irreducible component `c` — a **smooth window**
(`SmoothWindow`):

* every member of the boundary is empty over `W`;
* over `W` the ideal is either the unit ideal or the restriction of a single member `c` of the
  loop's component set, integral, with `V(c) ∩ W` smooth over `k`, no other member meeting `W`.

The round lemma (`smoothWindow_round_one`): the run `BMO_1(T)` pulled back to `W` and stripped of
its empty blow-ups is `BMO_1(W, I|_W, 1, ∅)` (the second clause of [Kol07, 34.1],
`dimFreeBMO_commutesWithSmooth`; `indifferentToEmptyMembers` removes the empty boundary members),
whose first centre contains the generic point of `V(c) ∩ W` (`core_bmoOneRun`); so the FIRST
centre of `BMO_1(T)` with a point over `W` lies over the generic point of `c`, is the first centre
containing the strict transform of `c` (`firstCenterIndex`), and every earlier centre misses `W`.
The isolation lemma (`smoothWindow_isolated`): the loop's truncation index `n₀` is at most that
first index (`Nat.find_min'`), and the isolated marked triple at `n₀` seen through the lifted
window `W_{n₀} ≅ W` is again a smooth window — the ideal there is `𝒪` if `c` was absorbed at `n₀`
(the colon `I_c : I_c`), else the strict transform of `c` (the colon by the other absorbed
members, all empty over `W`); the boundary members, exceptional divisors of centres missing `W`,
are empty over `W`. The induction on the number of members (`centersMiss_bedAux_of_smoothWindow`)
then gives a form of (b) stronger than Włodarczyk's: every centre of `BED` misses the preimage of
`W` outright, whether or not the point lies on the strict transform of `Y`. The window at a smooth
point of `Y` and the clause itself are in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme
  BlowUpSequence Scheme.IdealSheafData Hironaka.Stage Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- **A smooth window** `j : W ⟶ T.X.left` for the marked triple `T` and the member set `C` — every
boundary member is empty over `W`; over `W` the ideal is the unit ideal or the restriction of ONE
member `c ∈ C`, which is integral, smooth over `k` on `W`, and the only member meeting `W`
([Wlo05, 4.6]: near a smooth point `Y` is smooth and irreducible). -/
structure SmoothWindow (T : MarkedTriple k) (C : Finset T.X.left.IdealSheafData) {W : Scheme.{u}}
    (j : W ⟶ T.X.left) : Prop where
  boundary : ∀ e, (T.E.component e).comap j = ⊤
  ideal : T.I.comap j = ⊤ ∨ ∃ c ∈ C, T.I.comap j = c.comap j ∧ IsIntegral c.subscheme ∧
    Smooth ((c.comap j).subschemeι ≫ j ≫ (T.X.left ↘ Spec (.of k))) ∧
    ∀ c' ∈ C, c'.comap j ≠ ⊤ → c' = c

/-! ### The run through the window -/

/-- The run of `BMO_1` on `T` pulled back through a smooth window and stripped of its empty
blow-ups begins with a centre containing a generic point of `V(I) ∩ W` (the second clause of
[Kol07, 34.1] through `dimFreeBMO_commutesWithSmooth`, `indifferentToEmptyMembers`, and the core
lemma `core_bmoOneRun`). -/
theorem exists_eraseEmpty_pullback_eq_cons_of_smoothWindow (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) {W : Scheme.{u}} (j : W ⟶ T.X.left) [IsOpenImmersion j]
    [CompactSpace W] (hw : SmoothWindow T C j) {c : T.X.left.IdealSheafData}
    (hIc : T.I.comap j = c.comap j)
    (hsm : Smooth ((c.comap j).subschemeι ≫ j ≫ (T.X.left ↘ Spec (.of k))))
    (hne : T.I.comap j ≠ ⊤) :
    ∃ (D₀ : W.IdealSheafData) (rest₀ : BlowUpSequence D₀.blowUp),
      ((bmoOneRun T hm).pullback j).eraseEmpty = BlowUpSequence.cons W D₀ rest₀ ∧
        ∃ η' ∈ (T.I.comap j).support.genericPoints, η' ∈ D₀.support := by
  have hPF : PerfectField k := PerfectField.ofCharZero
  let : W.Over (Spec (.of k)) := ⟨j ≫ (T.X.left ↘ Spec (.of k))⟩
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (W ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ (T.X.left ↘ Spec (.of k))))
  have : IsSeparated (W ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (j ≫ (T.X.left ↘ Spec (.of k))))
  have : Smooth (W ↘ Spec (.of k)) := inferInstanceAs (Smooth (j ≫ (T.X.left ↘ Spec (.of k))))
  have : QuasiCompact (W ↘ Spec (.of k)) := inferInstance
  have hY : ∃ n : ℕ, SmoothOfRelativeDimension n (W ↘ Spec (.of k)) := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact ⟨n, by simpa using smoothOfRelativeDimension_comp 0 n j (T.X.left ↘ Spec (.of k))⟩
  let TW : MarkedTriple k := T.pullback hY j
  have hsmj : @Smooth TW.X.left T.X.left j := inferInstanceAs (Smooth j)
  have hT : T.BMOClassFree 1 := ⟨le_rfl, hm⟩
  have hTW : TW.BMOClassFree 1 := ⟨le_rfl, hm⟩
  have hpull : (dimFreeBMO stage0 1 k).seq TW hTW =
      (((dimFreeBMO stage0 1 k).seq T hT).pullback j).eraseEmpty :=
    (dimFreeBMO_commutesWithSmooth stage0 1 (k := k)).2 T TW j
      (MarkedTriple.isPullbackOf_pullback T hY j) hT hTW
  have hsncE : (DivisorFamily.empty W).IsSnc :=
    isSnc_empty_of_smooth (W ↘ Spec (.of k))
  let TW' : MarkedTriple k := { TW with E := DivisorFamily.empty W, isSnc := hsncE }
  have hTW' : TW'.BMOClassFree 1 := ⟨le_rfl, hm⟩
  have : IsEmpty (DivisorFamily.empty W).ι := inferInstanceAs (IsEmpty PEmpty)
  have hind : (dimFreeBMO stage0 1 k).seq TW hTW = (dimFreeBMO stage0 1 k).seq TW' hTW' :=
    dimFreeBMO_indifferentToEmptyMembers stage0 1 TW (DivisorFamily.empty W) hsncE
      OrderEmbedding.ofIsEmpty (fun i => PEmpty.elim i) (fun b _ => hw.boundary b) hTW hTW'
  have hsm' : Smooth ((c.comap j).subschemeι ≫ (W ↘ Spec (.of k))) := hsm
  have hreg : ∀ x ∈ TW'.I.support,
      IsRegularLocalRing (W.presheaf.stalk x ⧸ TW'.I.stalkIdeal x) := by
    change ∀ x ∈ (T.I.comap j).support,
      IsRegularLocalRing (W.presheaf.stalk x ⧸ (T.I.comap j).stalkIdeal x)
    rw [hIc]
    intro x hx
    exact isRegularLocalRing_quotient_stalkIdeal (c.comap j) (W ↘ Spec (.of k)) hx
  obtain ⟨D₀, rest₀, hcons, η', hη', hη'D⟩ :=
    core_bmoOneRun TW' hm (inferInstanceAs (IsEmpty PEmpty)) hreg hne
  refine ⟨D₀, rest₀, ?_, η', hη', hη'D⟩
  change (((dimFreeBMO stage0 1 k).seq T hT).pullback j).eraseEmpty = _
  rw [← hpull, hind]
  exact hcons

/-- **The round lemma** ([Wlo05, 4.6]: "otherwise the generic points would be transformed
isomorphically"; the proof of [Kol07, Corollary 22]) — through a smooth window on which the ideal
is not the unit ideal, the distinguished member `c` is absorbed by the run of `BMO_1` on `T` (some
centre contains its strict transform), and every centre before the first containing one misses
`W`. The first centre of the run over `W` lies over the generic point of `V(c)` (the core lemma on
`(W, I|_W, 1, ∅)` transported through `eraseEmpty`), so its index is at least `firstCenterIndex`
(`notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex`), while all earlier centres of the
pullback are empty. -/
theorem smoothWindow_round_one (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) {W : Scheme.{u}} (j : W ⟶ T.X.left) [IsOpenImmersion j]
    [CompactSpace W] (hw : SmoothWindow T C j) (hne : T.I.comap j ≠ ⊤) :
    ∃ c ∈ C, T.I.comap j = c.comap j ∧ IsIntegral c.subscheme ∧
      Smooth ((c.comap j).subschemeι ≫ j ≫ (T.X.left ↘ Spec (.of k))) ∧
      (∀ c' ∈ C, c'.comap j ≠ ⊤ → c' = c) ∧
      (∃ n, CenterContains (bmoOneRun T hm) c n) ∧
      CentersMissBefore (bmoOneRun T hm) (Set.range j)
        (firstCenterIndex (bmoOneRun T hm) c) := by
  obtain ⟨c, hcC, hIc, hint, hsm, huniq⟩ := hw.ideal.resolve_left hne
  refine ⟨c, hcC, hIc, hint, hsm, huniq, ?_⟩
  have := hint
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  obtain ⟨D₀, rest₀, hSE, η', hη', hη'D⟩ :=
    exists_eraseEmpty_pullback_eq_cons_of_smoothWindow T hm C j hw hIc hsm hne
  obtain ⟨n, hn, q', hq'c, hq'm, hbefore⟩ :=
    exists_mem_center_support_of_eraseEmpty_eq_cons _ hSE hη'D
  have hnS : n < (bmoOneRun T hm).length := by rwa [length_pullback] at hn
  have hq'c' : q' ∈ (((bmoOneRun T hm).pullback j).center
      ((bmoOneRun T hm).pullbackCenterIdx j ⟨n, hnS⟩)).support := hq'c
  rw [center_pullback_mk] at hq'c'
  have hx₀ : (bmoOneRun T hm).pullbackStageHom j ⟨n, Nat.lt_succ_of_lt hnS⟩ q' ∈
      ((bmoOneRun T hm).center ⟨n, hnS⟩).support :=
    (mem_support_comap_iff_apply _ _ q').mp hq'c'
  have hx₀map : (bmoOneRun T hm).stageMap ⟨n, Nat.lt_succ_of_lt hnS⟩
      ((bmoOneRun T hm).pullbackStageHom j ⟨n, Nat.lt_succ_of_lt hnS⟩ q') = j η' := by
    rw [← Scheme.Hom.comp_apply, pullbackStageHom_stageMap_mk, Scheme.Hom.comp_apply]
    exact congrArg _ hq'm
  have hη'c : η' ∈ (c.comap j).support.genericPoints := by
    rw [← hIc]
    exact hη'
  have hgen : IsGenericPoint (j η') (c.support : Set T.X.left) :=
    isGenericPoint_of_mem_genericPoints_comap j c (isIrreducible_support_of_isIntegral c) hη'c
  have hle : firstCenterIndex (bmoOneRun T hm) c ≤ n := by
    by_contra hlt
    exact notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex (bmoOneRun T hm) c hgen
      ⟨n, hnS⟩ (not_le.mp hlt) _ hx₀map hx₀
  have hex : ∃ m, CenterContains (bmoOneRun T hm) c m := by
    by_contra hno
    have h1 : firstCenterIndex (bmoOneRun T hm) c = (bmoOneRun T hm).length := by
      unfold firstCenterIndex
      rw [dite_eq_right hno]
    omega
  refine ⟨hex, ?_⟩
  refine centersMissBefore_of_forall_center_pullback_eq_top (bmoOneRun T hm) j _
    fun i hi hi' => ?_
  have e : (bmoOneRun T hm).pullbackCenterIdx j ⟨i, hi'⟩ =
      ⟨i, lt_trans (lt_of_lt_of_le hi hle) hn⟩ := Fin.ext rfl
  rw [e]
  exact hbefore i (lt_of_lt_of_le hi hle)

/-! ### The isolated triple through the lifted window -/

section Isolated

variable (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData) {W : Scheme.{u}}
  (j : W ⟶ T.X.left) [IsOpenImmersion j] (n₀ : ℕ)

/-- The boundary of the isolated triple is empty over the lifted window: the total transform of
an all-empty family along a prefix all of whose centres miss `W` ([Kol07, 34.1] on the divisor
families, `totalTransformSeq_pullback`). -/
theorem isolatedTriple_E_comap_pullbackStageHom_eq_top
    (hb : ∀ e, (T.E.component e).comap j = ⊤)
    (hP : CentersMiss ((bmoOneRun T hm).take n₀) (Set.range j))
    (e : (isolatedTriple T hm C n₀).E.ι) :
    ((isolatedTriple T hm C n₀).E.component e).comap
      (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) = ⊤ := by
  have hPtop := forall_center_pullback_eq_top_of_centersMiss _ j hP
  have key := totalTransformSeq_component_eq_top_of_forall_center_eq_top _ hPtop (T.E.comap j) hb
    (((bmoOneRun T hm).take n₀).pullbackStageIdx j (Fin.last _))
  rw [totalTransformSeq_pullback ((bmoOneRun T hm).take n₀) j T.E (Fin.last _)] at key
  exact key e

/-- The marked transform of `I` at the end of the prefix, seen through the lifted window, is the
inverse image of `I|_W` under the (isomorphic) stage map of the pulled-back prefix
(`IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom`; all centres empty). -/
theorem markedTransformSeq_take_comap_pullbackStageHom
    (hP : CentersMiss ((bmoOneRun T hm).take n₀) (Set.range j)) :
    (((bmoOneRun T hm).take n₀).markedTransformSeq T.I T.m (Fin.last _)).comap
        (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) =
      (T.I.comap j).comap ((((bmoOneRun T hm).take n₀).pullback j).stageMap
        (((bmoOneRun T hm).take n₀).pullbackStageIdx j (Fin.last _))) := by
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have hOG : ((bmoOneRun T hm).take n₀).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
    isOrderGeSeq_take _ _ _ _ (isOrderGeSeq_bmoOneRun T hm) n₀
  rw [← IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom (T.X.left ↘ Spec (.of k)) d j hOG
    (Fin.last _)]
  exact markedTransformSeq_eq_comap_of_forall_center_eq_top _
    (forall_center_pullback_eq_top_of_centersMiss _ j hP) (T.I.comap j) T.m _

/-- The strict transform of a member at the end of the prefix, seen through the lifted window, is
the inverse image of its restriction under the stage map of the pulled-back prefix
(`strictTransformSeq_pullback`; all centres empty). -/
theorem strictTransformSeq_take_comap_pullbackStageHom
    (hP : CentersMiss ((bmoOneRun T hm).take n₀) (Set.range j)) (c : T.X.left.IdealSheafData) :
    (((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _)).comap
        (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) =
      (c.comap j).comap ((((bmoOneRun T hm).take n₀).pullback j).stageMap
        (((bmoOneRun T hm).take n₀).pullbackStageIdx j (Fin.last _))) := by
  rw [← strictTransformSeq_pullback ((bmoOneRun T hm).take n₀) j c (Fin.last _)]
  exact strictTransformSeq_eq_comap_of_forall_center_eq_top _
    (forall_center_pullback_eq_top_of_centersMiss _ j hP) (c.comap j) _

/-- On the prefix: no centre of the prefix `take n₀` contains the strict transform of `c` when
`n₀ ≤ firstCenterIndex run c`. -/
theorem not_centerContains_take_of_le_firstCenterIndex (c : T.X.left.IdealSheafData)
    (hle : n₀ ≤ firstCenterIndex (bmoOneRun T hm) c) (i : ℕ) :
    ¬ CenterContains ((bmoOneRun T hm).take n₀) c i := by
  intro hi
  have hi' : i < n₀ :=
    lt_of_lt_of_le hi.1 (by rw [length_take]; exact min_le_left _ _)
  exact not_centerContains_of_lt_firstCenterIndex' (bmoOneRun T hm) c (lt_of_lt_of_le hi' hle)
    ((centerContains_take_iff _ c n₀ i hi').mp hi)

/-- The proof of [Kol07, Corollary 22] on the prefix: the strict transform of an integral member at
the end of a prefix before its first containing centre is integral. -/
theorem isIntegral_strictTransformSeq_take_of_le_firstCenterIndex (c : T.X.left.IdealSheafData)
    [IsIntegral c.subscheme] (hle : n₀ ≤ firstCenterIndex (bmoOneRun T hm) c) :
    IsIntegral (((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _)).subscheme := by
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  refine isIntegral_strictTransformSeq_of_le_firstCenterIndex _ c (Fin.last _) ?_
  have hno : ¬ ∃ i, CenterContains ((bmoOneRun T hm).take n₀) c i :=
    fun ⟨i, hi⟩ => not_centerContains_take_of_le_firstCenterIndex T hm n₀ c hle i hi
  have h : firstCenterIndex ((bmoOneRun T hm).take n₀) c = ((bmoOneRun T hm).take n₀).length := by
    unfold firstCenterIndex
    rw [dite_eq_right hno]
  rw [h]
  exact le_of_eq (Fin.val_last _)

/-- The reduced ideal of the union of the strict transforms of members all empty over `W` is the
unit ideal over the lifted window (`vanishingIdeal_iSup`; strict transforms lie over `V(c')`). -/
theorem vanishingIdeal_iSup_strictTransformSeq_take_comap_eq_top
    (F : Finset T.X.left.IdealSheafData) (hF : ∀ c' ∈ F, c'.comap j = ⊤) :
    (IdealSheafData.vanishingIdeal (⨆ c' ∈ F,
        (((bmoOneRun T hm).take n₀).strictTransformSeq c' (Fin.last _)).support)).comap
      (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) = ⊤ := by
  have hoi : IsOpenImmersion (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) :=
    isOpenImmersion_pullbackStageHom _ j _
  -- the closed complement of the window at the end of the prefix
  have hopen : IsOpen (Set.range (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _))) :=
    (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)).isOpenEmbedding.isOpen_range
  let Z' : Closeds (((bmoOneRun T hm).take n₀).stage (Fin.last _)) :=
    ⟨(Set.range (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)))ᶜ,
      hopen.isClosed_compl⟩
  have hle : (⨆ c' ∈ F, (((bmoOneRun T hm).take n₀).strictTransformSeq c' (Fin.last _)).support)
      ≤ Z' := by
    refine iSup₂_le fun c' hc' => SetLike.le_def.mpr fun x hx => ?_
    change x ∉ Set.range (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _))
    rintro ⟨y, rfl⟩
    have h1 := stageMap_mem_support_of_mem_strictTransformSeq_support _ c' (Fin.last _) hx
    rw [← Scheme.Hom.comp_apply, pullbackStageHom_stageMap, Scheme.Hom.comp_apply] at h1
    have h2 := (mem_support_comap_iff_apply c' j _).mpr h1
    rw [hF c' hc', IdealSheafData.support_top, ← SetLike.mem_coe, Closeds.coe_bot] at h2
    exact h2
  have htop : (IdealSheafData.vanishingIdeal Z').comap
      (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) = ⊤ := by
    rw [← IdealSheafData.support_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [mem_support_comap_iff_apply, ← SetLike.mem_coe,
      IdealSheafData.coe_support_vanishingIdeal] at hy
    exact (hy ⟨y, rfl⟩).elim
  exact eq_top_iff.mpr (htop.symm.le.trans (IdealSheafData.comap_mono _
      (IdealSheafData.vanishingIdeal_antimono hle)))

/-- **The isolated ideal through the window, `c` not yet absorbed**: the colon by the reduced ideal
of the absorbed members — all empty over `W` — is the marked transform itself there, which is the
strict transform of `c` (Włodarczyk's isolation read through the window). -/
theorem isolatedTriple_I_comap_of_lt_firstCenterIndex
    (hP : CentersMiss ((bmoOneRun T hm).take n₀) (Set.range j)) (c : T.X.left.IdealSheafData)
    (hIc : T.I.comap j = c.comap j) (huniq : ∀ c' ∈ C, c'.comap j ≠ ⊤ → c' = c)
    (hlt : n₀ < firstCenterIndex (bmoOneRun T hm) c) :
    (isolatedTriple T hm C n₀).I.comap (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _))
      = (((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _)).comap
        (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) := by
  classical
  have hLN₁ : IsLocallyNoetherian (((bmoOneRun T hm).take n₀).stage (Fin.last _)) :=
    ((isolatedTriple T hm C n₀).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hoi : IsOpenImmersion (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) :=
    isOpenImmersion_pullbackStageHom _ j _
  change ((((bmoOneRun T hm).take n₀).markedTransformSeq T.I T.m (Fin.last _)).colon
      (IdealSheafData.vanishingIdeal (⨆ c' ∈ C.filter (fun c' => CenterContains
          (bmoOneRun T hm) c' n₀),
        (((bmoOneRun T hm).take n₀).strictTransformSeq c' (Fin.last _)).support))).comap
      (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) = _
  rw [Remark33.comap_colon_of_isOpenImmersion_of_isLocallyNoetherian,
    vanishingIdeal_iSup_strictTransformSeq_take_comap_eq_top T hm j n₀ _ ?_,
        IdealSheafData.colon_top,
    markedTransformSeq_take_comap_pullbackStageHom T hm j n₀ hP, hIc,
    strictTransformSeq_take_comap_pullbackStageHom T hm j n₀ hP c]
  intro c' hc'
  have hc'C := Finset.mem_filter.mp hc'
  by_contra hne
  have hcc : CenterContains (bmoOneRun T hm) c n₀ := by
    rw [← huniq c' hc'C.1 hne]
    exact hc'C.2
  exact not_centerContains_of_lt_firstCenterIndex' (bmoOneRun T hm) c hlt hcc

/-- **The isolated ideal through the window, `c` absorbed at `n₀`**: the colon `I_c : I_c` is the
unit ideal over `W` — the reduced ideal of the absorbed members is contained in the (reduced) strict
transform of `c`, which is the marked transform over `W`. -/
theorem isolatedTriple_I_comap_eq_top_of_eq_firstCenterIndex
    (hP : CentersMiss ((bmoOneRun T hm).take n₀) (Set.range j)) (c : T.X.left.IdealSheafData)
    (hcC : c ∈ C) (hIc : T.I.comap j = c.comap j) [IsIntegral c.subscheme]
    (hex : ∃ n, CenterContains (bmoOneRun T hm) c n)
    (hn₀ : n₀ = firstCenterIndex (bmoOneRun T hm) c) :
    (isolatedTriple T hm C n₀).I.comap (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _))
      = ⊤ := by
  classical
  have hLN₁ : IsLocallyNoetherian (((bmoOneRun T hm).take n₀).stage (Fin.last _)) :=
    ((isolatedTriple T hm C n₀).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hcc : CenterContains (bmoOneRun T hm) c n₀ := by
    rw [hn₀]
    exact firstCenterIndex_of_exists hex
  have hint₁ := isIntegral_strictTransformSeq_take_of_le_firstCenterIndex T hm n₀ c hn₀.le
  have hrad : (((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _)).radical =
      ((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _) :=
    radical_eq_self_of_isReduced_subscheme _
  have hJle : IdealSheafData.vanishingIdeal (⨆ c' ∈ C.filter (fun c' => CenterContains
      (bmoOneRun T hm) c' n₀),
        (((bmoOneRun T hm).take n₀).strictTransformSeq c' (Fin.last _)).support) ≤
      ((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _) := by
    refine (IdealSheafData.vanishingIdeal_antimono ?_).trans
        (IdealSheafData.vanishingIdeal_support.trans hrad).le
    exact le_iSup₂ (f := fun c' (_ : c' ∈ C.filter fun c' => CenterContains (bmoOneRun T hm) c' n₀)
      => (((bmoOneRun T hm).take n₀).strictTransformSeq c' (Fin.last _)).support) c
      (Finset.mem_filter.mpr ⟨hcC, hcc⟩)
  have hoi : IsOpenImmersion (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) :=
    isOpenImmersion_pullbackStageHom _ j _
  change ((((bmoOneRun T hm).take n₀).markedTransformSeq T.I T.m (Fin.last _)).colon
      (IdealSheafData.vanishingIdeal (⨆ c' ∈ C.filter (fun c' => CenterContains
          (bmoOneRun T hm) c' n₀),
        (((bmoOneRun T hm).take n₀).strictTransformSeq c' (Fin.last _)).support))).comap
      (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) = ⊤
  rw [Remark33.comap_colon_of_isOpenImmersion_of_isLocallyNoetherian, eq_top_iff,
    IdealSheafData.le_colon_iff_mul_le, IdealSheafData.top_mul]
  calc _ ≤ (((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _)).comap
        (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) :=
            IdealSheafData.comap_mono _ hJle
    _ = (c.comap j).comap _ := strictTransformSeq_take_comap_pullbackStageHom T hm j n₀ hP c
    _ = (T.I.comap j).comap _ := by rw [hIc]
    _ = _ := (markedTransformSeq_take_comap_pullbackStageHom T hm j n₀ hP).symm

/-- The strict transform of `c` seen through the lifted window is smooth over `k` when `V(c) ∩ W`
is: it is the inverse image of `c|_W` under an isomorphism (`smooth_comap_subschemeι_comp`). -/
theorem smooth_strictTransformSeq_take_comap
    (hP : CentersMiss ((bmoOneRun T hm).take n₀) (Set.range j)) (c : T.X.left.IdealSheafData)
    (hsm : Smooth ((c.comap j).subschemeι ≫ j ≫ (T.X.left ↘ Spec (.of k)))) :
    Smooth (((((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _)).comap
      (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _))).subschemeι ≫
        ((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _) ≫
          ((isolatedTriple T hm C n₀).X.left ↘ Spec (.of k))) := by
  have := hsm
  have : IsIso ((((bmoOneRun T hm).take n₀).pullback j).stageMap
      (((bmoOneRun T hm).take n₀).pullbackStageIdx j (Fin.last _))) :=
    isIso_stageMap_of_center_eq_top _ _
      fun j' _ => forall_center_pullback_eq_top_of_centersMiss _ j hP j'
  rw [strictTransformSeq_take_comap_pullbackStageHom T hm j n₀ hP c]
  change Smooth (_ ≫ ((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _) ≫
    ((bmoOneRun T hm).take n₀).stageMap (Fin.last _) ≫ (T.X.left ↘ Spec (.of k)))
  rw [← Category.assoc (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)),
    pullbackStageHom_stageMap, Category.assoc]
  exact smooth_comap_subschemeι_comp (j ≫ (T.X.left ↘ Spec (.of k))) _ (c.comap j)

omit [IsOpenImmersion j] in
/-- A remaining member meeting the lifted window is the strict transform of `c`: its points lie
over points of the original member over `W`, and `c` is the only member meeting `W`. -/
theorem eq_strictTransformSeq_take_of_comap_ne_top (c : T.X.left.IdealSheafData)
    (huniq : ∀ c' ∈ C, c'.comap j ≠ ⊤ → c' = c) :
    ∀ c'' ∈ remainingComponents T hm C n₀,
      c''.comap (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) ≠ ⊤ →
        c'' = ((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _) := by
  classical
  intro c'' hc'' hne''
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc''
  obtain ⟨y, hy⟩ := exists_mem_support_of_ne_top _ hne''
  have hy' : (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) y ∈
      (((bmoOneRun T hm).take n₀).strictTransformSeq c' (Fin.last _)).support :=
    (mem_support_comap_iff_apply
      (((bmoOneRun T hm).take n₀).strictTransformSeq c' (Fin.last _))
      (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) y).mp hy
  have h1 := stageMap_mem_support_of_mem_strictTransformSeq_support _ c' (Fin.last _) hy'
  rw [← Scheme.Hom.comp_apply, pullbackStageHom_stageMap, Scheme.Hom.comp_apply] at h1
  have h2 : c'.comap j ≠ ⊤ := by
    intro htop
    have := (mem_support_comap_iff_apply c' j _).mpr h1
    rw [htop, IdealSheafData.support_top, ← SetLike.mem_coe, Closeds.coe_bot] at this
    exact this
  rw [huniq c' (Finset.mem_filter.mp hc').1 h2]

/-- **The isolation lemma** — the isolated marked triple at an index `n₀` at most the first index
containing `c`, with the remaining members, seen through the lifted window, is again a smooth
window. -/
theorem smoothWindow_isolated (hw : SmoothWindow T C j) (c : T.X.left.IdealSheafData) (hcC : c ∈ C)
    (hIc : T.I.comap j = c.comap j) (hint : IsIntegral c.subscheme)
    (hsm : Smooth ((c.comap j).subschemeι ≫ j ≫ (T.X.left ↘ Spec (.of k))))
    (huniq : ∀ c' ∈ C, c'.comap j ≠ ⊤ → c' = c)
    (hex : ∃ n, CenterContains (bmoOneRun T hm) c n)
    (hn₀ : n₀ ≤ firstCenterIndex (bmoOneRun T hm) c)
    (hP : CentersMiss ((bmoOneRun T hm).take n₀) (Set.range j)) :
    SmoothWindow (isolatedTriple T hm C n₀) (remainingComponents T hm C n₀)
      (((bmoOneRun T hm).take n₀).pullbackStageHom j (Fin.last _)) := by
  classical
  have := hint
  refine ⟨fun e => isolatedTriple_E_comap_pullbackStageHom_eq_top T hm C j n₀ hw.boundary hP e, ?_⟩
  rcases lt_or_eq_of_le hn₀ with hlt | heq
  · refine Or.inr ⟨((bmoOneRun T hm).take n₀).strictTransformSeq c (Fin.last _), ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr
        ⟨hcC, not_centerContains_of_lt_firstCenterIndex' (bmoOneRun T hm) c hlt⟩, rfl⟩
    · exact isolatedTriple_I_comap_of_lt_firstCenterIndex T hm C j n₀ hP c hIc huniq hlt
    · exact isIntegral_strictTransformSeq_take_of_le_firstCenterIndex T hm n₀ c hn₀
    · exact smooth_strictTransformSeq_take_comap T hm C j n₀ hP c hsm
    · exact eq_strictTransformSeq_take_of_comap_ne_top T hm C j n₀ c huniq
  · exact Or.inl
      (isolatedTriple_I_comap_eq_top_of_eq_firstCenterIndex T hm C j n₀ hP c hcC hIc hex heq)

end Isolated

/-! ### The loop through a smooth window -/

/-- **No centre of the loop has a point over a smooth window** (clause (b) of
[Wlo05, Theorem 1.0.2] in a stronger form; [Wlo05, 4.6]) — by strong induction on the number of
members: over a window on which the ideal is the unit ideal every centre, lying over `V(I)`
(`stageMap_mem_support_of_mem_center` on the order-`≥ 1` sequence of clause (a)), misses `W`;
otherwise the round lemma places the truncation index `n₀ = Nat.find` at or before the first
centre containing `c` (`Nat.find_min'`), the prefix misses `W`, and the isolation lemma hands the
rest of the loop to the induction hypothesis through the lifted window. -/
theorem centersMiss_bedAux_of_smoothWindow (N : ℕ) :
    ∀ (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData), C.card = N →
      ∀ {W : Scheme.{u}} (j : W ⟶ T.X.left) [IsOpenImmersion j] [CompactSpace W],
        SmoothWindow T C j → CentersMiss (bedAux T hm C) (Set.range j) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T hm C hcard W j _ _ hw
  classical
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  by_cases htop : T.I.comap j = ⊤
  · refine centersMiss_of_isOrderGeSeq (T.X.left ↘ Spec (.of k)) d
      (isOrderGeSeq_bedAux C.card T hm C rfl) le_rfl _ ?_
    intro x hx hxr
    obtain ⟨w, rfl⟩ := hxr
    have hw' : w ∈ (T.I.comap j).support :=
      (mem_support_comap_iff_apply T.I j w).mpr hx
    rw [htop, IdealSheafData.support_top, ← SetLike.mem_coe, Closeds.coe_bot] at hw'
    exact hw'
  · obtain ⟨c, hcC, hIc, hint, hsm, huniq, hex, hmiss⟩ := smoothWindow_round_one T hm C j hw htop
    have hcc : CenterContains (bmoOneRun T hm) c (firstCenterIndex (bmoOneRun T hm) c) :=
      firstCenterIndex_of_exists hex
    have hexA : ∃ n, HasAbsorptionAt T hm C n := ⟨_, c, hcC, hcc⟩
    rw [bedAux_of_exists T hm C hexA]
    have hn₀ : Nat.find hexA ≤ firstCenterIndex (bmoOneRun T hm) c :=
      Nat.find_min' hexA ⟨c, hcC, hcc⟩
    have hP : CentersMiss ((bmoOneRun T hm).take (Nat.find hexA)) (Set.range j) :=
      centersMiss_take_of_centersMissBefore _ _ _
        fun i hi x hx => hmiss i (lt_of_lt_of_le hi hn₀) x hx
    refine centersMiss_concat _ _ (Set.range j) hP ?_
    have hrange : ((bmoOneRun T hm).take (Nat.find hexA)).composite ⁻¹' Set.range j =
        Set.range (((bmoOneRun T hm).take (Nat.find hexA)).pullbackStageHom j (Fin.last _)) :=
      (range_pullbackStageHom _ j (Fin.last _)).symm
    rw [hrange]
    have : @IsOpenImmersion _ (isolatedTriple T hm C (Nat.find hexA)).X.left
        (((bmoOneRun T hm).take (Nat.find hexA)).pullbackStageHom j (Fin.last _)) :=
      isOpenImmersion_pullbackStageHom _ j (Fin.last _)
    have : IsIso ((((bmoOneRun T hm).take (Nat.find hexA)).pullback j).stageMap
        (((bmoOneRun T hm).take (Nat.find hexA)).pullbackStageIdx j (Fin.last _))) :=
      isIso_stageMap_of_center_eq_top _ _
        fun j' _ => forall_center_pullback_eq_top_of_centersMiss _ j hP j'
    have : CompactSpace ((((bmoOneRun T hm).take (Nat.find hexA)).pullback j).stage
        (((bmoOneRun T hm).take (Nat.find hexA)).pullbackStageIdx j (Fin.last _))) :=
      Homeomorph.compactSpace (Scheme.homeoOfIso (asIso
        ((((bmoOneRun T hm).take (Nat.find hexA)).pullback j).stageMap
          (((bmoOneRun T hm).take (Nat.find hexA)).pullbackStageIdx j (Fin.last _))))).symm
    have hcard' : (remainingComponents T hm C (Nat.find hexA)).card < N :=
      hcard ▸ card_remainingComponents_lt T hm C hexA
    exact ih _ hcard' (isolatedTriple T hm C (Nat.find hexA)) hm
      (remainingComponents T hm C (Nat.find hexA)) rfl _
      (smoothWindow_isolated T hm C j (Nat.find hexA) hw c hcC hIc hint hsm huniq hex hn₀ hP)

/-- The loop `BED TX` through a smooth window for the loop's component set has no centre with a
point over the window. -/
theorem centersMiss_BED_of_smoothWindow (TX : Triple k) {W : Scheme.{u}} (j : W ⟶ TX.X.left)
    [IsOpenImmersion j] [CompactSpace W] (hw : SmoothWindow ⟨TX, 1⟩ (componentIdeals TX) j) :
    CentersMiss (BED TX) (Set.range j) :=
  centersMiss_bedAux_of_smoothWindow _ ⟨TX, 1⟩ rfl (componentIdeals TX) rfl j hw

end Hironaka.Resolution
