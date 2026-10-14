/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.MarkedData
public import Hironaka.Manifold.FiniteSuccession.Functor.LocalCover
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.MonomialPart
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Pieces
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Comap
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The input piece family of the monomial procedure on a relatively compact open set

On an analytic manifold the monomial procedure of [Kol07, 111, Step 3] is run on a relatively
compact open set `U`, as every step of the analytic order reduction is ([Wlo09, Theorem 2.0.3 (1)]).
For a triple `T = (M, 𝓘, E)` the **ambient pieces** are the connected components of the members of
`E` (`ComponentIndex`, the index set of the monomial part of `BMO/MonomialPart.lean`), each with its
exponent `componentExponent`, the order of `𝓘` along it. The ambient pieces form a locally finite
family, so only finitely many meet the compact set `closure U`: the **meeting pieces**. The **input
piece family** on `M.restrict U` (`inputFamily`) has as pieces the traces `D ∩ U` of the meeting
pieces `D`, enumerated; the label of a piece is the position of its member among the finitely many
members having a meeting piece, in the order of the members (`inputEmb`); its exponent is the
ambient exponent. It realises the boundary `E|_U` of the restricted triple (`inputFamily_realizes`):
a restricted member is the union of the traces of its meeting components, members without a meeting
piece are empty on `U`, and distinct components of one member are disjoint. It satisfies the
invariants of the combinatorial state for `(n, m)` when `T` is in the class `BMOClass m`
(`inputFamily_isValid`).

The pieces are the traces of the ambient components rather than the connected components of the
restricted members: an ambient component may meet `U` in infinitely many connected components. The
monomial part of the restricted triple, which is indexed by the components of the restricted
members, is nevertheless the monomial ideal of the input family
(`BMO/Step3Monomial/InputMonomial.lean`).
-/

@[expose] public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

section Input

variable (T : AnalyticTriple ψ₀ M) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The finitely many ambient pieces (connected components of the boundary members) meeting
`closure U`: the components form a locally finite family and `closure U` is compact. -/
noncomputable def meetingPieces : Finset (ComponentIndex T.F) :=
  ((componentSet_locallyFinite T.F T.isSnc).finite_nonempty_inter_compact hU).toFinset

theorem mem_meetingPieces_iff {i : ComponentIndex T.F} :
    i ∈ meetingPieces T U hU ↔ (componentSet T.F i ∩ closure (U : Set M)).Nonempty :=
  Set.Finite.mem_toFinset _

/-- An ambient piece through a point of `U` meets `closure U`. -/
theorem mem_meetingPieces_of_mem {i : ComponentIndex T.F} {x : M} (hx : x ∈ componentSet T.F i)
    (hxU : x ∈ U) : i ∈ meetingPieces T U hU :=
  (mem_meetingPieces_iff T U hU).mpr ⟨x, hx, subset_closure hxU⟩

/-- The members having a meeting piece. -/
noncomputable def meetingMembers : Finset T.F.ι := (meetingPieces T U hU).image Sigma.fst

/-- An enumeration of the meeting pieces; these are the pieces of the input family. -/
noncomputable def meetingPiece (c : Fin (meetingPieces T U hU).card) : ComponentIndex T.F :=
  ((meetingPieces T U hU).equivFin.symm c).1

theorem meetingPiece_mem (c : Fin (meetingPieces T U hU).card) :
    meetingPiece T U hU c ∈ meetingPieces T U hU :=
  ((meetingPieces T U hU).equivFin.symm c).2

theorem meetingPiece_injective : Function.Injective (meetingPiece T U hU) := fun _ _ h =>
  (meetingPieces T U hU).equivFin.symm.injective (Subtype.ext h)

theorem exists_meetingPiece_eq {i : ComponentIndex T.F} (hi : i ∈ meetingPieces T U hU) :
    ∃ c, meetingPiece T U hU c = i :=
  ⟨(meetingPieces T U hU).equivFin ⟨i, hi⟩, by
    change (((meetingPieces T U hU).equivFin.symm ((meetingPieces T U hU).equivFin ⟨i, hi⟩))).1 = i
    rw [Equiv.symm_apply_apply]⟩

/-- A point of `M.restrict U` lies in `U`. -/
theorem inclusion_mem (x : M.restrict U) : (M.inclusion U) x ∈ U := x.2

theorem fst_meetingPiece_mem (c : Fin (meetingPieces T U hU).card) :
    (meetingPiece T U hU c).1 ∈ meetingMembers T U hU :=
  Finset.mem_image_of_mem _ (meetingPiece_mem T U hU c)

/-- The **input piece family** on `M.restrict U`: the traces on `U` of the meeting pieces, in the
enumeration `meetingPiece`; the label of a piece is the position of its member among the members
having a meeting piece, sorted in the order of the members; its exponent is the ambient exponent
`componentExponent`, the order of `𝓘` along the component. -/
noncomputable def inputFamily : PieceFamily (M.restrict U) where
  nextComp := (meetingPieces T U hU).card
  nextLabel := (meetingMembers T U hU).card
  piece c := if h : c < (meetingPieces T U hU).card then
    ⇑(M.inclusion U) ⁻¹' componentSet T.F (meetingPiece T U hU ⟨c, h⟩) else ∅
  label c := if h : c < (meetingPieces T U hU).card then
    (((meetingMembers T U hU).orderIsoOfFin rfl).symm
      ⟨(meetingPiece T U hU ⟨c, h⟩).1, fst_meetingPiece_mem T U hU _⟩ : Fin _).1 else 0
  a c := if h : c < (meetingPieces T U hU).card then
    componentExponent T.F T.isSnc T.I (meetingPiece T U hU ⟨c, h⟩) else 0
  label_lt c hc := by
    rw [dite_eq_left hc]
    exact Fin.is_lt _
  isClosed_piece c := by
    split_ifs with h
    · exact (componentSubmanifold T.F T.isSnc _).isClosed.preimage
        (M.inclusion U).contMDiff.continuous
    · exact isClosed_empty

theorem inputFamily_nextComp : (inputFamily T U hU).nextComp = (meetingPieces T U hU).card := rfl

theorem inputFamily_nextLabel :
    (inputFamily T U hU).nextLabel = (meetingMembers T U hU).card := rfl

theorem inputFamily_piece_of_lt {c : ℕ} (hc : c < (meetingPieces T U hU).card) :
    (inputFamily T U hU).piece c =
      ⇑(M.inclusion U) ⁻¹' componentSet T.F (meetingPiece T U hU ⟨c, hc⟩) := by
  change (if h : c < _ then _ else _) = _
  rw [dite_eq_left hc]

theorem inputFamily_piece_of_le {c : ℕ} (hc : (meetingPieces T U hU).card ≤ c) :
    (inputFamily T U hU).piece c = ∅ := by
  change (if h : c < _ then _ else _) = _
  rw [dite_eq_right (not_lt.mpr hc)]

theorem inputFamily_piece (c : Fin (meetingPieces T U hU).card) :
    (inputFamily T U hU).piece c =
      ⇑(M.inclusion U) ⁻¹' componentSet T.F (meetingPiece T U hU c) :=
  inputFamily_piece_of_lt T U hU c.2

theorem inputFamily_label_of_lt {c : ℕ} (hc : c < (meetingPieces T U hU).card) :
    (inputFamily T U hU).label c =
      ((((meetingMembers T U hU).orderIsoOfFin rfl).symm
        ⟨(meetingPiece T U hU ⟨c, hc⟩).1, fst_meetingPiece_mem T U hU _⟩ : Fin _) : ℕ) := by
  change (if h : c < _ then _ else _) = _
  rw [dite_eq_left hc]

theorem inputFamily_a_of_lt {c : ℕ} (hc : c < (meetingPieces T U hU).card) :
    (inputFamily T U hU).a c = componentExponent T.F T.isSnc T.I (meetingPiece T U hU ⟨c, hc⟩) := by
  change (if h : c < _ then _ else _) = _
  rw [dite_eq_left hc]

theorem inputFamily_a (c : Fin (meetingPieces T U hU).card) :
    (inputFamily T U hU).a c = componentExponent T.F T.isSnc T.I (meetingPiece T U hU c) :=
  inputFamily_a_of_lt T U hU c.2

/-- The members having a meeting piece, sorted, as an order embedding of the labels into the
members. -/
noncomputable def inputEmb : Fin (inputFamily T U hU).nextLabel ↪o T.F.ι :=
  (meetingMembers T U hU).orderEmbOfFin rfl

theorem range_inputEmb : Set.range (inputEmb T U hU) = ↑(meetingMembers T U hU) :=
  Finset.range_orderEmbOfFin _ _

/-- The member of the label of a piece is the member of the piece. -/
theorem inputEmb_label (c : Fin (meetingPieces T U hU).card) :
    inputEmb T U hU ⟨(inputFamily T U hU).label c, (inputFamily T U hU).label_lt c c.2⟩ =
      (meetingPiece T U hU c).1 := by
  have h1 : (⟨(inputFamily T U hU).label c, (inputFamily T U hU).label_lt c c.2⟩ :
      Fin (inputFamily T U hU).nextLabel) =
      ((meetingMembers T U hU).orderIsoOfFin rfl).symm
        ⟨(meetingPiece T U hU c).1, fst_meetingPiece_mem T U hU c⟩ :=
    Fin.ext (inputFamily_label_of_lt T U hU c.2)
  rw [h1]
  exact ((Finset.coe_orderIsoOfFin_apply _ _ _).symm.trans
    (congrArg Subtype.val (OrderIso.apply_symm_apply _ _)))

/-- Pieces with the same label belong to the same member. -/
theorem fst_meetingPiece_eq_of_label_eq {c c' : Fin (meetingPieces T U hU).card}
    (h : (inputFamily T U hU).label c = (inputFamily T U hU).label c') :
    (meetingPiece T U hU c).1 = (meetingPiece T U hU c').1 := by
  rw [← inputEmb_label T U hU c, ← inputEmb_label T U hU c']
  congr 1
  exact Fin.ext h

/-- The input family realises the boundary of the restricted triple through the sorted meeting
members: a restricted member is the union of the traces of its meeting components, members without
a meeting piece are empty on `U`, and distinct components of one member are disjoint. -/
theorem inputFamily_realizes :
    (inputFamily T U hU).Realizes
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F (inputEmb T U hU) where
  hyp_eq ℓ := by
    ext x
    rw [Set.mem_iUnion₂]
    constructor
    · intro hx
      have hx' : (M.inclusion U) x ∈ T.F.hyp (inputEmb T U hU ℓ) := hx
      obtain ⟨c, hc⟩ := exists_meetingPiece_eq T U hU
        (mem_meetingPieces_of_mem T U hU (mem_componentSet_mk T.F _ hx') (inclusion_mem U x))
      refine ⟨c.1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr c.2, ?_⟩, ?_⟩
      · have h1 : (⟨(inputFamily T U hU).label c, (inputFamily T U hU).label_lt c c.2⟩ :
            Fin (inputFamily T U hU).nextLabel) = ℓ := by
          apply (inputEmb T U hU).injective
          rw [inputEmb_label T U hU c, hc]
        exact congrArg Fin.val h1
      · rw [inputFamily_piece T U hU c, hc]
        exact mem_componentSet_mk T.F _ hx'
    · rintro ⟨c, hc, hx⟩
      obtain ⟨hc, hl⟩ := Finset.mem_filter.mp hc
      have hc' : c < (meetingPieces T U hU).card := Finset.mem_range.mp hc
      rw [inputFamily_piece_of_lt T U hU hc'] at hx
      have hj : (meetingPiece T U hU ⟨c, hc'⟩).1 = inputEmb T U hU ℓ := by
        rw [← inputEmb_label T U hU ⟨c, hc'⟩]
        congr 1
        exact Fin.ext hl
      change (M.inclusion U) x ∈ T.F.hyp (inputEmb T U hU ℓ)
      rw [← hj]
      exact (Subtype.coe_image_subset _ _) hx
  hyp_eq_empty j hj := by
    ext x
    refine ⟨fun hx => ?_, fun h => ((Set.mem_empty_iff_false x).mp h).elim⟩
    have hx' : (M.inclusion U) x ∈ T.F.hyp j := hx
    have hi := mem_meetingPieces_of_mem T U hU (mem_componentSet_mk T.F j hx') (inclusion_mem U x)
    have hjm : j ∈ meetingMembers T U hU := Finset.mem_image_of_mem Sigma.fst hi
    exact hj ⟨((meetingMembers T U hU).orderIsoOfFin rfl).symm ⟨j, hjm⟩,
      (Finset.coe_orderIsoOfFin_apply _ _ _).symm.trans
        (congrArg Subtype.val (OrderIso.apply_symm_apply _ _))⟩
  disjoint c c' hc hc' hne hl := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [inputFamily_piece_of_lt T U hU hc, Set.mem_preimage] at hx
    rw [inputFamily_piece_of_lt T U hU hc', Set.mem_preimage] at hx'
    have hfst : (meetingPiece T U hU ⟨c, hc⟩).1 = (meetingPiece T U hU ⟨c', hc'⟩).1 :=
      fst_meetingPiece_eq_of_label_eq T U hU hl
    exact hne (congrArg Fin.val
      (meetingPiece_injective T U hU (componentIndex_ext_of_mem hx hx' hfst)))

/-- The input family satisfies the invariants of the combinatorial state for `(n, m)` when `T` is in
the class `BMOClass m` (which gives `1 ≤ m`). -/
theorem inputFamily_isValid {m : ℕ} (hT : AnalyticTriple.BMOClass m T) :
    (inputFamily T U hU).IsValid n m :=
  (inputFamily T U hU).valid_of_realizes
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
    (inputFamily_realizes T U hU) hT.one_le

end Input

end Hironaka.Manifold.BMO
