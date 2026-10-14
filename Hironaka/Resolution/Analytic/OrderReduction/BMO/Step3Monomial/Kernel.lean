/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.BlowUpPieces
import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Center
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Chart
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The nerve after the blow-up of a centre

Kollár describes the intersections after a blow-up of the monomial procedure as
"`E^{i₁} ∩ ⋯ ∩ E^{i_{r-1}} ∩ E^{jℓ}` for certain values of `i`" [Kol07, 111, Step 3]. The
combinatorial model `Hironaka.Monomial.MonomialState` makes the rule exact
(`MonomialState.blowUpNerve`) and proves the procedure on it; this file proves that the rule holds
on an analytic manifold, so that the nerve of the piece family after the blow-up of a centre of the
state is the combinatorial one (`Realizes.nerve_blowUpPieces`). Consequently the transported family
satisfies the invariants of the state (`valid_blowUpPieces`) and its state is the combinatorial
blow-up of the state (`toState_blowUpPieces`), which is how the run, its termination and its
postconditions, proved on the combinatorial model, transfer to the analytic run.

The rule consists of three facts about the loci, read in the blow-up charts over the chart of
`BMO/Step3Monomial/Chart.lean` at a point `x` of the centre:

* the strict transforms of the pieces of a face of the centre have no common point
  (`faceSet_blowUpPieces_of_mem`): at a point over `x` in the blow-up chart of index `i`, the strict
  transform of the piece whose coordinate is the scaling coordinate `σ i` misses the chart;
* a set of old pieces has a common point after the blow-up if and only if it had one before and
  contains no face of the centre (`faceSet_blowUpPieces_nonempty_iff`): off the centre the blow-up
  is an isomorphism, and over a point of the centre in the locus of `P₀`, a piece `c₀ ∈ P₀` outside
  the set gives a chart whose origin lies on the strict transforms of all the other pieces through
  `x`;
* the new piece of a face `P` together with old pieces `T₁` has a common point if and only if
  `T₁ ∪ P` had one and `P ⊄ T₁` (`faceSet_blowUpPieces_insert_newComp_nonempty_iff`), by the same
  origin.
-/

public section

open Set Topology Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO.PieceFamily

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {N : AnalyticManifold.{u} 𝕜 E} {Φ : PieceFamily N}
  {F : HypersurfaceFamily N} {e : Fin Φ.nextLabel ↪o F.ι} {m : ℕ} {hV : Φ.IsValid n m}
  {S : Finset (Finset ℕ)}

/-! ### Points of the new pieces -/

/-- A point of a new piece lies over the locus of the unique face of the centre allocated to that
piece. -/
theorem mem_blowUpPieces_piece_of_le {r : ℕ} (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r)
    {c : ℕ} (hc : Φ.nextComp ≤ c) {p : Manifold.blowUp ψ₀ hZ} :
    p ∈ (Φ.blowUpPieces S m hZ).piece c ↔
      ∃ P ∈ S, Φ.newComp S P = c ∧ Manifold.blowUpπ ψ₀ hZ p ∈ Φ.faceSet P := by
  have hnl : ¬ c < Φ.nextComp := not_lt.mpr hc
  change p ∈ (if c < Φ.nextComp then _ else
    ⋃ P ∈ S.filter (fun P => Φ.newComp S P = c), (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.faceSet P) ↔ _
  rw [ite_eq_right hnl]
  simp only [Set.mem_iUnion, Finset.mem_filter, Set.mem_preimage, exists_prop]
  constructor
  · rintro ⟨P, ⟨hP, hPc⟩, hx⟩
    exact ⟨P, hP, hPc, hx⟩
  · rintro ⟨P, hP, hPc, hx⟩
    exact ⟨P, ⟨hP, hPc⟩, hx⟩

/-- The blow-down of a point of the strict transform of an old piece lies on the piece. -/
theorem π_mem_piece_of_mem_blowUpPieces_piece {r : ℕ} (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r)
    {c : ℕ} (hc : c < Φ.nextComp) {p : Manifold.blowUp ψ₀ hZ} (hp : p ∈
        (Φ.blowUpPieces S m hZ).piece c) :
    Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c := by
  rw [Φ.blowUpPieces_piece_of_lt S m hZ hc] at hp
  exact strictTransform_subset_preimage (isBlowUp_blowUpπ ψ₀ hZ).contMDiff.continuous
    (Φ.isClosed_piece c) hp

/-- The blow-down of a common point of the strict transforms of old pieces is a common point of the
pieces. -/
theorem π_mem_faceSet_of_mem_faceSet_blowUpPieces {r : ℕ}
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r) {T : Finset ℕ} (hT : ∀ c ∈ T, c < Φ.nextComp)
    {p : Manifold.blowUp ψ₀ hZ} (hp : p ∈ (Φ.blowUpPieces S m hZ).faceSet T) :
    Manifold.blowUpπ ψ₀ hZ p ∈ Φ.faceSet T :=
  Φ.mem_faceSet.mpr fun c hc =>
    Φ.π_mem_piece_of_mem_blowUpPieces_piece hZ (hT c hc) ((Φ.blowUpPieces S m
      hZ).mem_faceSet.mp hp c hc)

/-! ### The origin of the chart of a piece of the face -/

/-- Kollár's coordinates at a point `x` of the locus of `P ∈ S`, in the blow-up chart of index
`σ i = κ c₀` for a piece `c₀ ∈ P`: the origin `p` of that chart over `x` lies on the strict
transform of every old piece through `x` other than `c₀`, and not on that of `c₀`. -/
theorem Realizes.exists_origin_of_mem_faceSet (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S))
    {P : Finset ℕ} (hP : P ∈ S) {x : N} (hxP : x ∈ Φ.faceSet P) {c₀ : ℕ} (hc₀ : c₀ ∈ P) :
    ∃ p : Manifold.blowUp ψ₀ hZ, Manifold.blowUpπ ψ₀ hZ p = x ∧
      (∀ c, c < Φ.nextComp → c ≠ c₀ → x ∈ Φ.piece c → p ∈ (Φ.blowUpPieces S m hZ).piece c) ∧
      p ∉ (Φ.blowUpPieces S m hZ).piece c₀ := by
  classical
  set π := Manifold.blowUpπ ψ₀ hZ with hπ
  have hbl : IsBlowUp ψ₀ (Φ.centerOf S) (faceCard S) π := isBlowUp_blowUpπ ψ₀ hZ
  have hxZ : x ∈ Φ.centerOf S := Φ.faceSet_subset_centerOf hP hxP
  obtain ⟨φ, σ, κ, hxφ, hφad, hκ, hcoord, hmiss, hPσ, hσP, -⟩ :=
    hΦ.exists_chart_of_mem_faceSet hF hS hP hxP
  have hc₀n : c₀ < Φ.nextComp := Φ.lt_nextComp_of_mem_nerve (subset_nerve_of_isCenter hS hP) hc₀
  let c₀' : {c : Fin Φ.nextComp // x ∈ Φ.piece c} := ⟨⟨c₀, hc₀n⟩, Φ.mem_faceSet.mp hxP c₀ hc₀⟩
  obtain ⟨i, hi⟩ := (hPσ c₀').mp hc₀
  obtain ⟨Φ', hΦ'⟩ := hbl.exists_chart φ σ hφad i
  obtain ⟨p, hpΦ, hpx, hpcoord⟩ := hΦ'.exists_mem_source_of_mem_center hφad hxZ hxφ
  have hφx : ∀ j, ψ₀ (φ x) j = 0 → ψ₀ (Φ' p) j = 0 := fun j hj => by rw [hpcoord]; exact hj
  refine ⟨p, hpx, fun c hc hcc₀ hxc => ?_, fun hp => ?_⟩
  · -- an old piece through `x` other than `c₀`
    let c' : {c : Fin Φ.nextComp // x ∈ Φ.piece c} := ⟨⟨c, hc⟩, hxc⟩
    have hH : ∀ y ∈ φ.source, y ∈ Φ.piece c ↔ ψ₀ (φ y) (κ c') = 0 := hcoord c'
    rw [Φ.blowUpPieces_piece_of_lt S m hZ hc]
    have hx0 : ψ₀ (Φ' p) (κ c') = 0 := hφx _ ((hcoord c' x hxφ).mp hxc)
    by_cases hin : κ c' ∈ Set.range σ
    · obtain ⟨k, hk⟩ := hin
      have hki : i ≠ k := by
        rintro rfl
        exact hcc₀ (congrArg (fun d => d.1.1) (hκ (hi.symm.trans hk))).symm
      have hH' : ∀ y ∈ φ.source, y ∈ Φ.piece c ↔ ψ₀ (φ y) (σ k) = 0 := by
        intro y hy
        rw [hk]
        exact hH y hy
      have hmem : p ∈ strictTransformSet π (Φ.centerOf S) (Φ.piece c) ∩ Φ'.source := by
        rw [strictTransform_inter_source_of_ne hφad hΦ' hH' hki]
        exact ⟨hpΦ, hk ▸ hx0⟩
      exact hmem.1
    · have hj : ∀ k, σ k ≠ κ c' := fun k hk => hin ⟨k, hk⟩
      have hmem : p ∈ strictTransformSet π (Φ.centerOf S) (Φ.piece c) ∩ Φ'.source := by
        rw [strictTransform_inter_source_off hφad hΦ' hj hH]
        exact ⟨hpΦ, hx0⟩
      exact hmem.1
  · -- the piece `c₀` itself: its strict transform misses the chart of its own index
    rw [Φ.blowUpPieces_piece_of_lt S m hZ hc₀n] at hp
    have hH : ∀ y ∈ φ.source, y ∈ Φ.piece c₀ ↔ ψ₀ (φ y) (σ i) = 0 := by
      intro y hy
      rw [hi]
      exact hcoord c₀' y hy
    have hmem : p ∈ strictTransformSet π (Φ.centerOf S) (Φ.piece c₀) ∩ Φ'.source := ⟨hp, hpΦ⟩
    rw [strictTransform_inter_source_self hφad hΦ' hH] at hmem
    exact (Set.mem_empty_iff_false p).mp hmem

/-! ### The three set facts -/

/-- The strict transforms of the pieces of a face of the centre have no common point: at a point
over `x` in a blow-up chart of index `i`, the strict transform of the piece whose coordinate is the
scaling coordinate `σ i` misses the chart. -/
theorem Realizes.faceSet_blowUpPieces_of_mem (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S))
    {P : Finset ℕ} (hP : P ∈ S) : (Φ.blowUpPieces S m hZ).faceSet P = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  have hPn : ∀ c ∈ P, c < Φ.nextComp := fun c hc =>
    Φ.lt_nextComp_of_mem_nerve (subset_nerve_of_isCenter hS hP) hc
  set x := Manifold.blowUpπ ψ₀ hZ p with hx
  have hxP : x ∈ Φ.faceSet P := Φ.π_mem_faceSet_of_mem_faceSet_blowUpPieces hZ hPn hp
  have hxZ : x ∈ Φ.centerOf S := Φ.faceSet_subset_centerOf hP hxP
  obtain ⟨φ, σ, κ, hxφ, hφad, hκ, hcoord, hmiss, hPσ, hσP, -⟩ :=
    hΦ.exists_chart_of_mem_faceSet hF hS hP hxP
  obtain ⟨i, Φ', hΦ', hpΦ⟩ := (isBlowUp_blowUpπ ψ₀ hZ).cover φ σ hφad p hxφ
  obtain ⟨c₀, hc₀P, hc₀i⟩ := hσP i
  have hH : ∀ y ∈ φ.source, y ∈ Φ.piece c₀.1.1 ↔ ψ₀ (φ y) (σ i) = 0 := by
    intro y hy
    rw [← hc₀i]
    exact hcoord c₀ y hy
  have hpc : p ∈ (Φ.blowUpPieces S m hZ).piece c₀.1.1 :=
    (Φ.blowUpPieces S m hZ).mem_faceSet.mp hp _ hc₀P
  rw [Φ.blowUpPieces_piece_of_lt S m hZ c₀.1.2] at hpc
  have hmem : p ∈ strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)
      (Φ.piece c₀.1.1) ∩ Φ'.source :=
    ⟨hpc, hpΦ⟩
  rw [strictTransform_inter_source_self hφad hΦ' hH] at hmem
  exact (Set.mem_empty_iff_false p).mp hmem

/-- Off the centre the blow-down is onto and the strict transform of a piece is its preimage, so a
common point of old pieces off the centre lifts to a common point of their strict transforms. -/
theorem exists_mem_faceSet_blowUpPieces_of_notMem_centerOf {r : ℕ}
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r) {T : Finset ℕ} (hT : ∀ c ∈ T, c < Φ.nextComp)
    {x : N} (hxT : x ∈ Φ.faceSet T) (hxZ : x ∉ Φ.centerOf S) :
    ∃ p : Manifold.blowUp ψ₀ hZ, Manifold.blowUpπ ψ₀ hZ p = x ∧ p ∈
        (Φ.blowUpPieces S m hZ).faceSet T := by
  obtain ⟨p, hpZ, hpx⟩ := (isBlowUp_blowUpπ ψ₀ hZ).bijOn_compl.surjOn hxZ
  refine ⟨p, hpx, (Φ.blowUpPieces S m hZ).mem_faceSet.mpr fun c hc => ?_⟩
  rw [Φ.blowUpPieces_piece_of_lt S m hZ (hT c hc)]
  have h1 : p ∈ (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.piece c := by
    change Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c
    rw [hpx]
    exact Φ.mem_faceSet.mp hxT c hc
  rcases preimage_subset_strictTransform_union h1 with h | h
  · exact h
  · exact absurd h hpZ

/-- A set of old pieces has a common point after the blow-up if and only if it had one before and
contains no face of the centre. -/
theorem Realizes.faceSet_blowUpPieces_nonempty_iff (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S))
    {T : Finset ℕ} (hT : ∀ c ∈ T, c < Φ.nextComp) :
    ((Φ.blowUpPieces S m hZ).faceSet T).Nonempty ↔
      (Φ.faceSet T).Nonempty ∧ ∀ P ∈ S, ¬ P ⊆ T := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨⟨_, Φ.π_mem_faceSet_of_mem_faceSet_blowUpPieces hZ hT hp⟩, fun P hP hPT => ?_⟩
    have := (Φ.blowUpPieces S m hZ).faceSet_anti hPT hp
    rw [hΦ.faceSet_blowUpPieces_of_mem hF hS hZ hP] at this
    exact this
  · rintro ⟨⟨x, hxT⟩, hnot⟩
    by_cases hxZ : x ∈ Φ.centerOf S
    · obtain ⟨P, hP, hxP⟩ := Φ.mem_centerOf.mp hxZ
      obtain ⟨c₀, hc₀P, hc₀T⟩ := Finset.not_subset.mp (hnot P hP)
      obtain ⟨p, -, hpT, -⟩ := hΦ.exists_origin_of_mem_faceSet hF hS hZ hP hxP hc₀P
      refine ⟨p, (Φ.blowUpPieces S m hZ).mem_faceSet.mpr fun c hc => hpT c (hT c hc) ?_
        (Φ.mem_faceSet.mp hxT c hc)⟩
      rintro rfl
      exact hc₀T hc
    · obtain ⟨p, -, hp⟩ := Φ.exists_mem_faceSet_blowUpPieces_of_notMem_centerOf hZ hT hxT hxZ
      exact ⟨p, hp⟩

/-- The new piece of the face `P` together with old pieces `T₁` has a common point if and only if
`T₁ ∪ P` had one and `P ⊄ T₁`. These are the intersections `E^{i₁} ∩ ⋯ ∩ E^{i_{r-1}} ∩ E^{jℓ}` after
a blow-up in [Kol07, 111, Step 3]. -/
theorem Realizes.faceSet_blowUpPieces_insert_newComp_nonempty_iff (hF : F.IsSnc ψ₀)
    (hΦ : Φ.Realizes F e) (hS : (Φ.toState n m hV).IsCenter S)
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S)) {P : Finset ℕ} (hP : P ∈ S)
    {T₁ : Finset ℕ} (hT₁ : ∀ c ∈ T₁, c < Φ.nextComp) :
    ((Φ.blowUpPieces S m hZ).faceSet (insert (Φ.newComp S P) T₁)).Nonempty ↔
      (Φ.faceSet (T₁ ∪ P)).Nonempty ∧ ¬ P ⊆ T₁ := by
  classical
  have hPn : ∀ c ∈ P, c < Φ.nextComp := fun c hc =>
    Φ.lt_nextComp_of_mem_nerve (subset_nerve_of_isCenter hS hP) hc
  constructor
  · rintro ⟨p, hp⟩
    have hpnew : p ∈ (Φ.blowUpPieces S m hZ).piece (Φ.newComp S P) :=
      (Φ.blowUpPieces S m hZ).mem_faceSet.mp hp _ (Finset.mem_insert_self _ _)
    rw [Φ.blowUpPieces_piece_newComp S m hZ hP] at hpnew
    have hpT₁ : p ∈ (Φ.blowUpPieces S m hZ).faceSet T₁ :=
      (Φ.blowUpPieces S m hZ).faceSet_anti (Finset.subset_insert _ _) hp
    refine ⟨⟨Manifold.blowUpπ ψ₀ hZ p, Φ.mem_faceSet.mpr fun c hc => ?_⟩, fun hPT => ?_⟩
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact Φ.mem_faceSet.mp (Φ.π_mem_faceSet_of_mem_faceSet_blowUpPieces hZ hT₁ hpT₁) c hc
      · exact Φ.mem_faceSet.mp hpnew c hc
    · have := (Φ.blowUpPieces S m hZ).faceSet_anti hPT hpT₁
      rw [hΦ.faceSet_blowUpPieces_of_mem hF hS hZ hP] at this
      exact this
  · rintro ⟨⟨x, hx⟩, hnot⟩
    obtain ⟨c₀, hc₀P, hc₀T⟩ := Finset.not_subset.mp hnot
    have hxP : x ∈ Φ.faceSet P := Φ.faceSet_anti Finset.subset_union_right hx
    have hxT₁ : x ∈ Φ.faceSet T₁ := Φ.faceSet_anti Finset.subset_union_left hx
    obtain ⟨p, hpx, hpT, -⟩ := hΦ.exists_origin_of_mem_faceSet hF hS hZ hP hxP hc₀P
    refine ⟨p, (Φ.blowUpPieces S m hZ).mem_faceSet.mpr fun c hc => ?_⟩
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rw [Φ.blowUpPieces_piece_newComp S m hZ hP]
      change Manifold.blowUpπ ψ₀ hZ p ∈ Φ.faceSet P
      rw [hpx]
      exact hxP
    · refine hpT c (hT₁ c hc) ?_ (Φ.mem_faceSet.mp hxT₁ c hc)
      rintro rfl
      exact hc₀T hc

/-! ### The nerve rule -/

/-- The nerve after the blow-up of a centre of the state is the combinatorial nerve
`Hironaka.Monomial.MonomialState.blowUpNerve` of the nerve: a face of the new family contains at
most one new piece (two new pieces lie over disjoint loci), and the two preceding lemmas identify
the faces without and with a new piece. -/
theorem Realizes.nerve_blowUpPieces (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S)) :
    (Φ.blowUpPieces S m hZ).nerve = MonomialState.blowUpNerve Φ.nerve S (Φ.newComp S) := by
  classical
  ext T
  rw [(Φ.blowUpPieces S m hZ).mem_nerve_iff, MonomialState.mem_blowUpNerve,
    Φ.blowUpPieces_nextComp]
  constructor
  · rintro ⟨hTr, hTne, x', hx'⟩
    have hx'' : x' ∈ (Φ.blowUpPieces S m hZ).faceSet T := (Φ.blowUpPieces S m
      hZ).mem_faceSet.mpr hx'
    set T₀ := T.filter fun c => c < Φ.nextComp with hT₀
    set T₁ := T.filter fun c => ¬ c < Φ.nextComp with hT₁
    have hTsplit : T₀ ∪ T₁ = T := by
      ext c
      simp only [hT₀, hT₁, Finset.mem_union, Finset.mem_filter]
      tauto
    have hT₀n : ∀ c ∈ T₀, c < Φ.nextComp := fun c hc => (Finset.mem_filter.mp hc).2
    -- every new index of `T` is the index allocated to the unique face of `S` through `π x'`
    have hnew : ∀ c ∈ T₁, ∃ P ∈ S, Φ.newComp S P = c ∧ Manifold.blowUpπ ψ₀ hZ x' ∈ Φ.faceSet P :=
        fun c hc =>
      (Φ.mem_blowUpPieces_piece_of_le hZ (not_lt.mp (Finset.mem_filter.mp hc).2)).mp
        (hx' c (Finset.mem_filter.mp hc).1)
    have hT₀' : x' ∈ (Φ.blowUpPieces S m hZ).faceSet T₀ :=
      (Φ.blowUpPieces S m hZ).faceSet_anti (Finset.filter_subset _ _) hx''
    rcases T₁.eq_empty_or_nonempty with hT₁e | ⟨c₀, hc₀⟩
    · -- no new piece: (h2)
      left
      have hTT₀ : T = T₀ := by rw [← hTsplit, hT₁e, Finset.union_empty]
      rw [hTT₀] at hx'' hTne ⊢
      obtain ⟨hb, hnot⟩ := (hΦ.faceSet_blowUpPieces_nonempty_iff hF hS hZ hT₀n).mp ⟨x', hx''⟩
      exact ⟨(Φ.mem_nerve_iff _).mpr ⟨fun c hc => Finset.mem_range.mpr (hT₀n c hc), hTne,
        hb.imp fun x hx => Φ.mem_faceSet.mp hx⟩, hnot⟩
    · -- exactly one new piece, the one of the face `P₀` through `π x'`: (h3)
      right
      obtain ⟨P₀, hP₀, hc₀P, hxP₀⟩ := hnew c₀ hc₀
      have hT₁s : T₁ = {c₀} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hc₀, fun c hc => ?_⟩
        obtain ⟨P, hP, hcP, hxP⟩ := hnew c hc
        rw [← hcP, ← hc₀P, hΦ.eq_of_mem_faceSet_of_isCenter hS hP hP₀ hxP hxP₀]
      have hTeq : T = insert (Φ.newComp S P₀) T₀ := by
        rw [← hTsplit, hT₁s, hc₀P, Finset.union_comm, ← Finset.insert_eq]
      rw [hTeq] at hx''
      obtain ⟨hb, hnot⟩ :=
        (hΦ.faceSet_blowUpPieces_insert_newComp_nonempty_iff hF hS hZ hP₀ hT₀n).mp ⟨x', hx''⟩
      have hP₀n : ∀ c ∈ P₀, c < Φ.nextComp := fun c hc =>
        Φ.lt_nextComp_of_mem_nerve (subset_nerve_of_isCenter hS hP₀) hc
      have hTP : T₀ ∪ P₀ ∈ Φ.nerve := (Φ.mem_nerve_iff _).mpr ⟨fun c hc => Finset.mem_range.mpr
        ((Finset.mem_union.mp hc).elim (hT₀n c) (hP₀n c)),
        (Φ.nonempty_of_mem_nerve (subset_nerve_of_isCenter hS hP₀)).mono Finset.subset_union_right,
        hb.imp fun x hx => Φ.mem_faceSet.mp hx⟩
      refine ⟨P₀, hP₀, T₀, ?_, hTP, fun Q hQ hQT => ?_, hTeq⟩
      · rcases T₀.eq_empty_or_nonempty with h | h
        · exact Or.inl h
        · exact Or.inr (Φ.mem_nerve_of_subset hTP Finset.subset_union_left h)
      · exact hnot (MonomialState.eq_of_isCenter_of_subset (st := Φ.toState n m hV) (S := S) hS hQ
          hP₀ hTP (hQT.trans Finset.subset_union_left) Finset.subset_union_right ▸ hQT)
  · rintro (⟨hTN, hnot⟩ | ⟨P, hP, T₁, -, hTP, hnot, rfl⟩)
    · -- an old face without a face of the centre: (h2)
      obtain ⟨hTr, hTne, hTb⟩ := (Φ.mem_nerve_iff T).mp hTN
      have hTn : ∀ c ∈ T, c < Φ.nextComp := fun c hc => Finset.mem_range.mp (hTr hc)
      obtain ⟨x', hx'⟩ := (hΦ.faceSet_blowUpPieces_nonempty_iff hF hS hZ hTn).mpr
        ⟨hTb.imp fun x hx => Φ.mem_faceSet.mpr hx, hnot⟩
      exact ⟨fun c hc => Finset.mem_range.mpr ((hTn c hc).trans_le (Nat.le_add_right _ _)), hTne,
        x', (Φ.blowUpPieces S m hZ).mem_faceSet.mp hx'⟩
    · -- the new piece of `P` with old pieces `T₁`: (h3)
      obtain ⟨hTr, -, hTb⟩ := (Φ.mem_nerve_iff _).mp hTP
      have hT₁n : ∀ c ∈ T₁, c < Φ.nextComp := fun c hc =>
        Finset.mem_range.mp (hTr (Finset.mem_union_left _ hc))
      obtain ⟨x', hx'⟩ := (hΦ.faceSet_blowUpPieces_insert_newComp_nonempty_iff hF hS hZ hP hT₁n).mpr
        ⟨hTb.imp fun x hx => Φ.mem_faceSet.mpr hx, hnot P hP⟩
      refine ⟨fun c hc => Finset.mem_range.mpr ?_, Finset.insert_nonempty _ _, x',
        (Φ.blowUpPieces S m hZ).mem_faceSet.mp hx'⟩
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact (Φ.toState n m hV).newComp_lt hP
      · exact (hT₁n c hc).trans_le (Nat.le_add_right _ _)

/-! ### The transported family is valid and its state is the transition -/

/-- The family after the blow-up satisfies the invariants of the state: its data are those of the
combinatorial blow-up of the state, whose invariants are proved on the combinatorial model. -/
theorem Realizes.valid_blowUpPieces (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S)) :
    (Φ.blowUpPieces S m hZ).IsValid n m := by
  have h := ((Φ.toState n m hV).blowUp S).valid_self
  change MonomialState.Valid n m _ _ _ (Φ.blowUpPieces S m hZ).nerve
  rw [hΦ.nerve_blowUpPieces hF hS hZ]
  exact h

/-- The state of the family after the blow-up is the combinatorial blow-up of the state. -/
theorem Realizes.toState_blowUpPieces (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S))
    (hV' : (Φ.blowUpPieces S m hZ).IsValid n m) :
    (Φ.blowUpPieces S m hZ).toState n m hV' = (Φ.toState n m hV).blowUp S :=
  Φ.toState_blowUpPieces_of_nerve_eq S m hZ hV hV' (hΦ.nerve_blowUpPieces hF hS hZ)

end Hironaka.Manifold.BMO.PieceFamily
