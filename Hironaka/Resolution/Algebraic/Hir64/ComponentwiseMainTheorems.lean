/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Hir64.MainTheoremIIN
import Hironaka.Resolution.Algebraic.Hir64.ComponentDeletion
import Hironaka.Resolution.Algebraic.Hir64.Corollary1
import Hironaka.Resolution.Algebraic.Hir64.ExtendOpen
import Hironaka.Resolution.Algebraic.Hir64.OpenPieceTransport
import Hironaka.Resolution.Algebraic.Hir64.OrderReductionRound
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.Kol07.Thm36.RelativeDimensionConstancy
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Scheme.BlowUpSequence.ConcatCenters
import Hironaka.Scheme.BlowUpSequence.ConcatClauses
import Hironaka.Scheme.BlowUpSequence.OpenTransport
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.DictionaryOrder
public import Hironaka.Scheme.FiniteType
public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.DisjointIntegralComponents
public import Hironaka.Scheme.Resolution.Defs
import Hironaka.Scheme.Resolution.Basic

/-!
# Hironaka's Main Theorems II and II(N) for every smooth scheme

Hironaka's Main Theorem II [Hir64, Main Theorem II, pp. 142–143] and Main Theorem II(N)
[Hir64, Main Theorem II(N), p. 176] are stated for a non-singular algebraic scheme, whose
irreducible components may have different dimensions; the order reduction of the library
(`exists_orderReductionRound`, Kollár's `BO_d` of [Kol07, Theorem 68] with irreducible centres) runs
on a scheme smooth of a single relative dimension, Kollár's Notation 64. This module derives the
theorems for every scheme smooth and of finite type over the field from that case.

* **One round, by components** (`exists_orderReductionRound_smooth`). The irreducible components
  of a smooth Noetherian scheme are pairwise disjoint, open and closed, and each, as an open
  subscheme, is irreducible and hence smooth of one relative dimension. The round of order `d` is
  run on the component opens meeting the maximal order one after another: on a component the
  Triple round gives a succession with constant order `d` along its centres, with the order of the
  weak transform at most `d` at every stage and less than `d` at the end
  (`exists_orderReductionRound_opens`); it is extended to the whole scheme by the unit ideal on the
  complement (`Hironaka/Resolution/Algebraic/Hir64/ExtendOpen.lean`) and its clauses transport
  along the stage lifts and, over the untouched complement, along the isomorphisms of the stage maps
  (`Hironaka/Resolution/Algebraic/Hir64/OpenPieceTransport.lean`); the successions of the
  components are concatenated. The induction (`exists_orderReductionRound_extend_aux`) runs over
  the closed opens `O` of `X` on the number of components of `X` meeting `O`, and produces the
  succession on any scheme `Z` containing `O` as an open and closed subscheme, so that the
  induction hypothesis applies directly to the last stage of the previous component's round. The
  clauses of Hironaka's theorem are pointwise, on the centres, their supports and the points of the
  stages, and this is what makes the assembly possible.
* **Main Theorem II** (`AlgebraicGeometry.exists_blowUpSequence_ord_weakTransformSeq_lt`, below):
  for `0 < d`, one round of order `d` (`exists_orderReductionRound_smooth`); for `d = 0`, blowing up
  the irreducible components one after another
  (`Hironaka.Sequence.exists_blowUpSequence_isEmpty_last_of_smooth`).
* **Main Theorem II(N)** (`AlgebraicGeometry.exists_blowUpSequence_weakTransformSeq_eq_top`, below):
  induction on the maximal order `d` of `J`, not Hironaka's route (he deduces II(N) from his
  fundamental theorem II₂^N, [Hir64, pp. 176–177]). For `d = 0` the ideal is the unit ideal and the
  empty succession does; otherwise one round of order `d` of the general Main Theorem II has all its
  centres of order exactly `d`, the maximal order of the weak transform at every stage, so clause
  (2) of Main Theorem II(N) holds along it with that `d`; its last stage is again smooth and of
  finite type over the field, the weak transform there has maximal order less than `d`, and the
  induction hypothesis continues with the last weak transform and boundary; the rounds concatenate
  (`isHironakaIIN_concat`). This is the induction of `exists_isHironakaIIN_of_maxOrd_le` on triples,
  run at the level of the main theorem so that the equidimensionality of the triples never enters.
-/

public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry Scheme Scheme.IdealSheafData
  Scheme.BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry Hironaka.Resolution

variable {X Y : Scheme.{u}}

/-! ### Definition 2 at a point -/

/-- Hironaka's Definition 2 [Hir64, Ch. 0, §5, Definition 2] at one point, without a second
subscheme: some regular system of parameters of `𝒪_{X,x}` contains a generator of the ideal of each
irreducible component of `E` through `x`. `IsSncBoundary E` is this at every point. -/
def IsSncBoundaryAt (E : X.IdealSheafData) (x : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), IsLocalRing.IsRegularSystemOfParameters z ∧
    ∀ P ∈ (E.stalkIdeal x).minimalPrimes, ∃ i, P = Ideal.span {z i}

/-- `E` has only normal crossings iff it has only normal crossings at every point (the clause on
the zero ideal sheaf in `IsSncBoundaryWith E ⊥` is satisfied by the empty set of
parameters). -/
theorem isSncBoundary_iff_forall_isSncBoundaryAt (E : X.IdealSheafData) :
    IsSncBoundary E ↔ ∀ x, IsSncBoundaryAt E x := by
  constructor
  · intro h x
    obtain ⟨n, z, hz, hmin, -⟩ := h x (by rw [support_bot]; trivial)
    exact ⟨n, z, hz, hmin⟩
  · intro h x _
    obtain ⟨n, z, hz, hmin⟩ := h x
    exact ⟨n, z, hz, hmin, ∅, by
      rw [stalkIdeal_bot, Finset.coe_empty, Set.image_empty, Ideal.span_empty]⟩

/-- Definition 2 at a point in the range of an open immersion, from Definition 2 at the preimage
for the inverse image. -/
theorem IsSncBoundaryAt.of_comap (u : Y ⟶ X) [IsOpenImmersion u] {E : X.IdealSheafData}
    {y : Y} (h : IsSncBoundaryAt (E.comap u) y) : IsSncBoundaryAt E (u y) := by
  obtain ⟨n, z, hz, hmin⟩ := h
  obtain ⟨n', z', hz', hmin', -⟩ := exists_isRegularSystemOfParameters_apply_of_comap u E ⊥ y
    ⟨n, z, hz, hmin, ∅, by
      rw [comap_bot, stalkIdeal_bot, Finset.coe_empty, Set.image_empty, Ideal.span_empty]⟩
  exact ⟨n', z', hz', hmin'⟩

/-- Definition 2 descends along an open immersion: at the preimage `y` of a point `u y`, for the
inverse image ideal sheaf. -/
theorem IsSncBoundaryAt.comap (u : Y ⟶ X) [IsOpenImmersion u] {E : X.IdealSheafData}
    (y : Y) (h : IsSncBoundaryAt E (u y)) : IsSncBoundaryAt (E.comap u) y := by
  obtain ⟨n, z, hz, hmin⟩ := h
  set e : X.presheaf.stalk (u y) ≃+* Y.presheaf.stalk y := stalkEquivOfIsOpenImmersion u y
    with he_def
  set e' : X.presheaf.stalk (u y) →+* Y.presheaf.stalk y :=
    (e : X.presheaf.stalk (u y) →+* Y.presheaf.stalk y) with he'_def
  have he : (E.comap u).stalkIdeal y = (E.stalkIdeal (u y)).map e' := by
    rw [stalkIdeal_comap, he'_def, he_def, stalkEquivOfIsOpenImmersion_toRingHom]
  refine ⟨n, fun i => e (z i), isRegularSystemOfParameters_comp_ringEquiv e hz, ?_⟩
  intro P hP
  rw [he] at hP
  have hP' : P.comap e' ∈ (E.stalkIdeal (u y)).minimalPrimes := by
    have h1 := Ideal.comap_minimalPrimes_eq_of_surjective (f := e') e.surjective
      ((E.stalkIdeal (u y)).map e')
    rw [Ideal.comap_map_of_bijective e' e.bijective] at h1
    rw [h1]
    exact ⟨P, hP, rfl⟩
  obtain ⟨i, hi⟩ := hmin _ hP'
  refine ⟨i, ?_⟩
  rw [← Ideal.map_comap_of_surjective e' e.surjective P, hi, Ideal.map_span,
    Set.image_singleton]
  rfl

/-! ### Boundaries and smooth sequences along a concatenation -/

/-- Hironaka's boundaries are reduced: `E₀` is, and every later boundary is a vanishing ideal
sheaf. -/
theorem isReduced_subscheme_boundarySeq :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E : X.IdealSheafData) [IsReduced E.subscheme]
      (i : Fin (S.length + 1)), IsReduced (S.boundarySeq E i).subscheme
  | _, nil _, _, h, ⟨0, _⟩ => h
  | _, nil _, _, _, ⟨_ + 1, hj⟩ => (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | _, cons _ _ _, _, h, ⟨0, _⟩ => h
  | _, cons X D rest, E, _, ⟨j + 1, hj⟩ =>
    haveI : IsReduced (E.reducedTransform D).subscheme := isReduced_subscheme_vanishingIdeal _
    isReduced_subscheme_boundarySeq rest (E.reducedTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩

variable {k : Type u} [Field k]

/-- A smooth sequence followed by a sequence smooth over the composite of the first is a smooth
sequence. -/
theorem isSmooth_concat :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (T : BlowUpSequence S.last)
      (f : X ⟶ Spec (.of k)), S.IsSmooth f → T.IsSmooth (S.composite ≫ f) →
      (S.concat T).IsSmooth f
  | _, nil X, T, f, _, hT => by
    intro i
    have h := hT i
    change Smooth (_ ≫ _ ≫ 𝟙 X ≫ f) at h
    rwa [Category.id_comp] at h
  | _, cons X D rest, T, f, hS, hT => by
    obtain ⟨hD, hrest⟩ := (isSmooth_cons_iff f D rest).1 hS
    refine (isSmooth_cons_iff f D (rest.concat T)).2 ⟨hD, isSmooth_concat rest T (D.blowUpπ ≫ f)
      hrest ?_⟩
    intro i
    have h := hT i
    change Smooth (_ ≫ _ ≫ (rest.composite ≫ D.blowUpπ) ≫ f) at h
    rwa [Category.assoc] at h

/-! ### One round on an irreducible open -/

variable [CharZero k]

/-- One round of order reduction of order `d` on an irreducible open subscheme `U` of a smooth
scheme (smooth of one relative dimension, since irreducible), packaged with every clause the
assembly reads off it: the succession is smooth over `k`, its centres are regular and irreducible
with the weak transform of constant order `d` along them, the weak transform has order at most `d`
at every point of every stage and less than `d` at the end, and Hironaka's boundaries have only
normal crossings with the centres and at the end. If the order `d` is not attained on `U` the empty
succession does; otherwise it is the Triple round `exists_orderReductionRound` of
[Kol07, Theorem 68], its clauses read through `IsOrderSeq.ord_eq_of_mem_center`,
`ord_weakTransformSeq_le_ord_stageMap` and `IsOrderSeq.hironakaClauses`. -/
theorem exists_orderReductionRound_opens (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [FiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))]
    (J : X.IdealSheafData) (hJ : IsNonzeroEverywhere J) (d : ℕ) (hd0 : 0 < d)
    (E₀ : X.IdealSheafData) [IsReduced E₀.subscheme] (hE₀ : IsSncBoundary E₀)
    (U : X.Opens) [IrreducibleSpace U] (hle : ∀ y : U, (J.comap U.ι).ord y ≤ d) :
    ∃ S : BlowUpSequence U,
      S.IsSmooth (U.ι ≫ (X ↘ Spec (.of k))) ∧
      (∀ i : Fin S.length,
        IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
      (∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
        (S.weakTransformSeq (J.comap U.ι) i.castSucc).ord x = d) ∧
      (∀ (i : Fin (S.length + 1)) (z : S.stage i),
        (S.weakTransformSeq (J.comap U.ι) i).ord z ≤ d) ∧
      (∀ i : Fin S.length,
        IsSncBoundaryWith (S.boundarySeq (E₀.comap U.ι) i.castSucc) (S.center i)) ∧
      (∀ z : S.last, (S.weakTransformSeq (J.comap U.ι) (Fin.last S.length)).ord z < d) ∧
      IsSncBoundary (S.boundarySeq (E₀.comap U.ι) (Fin.last S.length)) := by
  set f := X ↘ Spec (.of k) with hf
  have hnoeth : IsNoetherian X := f.isNoetherian_of_field
  have hEU : IsSncBoundary (E₀.comap U.ι) := hE₀.comap_of_isOpenImmersion U.ι
  have hEUred : IsReduced (E₀.comap U.ι).subscheme :=
    isReduced_subscheme_comap_of_isOpenImmersion U.ι E₀
  by_cases hatt : ∃ y : U, (J.comap U.ι).ord y = d
  · -- the order `d` is attained on `U`: the Triple round
    let _ : (U : Scheme.{u}).Over (Spec (.of k)) := ⟨U.ι ≫ f⟩
    have hft : FiniteType ((U : Scheme.{u}) ↘ Spec (.of k)) :=
      inferInstanceAs (FiniteType (U.ι ≫ f))
    have hsep : IsSeparated ((U : Scheme.{u}) ↘ Spec (.of k)) :=
      inferInstanceAs (IsSeparated (U.ι ≫ f))
    have hsm : Smooth ((U : Scheme.{u}) ↘ Spec (.of k)) := inferInstanceAs (Smooth (U.ι ≫ f))
    obtain ⟨N, hN⟩ := exists_smoothOfRelativeDimension_of_irreducibleSpace (U.ι ≫ f)
    have hN' : SmoothOfRelativeDimension N ((U : Scheme.{u}) ↘ Spec (.of k)) := hN
    have hnoethU : IsNoetherian (U : Scheme.{u}) :=
      ((U : Scheme.{u}) ↘ Spec (.of k)).isNoetherian_of_field
    have hsnc : (E₀.comap U.ι).componentFamily.IsSnc :=
      (isSncBoundary_iff_isSnc_componentFamily ((U : Scheme.{u}) ↘ Spec (.of k))
        (E₀.comap U.ι)).mp hEU
    let T : Triple k :=
      { X := .of (U : Scheme.{u})
        smoothOfRelativeDimension := ⟨N, hN'⟩
        I := J.comap U.ι
        isNonzeroEverywhere := isNonzeroEverywhere_comap_of_flat U.ι hJ
        E := (E₀.comap U.ι).componentFamily
        isSnc := hsnc }
    have hTI : T.I.maxOrd = d := by
      apply le_antisymm
      · rw [Scheme.IdealSheafData.maxOrd_le_iff]
        exact hle
      · obtain ⟨y, hy⟩ := hatt
        rw [← hy]
        exact Scheme.IdealSheafData.le_maxOrd T.I y
    obtain ⟨S, hS, hirr, hlt⟩ := exists_orderReductionRound T d hTI hd0
    have hsmS : S.IsSmooth (U.ι ≫ f) := hS.1
    have hcen : ∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
        (S.weakTransformSeq (J.comap U.ι) i.castSucc).ord x = d := fun i x hx =>
      IsOrderSeq.ord_eq_of_mem_center ((U : Scheme.{u}) ↘ Spec (.of k)) N hS hTI i hx
    have hpt : ∀ (j : ℕ) (hj : j < S.length), ∃ c : ℕ, ∀ y ∈ (S.center ⟨j, hj⟩).support,
        (S.weakTransformSeq (J.comap U.ι) ⟨j, Nat.lt_succ_of_lt hj⟩).ord y = c :=
      fun j hj => ⟨d, fun y hy => hcen ⟨j, hj⟩ y hy⟩
    have hE : T.E.unionIdeal = E₀.comap U.ι := unionIdeal_componentFamily_of_isReduced _
    obtain ⟨-, h3, h4⟩ := IsOrderSeq.hironakaClauses T hS
    rw [hE] at h3 h4
    refine ⟨S, hsmS, hirr, hcen, fun i z => ?_, h3, fun z => ?_, h4⟩
    · calc (S.weakTransformSeq (J.comap U.ι) i).ord z
          ≤ (J.comap U.ι).ord (S.stageMap i z) :=
            ord_weakTransformSeq_le_ord_stageMap (U.ι ≫ f) N S hsmS (J.comap U.ι) hpt i z
        _ ≤ d := hle _
    · exact lt_of_le_of_lt (Scheme.IdealSheafData.le_maxOrd _ z) hlt
  · -- the order `d` is not attained on `U`: the empty succession
    push Not at hatt
    refine ⟨nil U, isSmooth_nil _, fun i => i.elim0, fun i => i.elim0, fun i z => ?_,
      fun i => i.elim0, fun z => ?_, hEU⟩
    · exact hle z
    · exact lt_of_le_of_ne (hle z) (hatt z)

/-! ### The clauses of one round, relative to a set over which the centres lie -/

/-- The clauses of one round of order reduction of order `d` for `(J, E)` on `Z`, read on the
centres, on the points of the stages, and, for the final clauses, on the points of the last stage
lying over the set `R ⊆ Z` over which the centres lie: the centres are regular and irreducible
(Main Theorem II (i)) and lie over `R`; the weak transform has order `d` along them (ii) and order
at most `d` at every point of every stage; the boundaries have only normal crossings with them
(iii); the succession is smooth over `k`; and at the points of the last stage over `R` the weak
transform has order less than `d` and the boundary has only normal crossings (iv). -/
structure IsOrderRound {Z : Scheme.{u}} (S : BlowUpSequence Z) (J E : Z.IdealSheafData) (d : ℕ)
    (R : Set Z) (g : Z ⟶ Spec (.of k)) : Prop where
  center : ∀ i : Fin S.length,
    IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme
  ord_center : ∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
    (S.weakTransformSeq J i.castSucc).ord x = d
  ord_le : ∀ (i : Fin (S.length + 1)) (z : S.stage i), (S.weakTransformSeq J i).ord z ≤ d
  nc : ∀ i : Fin S.length, IsSncBoundaryWith (S.boundarySeq E i.castSucc) (S.center i)
  mem : ∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
    S.stageMap i.castSucc x ∈ R
  isSmooth : S.IsSmooth g
  ord_last : ∀ z : S.last, S.composite z ∈ R → (S.weakTransformSeq J (Fin.last S.length)).ord z < d
  nc_last : ∀ z : S.last, S.composite z ∈ R →
    IsSncBoundaryAt (S.boundarySeq E (Fin.last S.length)) z

omit [CharZero k] in
/-- The empty succession is a round over the empty set: only the order bound at the single stage
is to be checked. -/
theorem isOrderRound_nil {Z : Scheme.{u}} (J E : Z.IdealSheafData) (d : ℕ)
    (g : Z ⟶ Spec (.of k)) (hle : ∀ z : Z, J.ord z ≤ d) : IsOrderRound (nil Z) J E d ∅ g where
  center i := i.elim0
  ord_center i := i.elim0
  ord_le _ z := hle z
  nc i := i.elim0
  mem i := i.elim0
  isSmooth := isSmooth_nil g
  ord_last _ h := h.elim
  nc_last _ h := h.elim

omit [CharZero k] in
/-- Two rounds concatenate: a round `S₁` on `Z` over `R₁` followed by a round `S₂` on its last
stage, for the last weak transform and boundary, over `R₂`, is a round over any `R ⊇ R₁` such that
`R₂` lies over `R` and every point of the last stage of `S₁` over `R` is in `R₂` or over `R₁`. The
clauses on the centres pass through `forall_center_concat`, `forall_stage_concat` and
`forall_center_concat_mem`; the final clauses at a point over `R₂` are those of `S₂`, and at a
point not over `R₂` the data of `S₂` is the inverse image of the last data of `S₁`
(`ord_weakTransformSeq_of_stageMap_notMem`, `boundarySeq_comap_ι_preimage`), for which the final
clauses of `S₁` hold. -/
theorem IsOrderRound.concat {Z : Scheme.{u}} [IsNoetherian Z] (S₁ : BlowUpSequence Z)
    (S₂ : BlowUpSequence S₁.last) {J E : Z.IdealSheafData} [IsReduced E.subscheme] {d : ℕ}
    {R₁ : Set Z} {R₂ : Set S₁.last} {R : Set Z} {g : Z ⟶ Spec (.of k)}
    (h₁ : IsOrderRound S₁ J E d R₁ g)
    (h₂ : IsOrderRound S₂ (S₁.weakTransformSeq J (Fin.last _)) (S₁.boundarySeq E (Fin.last _)) d
      R₂ (S₁.composite ≫ g))
    (hR₂c : IsClosed R₂) (hR₁ : R₁ ⊆ R) (hR₂ : ∀ z₁ ∈ R₂, S₁.composite z₁ ∈ R)
    (hcover : ∀ z₁ : S₁.last, S₁.composite z₁ ∈ R → z₁ ∈ R₂ ∨ S₁.composite z₁ ∈ R₁) :
    IsOrderRound (S₁.concat S₂) J E d R g := by
  have hnoeth₁ : IsNoetherian S₁.last := isNoetherian_stage S₁ (Fin.last _)
  have hEred : IsReduced (S₁.boundarySeq E (Fin.last _)).subscheme :=
    isReduced_subscheme_boundarySeq S₁ E _
  have hlast := last_concat S₁ S₂
  have hcomp : ∀ z : (S₁.concat S₂).last, (S₁.concat S₂).composite z =
      S₁.composite (S₂.composite (eqToHom hlast z)) := fun z => by
    rw [composite_concat, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  -- over the complement of `R₂` the round `S₂` changes nothing
  set W : S₁.last.Opens := ⟨R₂ᶜ, hR₂c.isOpen_compl⟩ with hW
  have hmemW : ∀ (i : Fin S₂.length) (y : S₂.stage i.castSucc), y ∈ (S₂.center i).support →
      S₂.stageMap i.castSucc y ∉ W := fun i y hy hmem => hmem (h₂.mem i y hy)
  refine ⟨forall_center_concat (fun D => IsRegular D.subscheme ∧ IrreducibleSpace D.subscheme)
      S₁ S₂ h₁.center h₂.center, ?_, ?_, ?_, ?_, isSmooth_concat S₁ S₂ g h₁.isSmooth h₂.isSmooth,
      ?_, ?_⟩
  · exact forall_stage_concat (fun D J' _ => ∀ x ∈ D.support, J'.ord x = d) S₁ S₂ J E
      h₁.ord_center h₂.ord_center
  · rintro ⟨j, hj⟩ z
    rcases Nat.lt_or_ge j (S₁.concat S₂).length with hi | hi
    · exact forall_stage_concat (fun _ J' _ => ∀ z, J'.ord z ≤ d) S₁ S₂ J E
        (fun i => h₁.ord_le i.castSucc) (fun i => h₂.ord_le i.castSucc) ⟨j, hi⟩ z
    · obtain rfl : j = (S₁.concat S₂).length := le_antisymm (Nat.lt_succ_iff.mp hj) hi
      change ((S₁.concat S₂).weakTransformSeq J (Fin.last _)).ord z ≤ d
      rw [weakTransformSeq_concat_last]
      exact (ord_comap_of_isIso _ (eqToHom hlast) z).trans_le (h₂.ord_le (Fin.last _) _)
  · exact forall_stage_concat (fun D _ E' => IsSncBoundaryWith E' D) S₁ S₂ J E h₁.nc h₂.nc
  · exact forall_center_concat_mem S₁ S₂ R (fun i x hx => hR₁ (h₁.mem i x hx))
      (fun i x hx => hR₂ _ (h₂.mem i x hx))
  · intro z hz
    rw [hcomp] at hz
    rw [weakTransformSeq_concat_last]
    refine (ord_comap_of_isIso _ (eqToHom hlast) z).trans_lt ?_
    by_cases hz₂ : S₂.composite (eqToHom hlast z) ∈ R₂
    · exact h₂.ord_last _ hz₂
    · have h := (hcover _ hz).resolve_left hz₂
      exact (ord_weakTransformSeq_of_stageMap_notMem S₂ _ R₂ h₂.mem (Fin.last _) _ hz₂).trans_lt
        (h₁.ord_last _ h)
  · intro z hz
    rw [hcomp] at hz
    rw [boundarySeq_concat_last]
    refine IsSncBoundaryAt.comap (eqToHom hlast) z ?_
    by_cases hz₂ : S₂.composite (eqToHom hlast z) ∈ R₂
    · exact h₂.nc_last _ hz₂
    · have h := (hcover _ hz).resolve_left hz₂
      have hz' : eqToHom hlast z ∈
          ((S₂.stageMap (Fin.last _) ⁻¹ᵁ W : S₂.last.Opens) : Set S₂.last) := hz₂
      rw [← Scheme.Opens.range_ι] at hz'
      obtain ⟨q, hq⟩ := hz'
      rw [← hq]
      refine IsSncBoundaryAt.of_comap _ ?_
      erw [@boundarySeq_comap_ι_preimage _ S₂ _ hEred W hmemW (Fin.last _)]
      have hoi := isOpenImmersion_ι_preimage_comp_stageMap S₂ W hmemW (Fin.last _)
      refine @IsSncBoundaryAt.comap _ _ _ hoi _ q ?_
      erw [Scheme.Hom.comp_apply, hq]
      exact h₁.nc_last _ h

/-! ### The round on a component, extended to an ambient scheme -/

/-- The image of the range of the inclusion `U ⟶ O` of opens under an open immersion `w` with
closed range is closed when `U` is closed in `X`: the range of the inclusion is the preimage of `U`
under `O.ι`, and `w` is a closed embedding. -/
theorem isClosed_range_homOfLE_comp {O U : X.Opens} (hUO : U ≤ O) (hUc : IsClosed (U : Set X))
    {Z : Scheme.{u}} (w : (O : Scheme.{u}) ⟶ Z) [IsOpenImmersion w] (hw : IsClosed (Set.range w)) :
    IsClosed (Set.range (X.homOfLE hUO ≫ w)) := by
  have hA : Set.range (X.homOfLE hUO) = O.ι ⁻¹' (U : Set X) := by
    ext o
    constructor
    · rintro ⟨x, rfl⟩
      change O.ι (X.homOfLE hUO x) ∈ (U : Set X)
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, ← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    · intro ho
      have : O.ι o ∈ Set.range U.ι := by
        rw [Scheme.Opens.range_ι]
        exact ho
      obtain ⟨x, hx⟩ := this
      refine ⟨x, O.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, hx]
  have hAc : IsClosed (Set.range (X.homOfLE hUO)) := by
    rw [hA]
    exact hUc.preimage O.ι.continuous
  have hrange : Set.range (X.homOfLE hUO ≫ w) = w '' Set.range (X.homOfLE hUO) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨X.homOfLE hUO x, ⟨x, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩
  rw [hrange]
  exact isClosed_image_of_isOpenImmersion w hAc hw subset_rfl fun _ ⟨a, _, ha⟩ => ⟨a, ha⟩

/-- One round of order reduction on an irreducible open subscheme `U` of `X`, closed in `X` and
contained in the open `O`, carried out inside an ambient scheme `Z` containing `O` as an open
subscheme with closed range along `w`: the round of `exists_orderReductionRound_opens` on `U` is
extended across the complement (`exists_extend_of_isOpenImmersion`), and its clauses are read on
`Z` for the ideal `J_Z` and boundary `E_Z` restricting to `J` and `E₀` on `O`. Along the stage
lifts of the pull-back (which contain the centres) the weak transforms and boundaries are the
pull-backs (`weakTransformSeq_pullback_of_centersInRange`, `boundarySeq_pullback`), so the clauses
on the centres, the order bound `≤ d` at points over `U` and the final clauses at points over `U`
transport; off the range of the lifts the weak transform has the order of `J_Z` at the image
(`ord_weakTransformSeq_of_stageMap_notMem`), which is `≤ d` by hypothesis. -/
theorem exists_orderReductionRound_extend (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [FiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))]
    (J : X.IdealSheafData) (hJ : IsNonzeroEverywhere J) (d : ℕ) (hd0 : 0 < d)
    (E₀ : X.IdealSheafData) [IsReduced E₀.subscheme] (hE₀ : IsSncBoundary E₀)
    (U O : X.Opens) (hUO : U ≤ O) (hUc : IsClosed (U : Set X)) [IrreducibleSpace U]
    {Z : Scheme.{u}} [IsNoetherian Z] (w : (O : Scheme.{u}) ⟶ Z) [IsOpenImmersion w]
    (hw : IsClosed (Set.range w)) (g : Z ⟶ Spec (.of k)) (hg : w ≫ g = O.ι ≫ (X ↘ Spec (.of k)))
    (J_Z E_Z : Z.IdealSheafData) (hJZ : J_Z.comap w = J.comap O.ι)
    (hEZ : E_Z.comap w = E₀.comap O.ι) [IsReduced E_Z.subscheme] (hle : ∀ z : Z, J_Z.ord z ≤ d) :
    ∃ S : BlowUpSequence Z, IsOrderRound S J_Z E_Z d (Set.range (X.homOfLE hUO ≫ w)) g := by
  set f := X ↘ Spec (.of k) with hf
  set v : (U : Scheme.{u}) ⟶ Z := X.homOfLE hUO ≫ w with hv
  have hvι : X.homOfLE hUO ≫ O.ι = U.ι := Scheme.homOfLE_ι X hUO
  have hvg : v ≫ g = U.ι ≫ f := by rw [hv, Category.assoc, hg, ← Category.assoc, hvι]
  have hJv : J_Z.comap v = J.comap U.ι := by rw [hv, comap_comp, hJZ, ← comap_comp, hvι]
  have hEv : E_Z.comap v = E₀.comap U.ι := by rw [hv, comap_comp, hEZ, ← comap_comp, hvι]
  have hleU : ∀ y : (U : Scheme.{u}), (J.comap U.ι).ord y ≤ d := fun y => by
    rw [← hJv, ord_comap_of_isOpenImmersion]
    exact hle _
  obtain ⟨S', hsm', hirr', hcen', hle', hnc', hlt', hnc'last⟩ :=
    exists_orderReductionRound_opens (k := k) X J hJ d hd0 E₀ hE₀ U hleU
  -- the extension across the complement of `U`
  set C : Set Z := Set.range v with hC
  have hCclosed : IsClosed C := isClosed_range_homOfLE_comp hUO hUc w hw
  have hcent : ∀ (i : Fin S'.length) (y : S'.stage i.castSucc), y ∈ (S'.center i).support →
      v (S'.stageMap i.castSucc y) ∈ C := fun _ _ _ => ⟨_, rfl⟩
  obtain ⟨S, hpull, hcentC⟩ := exists_extend_of_isOpenImmersion v S' C hCclosed subset_rfl hcent
  subst hpull
  have hCR : S.CentersInRange v := fun i y hy => by
    rw [range_pullbackStageHom]
    exact hcentC i y hy
  have hreg := forall_isRegular_center_of_pullback v S hCR fun i => (hirr' i).1
  have hirrS := forall_irreducibleSpace_center_of_pullback v S hCR fun i => (hirr' i).2
  have hsmS : S.IsSmooth g := isSmooth_of_isSmooth_pullback v S g hCR (by rw [hvg]; exact hsm')
  have hwt : ∀ i : Fin (S.length + 1),
      (S.pullback v).weakTransformSeq (J.comap U.ι) (S.pullbackStageIdx v i) =
        (S.weakTransformSeq J_Z i).comap (S.pullbackStageHom v i) := fun i => by
    rw [← hJv]
    exact weakTransformSeq_pullback_of_centersInRange S v hCR J_Z i
  have hbd : ∀ i : Fin (S.length + 1),
      (S.pullback v).boundarySeq (E₀.comap U.ι) (S.pullbackStageIdx v i) =
        (S.boundarySeq E_Z i).comap (S.pullbackStageHom v i) := fun i => by
    rw [← hEv]
    exact boundarySeq_pullback S v E_Z i
  -- the clauses on the centres
  have hb : ∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
      (S.weakTransformSeq J_Z i.castSucc).ord x = d := by
    rintro ⟨i, hi⟩ x hx
    obtain ⟨y, rfl⟩ := hCR ⟨i, hi⟩ hx
    have hy : y ∈ ((S.pullback v).center (S.pullbackCenterIdx v ⟨i, hi⟩)).support := by
      rw [center_pullback_mk S v i hi]
      exact (mem_support_comap_iff_apply _ _ _).mpr hx
    have := isOpenImmersion_pullbackStageHom S v (Fin.castSucc ⟨i, hi⟩)
    rw [← ord_comap_of_isOpenImmersion, ← hwt]
    exact hcen' (S.pullbackCenterIdx v ⟨i, hi⟩) y hy
  have hc : ∀ (i : Fin (S.length + 1)) (z : S.stage i), (S.weakTransformSeq J_Z i).ord z ≤ d :=
    fun i z => by
    by_cases hz : z ∈ Set.range (S.pullbackStageHom v i)
    · obtain ⟨y, rfl⟩ := hz
      have := isOpenImmersion_pullbackStageHom S v i
      rw [← ord_comap_of_isOpenImmersion, ← hwt]
      exact hle' _ y
    · have hnot : S.stageMap i z ∉ C := fun h => hz (by rw [range_pullbackStageHom]; exact h)
      rw [ord_weakTransformSeq_of_stageMap_notMem S J_Z C hcentC i z hnot]
      exact hle _
  have hd : ∀ i : Fin S.length,
      IsSncBoundaryWith (S.boundarySeq E_Z i.castSucc) (S.center i) := fun i => by
    have := isOpenImmersion_pullbackStageHom S v i.castSucc
    refine isSncBoundaryWith_of_comap_of_isOpenImmersion (S.pullbackStageHom v i.castSucc)
      (hCR i) ?_
    rw [← hbd, ← center_pullback]
    exact hnc' (S.pullbackCenterIdx v i)
  -- the last stage over `U`
  have hidx : S.pullbackStageIdx v (Fin.last S.length) = Fin.last _ := pullbackStageIdx_last S v
  have hf1 : ∀ z : S.last, S.composite z ∈ C →
      (S.weakTransformSeq J_Z (Fin.last S.length)).ord z < d := fun z hz => by
    have hz' : z ∈ Set.range (S.pullbackStageHom v (Fin.last _)) := by
      rw [range_pullbackStageHom]
      exact hz
    obtain ⟨y, rfl⟩ := hz'
    have := isOpenImmersion_pullbackStageHom S v (Fin.last _)
    rw [← ord_comap_of_isOpenImmersion, ← hwt]
    have hlt'' : ∀ y' : (S.pullback v).stage (S.pullbackStageIdx v (Fin.last _)),
        ((S.pullback v).weakTransformSeq (J.comap U.ι) (S.pullbackStageIdx v (Fin.last _))).ord y' <
          d := by
      rw [hidx]
      exact hlt'
    exact hlt'' y
  have hf2 : ∀ z : S.last, S.composite z ∈ C →
      IsSncBoundaryAt (S.boundarySeq E_Z (Fin.last S.length)) z := fun z hz => by
    have hz' : z ∈ Set.range (S.pullbackStageHom v (Fin.last _)) := by
      rw [range_pullbackStageHom]
      exact hz
    obtain ⟨y, rfl⟩ := hz'
    have := isOpenImmersion_pullbackStageHom S v (Fin.last _)
    refine IsSncBoundaryAt.of_comap _ ?_
    rw [← hbd]
    have hnc'' : IsSncBoundary
        ((S.pullback v).boundarySeq (E₀.comap U.ι) (S.pullbackStageIdx v (Fin.last _))) := by
      rw [hidx]
      exact hnc'last
    exact (isSncBoundary_iff_forall_isSncBoundaryAt _).mp hnc'' y
  exact ⟨S, ⟨fun i => ⟨hreg i, hirrS i⟩, hb, hc, hd, hcentC, hsmS, hf1, hf2⟩⟩

/-- The untouched piece embeds into the last stage. Let `U` and `V` be disjoint closed opens of
`X` inside the open `O`, `w : O ⟶ Z` an open immersion with closed range, and `S₁` a succession
on `Z` whose centres lie over `w(U)`. Then `V` embeds into the last stage of `S₁` by an open
immersion `w'` over `w`, with range the preimage of `w(V)` under the composite, closed, along
which the last weak transform of any `J_Z` and the last boundary of any reduced `E_Z` restrict to
the restrictions of `J_Z` and `E_Z` to `V` (`weakTransformSeq_comap_ι_preimage`,
`boundarySeq_comap_ι_preimage`): `w'` is the lift of `V ⟶ Z` along the open immersion of the
untouched open `Z ∖ w(U)` into `Z` through the last stage (`isIso_stageMap_restrict`). -/
theorem exists_untouched_embedding {U V O : X.Opens} (hUO : U ≤ O) (hVO : V ≤ O)
    (hUV : ∀ x : X, x ∈ U → x ∈ V → False) (hUc : IsClosed (U : Set X))
    (hVc : IsClosed (V : Set X)) {Z : Scheme.{u}} [IsNoetherian Z] (w : (O : Scheme.{u}) ⟶ Z)
    [IsOpenImmersion w] (hw : IsClosed (Set.range w)) (S₁ : BlowUpSequence Z)
    (hmem : ∀ (i : Fin S₁.length) (x : S₁.stage i.castSucc), x ∈ (S₁.center i).support →
      S₁.stageMap i.castSucc x ∈ Set.range (X.homOfLE hUO ≫ w)) :
    ∃ w' : (V : Scheme.{u}) ⟶ S₁.stage (Fin.last S₁.length), IsOpenImmersion w' ∧
      w' ≫ S₁.stageMap (Fin.last S₁.length) = X.homOfLE hVO ≫ w ∧
      Set.range w' = S₁.stageMap (Fin.last S₁.length) ⁻¹' Set.range (X.homOfLE hVO ≫ w) ∧
      IsClosed (Set.range w') ∧
      (∀ J_Z : Z.IdealSheafData, (S₁.weakTransformSeq J_Z (Fin.last S₁.length)).comap w' =
        (J_Z.comap w).comap (X.homOfLE hVO)) ∧
      ∀ (E_Z : Z.IdealSheafData) [IsReduced E_Z.subscheme],
        (S₁.boundarySeq E_Z (Fin.last S₁.length)).comap w' =
          (E_Z.comap w).comap (X.homOfLE hVO) := by
  have hmemO : ∀ (O : X.Opens) (o : (O : Scheme.{u})), O.ι o ∈ (O : Set X) := fun O o => by
    rw [← Scheme.Opens.range_ι]
    exact ⟨o, rfl⟩
  set R₁ : Set Z := Set.range (X.homOfLE hUO ≫ w) with hR₁
  have hR₁c : IsClosed R₁ := isClosed_range_homOfLE_comp hUO hUc w hw
  set W : Z.Opens := ⟨R₁ᶜ, hR₁c.isOpen_compl⟩ with hW
  have hmemW : ∀ (i : Fin S₁.length) (y : S₁.stage i.castSucc), y ∈ (S₁.center i).support →
      S₁.stageMap i.castSucc y ∉ W := fun i y hy hm => hm (hmem i y hy)
  have hstageIso : IsIso (S₁.stageMap (Fin.last S₁.length) ∣_ W) :=
    isIso_stageMap_restrict S₁ W hmemW _
  have hoi := isOpenImmersion_ι_preimage_comp_stageMap S₁ W hmemW (Fin.last S₁.length)
  -- `V` maps into the untouched open `W`, hence lifts into the last stage
  have hVW : ∀ x : (V : Scheme.{u}), (X.homOfLE hVO ≫ w) x ∈ W := fun x => by
    change (X.homOfLE hVO ≫ w) x ∉ R₁
    rintro ⟨y, hy⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hy
    have h1 : X.homOfLE hUO y = X.homOfLE hVO x := w.isOpenEmbedding.injective hy
    have h2 : U.ι y = V.ι x := by
      rw [← Scheme.homOfLE_ι X hUO, ← Scheme.homOfLE_ι X hVO, Scheme.Hom.comp_apply,
        Scheme.Hom.comp_apply, h1]
    have hV : V.ι x ∈ (V : Set X) := hmemO V x
    rw [← h2] at hV
    exact hUV _ (hmemO U y) hV
  have hlift : Set.range (X.homOfLE hVO ≫ w) ⊆
      Set.range ((S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι ≫
        S₁.stageMap (Fin.last S₁.length)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨q, hq⟩ := (S₁.stageMap (Fin.last S₁.length) ∣_ W).homeomorph.surjective ⟨_, hVW x⟩
    refine ⟨q, ?_⟩
    rw [Scheme.Hom.homeomorph_apply] at hq
    rw [← morphismRestrict_ι, Scheme.Hom.comp_apply, hq, Scheme.Opens.ι_apply]
  set w' : (V : Scheme.{u}) ⟶ S₁.stage (Fin.last S₁.length) :=
    IsOpenImmersion.lift ((S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι ≫
        S₁.stageMap (Fin.last S₁.length)) (X.homOfLE hVO ≫ w) hlift ≫
      (S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι with hw'
  have hlift_oi : IsOpenImmersion (IsOpenImmersion.lift
      ((S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι ≫ S₁.stageMap (Fin.last S₁.length))
      (X.homOfLE hVO ≫ w) hlift) := by
    have : IsOpenImmersion (IsOpenImmersion.lift
        ((S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι ≫ S₁.stageMap (Fin.last S₁.length))
        (X.homOfLE hVO ≫ w) hlift ≫
        ((S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι ≫ S₁.stageMap (Fin.last S₁.length))) := by
      rw [IsOpenImmersion.lift_fac]
      infer_instance
    exact IsOpenImmersion.of_comp _
      ((S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι ≫ S₁.stageMap (Fin.last S₁.length))
  have hw'oi : IsOpenImmersion w' := by
    rw [hw']
    infer_instance
  have hw'comp : w' ≫ S₁.stageMap (Fin.last S₁.length) = X.homOfLE hVO ≫ w := by
    rw [hw', Category.assoc]
    exact IsOpenImmersion.lift_fac _ _ _
  have hw'range : Set.range w' =
      S₁.stageMap (Fin.last S₁.length) ⁻¹' Set.range (X.homOfLE hVO ≫ w) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [← Scheme.Hom.comp_apply, hw'comp]⟩
    · rintro ⟨x, hx⟩
      have hzW : z ∈ Set.range (S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι := by
        rw [Scheme.Opens.range_ι]
        change S₁.stageMap (Fin.last S₁.length) z ∈ W
        rw [← hx]
        exact hVW x
      obtain ⟨q, rfl⟩ := hzW
      refine ⟨x, ?_⟩
      have h1 : IsOpenImmersion.lift ((S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι ≫
          S₁.stageMap (Fin.last S₁.length)) (X.homOfLE hVO ≫ w) hlift x = q := by
        apply ((S₁.stageMap (Fin.last S₁.length) ⁻¹ᵁ W).ι ≫
          S₁.stageMap (Fin.last S₁.length)).isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac, hx]
        rfl
      rw [hw', Scheme.Hom.comp_apply, h1]
  have hw'c : IsClosed (Set.range w') := by
    rw [hw'range]
    exact (isClosed_range_homOfLE_comp hVO hVc w hw).preimage
      (S₁.stageMap (Fin.last S₁.length)).continuous
  refine ⟨w', hw'oi, hw'comp, hw'range, hw'c, fun J_Z => ?_, fun E_Z _ => ?_⟩
  · rw [hw', comap_comp]
    erw [weakTransformSeq_comap_ι_preimage S₁ J_Z W hmemW (Fin.last S₁.length)]
    rw [← comap_comp, ← Category.assoc]
    change J_Z.comap (w' ≫ S₁.stageMap (Fin.last S₁.length)) = _
    rw [hw'comp, comap_comp]
  · rw [hw', comap_comp]
    erw [boundarySeq_comap_ι_preimage S₁ E_Z W hmemW (Fin.last S₁.length)]
    rw [← comap_comp, ← Category.assoc]
    change E_Z.comap (w' ≫ S₁.stageMap (Fin.last S₁.length)) = _
    rw [hw'comp, comap_comp]

/-- The two pieces of a closed open `O` of the smooth `X` at a point `o` of `O`: `U = C ∩ O` for the
irreducible component `C` of `X` through `o`, and `V = O ∖ C`. They are disjoint closed opens of `X`
covering `O`, `U` is integral (a nonempty open of the integral component open
`irreducibleComponentOpen C`, the component itself since the components of the regular `X` are
pairwise disjoint), and `V` meets one component of `X` fewer than `O` does. -/
theorem exists_disjoint_pieces (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [FiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))]
    (O : X.Opens) (hOc : IsClosed (O : Set X)) (o : (O : Scheme.{u})) :
    ∃ (U V : X.Opens) (hUO : U ≤ O) (hVO : V ≤ O),
      (∀ x : X, x ∈ U → x ∈ V → False) ∧ IsClosed (U : Set X) ∧ IsClosed (V : Set X) ∧
      IsIntegral (U : Scheme.{u}) ∧
      (∀ o' : (O : Scheme.{u}), (∃ y : (U : Scheme.{u}), X.homOfLE hUO y = o') ∨
        ∃ x : (V : Scheme.{u}), X.homOfLE hVO x = o') ∧
      {C ∈ irreducibleComponents X | (C ∩ (V : Set X)).Nonempty}.ncard + 1 ≤
        {C ∈ irreducibleComponents X | (C ∩ (O : Set X)).Nonempty}.ncard := by
  set f := X ↘ Spec (.of k) with hf
  have hnoeth : IsNoetherian X := f.isNoetherian_of_field
  have hreg : IsRegular X := isRegular_of_smooth f
  have hX : HasDisjointIntegralComponents X := hasDisjointIntegralComponents_of_isRegular
  have hfin : {C ∈ irreducibleComponents X | (C ∩ (O : Set X)).Nonempty}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1
  have hmemO : ∀ (O : X.Opens) (o : (O : Scheme.{u})), O.ι o ∈ (O : Set X) := fun O o => by
    rw [← Scheme.Opens.range_ι]
    exact ⟨o, rfl⟩
  obtain ⟨C, hC, hoC⟩ : ∃ C ∈ irreducibleComponents X, O.ι o ∈ C :=
    ⟨_, irreducibleComponent_mem_irreducibleComponents (O.ι o), mem_irreducibleComponent⟩
  set U₀ : X.Opens := X.irreducibleComponentOpen C with hU₀def
  have hU₀ : (U₀ : Set X) = C := hX.irreducibleComponentOpen_eq C hC
  have hU₀c : IsClosed (U₀ : Set X) := by
    rw [hU₀]
    exact isClosed_of_mem_irreducibleComponents C hC
  have hU₀int : IsIntegral (U₀ : Scheme.{u}) := isIntegral_irreducibleComponentOpen hX C hC
  set U : X.Opens := U₀ ⊓ O with hUdef
  set V : X.Opens := ⟨(U₀ : Set X)ᶜ, hU₀c.isOpen_compl⟩ ⊓ O with hVdef
  have hUO : U ≤ O := inf_le_right
  have hVO : V ≤ O := inf_le_right
  have hUc : IsClosed (U : Set X) := by
    rw [hUdef, Opens.coe_inf]
    exact hU₀c.inter hOc
  have hVc : IsClosed (V : Set X) := by
    rw [hVdef, Opens.coe_inf]
    exact U₀.isOpen.isClosed_compl.inter hOc
  have hoU₀ : O.ι o ∈ U₀ := by
    change O.ι o ∈ (U₀ : Set X)
    rw [hU₀]
    exact hoC
  have hUne : Nonempty (U : Scheme.{u}) := ⟨⟨O.ι o, Opens.mem_inf.mpr ⟨hoU₀, hmemO O o⟩⟩⟩
  have hUint : IsIntegral (U : Scheme.{u}) :=
    isIntegral_of_isOpenImmersion (X.homOfLE (inf_le_left : U ≤ U₀))
  refine ⟨U, V, hUO, hVO, fun x hxU hxV =>
    ((Opens.mem_inf.mp hxV).1 : x ∉ (U₀ : Set X)) (Opens.mem_inf.mp hxU).1, hUc, hVc, hUint,
    fun o' => ?_, ?_⟩
  · by_cases hoU : O.ι o' ∈ U₀
    · left
      refine ⟨(⟨O.ι o', Opens.mem_inf.mpr ⟨hoU, hmemO O o'⟩⟩ : ↥(U : Scheme.{u})), ?_⟩
      apply Subtype.ext
      rw [Scheme.homOfLE_apply]
      rfl
    · right
      refine ⟨(⟨O.ι o', Opens.mem_inf.mpr ⟨hoU, hmemO O o'⟩⟩ : ↥(V : Scheme.{u})), ?_⟩
      apply Subtype.ext
      rw [Scheme.homOfLE_apply]
      rfl
  · have hsub : {C' ∈ irreducibleComponents X | (C' ∩ (V : Set X)).Nonempty} ⊆
        {C' ∈ irreducibleComponents X | (C' ∩ (O : Set X)).Nonempty} \ {C} := by
      rintro C' ⟨hC', x, hxC', hxV⟩
      refine ⟨⟨hC', x, hxC', (Opens.mem_inf.mp hxV).2⟩, fun hC'C => ?_⟩
      rw [Set.mem_singleton_iff] at hC'C
      subst hC'C
      refine ((Opens.mem_inf.mp hxV).1 : x ∉ (U₀ : Set X)) ?_
      rw [hU₀]
      exact hxC'
    have hmemC : C ∈ {C' ∈ irreducibleComponents X | (C' ∩ (O : Set X)).Nonempty} :=
      ⟨hC, O.ι o, hoC, hmemO O o⟩
    have h1 := Set.ncard_le_ncard hsub hfin.sdiff
    rw [Set.ncard_sdiff_singleton_of_mem hmemC] at h1
    have h2 := (Set.ncard_pos hfin).mpr ⟨_, hmemC⟩
    omega

/-! ### The induction over the components -/

/-- The round of order `d`, by components: for every closed open `O` of `X` and every scheme `Z`
containing `O` as an open subscheme with closed range along `w`, with an ideal sheaf `J_Z` and a
reduced boundary `E_Z` restricting on `O` to `J` and `E₀` and with `J_Z` of order at most `d`
everywhere, a round of order `d` on `Z` over the range of `w`, by induction on the number of
irreducible components of `X` meeting `O`. If `O` is empty the empty succession does. Otherwise a
component `C` meets `O`; `U := C ∩ O` is a closed irreducible open of `X`, on which the round is
run and extended to `Z` (`exists_orderReductionRound_extend`), with centres over
`R₁ = w(U)`; the complement `V := O ∖ C` meets one component fewer and embeds into the last
stage of that round over the untouched open `W = Z ∖ R₁`, where the stage map is an isomorphism
(`isIso_stageMap_restrict`) and the last weak transform and boundary are the inverse images of
`J_Z` and `E_Z` (`weakTransformSeq_comap_ι_preimage`, `boundarySeq_comap_ι_preimage`), so the
induction hypothesis gives a round on that last stage over the embedded `V`; the two rounds
concatenate (`IsOrderRound.concat`). -/
theorem exists_orderReductionRound_extend_aux (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [FiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))]
    (J : X.IdealSheafData) (hJ : IsNonzeroEverywhere J) (d : ℕ) (hd0 : 0 < d)
    (E₀ : X.IdealSheafData) [IsReduced E₀.subscheme] (hE₀ : IsSncBoundary E₀) (n : ℕ) :
    ∀ (O : X.Opens), IsClosed (O : Set X) →
      {C ∈ irreducibleComponents X | (C ∩ (O : Set X)).Nonempty}.ncard ≤ n →
      ∀ {Z : Scheme.{u}} [IsNoetherian Z] (w : (O : Scheme.{u}) ⟶ Z) [IsOpenImmersion w],
        IsClosed (Set.range w) →
      ∀ (g : Z ⟶ Spec (.of k)), w ≫ g = O.ι ≫ (X ↘ Spec (.of k)) →
      ∀ (J_Z E_Z : Z.IdealSheafData) [IsReduced E_Z.subscheme],
        J_Z.comap w = J.comap O.ι → E_Z.comap w = E₀.comap O.ι → (∀ z : Z, J_Z.ord z ≤ d) →
      ∃ S : BlowUpSequence Z, IsOrderRound S J_Z E_Z d (Set.range w) g := by
  set f := X ↘ Spec (.of k) with hf
  have hnoeth : IsNoetherian X := f.isNoetherian_of_field
  induction n with
  | zero =>
    intro O hOc hn Z _ w _ hw g hg J_Z E_Z _ hJZ hEZ hle
    have hO : IsEmpty (O : Scheme.{u}) := ⟨fun o => by
      obtain ⟨_, _, _, _, _, _, _, _, _, hnV'⟩ := exists_disjoint_pieces (k := k) X O hOc o
      omega⟩
    refine ⟨nil Z, ?_⟩
    rw [Set.range_eq_empty w]
    exact isOrderRound_nil J_Z E_Z d g hle
  | succ n ih =>
    intro O hOc hn Z _ w _ hw g hg J_Z E_Z _ hJZ hEZ hle
    by_cases hO : IsEmpty (O : Scheme.{u})
    · refine ⟨nil Z, ?_⟩
      rw [Set.range_eq_empty w]
      exact isOrderRound_nil J_Z E_Z d g hle
    obtain ⟨o⟩ := not_isEmpty_iff.mp hO
    obtain ⟨U, V, hUO, hVO, hUV, hUc, hVc, hUint, hcov, hnV'⟩ :=
      exists_disjoint_pieces (k := k) X O hOc o
    have hnV : {C ∈ irreducibleComponents X | (C ∩ (V : Set X)).Nonempty}.ncard ≤ n := by omega
    -- the round on `U`, extended to `Z`
    obtain ⟨S₁, h₁⟩ := exists_orderReductionRound_extend (k := k) X J hJ d hd0 E₀ hE₀ U O hUO hUc
      w hw g hg J_Z E_Z hJZ hEZ hle
    obtain ⟨w', hw'oi, hw'comp, hw'range, hw'c, hJw', hEw'⟩ :=
      exists_untouched_embedding hUO hVO hUV hUc hVc w hw S₁ h₁.mem
    have hnoeth₁ : IsNoetherian (S₁.stage (Fin.last S₁.length)) :=
      isNoetherian_stage S₁ (Fin.last S₁.length)
    have hE'red : IsReduced (S₁.boundarySeq E_Z (Fin.last S₁.length)).subscheme :=
      isReduced_subscheme_boundarySeq S₁ E_Z _
    have hg' : w' ≫ (S₁.stageMap (Fin.last S₁.length) ≫ g) = V.ι ≫ f := by
      rw [← Category.assoc, hw'comp, Category.assoc, hg, ← Category.assoc, Scheme.homOfLE_ι]
    have hVO' : X.homOfLE hVO ≫ O.ι = V.ι := Scheme.homOfLE_ι X hVO
    have hJ' : (S₁.weakTransformSeq J_Z (Fin.last S₁.length)).comap w' = J.comap V.ι := by
      rw [hJw', hJZ, ← comap_comp, hVO']
    have hE' : (S₁.boundarySeq E_Z (Fin.last S₁.length)).comap w' = E₀.comap V.ι := by
      rw [hEw', hEZ, ← comap_comp, hVO']
    have hle' : ∀ z : S₁.stage (Fin.last S₁.length),
        (S₁.weakTransformSeq J_Z (Fin.last S₁.length)).ord z ≤ d :=
      h₁.ord_le (Fin.last S₁.length)
    obtain ⟨S₂, h₂⟩ := ih V hVc hnV w' hw'c (S₁.stageMap (Fin.last S₁.length) ≫ g) hg'
      (S₁.weakTransformSeq J_Z (Fin.last S₁.length)) (S₁.boundarySeq E_Z (Fin.last S₁.length))
      hJ' hE' hle'
    refine ⟨S₁.concat S₂, IsOrderRound.concat S₁ S₂ h₁ h₂ hw'c ?_ ?_ ?_⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨X.homOfLE hUO y, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨X.homOfLE hVO x, ?_⟩
      change (X.homOfLE hVO ≫ w) x = S₁.stageMap (Fin.last S₁.length) (w' x)
      rw [← Scheme.Hom.comp_apply, hw'comp]
    · intro z₁ hz₁
      obtain ⟨o', ho'⟩ := hz₁
      rcases hcov o' with ⟨y, rfl⟩ | ⟨x, rfl⟩
      · exact Or.inr ⟨y, by rw [Scheme.Hom.comp_apply, ho']⟩
      · left
        rw [hw'range]
        change S₁.composite z₁ ∈ Set.range (X.homOfLE hVO ≫ w)
        exact ⟨x, by rw [Scheme.Hom.comp_apply, ho']⟩

/-! ### Main Theorem II for every smooth scheme -/

/-- One round of order reduction of order `d` on a smooth algebraic scheme `X` over `k`, every
irreducible component treated in turn (`exists_orderReductionRound_extend_aux` with `O = X`):
the clauses of `IsOrderRound` over all of `X`. -/
theorem exists_orderReductionRound_smooth (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [FiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))]
    (J : X.IdealSheafData) (hJ : IsNonzeroEverywhere J) (d : ℕ) (hd0 : 0 < d)
    (hle : ∀ x : X, J.ord x ≤ d) (E₀ : X.IdealSheafData) [IsReduced E₀.subscheme]
    (hE₀ : IsSncBoundary E₀) :
    ∃ S : BlowUpSequence X, IsOrderRound S J E₀ d Set.univ (X ↘ Spec (.of k)) := by
  have hnoeth : IsNoetherian X := (X ↘ Spec (.of k)).isNoetherian_of_field
  have hrange : Set.range (⊤ : X.Opens).ι = Set.univ := by
    rw [Scheme.Opens.range_ι, Opens.coe_top]
  obtain ⟨S, hS⟩ := exists_orderReductionRound_extend_aux (k := k) X J hJ d hd0 E₀ hE₀ _ ⊤
    (by rw [Opens.coe_top]; exact isClosed_univ) le_rfl (⊤ : X.Opens).ι
    (by rw [hrange]; exact isClosed_univ) (X ↘ Spec (.of k)) rfl J E₀ rfl rfl hle
  rw [hrange] at hS
  exact ⟨S, hS⟩

/-- The order of an ideal sheaf with nonzero stalks is bounded on a smooth algebraic scheme over
`k`: on each of the finitely many irreducible components, smooth of one relative dimension, the
maximal order is finite (`maxOrd_ne_top`), and the bound is the largest of these. -/
theorem exists_forall_ord_le_of_smooth (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [FiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))]
    (J : X.IdealSheafData) (hJ : IsNonzeroEverywhere J) : ∃ d : ℕ, ∀ x : X, J.ord x ≤ d := by
  set f := X ↘ Spec (.of k) with hf
  have hnoeth : IsNoetherian X := f.isNoetherian_of_field
  have hreg : IsRegular X := isRegular_of_smooth f
  have hX : HasDisjointIntegralComponents X := hasDisjointIntegralComponents_of_isRegular
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have hbound : ∀ C ∈ irreducibleComponents X, ∃ d : ℕ, ∀ x ∈ C, J.ord x ≤ d := by
    intro C hC
    set U : X.Opens := X.irreducibleComponentOpen C with hUdef
    have hU : (U : Set X) = C := hX.irreducibleComponentOpen_eq C hC
    have hUint : IsIntegral (U : Scheme.{u}) := isIntegral_irreducibleComponentOpen hX C hC
    let _ : (U : Scheme.{u}).Over (Spec (.of k)) := ⟨U.ι ≫ f⟩
    have hft : FiniteType ((U : Scheme.{u}) ↘ Spec (.of k)) :=
      inferInstanceAs (FiniteType (U.ι ≫ f))
    have hnoethU : IsNoetherian (U : Scheme.{u}) :=
      ((U : Scheme.{u}) ↘ Spec (.of k)).isNoetherian_of_field
    obtain ⟨N, hN⟩ := exists_smoothOfRelativeDimension_of_irreducibleSpace (U.ι ≫ f)
    have hne : (J.comap U.ι).maxOrd ≠ ⊤ :=
      (J.comap U.ι).maxOrd_ne_top (U.ι ≫ f) N (isNonzeroEverywhere_comap_of_flat U.ι hJ)
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hne
    refine ⟨d, fun x hx => ?_⟩
    have hx' : x ∈ Set.range U.ι := by
      rw [Scheme.Opens.range_ι, hU]
      exact hx
    obtain ⟨y, rfl⟩ := hx'
    rw [← ord_comap_of_isOpenImmersion J U.ι y, hd]
    exact (J.comap U.ι).le_maxOrd y
  choose! dC hdC using hbound
  refine ⟨hfin.toFinset.sup dC, fun x => ?_⟩
  have hC := irreducibleComponent_mem_irreducibleComponents x
  calc J.ord x ≤ dC (irreducibleComponent x) := hdC _ hC x mem_irreducibleComponent
    _ ≤ hfin.toFinset.sup dC := by
      exact_mod_cast Finset.le_sup (f := dC) (hfin.mem_toFinset.mpr hC)

/-! ### Main Theorem II(N) for every smooth scheme -/

/-- Main Theorem II(N) on every smooth algebraic scheme whose ideal has order at most `d`
everywhere, by induction on `d`, iterating Main Theorem II (the induction of
`exists_isHironakaIIN_of_maxOrd_le`, run at the level of the main theorem; Hironaka instead deduces
II(N) from his fundamental theorem II₂^N): if the order is at most `0` the ideal is the unit ideal
and the empty succession does; otherwise either the order is at most `d` already, or one round of
order `d + 1` (`exists_orderReductionRound_smooth`) has every centre of order exactly `d + 1`, the
maximal order at its stage, so it satisfies clauses (1)–(3) with `d_i = d + 1`, and its last stage,
again smooth of finite type over `k`, carries the last weak transform, of order at most `d`, and the
last boundary, reduced with only normal crossings, to which the induction hypothesis applies; the
two are concatenated (`isHironakaIIN_concat`). -/
theorem exists_isHironakaIIN_smooth_of_forall_ord_le (d : ℕ) :
    ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] [FiniteType (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))]
      (J : X.IdealSheafData), IsNonzeroEverywhere J → (∀ x : X, J.ord x ≤ d) →
      ∀ (E : X.IdealSheafData) [IsReduced E.subscheme], IsSncBoundary E →
      ∃ S : BlowUpSequence X, S.IsHironakaIIN J E := by
  induction d with
  | zero =>
    intro X _ _ _ _ J _ hle E _ hE
    have hJ : J = ⊤ := by
      rw [← support_eq_bot_iff]
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      have h0 : J.ord x = 0 := le_antisymm (by exact_mod_cast hle x) zero_le
      exact (Scheme.IdealSheafData.ord_eq_zero_iff _ _).mp h0 hx
    exact ⟨nil X, fun i => i.elim0, hE, hJ⟩
  | succ d ih =>
    intro X _ _ _ _ J hJ hle E _ hE
    set f := X ↘ Spec (.of k) with hf
    have hnoeth : IsNoetherian X := f.isNoetherian_of_field
    by_cases hd : ∀ x : X, J.ord x ≤ d
    · exact ih X J hJ hd E hE
    -- one round of order `d + 1`
    obtain ⟨S₁, h₁⟩ := exists_orderReductionRound_smooth (k := k) X J hJ (d + 1) (Nat.succ_pos d)
      hle E hE
    -- clauses (1)–(3) of Main Theorem II(N) along the round
    have hS₁ : ∀ i : Fin S₁.length, IINStage (S₁.center i) (S₁.weakTransformSeq J i.castSucc)
        (S₁.boundarySeq E i.castSucc) := fun i => by
      refine ⟨h₁.center i, ⟨d + 1, Nat.succ_pos d, ⟨?_, fun y hy => ?_⟩, h₁.ord_center i⟩, h₁.nc i⟩
      · have := (h₁.center i).2
        obtain ⟨p⟩ := (inferInstance : Nonempty (S₁.center i).subscheme)
        have hp : (S₁.center i).subschemeι p ∈ (S₁.center i).support := by
          have : (S₁.center i).subschemeι p ∈ Set.range (S₁.center i).subschemeι := ⟨p, rfl⟩
          rwa [range_subschemeι] at this
        exact ⟨_, h₁.ord_center i _ hp⟩
      · obtain ⟨z, rfl⟩ := hy
        exact h₁.ord_le i.castSucc z
    -- the last stage of the round, smooth and of finite type over `k`
    let _ : (S₁.stage (Fin.last S₁.length)).Over (Spec (.of k)) :=
      ⟨S₁.stageMap (Fin.last S₁.length) ≫ f⟩
    have hprop := isProper_stageMap S₁ (Fin.last S₁.length)
    have hft : FiniteType (S₁.stage (Fin.last S₁.length) ↘ Spec (.of k)) :=
      inferInstanceAs (FiniteType (S₁.stageMap (Fin.last S₁.length) ≫ f))
    have hsep : IsSeparated (S₁.stage (Fin.last S₁.length) ↘ Spec (.of k)) :=
      inferInstanceAs (IsSeparated (S₁.stageMap (Fin.last S₁.length) ≫ f))
    have hsm : Smooth (S₁.stage (Fin.last S₁.length) ↘ Spec (.of k)) :=
      IsSmooth.smooth_stageMap' h₁.isSmooth (Fin.last S₁.length)
    have hnoeth₁ : IsNoetherian (S₁.stage (Fin.last S₁.length)) :=
      isNoetherian_stage S₁ (Fin.last S₁.length)
    -- the last weak transform has order at most `d` and nonzero stalks
    have hle₁ : ∀ z : S₁.stage (Fin.last S₁.length),
        (S₁.weakTransformSeq J (Fin.last S₁.length)).ord z ≤ d := fun z => by
      have h := h₁.ord_last z (Set.mem_univ _)
      rw [Nat.cast_succ] at h
      exact (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).mp h
    have hJ₁ : IsNonzeroEverywhere (S₁.weakTransformSeq J (Fin.last S₁.length)) := fun z hz => by
      have h := hle₁ z
      rw [← Scheme.IdealSheafData.ord_eq_top_iff] at hz
      rw [hz] at h
      exact absurd h (not_le.mpr (WithTop.coe_lt_top _))
    have hE₁red : IsReduced (S₁.boundarySeq E (Fin.last S₁.length)).subscheme :=
      isReduced_subscheme_boundarySeq S₁ E _
    have hE₁ : IsSncBoundary (S₁.boundarySeq E (Fin.last S₁.length)) :=
      (isSncBoundary_iff_forall_isSncBoundaryAt _).mpr
        fun z => h₁.nc_last z (Set.mem_univ _)
    obtain ⟨S₂, h₂⟩ := ih (S₁.stage (Fin.last S₁.length))
      (S₁.weakTransformSeq J (Fin.last S₁.length)) hJ₁ hle₁
      (S₁.boundarySeq E (Fin.last S₁.length)) hE₁
    exact ⟨S₁.concat S₂, isHironakaIIN_concat S₁ S₂ J E hS₁ h₂⟩

end Hironaka.Sequence

end

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme

namespace AlgebraicGeometry

/-- **Hironaka's Main Theorem II** [Hir64, Main Theorem II, pp. 142–143]: order reduction. Let `X`
be a smooth algebraic `k`-scheme (`AlgScheme k`), `k` of characteristic zero, `J` an ideal sheaf on
`X` with nonzero stalks whose greatest order `ν(J_x)` over the points `x` of `X` is `d`, and `E₀` a
reduced closed subscheme of `X` with only normal crossings. Then there is a finite succession of
monoidal transformations `f_i : X_{i+1} → X_i` with centres `D_i ⊆ X_i` such that
* (i) each `D_i` is non-singular and irreducible (`BlowUpSequence.HasRegularIrreducibleCenters`);
* (ii) the weak transform `J_i` of `J` on `X_i` has order at least `d` at every point of `D_i`;
* (iii) with `E_{i+1} = red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`, each `E_i` has only normal crossings with
  `D_i`;
* (iv) `E_r` has only normal crossings and `J_r` has order less than `d` at every point of `X_r`.

Clause (iii) and the first half of (iv) are `BlowUpSequence.HasSncBoundaries`; the second half of
(iv) is the last conjunct. The weak transform `J_{i+1}` is the pull-back of `J_i` along `f_i`
divided by the largest power of the ideal of the exceptional divisor that divides it; "has only
normal crossings (with)" is Hironaka's Definition 2 (`IsSncBoundary`, `IsSncBoundaryWith`), which
on a scheme is simple normal crossings of the reduced `E_i`: the condition `DivisorFamily.IsSnc`
(`DivisorFamily.HasSncWith`) of the functorial theorems, read on the family of irreducible
components of `E_i`.

For `d = 0` (`J = 𝒪_X`), which the printed statement does not exclude, clause (iv) forces `X_r` to
be empty; blowing up the irreducible components of `X` one after another achieves it
(`Hironaka.Sequence.exists_blowUpSequence_isEmpty_last_of_smooth`). Hironaka's monoidal
transformation, defined by a universal property [Hir64, pp. 129, 166], is empty over a centre that
is a whole component, and clause (i) asks no density.

Relation to the source.
* **Translation.** `S.weakTransformSeq J i` is Hironaka's $J_i$, `S.boundarySeq E₀ i` his $E_i$,
  and `J.ord x` his $\nu(J_x)$; `IsGreatest (Set.range J.ord) d` says that $d$ is the greatest
  of the orders $\nu(J_x)$.
* **Translation.** `[Smooth (X.left ↘ Spec (.of k))]` is Hironaka's "non-singular": for a scheme of
  finite type over the perfect field `k` the two agree (smoothness gives the regularity of every
  local ring, and a non-singular such scheme is smooth). As in the print, the irreducible components
  of `X` may have different dimensions.
* **Interpretation.** Hironaka's "coherent sheaf of non-zero ideals" is read as an ideal sheaf
  (`X.left.IdealSheafData`, quasi-coherent, hence coherent on the Noetherian `X`) with nonzero
  stalks (`hJ`).
* **Restatement.** The regularity of the local rings of `X` and the invertibility of the ideal sheaf
  of `E₀` ("of everywhere codimension one"), which Hironaka also assumes, are not separate
  hypotheses: they follow from the hypotheses kept (regularity from smoothness over the perfect
  field `k`; invertibility from reducedness and normal crossings on a regular scheme, see
  `IsSncBoundaryWith`). Of his "reduced subscheme of everywhere codimension one" only the
  reducedness, `[IsReduced E₀.subscheme]`, is assumed.
* **Out of scope.** Hironaka's remark that the theorem remains true over any local ring of his class
  ℬ [Hir64, p. 151; ℬ defined on p. 161], which he uses for local rings of analytic spaces (Main
  Theorem II′, p. 152). The base here is a field of characteristic zero, as in the print ("a field
  **B** of characteristc [sic] zero").

Source statement: [Hir64, Main Theorem II, pp. 142–143] -/
theorem exists_blowUpSequence_ord_weakTransformSeq_lt {k : Type u} [Field k] [CharZero k]
    (X : AlgScheme k) [Smooth (X.left ↘ Spec (.of k))]
    (J : X.left.IdealSheafData) (hJ : IsNonzeroEverywhere J)
    (d : ℕ) (hd : IsGreatest (Set.range J.ord) (d : ℕ∞))
    (E₀ : X.left.IdealSheafData) [IsReduced E₀.subscheme] (hE₀ : IsSncBoundary E₀) :
    ∃ S : BlowUpSequence X.left,
      -- (i)
      S.HasRegularIrreducibleCenters ∧
      -- (ii)
      (∀ i : Fin S.length, ∀ x ∈ (S.center i).support,
        (d : ℕ∞) ≤ (S.weakTransformSeq J i.castSucc).ord x) ∧
      -- (iii) and the first half of (iv)
      S.HasSncBoundaries E₀ ∧
      -- the second half of (iv)
      ∀ y : S.last, (S.weakTransformSeq J (Fin.last S.length)).ord y < d := by
  have : IsNoetherian X.left := (X.left ↘ Spec (.of k)).isNoetherian_of_field
  -- The degenerate case `d = 0`, `J = 𝒪_X`, in which clause (iv) asks for an empty `X_r`: blowing
  -- up the irreducible components of `X` one after another empties it, with regular irreducible
  -- centres and, at each stage, the restriction of `E₀` as boundary
  -- (`exists_blowUpSequence_isEmpty_last_of_smooth`); clause (ii) is `0 ≤ ν` and clause (iv) is
  -- vacuous.
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · obtain ⟨S, h1, h3, h5⟩ :=
      Hironaka.Sequence.exists_blowUpSequence_isEmpty_last_of_smooth (k := k) X.left E₀ hE₀
    exact ⟨S, h1, fun _ _ _ => by simp, ⟨h3, fun x _ => (h5.false x).elim⟩,
      fun y => (h5.false y).elim⟩
  -- For `0 < d`: one round of order reduction of order `d`, componentwise.
  obtain ⟨S, hS⟩ := Hironaka.Sequence.exists_orderReductionRound_smooth (k := k) X.left J hJ d hd0
    (fun x => hd.2 ⟨x, rfl⟩) E₀ hE₀
  exact ⟨S, hS.center, fun i x hx => (hS.ord_center i x hx).ge,
    ⟨hS.nc, (Hironaka.Sequence.isSncBoundary_iff_forall_isSncBoundaryAt _).mpr
      fun z => hS.nc_last z (Set.mem_univ _)⟩,
    fun y => hS.ord_last y (Set.mem_univ _)⟩

/-- **Hironaka's Main Theorem II(N)** [Hir64, Main Theorem II(N), p. 176]: principalization by
iterated order reduction. Let `X` be a smooth algebraic `k`-scheme (`AlgScheme k`), `k` of
characteristic zero, `J` an ideal sheaf on `X` with nonzero stalks, and `E` a reduced closed
subscheme of `X` with only normal crossings. Then there is a finite succession of monoidal
transformations `f_i : X_{i+1} → X_i` with centres `B_i ⊆ X_i` such that
* (1) each `B_i` is non-singular and irreducible (`BlowUpSequence.HasRegularIrreducibleCenters`);
* (2) for each `i` there is a positive integer `d_i` that is the greatest order of the weak
  transform `J_i` of `J` on `X_i` and its order at every point of `B_i`;
* (3) with `E_{i+1} = red(f_i⁻¹(E_i ∪ B_i))`, each `E_i` has only normal crossings with `B_i`;
* (4) `E_r` has only normal crossings and `J_r = 𝒪_{X_r}`.

Clause (3) and the first half of (4) are `BlowUpSequence.HasSncBoundaries`; the second half of (4)
is the last conjunct. II(N) writes `red(f_i⁻¹(E_i ∪ B_i))` where II writes
`red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`, the same reduced subscheme: both are the reduced structure on
`f_i⁻¹(|E_i| ∪ |B_i|)`. For `J = 𝒪_X` the empty succession satisfies every clause.

Relation to the source.
* **Translation.** The notation is that of Main Theorem II
  (`exists_blowUpSequence_ord_weakTransformSeq_lt`): `S.weakTransformSeq J i` is $J_i$ and
  `S.boundarySeq E i` is $E_i$. `S.weakTransformSeq J (Fin.last S.length) = ⊤` is
  $J_r = \mathcal{O}_{X_r}$, the top ideal sheaf `⊤` being the unit ideal.
* **Translation.** As in Main Theorem II, `[Smooth (X.left ↘ Spec (.of k))]` is Hironaka's
  "non-singular" (the two agree for a scheme of finite type over the perfect field `k`).
* **Interpretation.** As in Main Theorem II, Hironaka's "coherent sheaf of non-zero ideals" is read
  as an ideal sheaf with nonzero stalks (`hJ`).
* **Gap.** Hironaka's "algebraic scheme" [Hir64, Ch. I, p. 162] is a scheme of finite type over
  $\operatorname{Spec} S$ for some local ring $S$ of his class ℬ (Noetherian, residue field of
  characteristic zero, his condition (ii) on completions, p. 161), a class containing every field of
  characteristic zero and the local rings of analytic spaces. Here `X` is separated and of finite
  type over a field `k` of characteristic zero.
* **Restatement.** As in Main Theorem II, the regularity of `X` and the invertibility of the ideal
  sheaf of `E`, which Hironaka also assumes, are not separate hypotheses: they follow from the
  hypotheses kept (regularity from smoothness over the perfect field `k`; invertibility from
  reducedness and normal crossings on a regular scheme).
* **Restatement.** Hironaka states the theorem for $X$ of dimension $N$, the index of the
  fundamental theorem II₂^N from which he deduces it [Hir64, p. 176]; $N$ does not appear in the
  conclusion. The statement here is II(N) for all $N$ at once. As in the print, `X` may have several
  irreducible components (Hironaka reduces the proof to irreducible $X$).

Source statement: [Hir64, Main Theorem II(N), p. 176] -/
theorem exists_blowUpSequence_weakTransformSeq_eq_top {k : Type u} [Field k] [CharZero k]
    (X : AlgScheme k) [Smooth (X.left ↘ Spec (.of k))]
    (J : X.left.IdealSheafData) (hJ : IsNonzeroEverywhere J)
    (E : X.left.IdealSheafData) [IsReduced E.subscheme] (hE : IsSncBoundary E) :
    ∃ S : BlowUpSequence X.left,
      -- (1)
      S.HasRegularIrreducibleCenters ∧
      -- (2)
      (∀ i : Fin S.length, ∃ d : ℕ, 0 < d ∧
        IsGreatest (Set.range (S.weakTransformSeq J i.castSucc).ord) (d : ℕ∞) ∧
        ∀ z ∈ (S.center i).support, (S.weakTransformSeq J i.castSucc).ord z = d) ∧
      -- (3) and the first half of (4)
      S.HasSncBoundaries E ∧
      -- the second half of (4)
      S.weakTransformSeq J (Fin.last S.length) = ⊤ := by
  have hnoeth : IsNoetherian X.left := (X.left ↘ Spec (.of k)).isNoetherian_of_field
  obtain ⟨d, hd⟩ := Hironaka.Sequence.exists_forall_ord_le_of_smooth (k := k) X.left J hJ
  obtain ⟨S, h1, h2, h3⟩ :=
    Hironaka.Sequence.exists_isHironakaIIN_smooth_of_forall_ord_le (k := k) d X.left J hJ hd E hE
  exact ⟨S, fun i => (h1 i).1, fun i => (h1 i).2.1, ⟨fun i => (h1 i).2.2, h2⟩, h3⟩

end AlgebraicGeometry
