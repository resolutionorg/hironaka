/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.MaximalContactClasses
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Resolution.Algebraic.MaximalContact.Existence
import Hironaka.Resolution.Algebraic.MaximalContact.Restrict
import Hironaka.Resolution.Algebraic.MaximalContact.Transform
import Hironaka.Resolution.Algebraic.Snc.SmoothDivisorLocal
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.IdealSheaf.Derivative.Pullback
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The maximal contact classes satisfy the hypotheses of Theorem 105

The global case of the proof of Theorem 103 [Kol07, 104, Step 3] globalizes the maximal contact
case by [Kol07, Theorem 105] with `M` = coproducts of open immersions, `GT = GT_{n,m}` (triples
with `dim X = n`, `max-ord I ≤ m`) and `LT = LT_{n,m}` (those admitting a global smooth
hypersurface of maximal contact). This module proves that these classes
(`Hironaka/Resolution/Algebraic/Kol07/MaximalContactClasses.lean`) satisfy the hypotheses
(2)(i)–(ii) of Theorem 105, the local existence resting on the local existence of hypersurfaces of
maximal contact [Kol07, Theorem 80 (2)].

* **The classes** (`orderClass_iff`, `maximalContactClass_iff`, `MaximalContactClass.orderClass`):
  unfoldings and `LT ⊆ GT`.
* **Below the mark** (`hasMaximalContact_of_maxOrd_lt`): when `max-ord I < m`,
  `MC(I) = D^{m-1}(I)` has order `0` at every point (`ord_MC_eq_zero`, a characteristic-zero
  fact), so it is the unit ideal and the empty hypersurface `H = 𝒪_X`, a smooth divisor
  (`isSmoothDivisor_top`), is of maximal contact.
* **Closure under finite disjoint unions** (Theorem 105 (2)(ii); "this condition is also
  preserved under disjoint unions", [Kol07, 104, Step 2]): the dimension is local on the source,
  so a finite coproduct of `n`-dimensional pieces is `n`-dimensional (`closedUnderSigma_hasDim`,
  via `IsZariskiLocalAtSource.sigmaDesc` and the isomorphism `∐ Xⁱ ≅ X`); `max-ord ≤ m` is
  `closedUnderSigma_maxOrd_le`; and the union `H^* = ∐ H^(j)`, realised as the intersection
  `⨅ j, (H^(j)).map (ι j)` of the ideals of the closed pieces, restricts to `H^(j)` on the `j`-th
  piece (each `ι j` is a closed immersion, an open immersion with closed image, the complement
  being the union of the other pieces; the direct image of `H^(i)` along `ι i` restricts to the
  unit ideal on a different piece; and inverse images along open immersions commute with finite
  intersections), so it is a smooth divisor (`isSmoothDivisor_of_forall_comap`) and lies in
  `MC(I)` (`le_of_forall_comap_le`, with `MC(I|_{Xʲ}) = MC(I)|_{Xʲ}` by
  `derivativeIter_comap_of_smooth`).
* **Closure under pullback along coproducts of open immersions** (the hypothesis
  `LocalCoversFibreClosed` of the descent): such a morphism is étale, hence of relative dimension
  `0`, so the dimension persists; the order of `g^* I` at a point is the order of `I` at its image
  (through the summand containing the point); `g^{-1} H` is a smooth divisor (restriction along
  each summand's open immersion) inside `MC(g^* I) = g^* MC(I)`.
* **Local existence** (Theorem 105 (2)(i); `exists_isPullbackOf_maximalContactClass`): at a point
  where `max-ord I < m` the triple itself, along the identity, is a local triple (below the mark);
  at a point where `max-ord I = m`, [Kol07, Theorem 80 (2)]
  (`exists_opens_isSmoothDivisor_isMaximalContact`) gives an open `U ∋ x` with a smooth divisor
  of maximal contact `H`; an affine `V ≤ U` around `x` (`exists_isAffineOpen_mem_and_subset`)
  makes `T|_V` a triple (`Triple.pullback` along the open immersion `V.ι`, the class hypotheses by
  composition and affineness), `V.ι` is a coproduct of open immersions with one summand, and
  `H|_V` is a smooth divisor of maximal contact for `T|_V`.
* **The assembly and the instance** (`globalizationData_of_exists_isPullbackOf`,
  `globalizationData_maximalContact`): the local existence together with (2)(ii) is the
  `GlobalizationData`.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicGeometry.Scheme.IdealSheafData

open AlgebraicGeometry (comap_map_of_isClosedImmersion)

open Hironaka.Sequence
  (exists_eq_of_isColimit_cofan isOpenImmersion_of_isColimit_cofan openImmersionCoprods_etale
      openImmersionCoprods_of_isOpenImmersion)

namespace AlgebraicGeometry.Triple

open Hironaka

open AlgebraicGeometry

variable {k : Type u} [Field k]

/-! ### The classes -/

/-- The class `GT_{n,m}` of [Kol07, Theorem 103], unfolded. -/
theorem orderClass_iff (n m : ℕ) (T : Triple k) :
    OrderClass n m T ↔ T.HasDim n ∧ T.I.maxOrd ≤ (m : ℕ∞) := Iff.rfl

/-- The class `LT_{n,m}` of [Kol07, 104, Step 3], unfolded. -/
theorem maximalContactClass_iff (n m : ℕ) (T : Triple k) :
    MaximalContactClass n m T ↔ OrderClass n m T ∧ T.HasMaximalContact m := Iff.rfl

/-- `LT_{n,m} ⊆ GT_{n,m}`. -/
theorem MaximalContactClass.orderClass {n m : ℕ} {T : Triple k} (h : MaximalContactClass n m T) :
    OrderClass n m T := h.1

/-- Below the mark the empty hypersurface `H = 𝒪_X` is a smooth divisor of maximal contact, since
`MC(I) = 𝒪_X` (`ord_MC_eq_zero`). Not in the sources; the case `max-ord I < m`, where Kollár's
functor does nothing. -/
theorem hasMaximalContact_of_maxOrd_lt [CharZero k] (T : Triple k) {m : ℕ}
    (h : T.I.maxOrd < m) : T.HasMaximalContact m := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  refine ⟨⊤, Hironaka.Snc.isSmoothDivisor_top, ?_⟩
  · change (⊤ : T.X.left.IdealSheafData) ≤ MC (T.X.left ↘ Spec (.of k)) T.I m
    refine top_le_iff.mpr ?_
    rw [← support_eq_bot_iff]
    refine TopologicalSpace.Closeds.ext ?_
    rw [TopologicalSpace.Closeds.coe_bot, Set.eq_empty_iff_forall_notMem]
    intro x hx
    have h0 := ord_MC_eq_zero (T.X.left ↘ Spec (.of k)) n T.I (x := x)
      (lt_of_le_of_lt (le_maxOrd T.I x) h)
    have hx1 : (1 : ℕ∞) ≤ (MC (T.X.left ↘ Spec (.of k)) T.I m).ord x := by
      rw [one_le_ord_iff]
      exact hx
    rw [h0] at hx1
    exact absurd hx1 (by simp)

/-! ### Closure under finite disjoint unions (Theorem 105 (2)(ii)) -/

/-- The dimension is local on the source, so `dim X = n` is closed under finite disjoint unions
(the disjoint union `X^* = ∐ X^(j)` of [Kol07, 104, Step 3]). -/
theorem closedUnderSigma_hasDim (n : ℕ) :
    Triple.ClosedUnderSigma (fun T : Triple k => T.HasDim n) := by
  intro σ _ _ Ts T ι h hD
  have := h.isIso_sigmaDesc
  have hcomp : Sigma.desc ι ≫ (T.X.left ↘ Spec (.of k)) =
      Sigma.desc fun i => (Ts i).X.left ↘ Spec (.of k) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, h.2.1 i]
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have hP : SmoothOfRelativeDimension n (Sigma.desc fun i => (Ts i).X.left ↘ Spec (.of k)) :=
    IsZariskiLocalAtSource.sigmaDesc fun i => (hD i : SmoothOfRelativeDimension n _)
  rw [← hcomp] at hP
  have hP' := IsZariskiLocalAtSource.comp hP (inv (Sigma.desc ι))
  rwa [IsIso.inv_hom_id_assoc] at hP'

/-- `GT_{n,m}` is closed under finite disjoint unions (`closedUnderSigma_maxOrd_le` for the
order). -/
theorem closedUnderSigma_orderClass (n m : ℕ) :
    Triple.ClosedUnderSigma (OrderClass (k := k) n m) := by
  change Triple.ClosedUnderSigma (fun T : Triple k => T.HasDim n ∧ T.I.maxOrd ≤ (m : ℕ∞))
  exact Triple.ClosedUnderSigma.and (D₁ := fun T : Triple k => T.HasDim n)
    (D₂ := fun T : Triple k => T.I.maxOrd ≤ (m : ℕ∞)) (closedUnderSigma_hasDim n)
    (closedUnderSigma_maxOrd_le m)

/-- "`H^* := ∐ H^(j) ⊂ ∐ X^(j) =: X^*` is a smooth hypersurface of maximal contact"
[Kol07, 104, Step 3]: the union of the pieces' hypersurfaces is a smooth hypersurface of maximal
contact on the disjoint union. -/
theorem IsSigmaOf.isMaximalContact_sigma {σ : Type u} [Finite σ] {T : Triple k}
    {Ts : σ → Triple k} {ι : ∀ i, (Ts i).X.left ⟶ T.X.left} (h : T.IsSigmaOf Ts ι) {m : ℕ}
    (H : ∀ i, (Ts i).X.left.IdealSheafData) (hs : ∀ i, IsSmoothDivisor (H i))
    (hmc : ∀ i, IsMaximalContact ((Ts i).X.left ↘ Spec (.of k)) (Ts i).I m (H i)) :
    IsSmoothDivisor (⨅ i, (H i).map (ι i)) ∧
      IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m (⨅ i, (H i).map (ι i)) := by
  classical
  have hopen : ∀ i, IsOpenImmersion (ι i) := h.isOpenImmersion
  have hcov : ∀ x : T.X.left, ∃ (i : σ) (y : (Ts i).X.left), ι i y = x := fun x => by
    have hx : x ∈ ⋃ i, Set.range (ι i) := h.iUnion_range ▸ Set.mem_univ x
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 hx
    exact ⟨i, y, hy⟩
  -- each piece is closed: its complement is the union of the other pieces
  have hclosed : ∀ i, IsClosedImmersion (ι i) := fun i => by
    have := hopen i
    refine IsClosedImmersion.of_isPreimmersion (ι i) ?_
    have hc : (Set.range (ι i))ᶜ = ⋃ j ∈ ({i}ᶜ : Set σ), Set.range (ι j) := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, y, rfl⟩ := hcov x
        refine Set.mem_iUnion₂.2 ⟨j, fun hj => hx ?_, y, rfl⟩
        rw [Set.mem_singleton_iff] at hj
        subst hj
        exact ⟨y, rfl⟩
      · intro hx hxi
        obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hx
        exact Set.disjoint_left.1 (h.disjoint_range fun e => hj (Set.mem_singleton_iff.2 e.symm))
          hxi hxj
    rw [← isOpen_compl_iff, hc]
    exact isOpen_biUnion fun j _ => (ι j).isOpenEmbedding.isOpen_range
  -- the union restricts to the given hypersurface on each piece
  have hres : ∀ j, (⨅ i, (H i).map (ι i)).comap (ι j) = H j := fun j => by
    have := hopen j
    rw [Hironaka.Snc.comap_iInf_of_isOpenImmersion]
    refine le_antisymm ((iInf_le _ j).trans ?_) (le_iInf fun i => ?_)
    · have := hclosed j
      exact (comap_map_of_isClosedImmersion (ι j) (H j)).le
    · by_cases hij : i = j
      · subst hij
        have := hclosed i
        exact (comap_map_of_isClosedImmersion (ι i) (H i)).ge
      · have := hclosed i
        rw [Hironaka.Snc.comap_map_eq_top_of_disjoint (H i) (ι i) (ι j) (h.disjoint_range hij)]
        exact le_top
  refine ⟨Hironaka.Snc.isSmoothDivisor_of_forall_comap ι hcov fun j => ?_, ?_⟩
  · rw [hres j]
    exact hs j
  · change (⨅ i, (H i).map (ι i)) ≤ MC (T.X.left ↘ Spec (.of k)) T.I m
    refine Hironaka.Snc.le_of_forall_comap_le ι hcov fun j => ?_
    rw [hres j]
    have := hopen j
    have hMC : MC ((Ts j).X.left ↘ Spec (.of k)) (Ts j).I m =
        (MC (T.X.left ↘ Spec (.of k)) T.I m).comap (ι j) := by
      rw [← h.2.1 j, h.2.2.1 j, MC_eq, MC_eq, derivativeIter_comap_of_smooth]
    rw [← hMC]
    exact hmc j

/-- Admitting a global smooth hypersurface of maximal contact is closed under finite disjoint
unions ("this condition is also preserved under disjoint unions", [Kol07, 104, Step 2]). -/
theorem closedUnderSigma_hasMaximalContact (m : ℕ) :
    Triple.ClosedUnderSigma (fun T : Triple k => T.HasMaximalContact m) := by
  intro σ _ _ Ts T ι h hD
  unfold HasMaximalContact at hD
  choose H hs hmc using hD
  exact ⟨_, (h.isMaximalContact_sigma H hs hmc).1, (h.isMaximalContact_sigma H hs hmc).2⟩

/-- Hypothesis (2)(ii) of [Kol07, Theorem 105] for the instance: `LT_{n,m}` is closed under finite
disjoint unions. -/
theorem closedUnderSigma_maximalContactClass (n m : ℕ) :
    Triple.ClosedUnderSigma (MaximalContactClass (k := k) n m) := by
  change Triple.ClosedUnderSigma (fun T : Triple k => OrderClass n m T ∧ T.HasMaximalContact m)
  exact Triple.ClosedUnderSigma.and (D₁ := OrderClass n m)
    (D₂ := fun T : Triple k => T.HasMaximalContact m) (closedUnderSigma_orderClass n m)
    (closedUnderSigma_hasMaximalContact m)

/-! ### Closure under pullback along coproducts of open immersions -/

variable {T T' : Triple k} {g : T'.X.left ⟶ T.X.left}

/-- Pulling back along a coproduct of open immersions (étale, hence of relative dimension `0`)
keeps the dimension. -/
theorem HasDim.isPullbackOf {n : ℕ} (hT : T.HasDim n) (hg : openImmersionCoprods g)
    (hT' : T'.IsPullbackOf T g) : T'.HasDim n := by
  have : Etale g := openImmersionCoprods_etale g hg
  have : SmoothOfRelativeDimension n (T.X.left ↘ Spec (.of k)) := hT
  have h0 : SmoothOfRelativeDimension 0 g := inferInstance
  have h1 : SmoothOfRelativeDimension (0 + n) (g ≫ (T.X.left ↘ Spec (.of k))) := inferInstance
  rw [zero_add] at h1
  unfold HasDim
  rw [← hT'.1]
  exact h1

/-- `GT_{n,m}` is closed under pullback along coproducts of open immersions
(`ord_comap_of_isOpenImmersion` for the order). -/
theorem OrderClass.isPullbackOf {n m : ℕ} (hT : OrderClass n m T) (hg : openImmersionCoprods g)
    (hT' : T'.IsPullbackOf T g) : OrderClass n m T' := by
  refine ⟨hT.1.isPullbackOf hg hT', ?_⟩
  rw [hT'.2.1, maxOrd_le_iff]
  intro y
  obtain ⟨σ, U, ι, hc, hι⟩ := hg
  obtain ⟨i, z, rfl⟩ := exists_eq_of_isColimit_cofan ι hc y
  have := isOpenImmersion_of_isColimit_cofan ι hc i
  have := hι i
  rw [← ord_comap_of_isOpenImmersion (T.I.comap g) (ι i) z, ← comap_comp,
    ord_comap_of_isOpenImmersion]
  exact (le_maxOrd T.I _).trans hT.2

/-- A global smooth hypersurface of maximal contact restricts along a coproduct of open
immersions: `g^{-1} H` is a smooth divisor on each summand and `MC(g^* I) = g^* MC(I)`
(`derivativeIter_comap_of_smooth`). -/
theorem HasMaximalContact.isPullbackOf {m : ℕ} (hT : T.HasMaximalContact m)
    (hg : openImmersionCoprods g) (hT' : T'.IsPullbackOf T g) : T'.HasMaximalContact m := by
  obtain ⟨H, hs, hmc⟩ := hT
  have : Etale g := openImmersionCoprods_etale g hg
  refine ⟨H.comap g, ?_, ?_⟩
  · obtain ⟨σ, U, ι, hc, hι⟩ := hg
    have : ∀ i, IsOpenImmersion (ι i) := isOpenImmersion_of_isColimit_cofan ι hc
    refine Hironaka.Snc.isSmoothDivisor_of_forall_comap ι (fun y => ?_) fun i => ?_
    · obtain ⟨i, z, hz⟩ := exists_eq_of_isColimit_cofan ι hc y
      exact ⟨i, z, hz⟩
    · have := hι i
      rw [← comap_comp]
      exact hs.comap_of_isOpenImmersion (ι i ≫ g)
  · change H.comap g ≤ MC (T'.X.left ↘ Spec (.of k)) T'.I m
    rw [← hT'.1, hT'.2.1, MC_eq, derivativeIter_comap_of_smooth]
    exact comap_mono g hmc

/-- `LT_{n,m}` is closed under pullback along coproducts of open immersions (the hypothesis
`LocalCoversFibreClosed` of the descent, for this instance). -/
theorem MaximalContactClass.isPullbackOf {n m : ℕ} (hT : MaximalContactClass n m T)
    (hg : openImmersionCoprods g) (hT' : T'.IsPullbackOf T g) : MaximalContactClass n m T' :=
  ⟨hT.1.isPullbackOf hg hT', hT.2.isPullbackOf hg hT'⟩

/-! ### The assembly -/

/-- The local existence as a hypothesis and the closure under disjoint unions make the data (2)
of [Kol07, Theorem 105]. -/
theorem globalizationData_of_exists_isPullbackOf (n m : ℕ)
    (h : ∀ T : Triple k, OrderClass n m T → ∀ x : T.X.left,
      ∃ (T' : Triple k) (g : T'.X.left ⟶ T.X.left), openImmersionCoprods g ∧ x ∈ Set.range g ∧
        T'.IsPullbackOf T g ∧ MaximalContactClass n m T') :
    Triple.GlobalizationData openImmersionCoprods (OrderClass (k := k) n m)
      (MaximalContactClass n m) :=
  ⟨h, closedUnderSigma_maximalContactClass n m⟩


/-! ### Local existence (Theorem 105 (2)(i)) and the instance -/

/-- Hypothesis (2)(i) of [Kol07, Theorem 105] for the instance: every point of a `GT_{n,m}`-triple
lies in the image of a coproduct of open immersions from an `LT_{n,m}`-triple carrying the
pullback data. At a point of order `m` this is the local existence of a smooth hypersurface of
maximal contact [Kol07, Theorem 80 (2)]; below the mark, `hasMaximalContact_of_maxOrd_lt`. -/
theorem exists_isPullbackOf_maximalContactClass [CharZero k] (n m : ℕ) (T : Triple k)
    (hT : OrderClass n m T) (x : T.X.left) :
    ∃ (T' : Triple k) (g : T'.X.left ⟶ T.X.left), openImmersionCoprods g ∧ x ∈ Set.range g ∧
      T'.IsPullbackOf T g ∧ MaximalContactClass n m T' := by
  classical
  rcases lt_or_eq_of_le hT.2 with hlt | heq
  · refine ⟨T, 𝟙 T.X.left, openImmersionCoprods_of_isOpenImmersion _, ⟨x, rfl⟩,
      ⟨Category.id_comp _, (comap_id _).symm, (Scheme.DivisorFamily.comap_id _).symm⟩, hT,
      hasMaximalContact_of_maxOrd_lt T hlt⟩
  · have hdim : SmoothOfRelativeDimension n (T.X.left ↘ Spec (.of k)) := hT.1
    obtain ⟨U, hxU, H, hs, hmc⟩ :=
      exists_opens_isSmoothDivisor_isMaximalContact (T.X.left ↘ Spec (.of k)) n T.I heq x
    obtain ⟨V, hV, hxV, hVU₀⟩ := exists_isAffineOpen_mem_and_subset hxU
    have hVU : V ≤ U := hVU₀
    have hVa : IsAffine (V : Scheme.{u}) := hV
    let _ : (V : Scheme.{u}).Over (Spec (.of k)) := ⟨V.ι ≫ (T.X.left ↘ Spec (.of k))⟩
    have hover : V.ι.IsOver (Spec (.of k)) := ⟨rfl⟩
    have hlft : LocallyOfFiniteType ((V : Scheme.{u}) ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (V.ι ≫ (T.X.left ↘ Spec (.of k))))
    have hqc : QuasiCompact ((V : Scheme.{u}) ↘ Spec (.of k)) := inferInstance
    have hsep : IsSeparated ((V : Scheme.{u}) ↘ Spec (.of k)) := IsSeparated.of_isAffineHom _
    have hY : ∃ n', SmoothOfRelativeDimension n' ((V : Scheme.{u}) ↘ Spec (.of k)) := ⟨n, by
      have h1 : SmoothOfRelativeDimension (0 + n) (V.ι ≫ (T.X.left ↘ Spec (.of k))) := inferInstance
      rwa [zero_add] at h1⟩
    have hT'p : (Triple.pullback T hY V.ι).IsPullbackOf T V.ι :=
      Triple.isPullbackOf_pullback T hY V.ι
    have hg : openImmersionCoprods V.ι := openImmersionCoprods_of_isOpenImmersion _
    refine ⟨Triple.pullback T hY V.ι, V.ι, hg, ⟨⟨x, hxV⟩, rfl⟩, hT'p,
      hT.isPullbackOf hg hT'p, ?_⟩
    have hVU' : T.X.left.homOfLE hVU ≫ U.ι = V.ι := Scheme.homOfLE_ι _ _
    refine ⟨H.comap (T.X.left.homOfLE hVU), hs.comap_of_isOpenImmersion (T.X.left.homOfLE hVU), ?_⟩
    change H.comap (T.X.left.homOfLE hVU) ≤ MC (V.ι ≫ (T.X.left ↘ Spec (.of k))) (T.I.comap V.ι) m
    rw [← hVU', comap_comp, Category.assoc, MC_eq, derivativeIter_comap_of_smooth]
    exact comap_mono _ hmc

/-- The instance of [Kol07, Theorem 105] used in the global case of the proof of Theorem 103
[Kol07, 104, Step 3]: `M` = coproducts of open immersions, `GT = GT_{n,m}` and `LT = LT_{n,m}`
satisfy the hypotheses (2)(i)–(ii). -/
theorem globalizationData_maximalContact [CharZero k] (n m : ℕ) :
    Triple.GlobalizationData openImmersionCoprods (OrderClass (k := k) n m)
      (MaximalContactClass n m) :=
  globalizationData_of_exists_isPullbackOf n m (exists_isPullbackOf_maximalContactClass n m)

end AlgebraicGeometry.Triple
