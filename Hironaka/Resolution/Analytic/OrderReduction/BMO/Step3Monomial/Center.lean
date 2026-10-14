/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Ideal
public import Hironaka.Resolution.Analytic.Principalization.Collapse
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.MarkedAlgebra
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Submanifold.Clopen
import Hironaka.Resolution.Analytic.Principalization.MeetLocusSubfamily
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Resolution.Analytic.Principalization.SncClopen
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The centres of the monomial procedure are closed submanifolds

A **centre** of the combinatorial state is a set `S` of faces of the nerve with a common label tuple
`L` (`Hironaka.Monomial.MonomialState.IsCenter`); Kollár's choice at level `r` in
[Kol07, 111, Step 3] is one (`MonomialState.isCenter_choice`). This file proves that its locus
`centerOf S = ⋃_{P ∈ S} ⋂_{c ∈ P} piece c` is a closed submanifold of codimension `r`, the number of
labels, having simple normal crossings with the boundary family, and that the monomial ideal has
order `≥ m` along it when every face of `S` has exponent sum `≥ m`, as the order clause of
[Kol07, Definition 66 (4′)] requires of a centre.

The locus is a clopen part of the `r`-fold intersection `⋂_{ℓ ∈ L} E^{e ℓ}` of the members of the
tuple: through a point of the intersection passes exactly one piece of each label, so the point lies
in the locus of exactly one face with labels `L`, and the faces with labels `L` outside `S` cut out
a closed set whose complement is the open part. The intersection is a closed submanifold of
codimension `r` with simple normal crossings with the family (in a chart of simple normal crossings
it is a coordinate subspace), hence so is the clopen part. Near a point of the locus of `P ∈ S` the
locus is contained in every piece of `P`, so each `𝓘_{piece c}`, `c ∈ P`, has order `≥ 1` along it
and the monomial ideal has order at least the exponent sum of `P`.
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

/-! ### Faces of a centre -/

/-- The faces of a centre of the state are faces of the nerve. -/
theorem subset_nerve_of_isCenter (hS : (Φ.toState n m hV).IsCenter S) : S ⊆ Φ.nerve := hS.1

/-- The faces of a centre have a common label tuple. -/
theorem labels_eq_of_isCenter (hS : (Φ.toState n m hV).IsCenter S) {P Q : Finset ℕ} (hP : P ∈ S)
    (hQ : Q ∈ S) : Φ.labels P = Φ.labels Q :=
  hS.2 P hP Q hQ

/-- Two faces of the nerve with the same labels and a common point are equal, since through a point
passes at most one piece with a given label. -/
theorem Realizes.eq_of_labels_eq_of_mem_faceSet (hΦ : Φ.Realizes F e) {P Q : Finset ℕ}
    (hP : P ∈ Φ.nerve) (hQ : Q ∈ Φ.nerve) (hl : Φ.labels P = Φ.labels Q) {x : N}
    (hxP : x ∈ Φ.faceSet P) (hxQ : x ∈ Φ.faceSet Q) : P = Q := by
  have key : ∀ {P Q : Finset ℕ}, P ∈ Φ.nerve → Q ∈ Φ.nerve → Φ.labels P = Φ.labels Q →
      x ∈ Φ.faceSet P → x ∈ Φ.faceSet Q → P ⊆ Q := by
    intro P Q hP hQ hl hxP hxQ c hc
    have hcl : Φ.label c ∈ Φ.labels Q := hl ▸ Finset.mem_image_of_mem _ hc
    obtain ⟨c', hc', hlc⟩ := Finset.mem_image.mp hcl
    have := hΦ.eq_of_label_eq_of_mem (Φ.lt_nextComp_of_mem_nerve hP hc)
      (Φ.lt_nextComp_of_mem_nerve hQ hc') hlc.symm (Φ.mem_faceSet.mp hxP c hc)
      (Φ.mem_faceSet.mp hxQ c' hc')
    exact this ▸ hc'
  exact Finset.Subset.antisymm (key hP hQ hl hxP hxQ) (key hQ hP hl.symm hxQ hxP)

/-- A point of the locus of a centre lies in the locus of exactly one of its faces. -/
theorem Realizes.eq_of_mem_faceSet_of_isCenter (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) {P Q : Finset ℕ} (hP : P ∈ S) (hQ : Q ∈ S) {x : N}
    (hxP : x ∈ Φ.faceSet P) (hxQ : x ∈ Φ.faceSet Q) : P = Q :=
  hΦ.eq_of_labels_eq_of_mem_faceSet (subset_nerve_of_isCenter hS hP)
    (subset_nerve_of_isCenter hS hQ) (labels_eq_of_isCenter hS hP hQ) hxP hxQ

/-- All faces of a nonempty centre have the cardinality `faceCard S`. -/
theorem Realizes.card_eq_faceCard_of_isCenter (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) {P : Finset ℕ} (hP : P ∈ S) : P.card = faceCard S := by
  have h : ∀ Q ∈ S, Q.card = P.card := fun Q hQ => by
    rw [← hΦ.card_labels_of_mem_nerve (subset_nerve_of_isCenter hS hQ),
      ← hΦ.card_labels_of_mem_nerve (subset_nerve_of_isCenter hS hP),
      labels_eq_of_isCenter hS hQ hP]
  rw [faceCard, Finset.sup_congr rfl h, Finset.sup_const ⟨P, hP⟩]

/-- A nonempty centre of the state has a nonempty locus. -/
theorem centerOf_nonempty (hS : (Φ.toState n m hV).IsCenter S) (hne : S.Nonempty) :
    (Φ.centerOf S).Nonempty := by
  obtain ⟨P, hP⟩ := hne
  obtain ⟨x, hx⟩ := Φ.faceSet_nonempty_of_mem_nerve (subset_nerve_of_isCenter hS hP)
  exact ⟨x, Φ.faceSet_subset_centerOf hP hx⟩

/-! ### The locus as a clopen part of the members' intersection -/

/-- The `card`-fold meet locus of a finite subfamily is the intersection of its members. -/
theorem mem_meetLocus_subfamily_card_iff (Ls : Finset F.ι) {x : N} :
    x ∈ (F.subfamily (· ∈ Ls)).meetLocus Ls.card ↔ ∀ j ∈ Ls, x ∈ F.hyp j := by
  classical
  let _ : Fintype (F.subfamily (· ∈ Ls)).ι := inferInstanceAs (Fintype {j // j ∈ Ls})
  have hcard : Fintype.card (F.subfamily (· ∈ Ls)).ι = Ls.card := Fintype.card_coe Ls
  rw [HypersurfaceFamily.mem_meetLocus]
  constructor
  · rintro ⟨s, hs, hx⟩ j hj
    have hsu : s = Finset.univ := Finset.eq_univ_of_card s (by rw [hs, hcard])
    exact hx ⟨j, hj⟩ (hsu ▸ Finset.mem_univ _)
  · intro hx
    exact ⟨Finset.univ, by rw [Finset.card_univ, hcard], fun j _ => hx j.1 j.2⟩

/-- No point lies on `card + 1` members of a finite subfamily. -/
theorem meetLocus_subfamily_card_succ_eq_empty (Ls : Finset F.ι) :
    (F.subfamily (· ∈ Ls)).meetLocus (Ls.card + 1) = ∅ := by
  classical
  let _ : Fintype (F.subfamily (· ∈ Ls)).ι := inferInstanceAs (Fintype {j // j ∈ Ls})
  have hcard : Fintype.card (F.subfamily (· ∈ Ls)).ι = Ls.card := Fintype.card_coe Ls
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨s, hs, -⟩
  have := Finset.card_le_univ s
  rw [hs, hcard] at this
  omega

/-- The locus of a nonempty centre of the state is a clopen part of the intersection of the members
of its label tuple: it is the intersection of the members `Ls` of the tuple with the open complement
of the loci of the faces with the same labels that are not in the centre. -/
theorem Realizes.exists_centerOf_eq_meetLocus_inter (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hne : S.Nonempty) :
    ∃ (Ls : Finset F.ι) (O : Set N), Ls.card = faceCard S ∧ IsOpen O ∧
      Φ.centerOf S = (F.subfamily (· ∈ Ls)).meetLocus Ls.card ∩ O := by
  classical
  obtain ⟨P₀, hP₀⟩ := hne
  have hP₀n : P₀ ∈ Φ.nerve := subset_nerve_of_isCenter hS hP₀
  set L := Φ.labels P₀ with hL
  have hlt : ∀ ℓ ∈ L, ℓ < Φ.nextLabel := by
    intro ℓ hℓ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hℓ
    exact Φ.label_lt c (Φ.lt_nextComp_of_mem_nerve hP₀n hc)
  let Ls : Finset F.ι := L.attach.image fun ℓ => e ⟨ℓ.1, hlt ℓ.1 ℓ.2⟩
  have hLs : ∀ j, j ∈ Ls ↔ ∃ ℓ, ∃ hℓ : ℓ ∈ L, e ⟨ℓ, hlt ℓ hℓ⟩ = j := by
    intro j
    simp only [Ls, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  have hLs_card : Ls.card = faceCard S := by
    rw [Finset.card_image_of_injective _
        fun ℓ ℓ' h => Subtype.ext (Fin.mk.inj_iff.mp (e.injective h)),
      Finset.card_attach, hL, hΦ.card_labels_of_mem_nerve hP₀n,
      hΦ.card_eq_faceCard_of_isCenter hS hP₀]
  -- the faces with labels `L` outside the centre
  let bad : Finset (Finset ℕ) := Φ.nerve.filter fun T => Φ.labels T = L ∧ T ∉ S
  refine ⟨Ls, (⋃ T ∈ bad, Φ.faceSet T)ᶜ, hLs_card,
    (isClosed_biUnion_finset fun T _ => Φ.isClosed_faceSet T).isOpen_compl, ?_⟩
  -- a point on a face with labels `L` lies on every member of the tuple
  have hmeet : ∀ {T : Finset ℕ}, T ∈ Φ.nerve → Φ.labels T = L → ∀ {x : N}, x ∈ Φ.faceSet T →
      x ∈ (F.subfamily (· ∈ Ls)).meetLocus Ls.card := by
    intro T hT hTL x hx
    rw [mem_meetLocus_subfamily_card_iff]
    intro j hj
    obtain ⟨ℓ, hℓ, rfl⟩ := (hLs j).mp hj
    rw [← hTL] at hℓ
    obtain ⟨c, hc, hcl⟩ := Finset.mem_image.mp hℓ
    have hcn : c < Φ.nextComp := Φ.lt_nextComp_of_mem_nerve hT hc
    have : (⟨ℓ, hlt ℓ (hTL ▸ hℓ)⟩ : Fin Φ.nextLabel) = ⟨Φ.label c, Φ.label_lt c hcn⟩ :=
      Fin.ext hcl.symm
    rw [this]
    exact hΦ.piece_subset_hyp hcn (Φ.mem_faceSet.mp hx c hc)
  ext x
  constructor
  · intro hx
    obtain ⟨P, hP, hxP⟩ := Φ.mem_centerOf.mp hx
    have hPL : Φ.labels P = L := labels_eq_of_isCenter hS hP hP₀
    refine ⟨hmeet (subset_nerve_of_isCenter hS hP) hPL hxP, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro T hT hxT
    obtain ⟨hTn, hTL, hTS⟩ := Finset.mem_filter.mp hT
    exact hTS ((hΦ.eq_of_labels_eq_of_mem_faceSet hTn (subset_nerve_of_isCenter hS hP)
      (hTL.trans hPL.symm)
      hxT hxP) ▸ hP)
  · rintro ⟨hxY, hxO⟩
    rw [mem_meetLocus_subfamily_card_iff] at hxY
    -- the face through `x` with labels in `L`
    let T : Finset ℕ := (Φ.faceAt x).filter fun c => Φ.label c ∈ L
    have hTsub : T ⊆ Φ.faceAt x := Finset.filter_subset _ _
    have hxT : x ∈ Φ.faceSet T :=
      Φ.mem_faceSet.mpr fun c hc => (Φ.mem_faceAt.mp (hTsub hc)).2
    have hTL : Φ.labels T = L := by
      apply Finset.Subset.antisymm
      · intro ℓ hℓ
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hℓ
        exact (Finset.mem_filter.mp hc).2
      · intro ℓ hℓ
        have hj : e ⟨ℓ, hlt ℓ hℓ⟩ ∈ Ls := (hLs _).mpr ⟨ℓ, hℓ, rfl⟩
        obtain ⟨c, hcn, hcl, hxc⟩ := (hΦ.mem_hyp_iff _ x).mp (hxY _ hj)
        refine Finset.mem_image.mpr
          ⟨c, Finset.mem_filter.mpr ⟨Φ.mem_faceAt.mpr ⟨hcn, hxc⟩, ?_⟩, hcl⟩
        rw [hcl]
        exact hℓ
    have hLne : L.Nonempty := (Φ.nonempty_of_mem_nerve hP₀n).image _
    have hTne : T.Nonempty := by
      obtain ⟨ℓ, hℓ⟩ := hLne
      rw [← hTL] at hℓ
      obtain ⟨c, hc, -⟩ := Finset.mem_image.mp hℓ
      exact ⟨c, hc⟩
    have hTn : T ∈ Φ.nerve :=
      (Φ.mem_nerve_iff T).mpr ⟨hTsub.trans (Φ.faceAt_subset_range x), hTne, x,
        fun c hc => (Φ.mem_faceAt.mp (hTsub hc)).2⟩
    by_contra hxZ
    apply hxO
    simp only [Set.mem_iUnion]
    refine ⟨T, Finset.mem_filter.mpr ⟨hTn, hTL, fun hTS => hxZ ?_⟩, hxT⟩
    exact Φ.faceSet_subset_centerOf hTS hxT

/-- The locus of a centre of the state is a closed submanifold whose codimension is the common
cardinality of its faces ([Kol07, 111, Step 3]: the centre `E^{j₁} ∩ ⋯ ∩ E^{j_r}` is smooth of
codimension `r`). -/
theorem Realizes.isClosedSubmanifold_centerOf (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) :
    IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Φ.centerOf_empty]
    exact ⟨isClosed_empty, fun a ha => ha.elim⟩
  obtain ⟨Ls, O, hLs, hO, hZ⟩ := hΦ.exists_centerOf_eq_meetLocus_inter hS hne
  have hY := hF.isClosedSubmanifold_meetLocus_subfamily (p := (· ∈ Ls))
    (meetLocus_subfamily_card_succ_eq_empty Ls)
  have h := hY.inter_of_isOpen hO (hZ ▸ Φ.isClosed_centerOf S)
  rw [← hZ, hLs] at h
  exact h

/-- The boundary family has simple normal crossings with the locus of a centre of the state, the
condition [Kol07, Definition 66 (3′)] imposes on a centre. -/
theorem Realizes.hasSncWith_centerOf (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) :
    F.HasSncWith ψ₀ (Φ.centerOf S) (faceCard S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Φ.centerOf_empty]
    exact fun a ha => ha.elim
  obtain ⟨Ls, O, hLs, hO, hZ⟩ := hΦ.exists_centerOf_eq_meetLocus_inter hS hne
  have h := (hF.hasSncWith_meetLocus_subfamily (p := (· ∈ Ls))
    (meetLocus_subfamily_card_succ_eq_empty Ls)).inter_of_isOpen hO
  rw [← hZ, hLs] at h
  exact h

/-! ### The order of the monomial ideal along the locus -/

/-- Near a point of the locus of the face `P ∈ S`, the locus of the centre `S` is contained in the
locus of `P`: the other faces of the centre miss the point. -/
theorem Realizes.exists_mem_nhds_centerOf_inter_subset (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) {P : Finset ℕ} (hP : P ∈ S) {x : N}
    (hx : x ∈ Φ.faceSet P) :
    ∃ U ∈ 𝓝 x, Φ.centerOf S ∩ U ⊆ Φ.faceSet P := by
  classical
  refine ⟨(⋃ Q ∈ S.erase P, Φ.faceSet Q)ᶜ,
    (isClosed_biUnion_finset fun Q _ => Φ.isClosed_faceSet Q).isOpen_compl.mem_nhds ?_, ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro Q hQ hxQ
    have hQP := Finset.mem_erase.mp hQ
    exact hQP.1 (hΦ.eq_of_mem_faceSet_of_isCenter hS hQP.2 hP hxQ hx)
  · rintro y ⟨hyZ, hyO⟩
    obtain ⟨Q, hQ, hyQ⟩ := Φ.mem_centerOf.mp hyZ
    by_cases hQP : Q = P
    · exact hQP ▸ hyQ
    · exfalso
      apply hyO
      simp only [Set.mem_iUnion]
      exact ⟨Q, Finset.mem_erase.mpr ⟨hQP, hQ⟩, hyQ⟩

/-- The monomial ideal has order `≥ m` along the locus of a centre at every point of the locus, when
every face of the centre has exponent sum `≥ m` ([Kol07, Definition 66 (4′)]): near a point of the
locus of `P` the locus lies in every piece of `P`, so each factor `𝓘_{piece c}^{a c}`, `c ∈ P`, has
order `≥ a c` along it. -/
theorem Realizes.le_ordAlongIdeal_monomialIdeal_centerOf (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) {r : ℕ} (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r)
    (hge : ∀ P ∈ S, m ≤ Φ.total P) {x : N} (hx : x ∈ Φ.centerOf S) :
    (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hZ.idealSheaf (Φ.monomialIdeal hF hΦ) x := by
  classical
  obtain ⟨P, hP, hxP⟩ := Φ.mem_centerOf.mp hx
  obtain ⟨U, hU, hUP⟩ := hΦ.exists_mem_nhds_centerOf_inter_subset hS hP hxP
  have hPsub : P ⊆ Finset.range Φ.nextComp := ((Φ.mem_nerve_iff P).mp (subset_nerve_of_isCenter
    hS hP)).1
  -- each piece of `P` contains the locus near `x`, so its ideal has order `≥ 1` along the locus
  have hone : ∀ c : Fin Φ.nextComp, c.1 ∈ P →
      ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hZ.idealSheaf (Φ.pieceIdeal hF hΦ c) x := by
    intro c hc
    rw [IdealSheaf.le_ordAlongIdeal_iff, pow_one, pieceIdeal,
      (hΦ.isClosedSubmanifold_piece hF c).stalkIdeal_idealSheaf_eq_vanishingStalk,
      hZ.stalkIdeal_idealSheaf_eq_vanishingStalk]
    have h1 : vanishingStalk (𝕜 := 𝕜) (E := E) (Φ.centerOf S) x =
        vanishingStalk (𝕜 := 𝕜) (E := E) (Φ.centerOf S ∩ U) x :=
      (vanishingStalk_inter_of_mem_nhds hU).symm
    rw [h1]
    exact vanishingStalk_anti (𝕜 := 𝕜) (E := E) (hUP.trans (Φ.faceSet_subset_piece hc)) x
  have hsum : ∑ c : Fin Φ.nextComp, (if c.1 ∈ P then Φ.a c.1 else 0) = Φ.total P := by
    rw [Fin.sum_univ_eq_sum_range (fun c => if c ∈ P then Φ.a c else 0), ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hPsub]
    rfl
  calc (m : ℕ∞) ≤ (Φ.total P : ℕ∞) := by exact_mod_cast hge P hP
    _ = ((∑ c : Fin Φ.nextComp, (if c.1 ∈ P then Φ.a c.1 else 0) : ℕ) : ℕ∞) := by rw [hsum]
    _ ≤ IdealSheaf.ordAlongIdeal hZ.idealSheaf (Φ.monomialIdeal hF hΦ) x := by
      rw [monomialIdeal]
      apply le_ordAlongIdeal_finset_prod (hZ.idealSheaf : IdealSheaf (structureSheaf 𝕜 E N))
        Finset.univ
        (fun c : Fin Φ.nextComp => Φ.pieceIdeal hF hΦ c ^ Φ.a c.1)
        (fun c : Fin Φ.nextComp => if c.1 ∈ P then Φ.a c.1 else 0)
      intro c _
      by_cases hc : c.1 ∈ P
      · rw [ite_eq_left hc]
        have := le_ordAlongIdeal_pow hZ.idealSheaf (hone c hc) (Φ.a c.1)
        rwa [one_mul] at this
      · rw [ite_eq_right hc, Nat.cast_zero]
        exact zero_le

end Hironaka.Manifold.BMO.PieceFamily
