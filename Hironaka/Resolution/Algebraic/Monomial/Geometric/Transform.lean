/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
public import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Chart
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Exponent
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Kernel
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Snc.DictionaryRegular
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.TotalTransformOnCentre
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The marked transform of the monomial ideal

Kollár's Step 3 blows up a centre `Z_S` of order `≥ m` for the marked monomial ideal
`𝒪_X(−∑ a_D D)`; the marked transform `π_*^{-1}(I, m) = 𝒪(mF) · π^* I` of
[Kol07, Definition 60] is again the monomial ideal of the transported piece family: the
exponent of an old piece is unchanged and the exponent of the new piece `F_P = π⁻¹(Z_P)` is
`a(P) − m`, Kollár's "its coefficient is `a_{j_ℓ} = a_{j₁} + a_{j₂} − m`" of
[Kol07, 111, Step 3.2]. This module proves it stalk by stalk; the computation is the one behind
[Hau14, Proposition 5.4], not in the sources in this form.

* `stalkIdeal_monomial_exponentAt`, `monomial_exponentAt_eq_prod`: the marked monomial ideal of
  a realising piece family is the product `∏_c 𝓘(D_c)^{a_c}` over the pieces. At a point `x` its
  stalk is `∏_{c ∈ faceAt x} (𝓘(D_c))_x^{a_c}` (`stalkIdeal_monomial` of
  `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Split.lean`, the inner product over the
  components of a member collapsing to the one component through `x`). These are stated for a
  regular ambient scheme with `IsSnc` and `Realizes` only, without a structure morphism, so that
  they apply on the blow-up, where the hypotheses give regular stalks but no relative dimension.
* `stalkIdeal_vanishingIdeal_blowUpPieces_piece_of_lt`,
  `stalkIdeal_vanishingIdeal_blowUpPieces_piece_newComp`: the stalks of the transported pieces'
  ideals, the strict transform of the piece's ideal and the exceptional ideal.
* `comap_monomial_eq`, `markedTransform_monomial`:
  `π^* 𝒪_X(−∑ a_c D_c) = F^m · 𝒪_{X'}(−∑ a'_{c'} D'_{c'})`. At a point `x'` of `F` over
  `x ∈ Z_Q`, `π^* z_c = u_c · e` with `e` the exceptional generator and `(u_c)` the strict
  transform's stalk for `c ∈ Q`, while for `c ∉ Q` the strict transform is `(π^* z_c)`
  (`Hironaka/Scheme/Snc/TotalTransformSnc.lean`); so `π^* I_x = ∏_c (u_c)^{a_c} · e^{a(Q)}` and the
  exponent of `F_Q` is `a(Q) − m` once `F^m` is divided out. Off `F` the blow-up is an
  isomorphism.

`markedTransform_monomial` is applied at every step of the run in
`Hironaka/Resolution/Algebraic/Monomial/Geometric/OrderSeq.lean`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal
  Scheme.IdealSheafData Scheme IdealSheafData

namespace Hironaka.Monomial

variable {X : Scheme.{u}}

namespace PieceFamily

variable (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}

/-! ### The monomial ideal as a product over the pieces -/

/-- The stalk of the marked monomial ideal at `x` is the product over the pieces through `x` of
the powers of their reduced stalks: the inner product of `stalkIdeal_monomial`
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Split.lean`) over the components of a member
through `x` collapses to the one component through `x`, whose exponent is that of the unique piece
through its generic point, and the members through `x` correspond to the pieces through `x`. -/
theorem stalkIdeal_monomial_exponentAt [NoetherianSpace X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (hE : E.IsSnc)
    (hΦ : Φ.Realizes E e) (x : X) :
    (E.monomial Φ.exponentAt).stalkIdeal x =
      ∏ c ∈ Φ.faceAt x, (vanishingIdeal (Φ.piece c)).stalkIdeal x ^ Φ.a c := by
  classical
  -- the piece through `x` of each member through `x`
  have hpc : ∀ i : {i : E.ι // x ∈ (E.component i).support},
      ∃ c, c < Φ.nextComp ∧ Φ.label c = e i.1 ∧ x ∈ Φ.piece c := by
    intro i
    have := i.2
    rw [hΦ.support_eq, mem_finset_sup_iff] at this
    obtain ⟨c, hc, hxc⟩ := this
    exact ⟨c, Finset.mem_range.mp (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2, hxc⟩
  choose pc hpcn hpclab hpcx using hpc
  -- the exponent at a generic point of the component of `E^i` through `x` is `a (pc i)`
  have hexp : ∀ (i : {i : E.ι // x ∈ (E.component i).support}) {η : X},
      η ∈ (E.component i.1).support.genericPoints → η ⤳ x → Φ.exponentAt η = Φ.a (pc i) := by
    intro i η hη hηx
    obtain ⟨c, hc, hlab, hηc, -, hexp⟩ :=
      Φ.faceAt_eq_singleton_of_mem_genericPoints_of_regular hE hΦ (hreg η) hη
    rw [hexp]
    have hxc : x ∈ Φ.piece c := hηx.mem_closed (Φ.piece c).isClosed hηc
    by_cases h : c = pc i
    · rw [h]
    · exact (Φ.not_mem_piece_of_label_eq hΦ hc (hpcn i) h (hlab.trans (hpclab i).symm) hxc
        (hpcx i)).elim
  rw [Hironaka.BMO.stalkIdeal_monomial E
      (fun i => Hironaka.BMO.Snc.genericPoints_component_finite E i) _ x,
    ← Fintype.prod_subtype_mul_prod_subtype (fun i : E.ι => x ∈ (E.component i).support)]
  have h2 : ∏ i : {i : E.ι // ¬ x ∈ (E.component i).support},
      (∏ᶠ η ∈ (E.component i.1).support.genericPoints,
        ((vanishingIdeal (Closeds.closure {η})).stalkIdeal x) ^ Φ.exponentAt η) = 1 :=
    Finset.prod_eq_one fun i _ => Hironaka.BMO.Snc.finprod_stalk_eq_one_of_notMem E i.2 _
  have h1 : ∀ i : {i : E.ι // x ∈ (E.component i).support},
      (∏ᶠ η ∈ (E.component i.1).support.genericPoints,
        ((vanishingIdeal (Closeds.closure {η})).stalkIdeal x) ^ Φ.exponentAt η) =
        ((E.component i.1).stalkIdeal x) ^ Φ.a (pc i) := by
    intro i
    obtain ⟨η, hη, hηx⟩ := Hironaka.BMO.exists_genericPoint_specializes _ i.2
    rw [finprod_stalk_eq_of_specializes_of_isRegular_subscheme (hE.1 i.1) hη hηx, hexp i hη hηx]
  rw [h2, mul_one, Finset.prod_congr rfl fun i _ => h1 i]
  -- the pieces through `x` are exactly the `pc i`
  refine Finset.prod_bij (fun i _ => pc i) (fun i _ => Φ.mem_faceAt.mpr ⟨hpcn i, hpcx i⟩) ?_ ?_ ?_
  · intro i _ j _ hij
    have hlab : ((e i.1 : Fin _) : ℕ) = e j.1 := by rw [← hpclab i, ← hpclab j, hij]
    exact Subtype.ext (e.injective (Fin.ext hlab))
  · intro c hc
    obtain ⟨hcn, hxc⟩ := Φ.mem_faceAt.mp hc
    refine ⟨⟨Φ.memberOf e c hcn, Φ.mem_support_component_of_mem_piece hΦ hcn hxc⟩,
      Finset.mem_univ _, ?_⟩
    by_contra hne
    exact Φ.not_mem_piece_of_label_eq hΦ (hpcn _) hcn hne
      ((hpclab _).trans (Φ.coe_apply_memberOf e c hcn)) (hpcx _) hxc
  · intro i _
    rw [Φ.stalkIdeal_vanishingIdeal_piece hE hΦ (hpcn i) (hpcx i)]
    have hm : Φ.memberOf e (pc i) (hpcn i) = i.1 := by
      rw [memberOf, OrderIso.symm_apply_eq]
      exact Fin.ext (hpclab i)
    rw [hm]

/-- *The marked monomial ideal is the product over the pieces* `∏_{c < nextComp} 𝓘(D_c)^{a_c}`:
stalk by stalk, the pieces missing `x` contribute the unit ideal. -/
theorem monomial_exponentAt_eq_prod [NoetherianSpace X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (hE : E.IsSnc)
    (hΦ : Φ.Realizes E e) :
    E.monomial Φ.exponentAt =
      ∏ c ∈ Finset.range Φ.nextComp, vanishingIdeal (Φ.piece c) ^ Φ.a c := by
  refine ext_stalkIdeal fun x => ?_
  rw [Φ.stalkIdeal_monomial_exponentAt hreg hE hΦ x, stalkIdeal_finset_prod]
  simp only [stalkIdeal_pow]
  refine Finset.prod_subset (Φ.faceAt_subset_range x) fun c hc hcx => ?_
  have hxc : x ∉ Φ.piece c := fun h => hcx (Φ.mem_faceAt.mpr ⟨Finset.mem_range.mp hc, h⟩)
  rw [stalkIdeal_eq_top_of_notMem_support _ (by
      rw [Hironaka.Sequence.support_vanishingIdeal_eq]; exact hxc), Ideal.top_pow]
  exact Ideal.one_eq_top.symm

/-! ### The stalks of the transported pieces -/

variable {k : Type u} [Field k] [PerfectField k] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
  {n m : ℕ} {hV : Φ.IsValid n m}

include f in
/-- The reduced ideal of the strict transform of an old piece has, at every point, the stalk of
the strict transform of the piece's ideal: through the member of the transported family (a
smooth divisor, `stalkIdeal_vanishingIdeal_piece` on the blow-up), whose strict transform has
the same saturation stalk as the piece's (`stalkIdeal_strictTransformAlong_eq_iSup`). -/
theorem stalkIdeal_vanishingIdeal_blowUpPieces_piece_of_lt (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {c : ℕ} (hc : c < Φ.nextComp)
    (x' : IdealSheafData.blowUp (Φ.centerOf S)) :
    (vanishingIdeal ((Φ.blowUpPieces S m).piece c)).stalkIdeal x' =
      ((vanishingIdeal (Φ.piece c)).strictTransformAlong (IdealSheafData.blowUpπ (Φ.centerOf S))
          ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S)))).stalkIdeal x' := by
  have hE' := totalTransform_isSnc f E _ hE
    (Φ.hasSncWith_centerOf hE hΦ hS)
  have hΦ' := Φ.realizes_blowUpPieces f hE hΦ hS
  have hsupp : ((vanishingIdeal (Φ.piece c)).strictTransformAlong
      (IdealSheafData.blowUpπ (Φ.centerOf S)) ((Φ.centerOf S).comap
      (IdealSheafData.blowUpπ (Φ.centerOf S)))).support =
      (Φ.blowUpPieces S m).piece c := by
    rw [Φ.blowUpPieces_piece_of_lt S hc, strictTransformCloseds_eq_support f]
  by_cases hx' : x' ∈ (Φ.blowUpPieces S m).piece c
  · have hc' : c < (Φ.blowUpPieces S m).nextComp := lt_of_lt_of_le hc (Nat.le_add_right _ _)
    rw [(Φ.blowUpPieces S m).stalkIdeal_vanishingIdeal_piece hE' hΦ' hc' hx']
    -- the member of the transported piece is the strict transform of the piece's member
    have hmem : (Φ.blowUpPieces S m).memberOf (E := E.totalTransform (Φ.centerOf S))
        (extendIso e) c hc' = (toLex (Sum.inl (Φ.memberOf e c hc)) : E.ι ⊕ₗ PUnit.{u + 1}) := by
      refine (extendIso e).injective ?_
      change extendIso e ((extendIso e).symm ⟨(Φ.blowUpPieces S m).label c, _⟩) =
        extendIso e (toLex (Sum.inl (Φ.memberOf e c hc)))
      rw [OrderIso.apply_symm_apply, extendIso_inl]
      refine Fin.ext ?_
      change (Φ.blowUpPieces S m).label c = ((e (Φ.memberOf e c hc) : Fin _) : ℕ)
      rw [Φ.coe_apply_memberOf]
      exact Φ.blowUpPieces_label_of_lt S hc
    rw [hmem]
    change ((E.component (Φ.memberOf e c hc)).strictTransformAlong
        (IdealSheafData.blowUpπ (Φ.centerOf S)) ((Φ.centerOf S).comap
        (IdealSheafData.blowUpπ (Φ.centerOf S)))).stalkIdeal x' = _
    rw [stalkIdeal_strictTransformAlong_eq_iSup, stalkIdeal_strictTransformAlong_eq_iSup]
    refine iSup_colon_congr ?_ rfl
    rw [stalkIdeal_comap, stalkIdeal_comap, Φ.stalkIdeal_vanishingIdeal_piece hE hΦ hc
      (Φ.π_mem_piece_of_mem_blowUpPieces_piece f hc hx')]
  · rw [stalkIdeal_eq_top_of_notMem_support _ (by
        rw [Hironaka.Sequence.support_vanishingIdeal_eq]; exact hx'),
      stalkIdeal_eq_top_of_notMem_support _ (by rw [hsupp]; exact hx')]

include f in
/-- The reduced ideal of the new piece `F_P = π⁻¹(Z_P)` has, at a point over `Z_P`, the stalk of
the exceptional ideal (the new piece's member is the exceptional divisor). -/
theorem stalkIdeal_vanishingIdeal_blowUpPieces_piece_newComp (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {P : Finset ℕ} (hP : P ∈ S)
    (x' : IdealSheafData.blowUp (Φ.centerOf S)) (hx : IdealSheafData.blowUpπ
        (Φ.centerOf S) x' ∈ Φ.faceSet P) :
    (vanishingIdeal ((Φ.blowUpPieces S m).piece (Φ.newComp S P))).stalkIdeal x' =
      ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).stalkIdeal x' := by
  have hE' := totalTransform_isSnc f E _ hE
    (Φ.hasSncWith_centerOf hE hΦ hS)
  have hΦ' := Φ.realizes_blowUpPieces f hE hΦ hS
  have hx' : x' ∈ (Φ.blowUpPieces S m).piece (Φ.newComp S P) :=
    (Φ.mem_blowUpPieces_piece_of_le (Nat.le_add_right _ _)).mpr ⟨P, hP, rfl, hx⟩
  have hc' : Φ.newComp S P < (Φ.blowUpPieces S m).nextComp :=
    MonomialState.newComp_lt (st := Φ.toState n m hV) hP
  rw [(Φ.blowUpPieces S m).stalkIdeal_vanishingIdeal_piece hE' hΦ' hc' hx']
  have hmem : (Φ.blowUpPieces S m).memberOf (E := E.totalTransform (Φ.centerOf S)) (extendIso e)
      (Φ.newComp S P) hc' = (toLex (Sum.inr PUnit.unit) : E.ι ⊕ₗ PUnit.{u + 1}) := by
    refine (extendIso e).injective ?_
    change extendIso e ((extendIso e).symm ⟨(Φ.blowUpPieces S m).label (Φ.newComp S P), _⟩) =
      extendIso e (toLex (Sum.inr PUnit.unit))
    rw [OrderIso.apply_symm_apply, extendIso_inr]
    refine Fin.ext ?_
    change (Φ.blowUpPieces S m).label (Φ.newComp S P) = Φ.nextLabel
    exact Φ.blowUpPieces_label_newComp S P
  rw [hmem]
  rfl

/-! ### The total transform of a piece's ideal at a point of the exceptional divisor -/

include f in
/-- At a point `x'` of the exceptional divisor over `x ∈ Z_Q`, the total transform of the ideal
of a piece `c` is the strict transform times the exceptional ideal if `c ∈ Q` (`π^* z_c = u_c · e`)
and the strict transform itself if `c ∉ Q` (the piece is transversal to the centre, or misses
`x`); the two cases of `Hironaka/Scheme/Snc/TotalTransformSnc.lean`, as in [Hau14, Proposition 5.4].
-/
theorem stalkIdeal_comap_pieceIdeal_eq (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {Q : Finset ℕ} (hQ : Q ∈ S)
    {x' : IdealSheafData.blowUp (Φ.centerOf S)} (hxQ : IdealSheafData.blowUpπ
        (Φ.centerOf S) x' ∈ Φ.faceSet Q) {c : ℕ}
    (hc : c < Φ.nextComp) :
    ((vanishingIdeal (Φ.piece c)).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).stalkIdeal x' =
      ((vanishingIdeal (Φ.piece c)).strictTransformAlong (IdealSheafData.blowUpπ (Φ.centerOf S))
          ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S)))).stalkIdeal x' *
      ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).stalkIdeal x' ^
        (if c ∈ Q then 1 else 0) := by
  classical
  have hQn : ∀ c ∈ Q, c < Φ.nextComp := fun c hc => Φ.lt_nextComp_of_mem_nerve (hS.1 hQ) hc
  have hxZ : IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ (Φ.centerOf S).support :=
    Φ.faceSet_le_support_centerOf hQ hxQ
  have hx'F : x' ∈ ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).support :=
    (mem_support_comap_iff' (Φ.centerOf S) _ x').mpr hxZ
  have hZp := Φ.sncData_pieceIdeal hE hΦ hS
  have hreg := isRegularLocalRing_stalk f (IdealSheafData.blowUpπ (Φ.centerOf S) x')
  by_cases hxc : IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ Φ.piece c
  · -- Kollár's coordinates at `x`: `Z_x = (z_j : j ∈ s)`, `s` the coordinates of the pieces of `Q`
    obtain ⟨nx, z, hz⟩ := hE.2 (IdealSheafData.blowUpπ (Φ.centerOf S) x')
    obtain ⟨s, hs, hsQ, hsQ'⟩ := Φ.exists_stalkIdeal_faceIdeal_eq_span hE hΦ hQn hxQ hz
    have hZs : (Φ.centerOf S).stalkIdeal (IdealSheafData.blowUpπ (Φ.centerOf S) x') = span
        (z '' ↑s) :=
      (Φ.stalkIdeal_centerOf_eq_faceIdeal hS hQ hxQ).trans hs
    obtain ⟨jc, hjc⟩ := Φ.exists_stalkIdeal_vanishingIdeal_piece_eq_span hE hΦ hc hxc hz
    -- the exceptional generator `π^* z_{j₀}`
    obtain ⟨j₀, -, hF⟩ := exists_stalkIdeal_comap_eq_span_of_mem_support f Φ.pieceIdeal
      (Φ.centerOf S) hZp x' hx'F hZs fun j hj => by
        obtain ⟨c', hc', hc'j⟩ := hsQ' j hj
        exact ⟨⟨c', hQn c' hc'⟩, hc'j⟩
    rw [stalkIdeal_comap_π_eq (Φ.centerOf S) _ x' hjc]
    by_cases hjcs : jc ∈ s
    · -- `c` is a piece of `Q`: `π^* z_c = u · e`, the strict transform has stalk `(u)`
      have hcQ : c ∈ Q := by
        obtain ⟨c', hc'Q, hc'⟩ := hsQ' jc hjcs
        have := Φ.eq_of_stalkIdeal_vanishingIdeal_piece_eq f hE hΦ hc (hQn c' hc'Q) hxc
          (Φ.mem_faceSet.mp hxQ c' hc'Q) (hjc.trans hc'.symm)
        rw [this]
        exact hc'Q
      obtain ⟨u, hu, hstalk⟩ := exists_stalkIdeal_strictTransformAlong_eq_span_of_mem f
        Φ.pieceIdeal (Φ.centerOf S) hZp ⟨c, hc⟩ x' hx'F hz.1 hZs hjc hjcs hF
      rw [ite_eq_left hcQ, pow_one, hF,
        show ((vanishingIdeal (Φ.piece c)).strictTransformAlong
            (IdealSheafData.blowUpπ (Φ.centerOf S)) ((Φ.centerOf S).comap
            (IdealSheafData.blowUpπ (Φ.centerOf S)))).stalkIdeal x' = span {u} from hstalk,
        Ideal.span_singleton_mul_span_singleton, hu]
    · -- `c` is transversal to the center: the strict transform is the total transform
      have hcQ : c ∉ Q := fun hcQ => by
        obtain ⟨j, hj, hj'⟩ := hsQ c hcQ
        have hzz : z jc ∈ span {z j} := by
          rw [← hj', hjc]
          exact Ideal.mem_span_singleton_self _
        have hjj : jc = j := by
          by_contra hne
          exact notMem_span_singleton_of_ne hz.1.1 hz.1.2 (fun h => hne h.symm) hzz
        exact hjcs (hjj ▸ hj)
      rw [ite_eq_right hcQ, pow_zero, mul_one]
      exact (stalkIdeal_strictTransformAlong_of_notMem f Φ.pieceIdeal (Φ.centerOf S) hZp ⟨c, hc⟩
        x' hx'F hz.1 hZs hjc hjcs).symm
  · -- `x` off the piece: both sides are the unit ideal
    have hcQ : c ∉ Q := fun hcQ => hxc (Φ.mem_faceSet.mp hxQ c hcQ)
    have hxc' : IdealSheafData.blowUpπ (Φ.centerOf S) x' ∉ (vanishingIdeal (Φ.piece c)).support :=
        by
      rw [Hironaka.Sequence.support_vanishingIdeal_eq]
      exact hxc
    rw [ite_eq_right hcQ, pow_zero, mul_one, stalkIdeal_comap,
      stalkIdeal_eq_top_of_notMem_support _ hxc',
      Ideal.map_top, stalkIdeal_eq_top_of_notMem_support]
    intro h
    exact hxc' (π_mem_support_of_mem_support_strictTransformAlong (Φ.centerOf S) _ x' h)

/-! ### The total transform of the monomial ideal -/

variable [QuasiCompact f]

include f in
/-- Stalk by stalk: `π^* 𝒪_X(−∑ a_c D_c) = F^m · 𝒪_{X'}(−∑ a'_{c'} D'_{c'})` at every point of the
blow-up. Over a point of `Z_Q` the old pieces contribute their strict transforms and, for the
pieces of `Q`, one exceptional factor each (`F^{a(Q)}` in all), the new piece `F_Q` contributes
`F^{a(Q) − m}`, and the other new pieces miss the point; off the exceptional divisor the blow-up
is an isomorphism. -/
theorem stalkIdeal_comap_monomial_eq (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) (hge : ∀ P ∈ S, m ≤ Φ.total P)
    (x' : IdealSheafData.blowUp (Φ.centerOf S)) :
    ((E.monomial Φ.exponentAt).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).stalkIdeal x' =
      (((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))) ^ m *
        (E.totalTransform (Φ.centerOf S)).monomial
          (Φ.blowUpPieces S m).exponentAt).stalkIdeal x' := by
  classical
  have hLN : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hN : IsNoetherian X := f.isNoetherian_of_field
  have hproper := blowUp.isProper_π (Φ.centerOf S)
  have hN' : IsNoetherian (Φ.centerOf S).blowUp :=
    ((Φ.centerOf S).blowUpπ ≫ f).isNoetherian_of_field
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f
  have hZp := Φ.sncData_pieceIdeal hE hΦ hS
  have hreg' : ∀ x' : IdealSheafData.blowUp (Φ.centerOf S),
      IsRegularLocalRing ((IdealSheafData.blowUp (Φ.centerOf S)).presheaf.stalk x') :=
    isRegularLocalRing_stalk_blowUp' f Φ.pieceIdeal (Φ.centerOf S) hZp
  have hE' := totalTransform_isSnc f E _ hE
    (Φ.hasSncWith_centerOf hE hΦ hS)
  have hΦ' := Φ.realizes_blowUpPieces f hE hΦ hS
  rw [Φ.monomial_exponentAt_eq_prod hreg hE hΦ,
    (Φ.blowUpPieces S m).monomial_exponentAt_eq_prod hreg' hE' hΦ', comap_finset_prod,
    stalkIdeal_finset_prod, stalkIdeal_mul, stalkIdeal_pow, stalkIdeal_finset_prod]
  simp only [comap_pow, stalkIdeal_pow]
  rw [Φ.blowUpPieces_nextComp, Finset.prod_range_add]
  -- the old pieces: the strict transforms, with the old exponents
  have hold : ∀ c ∈ Finset.range Φ.nextComp,
      (vanishingIdeal ((Φ.blowUpPieces S m).piece c)).stalkIdeal x' ^ (Φ.blowUpPieces S m).a c =
        ((vanishingIdeal (Φ.piece c)).strictTransformAlong (IdealSheafData.blowUpπ (Φ.centerOf S))
            ((Φ.centerOf S).comap
            (IdealSheafData.blowUpπ (Φ.centerOf S)))).stalkIdeal x' ^ Φ.a c := by
    intro c hc
    have hcn := Finset.mem_range.mp hc
    rw [Φ.stalkIdeal_vanishingIdeal_blowUpPieces_piece_of_lt f hE hΦ hS hcn,
      Φ.blowUpPieces_a_of_lt S hcn]
  rw [Finset.prod_congr rfl hold]
  by_cases hx'F : x' ∈ ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).support
  · obtain ⟨Q, hQ, hxQ⟩ := (Φ.mem_support_centerOf_iff S _).mp
      ((mem_support_comap_iff' (Φ.centerOf S) _ x').mp hx'F)
    have hQn : Q ⊆ Finset.range Φ.nextComp := (Φ.mem_nerve.mp (hS.1 hQ)).1
    -- the new pieces: only `F_Q` passes through `x'`
    have hnew : ∏ r ∈ Finset.range S.card,
        (vanishingIdeal ((Φ.blowUpPieces S m).piece (Φ.nextComp + r))).stalkIdeal x' ^
          (Φ.blowUpPieces S m).a (Φ.nextComp + r) =
        ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).stalkIdeal x' ^
            (Φ.total Q - m) := by
      rw [Finset.prod_eq_single (MonomialState.rank S Q)]
      · change (vanishingIdeal ((Φ.blowUpPieces S m).piece (Φ.newComp S Q))).stalkIdeal x' ^
          (Φ.blowUpPieces S m).a (Φ.newComp S Q) = _
        rw [Φ.stalkIdeal_vanishingIdeal_blowUpPieces_piece_newComp f hE hΦ hS hQ x' hxQ,
          Φ.blowUpPieces_a_newComp S hQ]
      · intro r _ hr
        have hx'r : x' ∉ (Φ.blowUpPieces S m).piece (Φ.nextComp + r) := by
          intro h
          obtain ⟨P, hP, hPr, hxP⟩ := (Φ.mem_blowUpPieces_piece_of_le (Nat.le_add_right _ _)).mp h
          have hPQ : P = Q := Φ.eq_of_mem_faceSet_of_isCenter hS hP hQ hxP hxQ
          subst hPQ
          exact hr (Nat.add_left_cancel
            (hPr : Φ.nextComp + MonomialState.rank S _ = Φ.nextComp + r)).symm
        rw [stalkIdeal_eq_top_of_notMem_support _ (by
            rw [Hironaka.Sequence.support_vanishingIdeal_eq]; exact hx'r), Ideal.top_pow]
        exact Ideal.one_eq_top.symm
      · intro h
        exact absurd (Finset.mem_range.mpr (MonomialState.rank_lt_card hQ)) h
    rw [hnew]
    -- the old pieces: `π^* 𝓘(D_c) = 𝓘(D'_c) · F^{[c ∈ Q]}`
    have hT : ∀ c ∈ Finset.range Φ.nextComp,
        ((vanishingIdeal (Φ.piece c)).comap (IdealSheafData.blowUpπ
            (Φ.centerOf S))).stalkIdeal x' ^ Φ.a c =
          ((vanishingIdeal (Φ.piece c)).strictTransformAlong (IdealSheafData.blowUpπ (Φ.centerOf S))
              ((Φ.centerOf S).comap
              (IdealSheafData.blowUpπ (Φ.centerOf S)))).stalkIdeal x' ^ Φ.a c *
          ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).stalkIdeal x' ^
            (if c ∈ Q then Φ.a c else 0) := by
      intro c hc
      rw [Φ.stalkIdeal_comap_pieceIdeal_eq f hE hΦ hS hQ hxQ (Finset.mem_range.mp hc), mul_pow,
        ← pow_mul, boole_mul]
    rw [Finset.prod_congr rfl hT, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.sum_ite_mem, Finset.inter_eq_right.mpr hQn]
    have ht : ∑ c ∈ Q, Φ.a c = m + (Φ.total Q - m) := (Nat.add_sub_cancel' (hge Q hQ)).symm
    rw [ht, pow_add]
    ring
  · -- off the exceptional divisor: the blow-up is an isomorphism, no new piece passes
    have hnew : ∏ r ∈ Finset.range S.card,
        (vanishingIdeal ((Φ.blowUpPieces S m).piece (Φ.nextComp + r))).stalkIdeal x' ^
          (Φ.blowUpPieces S m).a (Φ.nextComp + r) = 1 := by
      refine Finset.prod_eq_one fun r _ => ?_
      have hx'r : x' ∉ (Φ.blowUpPieces S m).piece (Φ.nextComp + r) := by
        intro h
        obtain ⟨P, hP, -, hxP⟩ := (Φ.mem_blowUpPieces_piece_of_le (Nat.le_add_right _ _)).mp h
        exact hx'F ((mem_support_comap_iff' (Φ.centerOf S) _ x').mpr
          (Φ.faceSet_le_support_centerOf hP hxP))
      rw [stalkIdeal_eq_top_of_notMem_support _ (by
          rw [Hironaka.Sequence.support_vanishingIdeal_eq]; exact hx'r), Ideal.top_pow]
      exact Ideal.one_eq_top.symm
    rw [hnew, mul_one, stalkIdeal_eq_top_of_notMem_support _ hx'F, Ideal.top_pow, Ideal.top_mul]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [stalkIdeal_comap, stalkIdeal_strictTransformAlong_of_notMem_support (Φ.centerOf S) _ hx'F]

include f in
/-- *The total transform of the marked monomial ideal is `F^m` times the monomial ideal of the
transported piece family*: the old pieces keep their exponents, the new piece `F_P` gets
`a(P) − m` ([Kol07, 111, Step 3.2]). -/
theorem comap_monomial_eq (hE : E.IsSnc) (hΦ : Φ.Realizes E e) {S : Finset (Finset ℕ)}
    (hS : (Φ.toState n m hV).IsCenter S) (hge : ∀ P ∈ S, m ≤ Φ.total P) :
    (E.monomial Φ.exponentAt).comap (Φ.centerOf S).blowUpπ =
      (Φ.centerOf S).exceptionalDivisor ^ m *
        (E.totalTransform (Φ.centerOf S)).monomial (Φ.blowUpPieces S m).exponentAt :=
  ext_stalkIdeal fun x' => Φ.stalkIdeal_comap_monomial_eq f hE hΦ hS hge x'

include f in
/-- *The marked transform of the marked monomial ideal under the blow-up of a centre of order
`≥ m` is the monomial ideal of the transported piece family*: `𝒪(mF) · π^* I` of
[Kol07, Definition 60] divides `F^m` out of the total transform. -/
theorem markedTransform_monomial (hE : E.IsSnc) (hΦ : Φ.Realizes E e) {S : Finset (Finset ℕ)}
    (hS : (Φ.toState n m hV).IsCenter S) (hge : ∀ P ∈ S, m ≤ Φ.total P) :
    (E.monomial Φ.exponentAt).markedTransform (Φ.centerOf S) m =
      (E.totalTransform (Φ.centerOf S)).monomial (Φ.blowUpPieces S m).exponentAt :=
  (eq_markedTransform_of_pow_mul_eq (Φ.centerOf S) (E.monomial Φ.exponentAt) m _
    (Φ.comap_monomial_eq f hE hΦ hS hge).symm).symm

end PieceFamily

end Hironaka.Monomial
