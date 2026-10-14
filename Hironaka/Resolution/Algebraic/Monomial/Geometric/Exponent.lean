/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Local
public import Hironaka.Algebra.Local.Order
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
import Hironaka.Algebra.Local.CohenIso
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Snc.ComponentStalks
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Snc.DictionaryRegular
import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.ParameterAlgebra
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The exponents of a piece family and the order of its monomial ideal

The marked monomial ideal of a realising piece family is `E.monomial Φ.exponentAt` in the sense
of `Hironaka/Resolution/Algebraic/MarkedOrderReduction/MonomialPart.lean`, the exponent at a generic
point of a member being the exponent of the unique piece through it. Not in the sources as
statements.

* `faceAt_eq_singleton_of_mem_genericPoints`: exactly one piece passes through a generic point
  of a member, a piece of the member's label, since no other member passes
  (`notMem_support_of_ne` of `Hironaka/Resolution/Algebraic/Snc/ComponentStalks.lean`) and two
  pieces of one label are disjoint.
* `monomial_exponentAt_ofDivisorFamily`: the exponent function of the input family gives back
  the marked monomial ideal `E.monomial a` (`monomial_congr` of
  `Hironaka/Resolution/Algebraic/MarkedOrderReduction/SplitMain.lean`: a monomial ideal depends on
  its exponents at the generic points only, where the input family's exponent is `a`).
* `ord_monomial_eq_total`, `leOrdAlong_centerOf`: the order of the marked monomial ideal at a
  point is the sum of the exponents of the pieces through it. The stalk is a product of powers
  of distinct regular parameters, and the order is additive on a regular local ring containing
  `ℚ` (`ordElem_mul_of_algebraRat` of `Hironaka/Algebra/Local/CohenIso.lean`). So the order along a
  centre whose faces have sum `≥ m` is `≥ m`, condition (4′) of [Kol07, Definition 66] for the
  blow-ups of Step 3, Kollár's `a_{j₁} + ⋯ + a_{j_r} ≥ m` in [Kol07, 111, Step 3.r].

The last two results are what `Hironaka/Resolution/Algebraic/Monomial/Geometric/OrderSeq.lean` uses
to show that the geometric Step 3 is a blow-up sequence of order `≥ m` ending with `max-ord < m`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal Scheme
  Scheme.IdealSheafData

namespace Hironaka.Monomial.PieceFamily

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
  (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}

/-! ### The face through a generic point of a member -/

/-- Exactly one piece passes through a generic point `η` of a member, a piece of the member's
label, when the stalk at `η` is regular: the general form of
`faceAt_eq_singleton_of_mem_genericPoints` below, with the regularity of the stalk as the
hypothesis, for use on the blow-up. -/
theorem faceAt_eq_singleton_of_mem_genericPoints_of_regular (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {j : E.ι} {η : X} (hreg : IsRegularLocalRing (X.presheaf.stalk η))
    (hη : η ∈ (E.component j).support.genericPoints) :
    ∃ c, c < Φ.nextComp ∧ Φ.label c = e j ∧ η ∈ Φ.piece c ∧ Φ.faceAt η = {c} ∧
      Φ.exponentAt η = Φ.a c := by
  classical
  have hηj : η ∈ (E.component j).support := hη.1
  rw [hΦ.support_eq, mem_finset_sup_iff] at hηj
  obtain ⟨c, hc, hηc⟩ := hηj
  obtain ⟨hcr, hlab⟩ := Finset.mem_filter.mp hc
  have hcn := Finset.mem_range.mp hcr
  have huniq : ∀ c', c' < Φ.nextComp → η ∈ Φ.piece c' → c' = c := by
    intro c' hc' hηc'
    have hmem := Φ.mem_support_component_of_mem_piece hΦ hc' hηc'
    have hj : Φ.memberOf e c' hc' = j := by
      by_contra hne
      exact notMem_support_of_ne_of_isSnc hE hne hreg hη hmem
    have hlab' : Φ.label c' = Φ.label c := by
      have := congrArg (fun a : E.ι => ((e a : Fin _) : ℕ)) hj
      simp only [Φ.coe_apply_memberOf] at this
      rw [this, hlab]
    by_contra hne
    exact Φ.not_mem_piece_of_label_eq hΦ hc' hcn hne hlab' hηc' hηc
  have hface : Φ.faceAt η = {c} := by
    ext c'
    rw [Φ.mem_faceAt, Finset.mem_singleton]
    exact ⟨fun h => huniq c' h.1 h.2, fun h => h ▸ ⟨hcn, hηc⟩⟩
  refine ⟨c, hcn, hlab, hηc, hface, ?_⟩
  rw [exponentAt, hface, Finset.sup_singleton]

include f in
/-- Exactly one piece passes through a generic point `η` of a member `E^j`, a piece of the label
of `j` (the other members miss `η`), so the exponent at `η` is that piece's exponent. -/
theorem faceAt_eq_singleton_of_mem_genericPoints (hE : E.IsSnc) (hΦ : Φ.Realizes E e) {j : E.ι}
    {η : X} (hη : η ∈ (E.component j).support.genericPoints) :
    ∃ c, c < Φ.nextComp ∧ Φ.label c = e j ∧ η ∈ Φ.piece c ∧ Φ.faceAt η = {c} ∧
      Φ.exponentAt η = Φ.a c :=
  Φ.faceAt_eq_singleton_of_mem_genericPoints_of_regular hE hΦ
    (isRegularLocalRing_stalk f η) hη

/-! ### The input family's exponents -/

include f in
/-- The exponent function of the input family gives back the marked monomial ideal
`E.monomial a` (one exponent per generic point of a member): at a generic point of a member the
unique piece through it is its own irreducible component, whose exponent is `a` there. -/
theorem monomial_exponentAt_ofDivisorFamily (hE : E.IsSnc) {L k' : ℕ} (a : X → ℕ)
    (e' : E.ι ≃o Fin L) (σ : Fin k' ≃ Components E) :
    E.monomial (ofDivisorFamily E a e' σ).exponentAt = E.monomial a := by
  classical
  refine Hironaka.BMO.monomial_congr E fun i η hη => ?_
  have hΦ := ofDivisorFamily_realizes E a e' σ hE
  obtain ⟨c, hc, -, hηc, -, hexp⟩ :=
    (ofDivisorFamily E a e' σ).faceAt_eq_singleton_of_mem_genericPoints f hE hΦ hη
  rw [hexp]
  -- the piece `c` is the closure of the generic point of a component; `η` lies on it, so it is
  -- that generic point
  have hck : c < k' := hc
  change (if h : c < k' then a ((σ ⟨c, h⟩).2 : X) else 0) = a η
  rw [dite_eq_left hck]
  have hηc' : η ∈ (if h : c < k' then Closeds.closure {((σ ⟨c, h⟩).2 : X)} else ⊥) := hηc
  rw [dite_eq_left hck] at hηc'
  have hspec : ((σ ⟨c, hck⟩).2 : X) ⤳ η := specializes_iff_mem_closure.mpr hηc'
  -- both are generic points of the member `(σ ⟨c, hck⟩).1`, which is `i`
  have hmem : ((σ ⟨c, hck⟩).2 : X) ∈ (E.component i).support := by
    have h1 := (σ ⟨c, hck⟩).2.2.1
    have hi : (σ ⟨c, hck⟩).1 = i := by
      by_contra hne
      exact Hironaka.BMO.Snc.notMem_support_of_ne f E hE hne hη
        (hspec.mem_closed (E.component _).support.isClosed h1)
    rw [← hi]
    exact h1
  rw [hη.2 hmem hspec]

/-! ### The order of the monomial ideal at a point -/

/-- The order of a product of powers of principal ideals, when the order of elements is
additive (a regular local ring containing `ℚ`). -/
theorem ord_prod_span_singleton_pow {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hmul : ∀ f g : R, ordElem (f * g) =
      ordElem f + ordElem g)
    {ι : Type*} (s : Finset ι) (g : ι → R) (a : ι → ℕ) :
    ord (∏ i ∈ s, Ideal.span {g i} ^ a i) =
      ∑ i ∈ s, (a i : ℕ∞) * ordElem (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Ideal.span_singleton_pow,
      ord_span_singleton_mul_of_ordElem_mul hmul,
      ordElem_pow_of_ordElem_mul hmul, ih]

variable [CharZero k] [QuasiCompact f]

include f in
/-- The order of the marked monomial ideal at `x` is the sum of the exponents of the pieces
through `x`: its stalk is `∏_{c ∈ faceAt x} z_c^{a_c}` for the coordinates of the members
through `x`, and the order is additive on the regular local ring `𝒪_{X,x} ⊇ ℚ`. -/
theorem ord_monomial_eq_total (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (x : X) :
    (E.monomial Φ.exponentAt).ord x = (Φ.total (Φ.faceAt x) : ℕ∞) := by
  classical
  have hN : IsNoetherian X := f.isNoetherian_of_field
  have hreg := isRegularLocalRing_stalk f x
  let _ := f.stalkAlgebraRat x
  have hmul := ordElem_mul_of_algebraRat (X.presheaf.stalk x)
  obtain ⟨nx, z, hz⟩ := hE.2 x
  obtain ⟨hrsp, cE, hcinj, hcE⟩ := id hz
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
    obtain ⟨c, hc, hlab, hηc, -, hexp⟩ := Φ.faceAt_eq_singleton_of_mem_genericPoints f hE hΦ hη
    rw [hexp]
    have hxc : x ∈ Φ.piece c := hηx.mem_closed (Φ.piece c).isClosed hηc
    by_cases h : c = pc i
    · rw [h]
    · exact (Φ.not_mem_piece_of_label_eq hΦ hc (hpcn i) h (hlab.trans (hpclab i).symm) hxc
        (hpcx i)).elim
  -- the stalk of the monomial ideal at `x`: the members missing `x` contribute the unit ideal
  rw [IdealSheafData.ord_eq_ord_stalkIdeal,
    Hironaka.BMO.stalkIdeal_monomial E
      (fun i => Hironaka.BMO.Snc.genericPoints_component_finite E i) _ x,
    ← Fintype.prod_subtype_mul_prod_subtype (fun i : E.ι => x ∈ (E.component i).support)]
  have h2 : ∏ i : {i : E.ι // ¬ x ∈ (E.component i).support},
      (∏ᶠ η ∈ (E.component i.1).support.genericPoints,
        ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x) ^ Φ.exponentAt η) = 1
            :=
    Finset.prod_eq_one fun i _ => Hironaka.BMO.Snc.finprod_stalk_eq_one_of_notMem E i.2 _
  have h1 : ∀ i : {i : E.ι // x ∈ (E.component i).support},
      (∏ᶠ η ∈ (E.component i.1).support.genericPoints,
        ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x) ^ Φ.exponentAt η) =
        Ideal.span {z (cE i)} ^ Φ.a (pc i) := by
    intro i
    obtain ⟨η, hη, hηx⟩ := Hironaka.BMO.exists_genericPoint_specializes _ i.2
    rw [Hironaka.BMO.Snc.finprod_stalk_eq_of_specializes E hE hη hηx, hexp i hη hηx]
    exact congrArg (· ^ Φ.a (pc i)) (hcE i)
  rw [h2, mul_one, Finset.prod_congr rfl fun i _ => h1 i, ord_prod_span_singleton_pow hmul]
  simp only [ordElem_parameter hrsp, mul_one]
  -- the pieces through `x` are exactly the `pc i`
  rw [total, Nat.cast_sum]
  refine Finset.sum_bij (fun i _ => pc i) (fun i _ => Φ.mem_faceAt.mpr ⟨hpcn i, hpcx i⟩) ?_ ?_
    (fun i _ => rfl)
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

include f in
/-- When every face of the centre has sum `≥ m`, the marked monomial ideal has order `≥ m` along
the centre (condition (4′) of [Kol07, Definition 66]; Kollár's `a_{j₁} + ⋯ + a_{j_r} ≥ m` in
[Kol07, 111, Step 3.r]): at a generic point of `Z_P` the pieces of `P` pass, so the order is at
least `a(P)`. -/
theorem leOrdAlong_centerOf (hE : E.IsSnc) (hΦ : Φ.Realizes E e) {n m : ℕ} {hV : Φ.IsValid n m}
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S)
    (hge : ∀ P ∈ S, m ≤ Φ.total P) :
    (E.monomial Φ.exponentAt).LeOrdAlong (Φ.centerOf S).support (m : ℕ∞) := by
  intro η hη
  obtain ⟨P, hP, hηP⟩ := (Φ.mem_support_centerOf_iff S η).mp hη.1
  rw [Φ.ord_monomial_eq_total f hE hΦ η]
  have hsub : P ⊆ Φ.faceAt η := fun c hc => Φ.mem_faceAt.mpr
    ⟨Φ.lt_nextComp_of_mem_nerve (hS.1 hP) hc, Φ.mem_faceSet.mp hηP c hc⟩
  have : Φ.total P ≤ Φ.total (Φ.faceAt η) := Finset.sum_le_sum_of_subset hsub
  exact_mod_cast (hge P hP).trans this

end Hironaka.Monomial.PieceFamily
