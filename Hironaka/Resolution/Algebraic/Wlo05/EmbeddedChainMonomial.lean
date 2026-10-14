/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitSupport
import Hironaka.Resolution.Algebraic.Snc.ComponentStalks
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.MarkedTransformMul
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Glue.Product
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The monomial factor of the chain form

Step 1 of the proof of [Kol07, Theorem 107] runs the order reduction on the nonmonomial part
`N(I)` and carries the monomial part `M(I)` along as a pullback: at stage `i` of the run,
`I_i = N(I)_i · π_i^* M(I)` ([Kol07, Definition 60] for a product, `markedTransformSeq_mul_comap`).
The chain-relative form of the statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) at the absorbing stage is therefore
established for `N(I)_i` and multiplied by the pulled-back monomial. This module supplies the facts
that make the product a chain form:

* `exists_comap_monomial_eq_monomial_stageMap` — the pullback of a monomial `𝒪_X(−∑ a_D D)` of an
  snc family along a smooth blow-up sequence whose centres have simple normal crossings with the
  induced families is a monomial of the induced family at every stage (the one-step form is
  `exists_comap_monomial_eq_monomial`; the corresponding statement for the monomial part is
  `exists_comap_monomialPart_eq_monomial`);
* `chainRelativeAt_mul_monomial` — in chain coordinates at `p` a monomial of `E` is the principal
  ideal `(∏ z_k^{b′_k})` with `b′` supported on the members' coordinates (the stalk of a monomial
  is the product over the members through `p` of the powers of their stalks,
  `exists_stalkIdeal_monomial_eq_prod`), so the product with a chain form is a chain form with the
  top-level exponents added (`monomialOf_add`);
* `chainRelativeAt_markedTransformSeq_mul_monomial` — the two combined along a run of order `≥ m`.

Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step1` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainCaseA`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData Ideal

namespace Hironaka.Resolution

/-! ### Algebra: exponents add -/

/-- Exponent vectors add under the product of monomials. -/
theorem monomialOf_add {R : Type*} [CommRing R] {n : ℕ} (z : Fin n → R) (a b : Fin n → ℕ) :
    monomialOf z (a + b) = monomialOf z a * monomialOf z b := by
  unfold monomialOf
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

/-! ### The stalk of a monomial as a product over the members -/

section Stalk

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]

/-- The stalk at `x` of a monomial `𝒪_X(−∑ a_D D)` of an snc family is the product over the
members of powers of their stalks — the exponent of a member through `x` is the exponent of its
one component through `x`, a member missing `x` has stalk `⊤` and exponent `0`. -/
theorem exists_stalkIdeal_monomial_eq_prod [NoetherianSpace X] (E : DivisorFamily X)
    (hE : E.IsSnc) (a : X → ℕ) (x : X) :
    ∃ b : E.ι → ℕ, (E.monomial a).stalkIdeal x = ∏ i, ((E.component i).stalkIdeal x) ^ b i := by
  classical
  refine ⟨fun i => if h : x ∈ (E.component i).support then
    a (Classical.choose (Hironaka.BMO.exists_genericPoint_specializes _ h)) else 0, ?_⟩
  rw [Hironaka.BMO.stalkIdeal_monomial E (Hironaka.BMO.Snc.genericPoints_component_finite E) a x]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hx : x ∈ (E.component i).support
  · dsimp only
    rw [dite_eq_left hx]
    exact Hironaka.BMO.Snc.finprod_stalk_eq_of_specializes E hE
      (Classical.choose_spec (Hironaka.BMO.exists_genericPoint_specializes _ hx)).1
      (Classical.choose_spec (Hironaka.BMO.exists_genericPoint_specializes _ hx)).2 a
  · dsimp only
    rw [dite_eq_right hx, pow_zero]
    exact Hironaka.BMO.Snc.finprod_stalk_eq_one_of_notMem E hx a

/-- The support of a monomial of `E` lies in the support of `E` — off `E` every factor is the unit
ideal. -/
theorem support_monomial_le [NoetherianSpace X] (E : DivisorFamily X) (a : X → ℕ) :
    (E.monomial a).support ≤ E.support := by
  intro x hx
  by_contra hxE
  have hnot : ∀ i, x ∉ (E.component i).support := fun i hi =>
    hxE ((DivisorFamily.mem_support_iff_exists E x).mpr ⟨i, hi⟩)
  have htop : (E.monomial a).stalkIdeal x = ⊤ := by
    rw [Hironaka.BMO.stalkIdeal_monomial E (Hironaka.BMO.Snc.genericPoints_component_finite E) a x]
    exact (Finset.prod_eq_one fun i _ =>
      Hironaka.BMO.Snc.finprod_stalk_eq_one_of_notMem E (hnot i) a).trans one_eq_top
  have hle := (mem_support_iff_stalkIdeal_le_maximalIdeal _ x).mp hx
  rw [htop] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

end Stalk

/-! ### In chain coordinates -/

section Coords

variable {X : Scheme.{u}}

/-- In chain coordinates at `p` the product over the members of powers of their stalks is the
principal ideal of a monomial in the coordinates: a member through `p` contributes `z_{c j}^{b j}`,
a member missing `p` contributes `⊤ ^ b j = 1`; the exponent of `z_k` is the sum of the `b j` over
the members `j` through `p` with `c j = k`, so it is supported on `range c`. -/
theorem ChainCoords.prod_pow_stalkIdeal_eq_span {E : DivisorFamily X} {Γ : X.IdealSheafData}
    {p : X} {n : ℕ} {z : Fin n → X.presheaf.stalk p}
    {c : {j : E.ι // p ∈ (E.component j).support} → Fin n} {r : ℕ} {σ : Fin (r + 1) → Fin n}
    {a : Fin (r + 1) → Fin n → ℕ} (h : ChainCoords E Γ p z c σ a) (b : E.ι → ℕ) :
    ∃ b' : Fin n → ℕ, (∀ k, b' k ≠ 0 → k ∈ Set.range c) ∧
      ∏ j, ((E.component j).stalkIdeal p) ^ b j = span {monomialOf z b'} := by
  classical
  obtain ⟨-, -, hc, -, -, -, -⟩ := h
  refine ⟨fun k => ∑ j ∈ Finset.univ.filter
    (fun j : {j : E.ι // p ∈ (E.component j).support} => c j = k), b j.1, fun k hk => ?_, ?_⟩
  · by_contra hkc
    exact hk (Finset.sum_eq_zero fun j hj => absurd ⟨j, (Finset.mem_filter.mp hj).2⟩ hkc)
  -- the members missing `p` contribute the unit ideal
  have hsub : ∏ j, ((E.component j).stalkIdeal p) ^ b j =
      ∏ j : {j : E.ι // p ∈ (E.component j).support}, ((E.component j.1).stalkIdeal p) ^ b j.1 := by
    rw [← Finset.prod_subtype (Finset.univ.filter fun j : E.ι => p ∈ (E.component j).support)
      (fun j => by simp) (fun j => ((E.component j).stalkIdeal p) ^ b j)]
    refine (Finset.prod_filter_of_ne fun j _ hj => ?_).symm
    by_contra hjp
    exact hj (by rw [stalkIdeal_eq_top_of_notMem_support _ hjp, top_pow]; exact one_eq_top.symm)
  -- the members through `p` are coordinates
  have hcoord : ∀ j : {j : E.ι // p ∈ (E.component j).support},
      ((E.component j.1).stalkIdeal p) ^ b j.1 = span {z (c j) ^ b j.1} := fun j => by
    rw [hc j, span_singleton_pow]
  rw [hsub, Finset.prod_congr rfl fun j _ => hcoord j, prod_span_singleton]
  congr 2
  -- regroup the factors by the coordinate
  unfold monomialOf
  rw [← Finset.prod_fiberwise Finset.univ c fun j => z (c j) ^ b j.1]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]

end Coords

/-! ### The product of a chain form with a monomial -/

section Product

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]

/-- The monomial ingredient of CP1 (Step 1 of the proof of [Kol07, Theorem 107] carries the
monomial part along as a pullback): the product of an ideal sheaf in chain form along `Γ` at `p`
with a monomial of the snc family `E` is in chain form along `Γ` at `p`, with the monomial's
exponents added to the top-level exponents. -/
theorem chainRelativeAt_mul_monomial [NoetherianSpace X] {E : DivisorFamily X} (hE : E.IsSnc)
    {N Γ : X.IdealSheafData} {p : X} (h : ChainRelativeAt E N Γ p) (a : X → ℕ) :
    ChainRelativeAt E (N * E.monomial a) Γ p := by
  obtain ⟨n, z, c, r, σ, a₀, b₀, hcoords, hb₀, hN⟩ := h
  obtain ⟨b, hb⟩ := exists_stalkIdeal_monomial_eq_prod E hE a p
  obtain ⟨b', hb', hprod⟩ := hcoords.prod_pow_stalkIdeal_eq_span b
  refine ⟨n, z, c, r, σ, a₀, b₀ + b', hcoords, fun k hk => ?_, ?_⟩
  · by_cases h0 : b₀ k = 0
    · exact hb' k (by simpa [h0] using hk)
    · exact hb₀ k h0
  · rw [stalkIdeal_mul, hN, hb, hprod, mul_right_comm, span_singleton_mul_span_singleton,
      ← monomialOf_add]

end Product

/-! ### The pull-back of a monomial along a blow-up and along a run -/

section Pullback

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [Smooth f]

include f in
/-- The pullback of a monomial `𝒪_X(−∑ a_D D)` of `E` along the blow-up of a centre `D` with simple
normal crossings with `E` is a monomial of the total transform `π^{-1}_{tot} E` — invertible and
supported over `supp E`, hence on `supp π^{-1}_{tot} E` (a point off the exceptional divisor lies
on the strict transform of the member through its image); it is then its own monomial part
(`eq_monomialPart_of_isInvertible_of_support_le`). This is the observation in Step 1 of the proof
of [Kol07, Theorem 107] that the pullbacks differ from the transforms only in their monomial
part. -/
theorem exists_comap_monomial_eq_monomial [IsNoetherian X] (E : DivisorFamily X) (hE : E.IsSnc)
    (D : X.IdealSheafData) [Smooth (D.subschemeι ≫ f)] (hD : E.HasSncWith D) (a : X → ℕ) :
    ∃ a' : D.blowUp → ℕ,
      (E.monomial a).comap D.blowUpπ = (E.totalTransform D).monomial a' := by
  have hπ : Smooth (D.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth' f D
  have hE' : (E.totalTransform D).IsSnc :=
    totalTransform_isSnc f E D hE hD
  have hB : IsNoetherian D.blowUp := blowUp.isNoetherian D
  have hinv : ((E.monomial a).comap D.blowUpπ).IsInvertible :=
    blowUp.isInvertible_comap_of_isInvertible D _
      (Hironaka.BMO.Snc.isInvertible_monomial f E hE a)
  have hsupp : ((E.monomial a).comap D.blowUpπ).support ≤
      (E.totalTransform D).support := by
    intro b hb
    rw [support_comap] at hb
    have hbE : D.blowUpπ b ∈ E.support := support_monomial_le E a hb
    obtain ⟨i, hbi⟩ := (DivisorFamily.mem_support_iff_exists E _).mp hbE
    by_cases hF : b ∈ D.exceptionalDivisor.support
    · exact le_iSup (fun j => ((E.totalTransform D).component j).support)
        (toLex (Sum.inr PUnit.unit)) hF
    · refine (DivisorFamily.mem_support_iff_exists _ b).mpr ⟨toLex (Sum.inl i), ?_⟩
      have hbi' : b ∈ ((E.component i).comap D.blowUpπ).support := by
        rw [support_comap]
        exact hbi
      change b ∈ (((E.component i).comap D.blowUpπ).saturate
          D.exceptionalDivisor).support
      rw [← SetLike.mem_coe, coe_support_saturate]
      exact subset_closure ⟨hbi', hF⟩
  exact ⟨fun η => (((E.monomial a).comap D.blowUpπ).ord η).toNat,
    (Hironaka.BMO.Snc.eq_monomialPart_of_isInvertible_of_support_le
        (D.blowUpπ ≫ f) _ hE' hinv
      hsupp).trans (Hironaka.BMO.monomialPart_eq_monomial _ _)⟩

include f in
/-- `exists_comap_monomial_eq_monomial` iterated along a smooth blow-up sequence whose centres have
simple normal crossings with the induced families (the snc clause of `IsOrderGeSeq`), in the
`⟨j, hj⟩` form of the indices: the pull-back of a monomial of `E` to stage `j` is a monomial of the
induced family `E_j`. -/
theorem exists_comap_monomial_eq_monomial_stageMap_mk (hA : IsNoetherian X) (S : BlowUpSequence X)
    (E : DivisorFamily X) (hsm : S.IsSmooth f) (hE : E.IsSnc)
    (hsnc : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (a : X → ℕ) (j : ℕ) (hj : j < S.length + 1) :
    ∃ a' : S.stage ⟨j, hj⟩ → ℕ,
      (E.monomial a).comap (S.stageMap ⟨j, hj⟩) = (S.totalTransformSeq E ⟨j, hj⟩).monomial a' := by
  induction S generalizing j with
  | nil X => exact ⟨a, comap_id _⟩
  | cons X D rest ih =>
    cases j with
    | zero => exact ⟨a, comap_id _⟩
    | succ j =>
      obtain ⟨hD, hsm'⟩ := (isSmooth_cons_iff f D rest).1 hsm
      have hπ : Smooth (D.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth' f D
      have hB : IsNoetherian D.blowUp := blowUp.isNoetherian D
      obtain ⟨a₁, ha₁⟩ :=
        exists_comap_monomial_eq_monomial f E hE D (hsnc ⟨0, Nat.zero_lt_succ _⟩) a
      obtain ⟨a', ha'⟩ := ih (D.blowUpπ ≫ f) hB (E.totalTransform D) hsm'
        (totalTransform_isSnc f E D hE
          (hsnc ⟨0, Nat.zero_lt_succ _⟩))
        (fun ⟨i, hi⟩ => hsnc ⟨i + 1, Nat.succ_lt_succ hi⟩) a₁ j (Nat.lt_of_succ_lt_succ hj)
      refine ⟨a', ?_⟩
      change (E.monomial a).comap (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ) =
        (rest.totalTransformSeq (E.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩).monomial a'
      rw [comap_comp, ha₁]
      exact ha'

include f in
/-- `exists_comap_monomial_eq_monomial_stageMap_mk` at an arbitrary stage index. -/
theorem exists_comap_monomial_eq_monomial_stageMap [IsNoetherian X] (S : BlowUpSequence X)
    (E : DivisorFamily X) (hsm : S.IsSmooth f) (hE : E.IsSnc)
    (hsnc : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (a : X → ℕ) (i : Fin (S.length + 1)) :
    ∃ a' : S.stage i → ℕ,
      (E.monomial a).comap (S.stageMap i) = (S.totalTransformSeq E i).monomial a' := by
  obtain ⟨j, hj⟩ := i
  exact exists_comap_monomial_eq_monomial_stageMap_mk f inferInstance S E hsm hE hsnc a j hj

include f in
/-- The sequence form: along a run of order `≥ m` for `(N, m)` with snc boundary `E` the pullback
of a monomial of `E` is a monomial of the induced family at every stage. -/
theorem exists_comap_monomial_eq_monomial_of_isOrderGeSeq [IsNoetherian X] {S : BlowUpSequence X}
    {N : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X} (hS : S.IsOrderGeSeq f N m E)
    (hE : E.IsSnc) (a : X → ℕ) (i : Fin (S.length + 1)) :
    ∃ a' : S.stage i → ℕ,
      (E.monomial a).comap (S.stageMap i) = (S.totalTransformSeq E i).monomial a' :=
  exists_comap_monomial_eq_monomial_stageMap f S E hS.1 hE (fun i => (hS.2 i).1) a i

include f in
/-- Along a smooth run of order `≥ m` for `(N, m)` with snc boundary `E` (`IsOrderGeSeq`), the
chain form of the marked transform of `N` along `Γ` at a point of stage `i` gives the chain form of
the marked transform of `N · 𝒪_X(−∑ a_D D)` — [Kol07, Definition 60] for a product
(`markedTransformSeq_mul_comap`) splits off the pullback of the monomial, a monomial of the induced
family absorbed into the top-level exponents. -/
theorem chainRelativeAt_markedTransformSeq_mul_monomial [IsNoetherian X] (n : ℕ)
    [SmoothOfRelativeDimension n f] {S : BlowUpSequence X} {N : X.IdealSheafData} {m : ℕ}
    {E : DivisorFamily X} (hS : S.IsOrderGeSeq f N m E) (hE : E.IsSnc) (a : X → ℕ)
    (i : Fin (S.length + 1)) {Γ : (S.stage i).IdealSheafData} {p : S.stage i}
    (h : ChainRelativeAt (S.totalTransformSeq E i) (S.markedTransformSeq N m i) Γ p) :
    ChainRelativeAt (S.totalTransformSeq E i) (S.markedTransformSeq (N * E.monomial a) m i)
      Γ p := by
  obtain ⟨a', ha'⟩ := exists_comap_monomial_eq_monomial_of_isOrderGeSeq f hS hE a i
  have hNoeth : IsNoetherian (S.stage i) := isNoetherian_stage S i
  have hsm : Smooth (S.stageMap i ≫ f) := IsSmooth.smooth_stageMap' hS.1 i
  rw [Hironaka.Sequence.markedTransformSeq_mul_comap S N _ m
    (Hironaka.Sequence.exceptionalAt_pow_dvd_comap_step_of_isOrderGeSeq f n S N m E hS) i, ha']
  exact chainRelativeAt_mul_monomial (IsOrderGeSeq.isSnc_totalTransformSeq f n hS hE i) h a'

end Pullback

end Hironaka.Resolution
