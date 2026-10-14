/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Presentation
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Torsion-freeness of the chart presentation

Let `A` be a commutative ring, `a ∈ A`, `g : Fin k → A`, and suppose the list
`[a, g₀, …, g_{k-1}]` is weakly regular on `A`: `a` is a nonzerodivisor of `A` and each `gⱼ` is a
nonzerodivisor of `A/(a, g₀, …, g_{j-1})` (Mathlib's `RingTheory.Sequence.IsWeaklyRegular`, whose
definition is exactly this colon condition along `List.take`).  In `M = A[Y₀, …, Y_{k-1}]` let
`J = ⟨a Yᵢ − gᵢ⟩` be the presentation ideal of the affine blow-up algebra
(`Hironaka.Scheme.BlowUp.Presentation`).  Then `a f ∈ J` implies `f ∈ J`, so `a` and its powers are
nonzerodivisors on `M/J`.  This is the statement the Stacks Project proves for `H₁`-regular
sequences through the Koszul complex [Sta, Tag 0BIQ], and the reason Hauser's presentation of a
chart ring by a regular sequence has no torsion — the only linear relations among the generators
are the trivial ones [Hau14, Theorem 4.20 (b)]; the proof below is elementary and never leaves
`M`.  It is used to identify the chart rings of the blow-up of a smooth scheme along a regular
sequence of coordinates as quotients of polynomial rings.

**The peeling induction.**  With `J_j = ⟨a Yᵢ − gᵢ : i < j⟩` and `Q_j = (a, g₀, …, g_{j-1}) ⊆ A`,
two identities of ideals of `M`: `J_{j+1} = J_j + ⟨a Yⱼ − gⱼ⟩`, and `J_j + ⟨a⟩ = Q_j M`
(`aYᵢ − gᵢ ∈ (a, gᵢ)M`; conversely `gᵢ = aYᵢ − (aYᵢ − gᵢ)`).  Base `j = 0`: `J₀ = 0` and `a f = 0`
forces `f = 0` coefficientwise.  Step: from `a f = h + (aYⱼ − gⱼ) q` with `h ∈ J_j` we get
`gⱼ q = h + a Yⱼ q − a f ∈ J_j + ⟨a⟩ = Q_j M`, i.e. `gⱼ · coeff_m(q) ∈ Q_j` for every monomial `m`
(`MvPolynomial.mem_map_C_iff`); the regularity of `gⱼ` modulo `Q_j` gives `coeff_m(q) ∈ Q_j`, so
`q ∈ Q_j M = J_j + ⟨a⟩`, `q = h' + a q'`; substituting, `a (f − (aYⱼ − gⱼ) q') ∈ J_j`, the
induction hypothesis gives `f − (aYⱼ − gⱼ) q' ∈ J_j`, and `f ∈ J_{j+1}`.  The order with `a`
first is what the induction uses (`a = x`, `g₀ = xy` in `ℚ[x, y]` is a counterexample to the
statement without it).
-/

@[expose] public section

namespace AlgebraicGeometry.affineBlowUpAlgebra

open MvPolynomial RingTheory.Sequence

universe u

variable {A : Type u} [CommRing A] {k : ℕ} (a : A) (g : Fin k → A)

/-! ### The partial presentation ideals and their base ideals -/

/-- `J_j = ⟨a Yᵢ − gᵢ : i < j⟩`. -/
noncomputable def partialPresentationIdeal (j : ℕ) : Ideal (MvPolynomial (Fin k) A) :=
  Ideal.span ((fun i : Fin k => C a * X i - C (g i)) '' {i | i.val < j})

/-- `Q_j = (a, g₀, …, g_{j-1}) ⊆ A`. -/
noncomputable def partialBase (j : ℕ) : Ideal A :=
  Ideal.span (insert a (g '' {i : Fin k | i.val < j}))

theorem partialPresentationIdeal_zero : partialPresentationIdeal a g 0 = ⊥ := by
  have : {i : Fin k | i.val < 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun i hi => Nat.not_lt_zero _ hi
  rw [partialPresentationIdeal, this, Set.image_empty, Ideal.span_empty]

theorem partialPresentationIdeal_succ {j : ℕ} (hj : j < k) :
    partialPresentationIdeal a g (j + 1) =
      partialPresentationIdeal a g j ⊔ Ideal.span {C a * X ⟨j, hj⟩ - C (g ⟨j, hj⟩)} := by
  have : {i : Fin k | i.val < j + 1} = insert ⟨j, hj⟩ {i : Fin k | i.val < j} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  rw [partialPresentationIdeal, partialPresentationIdeal, this, Set.image_insert_eq,
    Ideal.span_insert, sup_comm]

theorem partialPresentationIdeal_eq_of_le {j : ℕ} (hj : k ≤ j) :
    partialPresentationIdeal a g j = presentationIdeal a g := by
  have : {i : Fin k | i.val < j} = Set.univ :=
    Set.eq_univ_of_forall fun i => lt_of_lt_of_le i.2 hj
  rw [partialPresentationIdeal, this, Set.image_univ]
  rfl

theorem a_mem_partialBase (j : ℕ) : a ∈ partialBase a g j :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem g_mem_partialBase {j : ℕ} {i : Fin k} (hi : i.val < j) : g i ∈ partialBase a g j :=
  Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩)

/-- The identity `J_j + ⟨a⟩ = Q_j M`. -/
theorem partialPresentationIdeal_sup_span_C (j : ℕ) :
    partialPresentationIdeal a g j ⊔ Ideal.span {C a} =
      (partialBase a g j).map (C : A →+* MvPolynomial (Fin k) A) := by
  apply le_antisymm
  · refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨i, hi, rfl⟩
      exact Ideal.sub_mem _
        (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (a_mem_partialBase a g j)))
        (Ideal.mem_map_of_mem _ (g_mem_partialBase a g hi))
    · rintro _ rfl
      exact Ideal.mem_map_of_mem _ (a_mem_partialBase a g j)
  · rw [partialBase, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | ⟨i, hi, rfl⟩
    · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    · have : (C (g i) : MvPolynomial (Fin k) A) = C a * X i - (C a * X i - C (g i)) := by ring
      rw [this]
      exact Ideal.sub_mem _
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
        (Ideal.mem_sup_left (Ideal.subset_span ⟨i, hi, rfl⟩))

/-! ### The regularity hypotheses, extracted from `IsWeaklyRegular` -/

theorem isSMulRegular_head (h : IsWeaklyRegular A (a :: List.ofFn g)) : IsSMulRegular A a :=
  ((isWeaklyRegular_cons_iff A a _).mp h).1

theorem ofList_take_cons_ofFn (j : ℕ) :
    Ideal.ofList ((a :: List.ofFn g).take (j + 1)) = partialBase a g j := by
  rw [List.take_succ_cons, Ideal.ofList_cons, partialBase, Ideal.span_insert]
  congr 1
  change Ideal.span {r | r ∈ (List.ofFn g).take j} = _
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_image, List.mem_iff_getElem, List.length_take,
    List.length_ofFn, List.getElem_take, List.getElem_ofFn, lt_min_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi.2⟩, hi.1, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, ⟨hi, i.2⟩, rfl⟩

/-- The `j`-th clause of weak regularity, in colon form: `gⱼ c ∈ Q_j ⟹ c ∈ Q_j`. -/
theorem mem_partialBase_of_mul_mem (h : IsWeaklyRegular A (a :: List.ofFn g)) (j : Fin k)
    {c : A} (hc : g j * c ∈ partialBase a g j) : c ∈ partialBase a g j := by
  have hreg := h.regular_mod_prev (j.val + 1) (by simp)
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hreg
  have hQ : (Ideal.ofList ((a :: List.ofFn g).take (j.val + 1)) • ⊤ : Submodule A A) =
      partialBase a g j := by
    rw [ofList_take_cons_ofFn a g j.val, smul_eq_mul, Ideal.mul_top]
  rw [hQ] at hreg
  simp only [List.getElem_cons_succ, List.getElem_ofFn, Fin.eta] at hreg
  exact hreg c (by rw [smul_eq_mul]; exact hc)

/-! ### The peeling induction -/

theorem mem_partialPresentationIdeal_of_C_mul_mem (h : IsWeaklyRegular A (a :: List.ofFn g)) :
    ∀ j ≤ k, ∀ p : MvPolynomial (Fin k) A,
      C a * p ∈ partialPresentationIdeal a g j → p ∈ partialPresentationIdeal a g j := by
  intro j
  induction j with
  | zero =>
    intro _ p hp
    rw [partialPresentationIdeal_zero, Ideal.mem_bot] at hp ⊢
    ext m
    have := congrArg (AddMonoidAlgebra.coeff · m) hp
    rw [coeff_C_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    exact isSMulRegular_head a g h (by simpa using this)
  | succ j ih =>
    intro hj p hp
    have hjk : j < k := hj
    rw [partialPresentationIdeal_succ a g hjk] at hp ⊢
    obtain ⟨h₁, hh₁, q₀, hq₀, hsum⟩ := Submodule.mem_sup.mp hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hq₀
    have h₁eq : h₁ = C a * p - q * (C a * X ⟨j, hjk⟩ - C (g ⟨j, hjk⟩)) := eq_sub_of_add_eq hsum
    have hgq : C (g ⟨j, hjk⟩) * q ∈ partialPresentationIdeal a g j ⊔ Ideal.span {C a} := by
      have : C (g ⟨j, hjk⟩) * q = h₁ + C a * (X ⟨j, hjk⟩ * q - p) := by
        rw [h₁eq]; ring
      rw [this]
      exact Submodule.add_mem _ (Ideal.mem_sup_left hh₁)
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    rw [partialPresentationIdeal_sup_span_C, MvPolynomial.mem_map_C_iff] at hgq
    have hq : q ∈ (partialBase a g j).map (C : A →+* MvPolynomial (Fin k) A) := by
      rw [MvPolynomial.mem_map_C_iff]
      intro m
      have := hgq m
      rw [coeff_C_mul] at this
      exact mem_partialBase_of_mul_mem a g h ⟨j, hjk⟩ this
    rw [← partialPresentationIdeal_sup_span_C] at hq
    obtain ⟨h', hh', q₁, hq₁, hq⟩ := Submodule.mem_sup.mp hq
    obtain ⟨q', rfl⟩ := Ideal.mem_span_singleton'.mp hq₁
    have key : C a * (p - q' * (C a * X ⟨j, hjk⟩ - C (g ⟨j, hjk⟩))) ∈
        partialPresentationIdeal a g j := by
      have : C a * (p - q' * (C a * X ⟨j, hjk⟩ - C (g ⟨j, hjk⟩))) =
          h₁ + h' * (C a * X ⟨j, hjk⟩ - C (g ⟨j, hjk⟩)) := by
        rw [h₁eq, ← hq]; ring
      rw [this]
      exact Submodule.add_mem _ hh₁ (Ideal.mul_mem_right _ _ hh')
    have hrest := ih hjk.le _ key
    have hp' : p = (p - q' * (C a * X ⟨j, hjk⟩ - C (g ⟨j, hjk⟩))) +
        q' * (C a * X ⟨j, hjk⟩ - C (g ⟨j, hjk⟩)) := by ring
    rw [hp']
    exact Submodule.add_mem _ (Ideal.mem_sup_left hrest)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

/-- The presentation ideal is saturated with respect to `a`: `a f ∈ J` implies `f ∈ J`
[Sta, Tag 0BIQ]; [Hau14, Theorem 4.20 (b)]. -/
theorem mem_presentationIdeal_of_C_mul_mem (h : IsWeaklyRegular A (a :: List.ofFn g))
    (p : MvPolynomial (Fin k) A) (hp : C a * p ∈ presentationIdeal a g) :
    p ∈ presentationIdeal a g := by
  rw [← partialPresentationIdeal_eq_of_le a g le_rfl] at hp ⊢
  exact mem_partialPresentationIdeal_of_C_mul_mem a g h k le_rfl p hp

/-- `a` is a nonzerodivisor on `A[Y]/J`. -/
theorem isSMulRegular_quotient_presentationIdeal (h : IsWeaklyRegular A (a :: List.ofFn g)) :
    IsSMulRegular (MvPolynomial (Fin k) A ⧸ presentationIdeal a g) a := by
  intro z w hzw
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective w
  have h1 : Ideal.Quotient.mk (presentationIdeal a g) (C a * p) =
      Ideal.Quotient.mk (presentationIdeal a g) (C a * q) := by
    have := hzw
    simp only at this
    rw [← Ideal.Quotient.mkₐ_eq_mk A, ← map_smul, ← map_smul, smul_eq_C_mul, smul_eq_C_mul] at this
    rwa [← Ideal.Quotient.mkₐ_eq_mk A]
  rw [Ideal.Quotient.eq, ← mul_sub] at h1
  exact Ideal.Quotient.eq.mpr (mem_presentationIdeal_of_C_mul_mem a g h _ h1)

/-- The powers of `a` are nonzerodivisors on `A[Y]/J`. -/
theorem isSMulRegular_pow_quotient_presentationIdeal (h : IsWeaklyRegular A (a :: List.ofFn g))
    (d : ℕ) : IsSMulRegular (MvPolynomial (Fin k) A ⧸ presentationIdeal a g) (a ^ d) :=
  (isSMulRegular_quotient_presentationIdeal a g h).pow d

end AlgebraicGeometry.affineBlowUpAlgebra
