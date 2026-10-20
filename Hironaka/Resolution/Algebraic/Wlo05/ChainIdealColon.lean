/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The colon of a chain ideal by its chain

For a chain `f₀, …, f_r` and monomials `M₀, …, M_{r−1}` in a commutative ring, the chain ideal
`I = (f₀, M₀ f₁, …, (M₀ ⋯ M_{r−1}) f_r)` (`chainIdeal`) and the K-shape
`K = (f₀, M₀ f₁, …, (M₀ ⋯ M_{r−2}) f_{r−1}, M₀ ⋯ M_{r−1})` (`chainKIdeal`;
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) satisfy `K ⊆ I : (f)` always
(`chainKIdeal_le_colon`) and `I : (f) = K` under two cancellation clauses at every level `i < r`,
with `S_i := (f₀, …, f_i)` (`colon_chainIdeal_eq_chainKIdeal`):

* (C) `M_i` is a nonzerodivisor modulo `S_i`: `M_i y ∈ S_i → y ∈ S_i`;
* (B) `M_i` cancels against the later chain equations modulo `S_i`: for `j > i`,
  `x f_j ∈ S_i + (M_i) → x ∈ S_i + (M_i)`.

The proof is an induction on `r` through the quotient by `f₀`: `I = (f₀) + M₀ I'` and
`K = (f₀) + M₀ K'` with `I'`, `K'` the chain ideal and the K-shape of the tail (`chainIdeal_succ`,
`chainKIdeal_succ`); from `h f_j ∈ I` for `j ≥ 1` clause (B) at level `0` gives `h = c f₀ + M₀ h'`,
clause (C) at level `0` gives `h' f_j ∈ (f₀) + I'`, so the class of `h'` lies in the colon of the
tail's chain ideal in `R/(f₀)`, which is the tail's K-shape by induction, and `h ∈ (f₀) + M₀ K'`.
The clauses (B), (C) hold for the chain coordinates of a regular system of parameters and
monomials in the remaining coordinates
(`Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColonRegular`), which is the statement CP2 of the
embedded desingularization: the isolated ideal `I_n : I_{Γ̃}` at the absorbing stage has the
K-shape. For example, `(x, e a, e² y) : (x, a, y) = (x, e a, e²)`. The identity is elementary and
not taken from the literature.
-/

@[expose] public section

universe u

open Ideal

namespace Hironaka.Resolution

variable {R : Type u} [CommRing R]

/-! ### The generators and the two decompositions -/

/-- The `i`-th generator `(∏_{i' < i} M_{i'}) f_i` of the chain ideal. -/
def chainGen {r : ℕ} (f M : Fin r → R) (i : Fin r) : R :=
  (∏ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), M i') * f i

theorem chainIdeal_eq_span_range_chainGen {r : ℕ} (f M : Fin r → R) :
    chainIdeal f M = span (Set.range (chainGen f M)) := rfl

theorem chainGen_mem {r : ℕ} (f M : Fin r → R) (i : Fin r) : chainGen f M i ∈ chainIdeal f M :=
  subset_span ⟨i, rfl⟩

theorem chainGen_zero {r : ℕ} (f M : Fin (r + 1) → R) : chainGen f M 0 = f 0 := by
  simp [chainGen]

theorem prod_filter_lt_succ {r : ℕ} (M : Fin (r + 2) → R) (j : Fin (r + 1)) :
    ∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 2) => i' < j.succ), M i' =
      M 0 * ∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < j), M i'.succ := by
  rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
  simp [Fin.succ_lt_succ_iff]

theorem chainGen_succ {r : ℕ} (f M : Fin (r + 2) → R) (j : Fin (r + 1)) :
    chainGen f M j.succ = M 0 * chainGen (Fin.tail f) (Fin.tail M) j := by
  simp only [chainGen, prod_filter_lt_succ, Fin.tail, mul_assoc]

/-- The chain ideal of `f₀, …, f_{r+1}` is `(f₀) + M₀ · (chain ideal of the tail)`. -/
theorem chainIdeal_succ {r : ℕ} (f M : Fin (r + 2) → R) :
    chainIdeal f M = span {f 0} ⊔ span {M 0} * chainIdeal (Fin.tail f) (Fin.tail M) := by
  apply le_antisymm
  · rw [chainIdeal_eq_span_range_chainGen, span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [chainGen_zero]
      exact mem_sup_left (subset_span (Set.mem_singleton _))
    · rw [chainGen_succ]
      exact mem_sup_right (mul_mem_mul (subset_span (Set.mem_singleton _)) (chainGen_mem _ _ j))
  · refine sup_le ?_ ?_
    · rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, ← chainGen_zero f M]
      exact chainGen_mem f M 0
    · rw [span_singleton_mul_le_iff]
      intro z hz
      obtain ⟨c, rfl⟩ := mem_span_range_iff_exists_fun.mp hz
      rw [Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      change M 0 * (c j * chainGen (Fin.tail f) (Fin.tail M) j) ∈ _
      rw [mul_left_comm, ← chainGen_succ]
      exact mul_mem_left _ _ (chainGen_mem f M j.succ)

/-- The K-shape of `f₀, …, f_{r+1}` is `(f₀) + M₀ · (K-shape of the tail)`. -/
theorem chainKIdeal_succ {r : ℕ} (f M : Fin (r + 2) → R) :
    chainKIdeal f M = span {f 0} ⊔ span {M 0} * chainKIdeal (Fin.tail f) (Fin.tail M) := by
  unfold chainKIdeal
  rw [chainIdeal_succ, Function.update_of_ne (Fin.last_pos).ne, ← Fin.succ_last,
    Fin.tail_update_succ]

/-- The K-shape of a chain of length one is the unit ideal. -/
theorem chainKIdeal_zero (f M : Fin 1 → R) : chainKIdeal f M = ⊤ := by
  unfold chainKIdeal
  refine Ideal.eq_top_of_isUnit_mem _ (subset_span ⟨0, ?_⟩) isUnit_one
  simp [Fin.last_zero]

/-! ### The colon by the chain -/

/-- Membership in the colon by the ideal of a family: `x ∈ I : (f) ↔ ∀ j, x f_j ∈ I`. -/
theorem mem_colon_span_range_iff {ι : Type*} (I : Ideal R) (f : ι → R) (x : R) :
    x ∈ I.colon (span (Set.range f)) ↔ ∀ j, x * f j ∈ I := by
  rw [Submodule.mem_colon]
  constructor
  · intro h j
    exact h (f j) (subset_span ⟨j, rfl⟩)
  · intro h s hs
    refine Submodule.span_induction (p := fun s _ => x • s ∈ I) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨j, rfl⟩
      exact h j
    · simp
    · intro a b _ _ ha hb
      rw [smul_add]
      exact add_mem ha hb
    · intro c a _ ha
      rw [smul_comm]
      exact Submodule.smul_mem _ _ ha

/-- The K-shape lies in the colon of the chain ideal by the chain (no hypotheses). -/
theorem chainKIdeal_le_colon :
    ∀ {r : ℕ} (f M : Fin (r + 1) → R),
      chainKIdeal f M ≤ (chainIdeal f M).colon (span (Set.range f)) := by
  intro r
  induction r with
  | zero =>
    intro f M
    rw [chainKIdeal_zero]
    refine top_le_iff.mpr (Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one)
    rw [mem_colon_span_range_iff]
    intro j
    rw [one_mul, Fin.fin_one_eq_zero j, ← chainGen_zero f M]
    exact chainGen_mem f M 0
  | succ r ih =>
    intro f M
    rw [chainKIdeal_succ, chainIdeal_succ]
    refine sup_le ?_ ?_
    · rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_colon_span_range_iff]
      intro j
      exact mem_sup_left (mul_mem_right _ _ (subset_span (Set.mem_singleton _)))
    · rw [span_singleton_mul_le_iff]
      intro z hz
      rw [mem_colon_span_range_iff]
      intro j
      refine Fin.cases ?_ (fun j' => ?_) j
      · rw [mul_assoc]
        exact mem_sup_left (mul_mem_left _ _ (mul_mem_left _ _ (subset_span (Set.mem_singleton _))))
      · have hz' := (mem_colon_span_range_iff _ _ _).mp (ih (Fin.tail f) (Fin.tail M) hz) j'
        rw [mul_assoc]
        exact mem_sup_right (mul_mem_mul (subset_span (Set.mem_singleton _)) hz')

/-! ### The two clauses and the identity -/

omit [CommRing R] in
/-- The image of the chain under an initial segment `{j ≤ 0}` is `{f₀}`. -/
theorem image_le_zero {r : ℕ} (f : Fin (r + 1) → R) :
    f '' {j : Fin (r + 1) | j.val ≤ 0} = {f 0} := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj0 : j = 0 := Fin.ext (by simpa using hj)
    rw [hj0]
  · rintro rfl
    exact ⟨0, le_rfl, rfl⟩

omit [CommRing R] in
/-- The image of the chain under `{j ≤ i + 1}` is `f₀` together with the tail's image under
`{j ≤ i}`. -/
theorem image_le_succ {r : ℕ} (f : Fin (r + 2) → R) (i : ℕ) :
    f '' {j : Fin (r + 2) | j.val ≤ i + 1} =
      insert (f 0) (Fin.tail f '' {j : Fin (r + 1) | j.val ≤ i}) := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.tail]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine Fin.cases (fun _ => Or.inl rfl) (fun j' hj' => Or.inr ⟨j', ?_, rfl⟩) j hj
    simpa [Fin.val_succ] using hj'
  · rintro (rfl | ⟨j', hj', rfl⟩)
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · exact ⟨j'.succ, by simpa [Fin.val_succ] using hj', rfl⟩

/-- The chain ideal is compatible with ring homomorphisms. -/
theorem chainIdeal_comp {S : Type u} [CommRing S] (φ : R →+* S) {r : ℕ} (f M : Fin r → R) :
    chainIdeal (φ ∘ f) (φ ∘ M) = map φ (chainIdeal f M) := by
  rw [chainIdeal_eq_span_range_chainGen, chainIdeal_eq_span_range_chainGen, map_span,
    ← Set.range_comp]
  congr 1
  refine congrArg Set.range (funext fun i => ?_)
  change (∏ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), φ (M i')) * φ (f i) =
    φ ((∏ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), M i') * f i)
  rw [map_mul, map_prod φ]

/-- The K-shape is compatible with ring homomorphisms. -/
theorem chainKIdeal_comp {S : Type u} [CommRing S] (φ : R →+* S) {r : ℕ}
    (f M : Fin (r + 1) → R) : chainKIdeal (φ ∘ f) (φ ∘ M) = map φ (chainKIdeal f M) := by
  unfold chainKIdeal
  rw [← chainIdeal_comp, Function.comp_update, map_one]

/-- The algebraic core of CP2: under the two cancellation clauses at every level, the colon of the
chain ideal by the chain is the K-shape. -/
theorem colon_chainIdeal_eq_chainKIdeal :
    ∀ (r : ℕ) (R : Type u) [CommRing R] (f M : Fin (r + 1) → R),
      (∀ (i : Fin r) (y : R), M i.castSucc * y ∈ span (f '' {j | j.val ≤ i.val}) →
        y ∈ span (f '' {j | j.val ≤ i.val})) →
      (∀ (i : Fin r) (j : Fin (r + 1)), i.val < j.val → ∀ x : R,
        x * f j ∈ span (f '' {j' | j'.val ≤ i.val}) ⊔ span {M i.castSucc} →
          x ∈ span (f '' {j' | j'.val ≤ i.val}) ⊔ span {M i.castSucc}) →
      (chainIdeal f M).colon (span (Set.range f)) = chainKIdeal f M := by
  intro r
  induction r with
  | zero =>
    intro R _ f M _ _
    rw [chainKIdeal_zero]
    refine (Ideal.eq_top_iff_one _).mpr ?_
    rw [mem_colon_span_range_iff]
    intro j
    rw [one_mul, Fin.fin_one_eq_zero j, ← chainGen_zero f M]
    exact chainGen_mem f M 0
  | succ r ih =>
    intro R _ f M hC hB
    refine le_antisymm ?_ (chainKIdeal_le_colon f M)
    intro h hh
    rw [mem_colon_span_range_iff, chainIdeal_succ] at hh
    -- the quotient by `f₀` and the tail's data
    have hS0 : span (f '' {j : Fin (r + 2) | j.val ≤ (0 : Fin (r + 1)).val}) = span {f 0} := by
      rw [Fin.val_zero, image_le_zero]
    have hspan : ∀ (A : Set (Fin (r + 1))) (x : R),
        Ideal.Quotient.mk (span {f 0}) x ∈
            span ((Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f) '' A) ↔
          x ∈ span {f 0} ⊔ span (Fin.tail f '' A) := by
      intro A x
      rw [Set.image_comp, ← map_span, Ideal.mem_quotient_iff_mem_sup, sup_comm]
    have himage : ∀ i : Fin r, span (f '' {j : Fin (r + 2) | j.val ≤ (i.succ).val}) =
        span {f 0} ⊔ span (Fin.tail f '' {j : Fin (r + 1) | j.val ≤ i.val}) := by
      intro i
      rw [Fin.val_succ, image_le_succ, span_insert]
    have hsupmap : ∀ (i : Fin r) (y : R),
        Ideal.Quotient.mk (span {f 0}) y ∈
            span ((Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f) ''
              {j' : Fin (r + 1) | j'.val ≤ i.val}) ⊔
            span {(Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) i.castSucc} ↔
          y ∈ span (f '' {j' : Fin (r + 2) | j'.val ≤ (i.succ).val}) ⊔
            span {M (i.succ).castSucc} := by
      intro i y
      have h1 : span ((Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f) ''
            {j' : Fin (r + 1) | j'.val ≤ i.val}) ⊔
          span {(Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) i.castSucc} =
            map (Ideal.Quotient.mk (span {f 0}))
              (span (Fin.tail f '' {j' : Fin (r + 1) | j'.val ≤ i.val}) ⊔
                span {M (i.succ).castSucc}) := by
        rw [Ideal.map_sup, map_span, map_span, Set.image_comp, Set.image_singleton]
        simp only [Function.comp_apply, Fin.tail, Fin.succ_castSucc]
      rw [h1, Ideal.mem_quotient_iff_mem_sup, himage, sup_comm _ (span {f 0}), ← sup_assoc]
    -- the tail's clauses in the quotient
    have hC' : ∀ (i : Fin r) (y : R ⧸ span {f 0}),
        (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) i.castSucc * y ∈
            span ((Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f) '' {j | j.val ≤ i.val}) →
          y ∈ span ((Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f) '' {j | j.val ≤ i.val}) := by
      intro i y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp only [Function.comp_apply, Fin.tail] at hy
      rw [← map_mul, hspan, ← himage] at hy
      rw [hspan, ← himage]
      exact hC i.succ y (by rwa [← Fin.succ_castSucc])
    have hB' : ∀ (i : Fin r) (j : Fin (r + 1)), i.val < j.val → ∀ x : R ⧸ span {f 0},
        x * (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f) j ∈
            span ((Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f) '' {j' | j'.val ≤ i.val}) ⊔
              span {(Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) i.castSucc} →
          x ∈ span ((Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f) '' {j' | j'.val ≤ i.val}) ⊔
            span {(Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) i.castSucc} := by
      intro i j hij x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk (span {f 0}) x * Ideal.Quotient.mk (span {f 0}) (Fin.tail f j) ∈ _
        at hx
      rw [← map_mul, hsupmap] at hx
      rw [hsupmap]
      exact hB i.succ j.succ (by simpa using hij) x hx
    have hIH := ih (R ⧸ span {f 0}) (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)
      (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) hC' hB'
    -- Step 1: `h ∈ (f₀) + (M₀)` by clause (B) at level `0`
    have h1 : h ∈ span {f 0} ⊔ span {M 0} := by
      have h0 : h * f (Fin.succ 0) ∈
          span (f '' {j' | j'.val ≤ (0 : Fin (r + 1)).val}) ⊔
            span {M (0 : Fin (r + 1)).castSucc} := by
        rw [hS0, Fin.castSucc_zero]
        exact IsConcreteLE.le_iff.mp
          (sup_le_sup_left (Ideal.mul_le.mpr fun a ha b _ => Ideal.mul_mem_right b _ ha) _)
          (hh (Fin.succ 0))
      have := hB 0 (Fin.succ 0) (by simp) h h0
      rwa [hS0, Fin.castSucc_zero] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, rfl⟩ := mem_span_singleton.mp ha
    obtain ⟨h', rfl⟩ := mem_span_singleton.mp hb
    -- Step 2: `h' f_j ∈ (f₀) + I'` by clause (C) at level `0`
    have h2 : ∀ k : Fin (r + 1),
        h' * f k.succ ∈ span {f 0} ⊔ chainIdeal (Fin.tail f) (Fin.tail M) := by
      intro k
      have hk := hh k.succ
      rw [← hab, add_mul] at hk
      have hf0 : f 0 * c * f k.succ ∈
          span {f 0} ⊔ span {M 0} * chainIdeal (Fin.tail f) (Fin.tail M) :=
        mem_sup_left (mul_mem_right _ _ (mul_mem_right _ _ (subset_span (Set.mem_singleton _))))
      have hM := (Submodule.add_mem_iff_right _ hf0).mp hk
      obtain ⟨a', ha', b', hb', hab'⟩ := Submodule.mem_sup.mp hM
      obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.mp hb'
      have hq : M 0 * (h' * f k.succ - w) ∈ span {f 0} := by
        have : M 0 * (h' * f k.succ - w) = a' := by linear_combination -hab'
        rw [this]
        exact ha'
      have hsub := hC 0 (h' * f k.succ - w) (by rwa [Fin.castSucc_zero, hS0])
      rw [hS0] at hsub
      exact Submodule.mem_sup.mpr ⟨_, hsub, w, hw, sub_add_cancel _ _⟩
    -- Step 3: the class of `h'` lies in the tail's colon, hence in the tail's K-shape
    have h3 : Ideal.Quotient.mk (span {f 0}) h' ∈
        (chainIdeal (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)
          (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M)).colon
        (span (Set.range (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f))) := by
      rw [mem_colon_span_range_iff]
      intro k
      rw [chainIdeal_comp, Function.comp_apply, ← map_mul, Ideal.mem_quotient_iff_mem_sup,
        sup_comm]
      exact h2 k
    rw [hIH, chainKIdeal_comp, Ideal.mem_quotient_iff_mem_sup] at h3
    -- Step 4: assemble
    rw [chainKIdeal_succ, ← hab]
    refine add_mem (mem_sup_left (mul_mem_right _ _ (subset_span (Set.mem_singleton _)))) ?_
    obtain ⟨k', hk', d, hd, rfl⟩ := Submodule.mem_sup.mp h3
    rw [mul_add]
    exact add_mem (mem_sup_right (mul_mem_mul (subset_span (Set.mem_singleton _)) hk'))
      (mem_sup_left (mul_mem_left _ _ hd))

end Hironaka.Resolution
