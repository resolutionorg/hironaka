/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainLift
import Hironaka.Scheme.Snc.ParameterSubset
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The algebra of CP3: strata in given coordinates, images of chain forms, lifts

The ring-level part of the statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`: the centres of a run on a protected
state are chain-relative strata). It provides: the predicates `StratumIn` and `TerminalIn` —
admissible and terminal-normal strata
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAdmissibleStratum`) IN given chain coordinates; the
images of the chain forms under ring homomorphisms; the truncation of the chain at the first level
whose monomial vanishes; the ideal identities for the restriction to a member of the boundary (two
cases: no level carries the killed coordinate, or a first level does and truncates the chain) and
for the descent to a chain hypersurface (the flag shortened, the monomials shifted, `M₀` the new top
monomial); the regular system of parameters of the member's stalk; and the lifts of strata along the
surjection to the member or to the hypersurface (the killed coordinate adjoined; the absorption
`(f̄)` lifting to a stratum one level up, or to the terminal-normal stratum `(f, z_{k₀})`).

The hypersurface of maximal contact and the restriction of the ideal to it are those of
[Kol07, Lemma 62] and the proof of [Kol07, Lemma 102]. These identities are not in the literature.
They are used by the CP3 modules `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Rebase`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Pass`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Chain`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Restrict` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Transport`.
-/

@[expose] public section

universe u

open IsLocalRing

namespace Hironaka.Resolution

section Algebra

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]

/-- `Z` is an admissible chain stratum IN the
coordinates `(z, σ, a, b)` with member coordinates `C`: `Z = (f₀, …, f_{l−1}, z_s)`, `l ≤ r`, `s ⊆
C`, and (★) at the stratum's own level. -/
def StratumIn {n : ℕ} (z : Fin n → R) (C : Set (Fin n)) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) (b : Fin n → ℕ) (Z : Ideal R) : Prop :=
  ∃ (l : ℕ) (_ : l ≤ r) (s : Finset (Fin n)), ↑s ⊆ C ∧
    Z = Ideal.span ((z ∘ σ) '' {i | i.val < l}) ⊔ Ideal.span (z '' ↑s) ∧
    (l = 0 → ∃ k ∈ s, b k ≠ 0) ∧ (0 < l → ∃ k ∈ s, a ⟨l - 1, by omega⟩ k ≠ 0)

/-- `Z` is a terminal-normal stratum IN the
coordinates `(z, σ)`: all chain equations plus a nonempty set of member coordinates. -/
def TerminalIn {n : ℕ} (z : Fin n → R) (C : Set (Fin n)) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (Z : Ideal R) : Prop :=
  ∃ s : Finset (Fin n), ↑s ⊆ C ∧ s.Nonempty ∧
    Z = Ideal.span (Set.range (z ∘ σ)) ⊔ Ideal.span (z '' ↑s)

/-- The image of a monomial under a ring homomorphism
is the monomial of the images. -/
theorem map_monomialOf (φ : R →+* S) {n : ℕ} (z : Fin n → R) (a : Fin n → ℕ) :
    φ (monomialOf z a) = monomialOf (φ ∘ z) a := by
  simp [monomialOf, map_prod, map_pow]

/-- The image of the un-isolated chain form is the
chain form of the images. -/
theorem map_chainIdeal (φ : R →+* S) {r : ℕ} (f M : Fin r → R) :
    (chainIdeal f M).map φ = chainIdeal (φ ∘ f) (φ ∘ M) := by
  unfold chainIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  simp [map_mul, map_prod]

/-- The image of the K-shape is the K-shape of the
images. -/
theorem map_chainKIdeal (φ : R →+* S) {r : ℕ} (f M : Fin (r + 1) → R) :
    (chainKIdeal f M).map φ = chainKIdeal (φ ∘ f) (φ ∘ M) := by
  unfold chainKIdeal
  rw [map_chainIdeal, Function.comp_update, map_one]

/-- The product over the indices below `castLE j` reindexed through `castLE`. -/
theorem prod_filter_lt_castLE {r l₀ : ℕ} (h : l₀ + 1 ≤ r + 1) (M : Fin (r + 1) → R)
    (j : Fin (l₀ + 1)) :
    ∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < Fin.castLE h j), M i' =
      ∏ j' ∈ Finset.univ.filter (fun j' : Fin (l₀ + 1) => j' < j), M (Fin.castLE h j') := by
  refine (Finset.prod_nbij (Fin.castLE h) ?_ ?_ ?_ ?_).symm
  · intro j' hj'
    have hj'' : j' < j := by simpa using hj'
    change Fin.castLE h j' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < Fin.castLE h j)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Fin.castLE_lt_castLE_iff h).mpr hj''⟩
  · intro a _ b _ hab
    exact Fin.castLE_injective h hab
  · intro i' hi'
    have hi'' : i' < Fin.castLE h j := by simpa using hi'
    have hlt : i'.val < j.val := hi''
    refine ⟨⟨i'.val, by omega⟩, ?_, Fin.ext rfl⟩
    change (⟨i'.val, _⟩ : Fin (l₀ + 1)) ∈ Finset.univ.filter (fun j' : Fin (l₀ + 1) => j' < j)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.lt_def.mpr hlt⟩
  · intros; rfl

/-- A generator whose product contains a vanishing
monomial is zero. -/
theorem prod_filter_lt_eq_zero {r : ℕ} (M : Fin r → R) {l₀ : Fin r} (h0 : M l₀ = 0) {i : Fin r}
    (hi : l₀ < i) : ∏ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), M i' = 0 :=
  Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) h0

/-- The truncation of the chain, un-isolated form: a vanishing monomial at level `l₀ < r`
truncates the chain at `l₀`. -/
theorem chainIdeal_eq_chainIdeal_castLE {r : ℕ} (f M : Fin r → R) {l₀ : ℕ} (hl : l₀ < r)
    (h0 : M ⟨l₀, hl⟩ = 0) :
    chainIdeal f M =
      chainIdeal (fun i : Fin (l₀ + 1) => f (Fin.castLE hl i))
        (fun i : Fin (l₀ + 1) => M (Fin.castLE hl i)) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold chainIdeal
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : l₀ < i.val
    · dsimp only
      rw [prod_filter_lt_eq_zero M h0 (Fin.lt_def.mpr hi), zero_mul]
      exact zero_mem _
    · have hi' : i.val ≤ l₀ := not_lt.mp hi
      refine Ideal.subset_span ⟨⟨i.val, by omega⟩, ?_⟩
      have hcast : Fin.castLE hl ⟨i.val, by omega⟩ = i := Fin.ext rfl
      have hp := prod_filter_lt_castLE hl M ⟨i.val, by omega⟩
      rw [hcast] at hp
      dsimp only
      rw [hcast, hp]
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine Ideal.subset_span ⟨Fin.castLE hl j, ?_⟩
    dsimp only
    rw [prod_filter_lt_castLE hl M j]

/-- The truncation of the chain, K-shape: a vanishing monomial at level `l₀ < r` turns the
K-shape into the un-isolated form of the chain truncated at `l₀` (`g := f_{l₀}`). -/
theorem chainKIdeal_eq_chainIdeal_castLE {r : ℕ} (f M : Fin (r + 1) → R) {l₀ : ℕ} (hl : l₀ < r)
    (h0 : M ⟨l₀, by omega⟩ = 0) :
    chainKIdeal f M =
      chainIdeal (fun i : Fin (l₀ + 1) => f (Fin.castLE (by omega) i))
        (fun i : Fin (l₀ + 1) => M (Fin.castLE (by omega) i)) := by
  unfold chainKIdeal
  rw [chainIdeal_eq_chainIdeal_castLE (Function.update f (Fin.last r) 1) M (l₀ := l₀) (by omega) h0]
  congr 1
  funext i
  have hne : Fin.castLE (by omega : l₀ + 1 ≤ r + 1) i ≠ Fin.last r := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  exact Function.update_of_ne hne _ _

/-- A monomial with exponent `0` at the killed
coordinate maps to the monomial of the remaining coordinates. -/
theorem map_monomialOf_of_apply_eq_zero {n : ℕ} (z : Fin (n + 1) → R) (k₀ : Fin (n + 1))
    (φ : R →+* S) (a : Fin (n + 1) → ℕ) (ha : a k₀ = 0) :
    φ (monomialOf z a) =
      monomialOf (fun i : Fin n => φ (z (k₀.succAbove i))) (a ∘ k₀.succAbove) := by
  rw [map_monomialOf]
  unfold monomialOf
  rw [Fin.prod_univ_succAbove _ k₀]
  simp [ha]

/-- A monomial with a positive exponent at the killed
coordinate maps to `0`. -/
theorem map_monomialOf_of_apply_ne_zero {n : ℕ} (z : Fin (n + 1) → R) (k₀ : Fin (n + 1))
    (φ : R →+* S) (hk : φ (z k₀) = 0) (a : Fin (n + 1) → ℕ) (ha : a k₀ ≠ 0) :
    φ (monomialOf z a) = 0 := by
  rw [map_monomialOf]
  unfold monomialOf
  rw [Fin.prod_univ_succAbove _ k₀]
  simp [hk, zero_pow ha]

/-- The chain monomials as an `ℕ`-indexed family (`1`
beyond the range). -/
def natExt {m : ℕ} (M : Fin m → R) (k : ℕ) : R := if h : k < m then M ⟨k, h⟩ else 1

/-- `natExt` agrees with `M` on the range. -/
theorem natExt_val {m : ℕ} (M : Fin m → R) (i : Fin m) : natExt M i.val = M i := by
  simp [natExt, i.isLt]

/-- `natExt` at `0`. -/
theorem natExt_zero {m : ℕ} (M : Fin (m + 1) → R) : natExt M 0 = M 0 := by
  simp [natExt]

/-- `natExt` of the shifted family. -/
theorem natExt_comp_succ {m : ℕ} (M : Fin (m + 1) → R) (k : ℕ) :
    natExt (M ∘ Fin.succ) k = natExt M (k + 1) := by
  unfold natExt
  split_ifs with h1 h2 h2
  · rfl
  · omega
  · omega
  · rfl

/-- `natExt` is `1` below a trivial block's end. -/
theorem natExt_eq_one_of_lt {m : ℕ} (M : Fin m → R) {t : Fin m}
    (ht : ∀ i : Fin m, i.val < t.val → M i = 1) {k : ℕ} (hk : k < t.val) : natExt M k = 1 := by
  unfold natExt
  split_ifs with h
  · exact ht ⟨k, h⟩ hk
  · rfl

/-- The chain product below `i` as a product over
`range i`. -/
theorem prod_filter_lt_eq_prod_range {m : ℕ} (M : Fin m → R) (i : Fin m) :
    ∏ i' ∈ Finset.univ.filter (fun i' : Fin m => i' < i), M i' =
      ∏ k ∈ Finset.range i.val, natExt M k := by
  refine Finset.prod_nbij Fin.val ?_ ?_ ?_ ?_
  · intro i' hi'
    have hi'' : i' < i := by simpa using hi'
    change i'.val ∈ Finset.range i.val
    exact Finset.mem_range.mpr hi''
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro k hk
    have hk' : k < i.val := by simpa using hk
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    change (⟨k, _⟩ : Fin m) ∈ Finset.univ.filter (fun i' : Fin m => i' < i)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.lt_def.mpr hk'⟩
  · intro i' _
    exact (natExt_val M i').symm

/-- The generator identity of the descent: with the
monomials before `t` trivial, the generator of the shortened chain at `j`, times `M₀`, is the
generator of the full chain at `t.succAbove j`. -/
theorem descent_generator_eq {r : ℕ} (M : Fin (r + 1) → R) (t : Fin (r + 1))
    (ht : ∀ i : Fin (r + 1), i.val < t.val → M i = 1) (j : Fin r) (x : R) :
    M 0 * ((∏ j' ∈ Finset.univ.filter (fun j' : Fin r => j' < j), (M ∘ Fin.succ) j') * x) =
      (∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 1) => i' < t.succAbove j), M i') * x := by
  rw [prod_filter_lt_eq_prod_range, prod_filter_lt_eq_prod_range]
  rcases lt_or_ge (Fin.castSucc j) t with hlt | hge
  · rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
    have hj : j.val < t.val := by
      have := Fin.lt_def.mp hlt
      rwa [Fin.val_castSucc] at this
    have h1 : ∏ k ∈ Finset.range (Fin.castSucc j).val, natExt M k = 1 := by
      refine Finset.prod_eq_one fun k hk => natExt_eq_one_of_lt M ht ?_
      have hk' : k < j.val := by simpa using hk
      omega
    have h2 : ∏ k ∈ Finset.range j.val, natExt (M ∘ Fin.succ) k = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      rw [natExt_comp_succ]
      refine natExt_eq_one_of_lt M ht ?_
      have hk' : k < j.val := by simpa using hk
      omega
    have h0t : (0 : Fin (r + 1)).val < t.val := by
      rw [Fin.val_zero]
      omega
    rw [h1, h2, ht 0 h0t]
    ring
  · rw [Fin.succAbove_of_le_castSucc _ _ hge, Fin.val_succ, Finset.prod_range_succ']
    simp_rw [natExt_comp_succ]
    rw [natExt_zero]
    ring

/-- The descent to a chain hypersurface, un-isolated form: killing the chain coordinate `f_t`
(the monomials before `t` trivial) gives `M₀ · I(f without t; M shifted)`. -/
theorem chainIdeal_eq_span_mul_chainIdeal_succAbove {r : ℕ} (f M : Fin (r + 1) → R)
    (t : Fin (r + 1)) (ht : ∀ i : Fin (r + 1), i.val < t.val → M i = 1) (h0 : f t = 0) :
    chainIdeal f M = Ideal.span {M 0} * chainIdeal (f ∘ t.succAbove) (M ∘ Fin.succ) := by
  unfold chainIdeal
  rw [Ideal.span_mul_span, Set.singleton_mul, ← Set.range_comp]
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hit : i = t
    · subst hit
      dsimp only
      rw [h0, mul_zero]
      exact zero_mem _
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hit
      exact Ideal.subset_span ⟨j, descent_generator_eq M t ht j _⟩
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨t.succAbove j, (descent_generator_eq M t ht j _).symm⟩

/-- The K-shape version: the K-last generator is
handled through `update`; when `t` is the last chain coordinate every monomial is trivial and both
sides are the unit ideal. -/
theorem chainKIdeal_eq_span_mul_chainKIdeal_succAbove {r : ℕ} (f M : Fin (r + 2) → R)
    (t : Fin (r + 2)) (ht : ∀ i : Fin (r + 2), i.val < t.val → M i = 1) (h0 : f t = 0) :
    chainKIdeal f M = Ideal.span {M 0} * chainKIdeal (f ∘ t.succAbove) (M ∘ Fin.succ) := by
  by_cases htl : t = Fin.last (r + 1)
  · subst htl
    have hall : ∀ i : Fin (r + 2), i.val < r + 1 → M i = 1 := fun i hi => ht i hi
    have hL : chainKIdeal f M = ⊤ := by
      refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨Fin.last (r + 1), ?_⟩) isUnit_one
      dsimp only
      rw [Function.update_self, mul_one]
      exact Finset.prod_eq_one fun i hi => hall i (Finset.mem_filter.mp hi).2
    have hR : chainKIdeal (f ∘ (Fin.last (r + 1)).succAbove) (M ∘ Fin.succ) = ⊤ := by
      refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨Fin.last r, ?_⟩) isUnit_one
      dsimp only
      rw [Function.update_self, mul_one]
      refine Finset.prod_eq_one fun i hi => hall _ ?_
      have := (Finset.mem_filter.mp hi).2
      rw [Fin.lt_def] at this
      simp only [Fin.val_succ]
      omega
    rw [hL, hR, ht 0 (by simp), Ideal.span_singleton_one, Ideal.top_mul]
  · have hkey : ∀ j : Fin (r + 1),
        M 0 * ((∏ j' ∈ Finset.univ.filter (fun j' : Fin (r + 1) => j' < j), (M ∘ Fin.succ) j') *
          Function.update (f ∘ t.succAbove) (Fin.last r) 1 j) =
        (∏ i' ∈ Finset.univ.filter (fun i' : Fin (r + 2) => i' < t.succAbove j), M i') *
          Function.update f (Fin.last (r + 1)) 1 (t.succAbove j) := by
      intro j
      have hf : Function.update f (Fin.last (r + 1)) 1 (t.succAbove j) =
          Function.update (f ∘ t.succAbove) (Fin.last r) 1 j := by
        by_cases hj : j = Fin.last r
        · subst hj
          have hs : t.succAbove (Fin.last r) = Fin.last (r + 1) := by
            rw [Fin.succAbove_of_le_castSucc _ _ ?_, Fin.succ_last]
            rw [Fin.le_def, Fin.val_castSucc, Fin.val_last]
            have := Fin.val_lt_last htl
            omega
          rw [hs, Function.update_self, Function.update_self]
        · have hne : t.succAbove j ≠ Fin.last (r + 1) := by
            intro h
            rcases lt_or_ge (Fin.castSucc j) t with hlt | hge
            · rw [Fin.succAbove_of_castSucc_lt _ _ hlt] at h
              have := congrArg Fin.val h
              rw [Fin.val_castSucc, Fin.val_last] at this
              omega
            · rw [Fin.succAbove_of_le_castSucc _ _ hge, ← Fin.succ_last] at h
              exact hj (Fin.succ_injective _ h)
          rw [Function.update_of_ne hne, Function.update_of_ne hj, Function.comp_apply]
      rw [hf]
      exact descent_generator_eq M t ht j _
    unfold chainKIdeal chainIdeal
    rw [Ideal.span_mul_span, Set.singleton_mul, ← Set.range_comp]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      by_cases hit : i = t
      · subst hit
        dsimp only
        rw [Function.update_of_ne htl, h0, mul_zero]
        exact zero_mem _
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hit
        exact Ideal.subset_span ⟨j, hkey j⟩
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨t.succAbove j, (hkey j).symm⟩

/-- The K-shape ignores the last monomial: agreement
below `r` suffices. -/
theorem chainKIdeal_congr_of_lt {r : ℕ} (f : Fin (r + 1) → R) {M M' : Fin (r + 1) → R}
    (h : ∀ i : Fin (r + 1), i.val < r → M i = M' i) : chainKIdeal f M = chainKIdeal f M' := by
  unfold chainKIdeal chainIdeal
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  congr 1
  refine Finset.prod_congr rfl fun i' hi' => h i' ?_
  have := (Finset.mem_filter.mp hi').2
  have hi := i.isLt
  rw [Fin.lt_def] at this
  omega

/-- The un-isolated form ignores the last monomial.
-/
theorem chainIdeal_congr_of_lt {r : ℕ} (f : Fin r → R) {M M' : Fin r → R}
    (h : ∀ i : Fin r, i.val + 1 < r → M i = M' i) : chainIdeal f M = chainIdeal f M' := by
  unfold chainIdeal
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  congr 1
  refine Finset.prod_congr rfl fun i' hi' => h i' ?_
  have := (Finset.mem_filter.mp hi').2
  have hi := i.isLt
  rw [Fin.lt_def] at this
  omega

/-- The restriction to a member, K-shape, when no level `< r` carries the killed coordinate:
the image is the K-shape of the restricted data. -/
theorem map_span_mul_chainKIdeal_of_forall {n : ℕ} (z : Fin (n + 1) → R) (k₀ : Fin (n + 1))
    (φ : R →+* S) {r : ℕ} (σ : Fin (r + 1) → Fin (n + 1))
    (σ' : Fin (r + 1) → Fin n) (hσ : ∀ i, k₀.succAbove (σ' i) = σ i)
    (a : Fin (r + 1) → Fin (n + 1) → ℕ) (b : Fin (n + 1) → ℕ) (hb : b k₀ = 0)
    (ha : ∀ i : Fin (r + 1), i.val < r → a i k₀ = 0) :
    (Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i))).map φ =
      Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (b ∘ k₀.succAbove)} *
        chainKIdeal ((fun i => φ (z (k₀.succAbove i))) ∘ σ')
          (fun i => monomialOf (fun i => φ (z (k₀.succAbove i))) (a i ∘ k₀.succAbove)) := by
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_chainKIdeal,
    map_monomialOf_of_apply_eq_zero z k₀ φ b hb]
  congr 1
  have hf : φ ∘ z ∘ σ = (fun i => φ (z (k₀.succAbove i))) ∘ σ' := by
    funext i
    simp only [Function.comp_apply, hσ]
  rw [hf]
  exact chainKIdeal_congr_of_lt _ fun i hi => by
    simp only [Function.comp_apply]
    exact map_monomialOf_of_apply_eq_zero z k₀ φ (a i) (ha i hi)

/-- The restriction to a member for the un-isolated form, when no level carries the killed
coordinate. -/
theorem map_span_mul_chainIdeal_of_forall {n : ℕ} (z : Fin (n + 1) → R) (k₀ : Fin (n + 1))
    (φ : R →+* S) {r : ℕ} (σ : Fin (r + 1) → Fin (n + 1))
    (σ' : Fin (r + 1) → Fin n) (hσ : ∀ i, k₀.succAbove (σ' i) = σ i)
    (a : Fin (r + 1) → Fin (n + 1) → ℕ) (b : Fin (n + 1) → ℕ) (hb : b k₀ = 0)
    (ha : ∀ i : Fin (r + 1), i.val < r → a i k₀ = 0) :
    (Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i))).map φ =
      Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (b ∘ k₀.succAbove)} *
        chainIdeal ((fun i => φ (z (k₀.succAbove i))) ∘ σ')
          (fun i => monomialOf (fun i => φ (z (k₀.succAbove i))) (a i ∘ k₀.succAbove)) := by
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_chainIdeal,
    map_monomialOf_of_apply_eq_zero z k₀ φ b hb]
  congr 1
  have hf : φ ∘ z ∘ σ = (fun i => φ (z (k₀.succAbove i))) ∘ σ' := by
    funext i
    simp only [Function.comp_apply, hσ]
  rw [hf]
  exact chainIdeal_congr_of_lt _ fun i hi => by
    simp only [Function.comp_apply]
    exact map_monomialOf_of_apply_eq_zero z k₀ φ (a i) (ha i (by omega))

/-- The restriction to a member, K-shape, when a first level `l₀ < r` carries the killed
coordinate: it truncates the chain — the image is the un-isolated form of `f₀, …, f_{l₀}`. -/
theorem map_span_mul_chainKIdeal_of_lt {n : ℕ} (z : Fin (n + 1) → R) (k₀ : Fin (n + 1))
    (φ : R →+* S) (hk : φ (z k₀) = 0) {r : ℕ} (σ : Fin (r + 1) → Fin (n + 1))
    (σ' : Fin (r + 1) → Fin n) (hσ : ∀ i, k₀.succAbove (σ' i) = σ i)
    (a : Fin (r + 1) → Fin (n + 1) → ℕ) (b : Fin (n + 1) → ℕ) (hb : b k₀ = 0) {l₀ : ℕ}
    (hl : l₀ < r) (h0 : a ⟨l₀, by omega⟩ k₀ ≠ 0)
    (hlt : ∀ i : Fin (r + 1), i.val < l₀ → a i k₀ = 0) :
    (Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i))).map φ =
      Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (b ∘ k₀.succAbove)} *
        chainIdeal (fun i : Fin (l₀ + 1) => φ (z (k₀.succAbove (σ' (Fin.castLE (by omega) i)))))
          (fun i : Fin (l₀ + 1) => monomialOf (fun i => φ (z (k₀.succAbove i)))
            (a (Fin.castLE (by omega) i) ∘ k₀.succAbove)) := by
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_chainKIdeal,
    map_monomialOf_of_apply_eq_zero z k₀ φ b hb]
  congr 1
  have h0' : (φ ∘ fun i => monomialOf z (a i)) ⟨l₀, by omega⟩ = 0 :=
    map_monomialOf_of_apply_ne_zero z k₀ φ hk _ h0
  rw [chainKIdeal_eq_chainIdeal_castLE _ _ hl h0']
  have hf : (fun i : Fin (l₀ + 1) => (φ ∘ z ∘ σ) (Fin.castLE (by omega) i)) =
      fun i : Fin (l₀ + 1) => φ (z (k₀.succAbove (σ' (Fin.castLE (by omega) i)))) := by
    funext i
    simp only [Function.comp_apply, hσ]
  rw [hf]
  exact chainIdeal_congr_of_lt _ fun i hi => by
    simp only [Function.comp_apply]
    exact map_monomialOf_of_apply_eq_zero z k₀ φ _ (hlt _ (by simp; omega))

/-- The restriction to a member for the un-isolated form, when a first level carries the killed
coordinate. -/
theorem map_span_mul_chainIdeal_of_lt {n : ℕ} (z : Fin (n + 1) → R) (k₀ : Fin (n + 1))
    (φ : R →+* S) (hk : φ (z k₀) = 0) {r : ℕ} (σ : Fin (r + 1) → Fin (n + 1))
    (σ' : Fin (r + 1) → Fin n) (hσ : ∀ i, k₀.succAbove (σ' i) = σ i)
    (a : Fin (r + 1) → Fin (n + 1) → ℕ) (b : Fin (n + 1) → ℕ) (hb : b k₀ = 0) {l₀ : ℕ}
    (hl : l₀ < r) (h0 : a ⟨l₀, by omega⟩ k₀ ≠ 0)
    (hlt : ∀ i : Fin (r + 1), i.val < l₀ → a i k₀ = 0) :
    (Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i))).map φ =
      Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (b ∘ k₀.succAbove)} *
        chainIdeal (fun i : Fin (l₀ + 1) => φ (z (k₀.succAbove (σ' (Fin.castLE (by omega) i)))))
          (fun i : Fin (l₀ + 1) => monomialOf (fun i => φ (z (k₀.succAbove i)))
            (a (Fin.castLE (by omega) i) ∘ k₀.succAbove)) := by
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_chainIdeal,
    map_monomialOf_of_apply_eq_zero z k₀ φ b hb]
  congr 1
  have h0' : (φ ∘ fun i => monomialOf z (a i)) ⟨l₀, by omega⟩ = 0 :=
    map_monomialOf_of_apply_ne_zero z k₀ φ hk _ h0
  rw [chainIdeal_eq_chainIdeal_castLE _ _ (by omega) h0']
  have hf : (fun i : Fin (l₀ + 1) => (φ ∘ z ∘ σ) (Fin.castLE (by omega) i)) =
      fun i : Fin (l₀ + 1) => φ (z (k₀.succAbove (σ' (Fin.castLE (by omega) i)))) := by
    funext i
    simp only [Function.comp_apply, hσ]
  rw [hf]
  exact chainIdeal_congr_of_lt _ fun i hi => by
    simp only [Function.comp_apply]
    exact map_monomialOf_of_apply_eq_zero z k₀ φ _ (hlt _ (by simp; omega))

/-- The descent to a chain hypersurface at the ring level, K-shape: killing the chain coordinate
`f_t` after a trivial block gives `M₀ · K(f without t; M shifted)`. -/
theorem map_chainKIdeal_succAbove_of_trivial {n : ℕ} (z : Fin (n + 1) → R) (k₀ : Fin (n + 1))
    (φ : R →+* S) (hk : φ (z k₀) = 0) {r : ℕ} (σ : Fin (r + 2) → Fin (n + 1)) (t : Fin (r + 2))
    (hk₀ : σ t = k₀) (σ' : Fin (r + 1) → Fin n)
    (hσ : ∀ i, k₀.succAbove (σ' i) = σ (t.succAbove i)) (a : Fin (r + 2) → Fin (n + 1) → ℕ)
    (ha : ∀ i κ, a i κ ≠ 0 → κ ≠ k₀) (ht : ∀ i : Fin (r + 2), i.val < t.val → a i = 0) :
    (chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i))).map φ =
      Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (a 0 ∘ k₀.succAbove)} *
        chainKIdeal ((fun i => φ (z (k₀.succAbove i))) ∘ σ')
          (fun i => monomialOf (fun i => φ (z (k₀.succAbove i))) (a (Fin.succ i) ∘ k₀.succAbove)) :=
  by
  rw [map_chainKIdeal]
  have hM1 : ∀ i : Fin (r + 2), i.val < t.val → (φ ∘ fun i => monomialOf z (a i)) i = 1 := by
    intro i hi
    simp only [Function.comp_apply, ht i hi, monomialOf_zero, map_one]
  have hf0 : (φ ∘ z ∘ σ) t = 0 := by
    simp only [Function.comp_apply, hk₀, hk]
  rw [chainKIdeal_eq_span_mul_chainKIdeal_succAbove _ _ t hM1 hf0]
  have e0 : (φ ∘ fun i => monomialOf z (a i)) 0 =
      monomialOf (fun i => φ (z (k₀.succAbove i))) (a 0 ∘ k₀.succAbove) := by
    simp only [Function.comp_apply]
    exact map_monomialOf_of_apply_eq_zero z k₀ φ (a 0) (by
      by_contra h
      exact ha 0 k₀ h rfl)
  rw [e0]
  congr 1
  congr 1
  · funext i
    simp only [Function.comp_apply, hσ]
  · funext i
    simp only [Function.comp_apply]
    exact map_monomialOf_of_apply_eq_zero z k₀ φ _ (by
      by_contra h
      exact ha _ k₀ h rfl)

/-- The same descent for the un-isolated form. -/
theorem map_chainIdeal_succAbove_of_trivial {n : ℕ} (z : Fin (n + 1) → R) (k₀ : Fin (n + 1))
    (φ : R →+* S) (hk : φ (z k₀) = 0) {r : ℕ} (σ : Fin (r + 1) → Fin (n + 1)) (t : Fin (r + 1))
    (hk₀ : σ t = k₀) (σ' : Fin r → Fin n) (hσ : ∀ i, k₀.succAbove (σ' i) = σ (t.succAbove i))
    (a : Fin (r + 1) → Fin (n + 1) → ℕ) (ha : ∀ i κ, a i κ ≠ 0 → κ ≠ k₀)
    (ht : ∀ i : Fin (r + 1), i.val < t.val → a i = 0) :
    (chainIdeal (z ∘ σ) (fun i => monomialOf z (a i))).map φ =
      Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (a 0 ∘ k₀.succAbove)} *
        chainIdeal ((fun i => φ (z (k₀.succAbove i))) ∘ σ')
          (fun i => monomialOf (fun i => φ (z (k₀.succAbove i))) (a (Fin.succ i) ∘ k₀.succAbove)) :=
  by
  rw [map_chainIdeal]
  have hM1 : ∀ i : Fin (r + 1), i.val < t.val → (φ ∘ fun i => monomialOf z (a i)) i = 1 := by
    intro i hi
    simp only [Function.comp_apply, ht i hi, monomialOf_zero, map_one]
  have hf0 : (φ ∘ z ∘ σ) t = 0 := by
    simp only [Function.comp_apply, hk₀, hk]
  rw [chainIdeal_eq_span_mul_chainIdeal_succAbove _ _ t hM1 hf0]
  have e0 : (φ ∘ fun i => monomialOf z (a i)) 0 =
      monomialOf (fun i => φ (z (k₀.succAbove i))) (a 0 ∘ k₀.succAbove) := by
    simp only [Function.comp_apply]
    exact map_monomialOf_of_apply_eq_zero z k₀ φ (a 0) (by
      by_contra h
      exact ha 0 k₀ h rfl)
  rw [e0]
  congr 1
  congr 1
  · funext i
    simp only [Function.comp_apply, hσ]
  · funext i
    simp only [Function.comp_apply]
    exact map_monomialOf_of_apply_eq_zero z k₀ φ _ (by
      by_contra h
      exact ha _ k₀ h rfl)


/-- `comap ∘ map` along a surjection with kernel `(z
k₀)`. -/
theorem comap_map_eq_sup_span {n : ℕ} {z : Fin (n + 1) → R} {k₀ : Fin (n + 1)} {φ : R →+* S}
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {z k₀}) (J : Ideal R) :
    (J.map φ).comap φ = J ⊔ Ideal.span {z k₀} := by
  rw [Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, hker]

/-- The killed coordinate maps to `0`. -/
theorem apply_eq_zero_of_ker {n : ℕ} {z : Fin (n + 1) → R} {k₀ : Fin (n + 1)} {φ : R →+* S}
    (hker : RingHom.ker φ = Ideal.span {z k₀}) : φ (z k₀) = 0 := by
  rw [← RingHom.mem_ker, hker]
  exact Ideal.mem_span_singleton_self _

/-- The images of a regular system of parameters
under a surjection killing exactly one of them form a regular system of parameters of the target. -/
theorem isRegularSystemOfParameters_comp_succAbove [IsRegularLocalRing R] [IsLocalRing S] {n : ℕ}
    {z : Fin (n + 1) → R} (hz : IsRegularSystemOfParameters z)
    (k₀ : Fin (n + 1)) (φ : R →+* S) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {z k₀}) :
    IsRegularSystemOfParameters (fun i : Fin n => φ (z (k₀.succAbove i))) := by
  obtain ⟨hspan, hdim⟩ := hz
  refine ⟨?_, ?_⟩
  · rw [← IsLocalRing.map_maximalIdeal_of_surjective φ hφ, ← hspan, Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨z (k₀.succAbove i), ⟨_, rfl⟩, rfl⟩
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i = k₀
      · subst hi
        rw [apply_eq_zero_of_ker hker]
        exact zero_mem _
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
        exact Ideal.subset_span ⟨j, rfl⟩
  · have h := AlgebraicGeometry.natCast_sub_card_eq_ringKrullDim_of_ker hspan.symm hdim hφ
      (s := {k₀}) (by rw [Finset.coe_singleton, Set.image_singleton]; exact hker)
    simpa using h

/-- The lift of a stratum along the surjection: the
preimage of a stratum in the restricted coordinates is a stratum in the original ones, the killed
coordinate adjoined. -/
theorem stratumIn_comap_of_stratumIn {n : ℕ} {z : Fin (n + 1) → R} {k₀ : Fin (n + 1)}
    {φ : R →+* S} (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {z k₀})
    {C : Set (Fin (n + 1))} (hk₀ : k₀ ∈ C) {C' : Set (Fin n)} (hC : ∀ k ∈ C', k₀.succAbove k ∈ C)
    {r : ℕ} {σ : Fin (r + 1) → Fin (n + 1)} {σ' : Fin (r + 1) → Fin n}
    (hσ : ∀ i, k₀.succAbove (σ' i) = σ i) {a : Fin (r + 1) → Fin (n + 1) → ℕ} {b : Fin (n + 1) → ℕ}
    {Z' : Ideal S}
    (h : StratumIn (fun i => φ (z (k₀.succAbove i))) C' σ' (fun i => a i ∘ k₀.succAbove)
      (b ∘ k₀.succAbove) Z') :
    StratumIn z C σ a b (Z'.comap φ) := by
  obtain ⟨l, hl, s', hs'C, hZ', hl0, hlpos⟩ := h
  classical
  refine ⟨l, hl, insert k₀ (s'.image k₀.succAbove), ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image] at hk
    rcases hk with rfl | ⟨k', hk', rfl⟩
    · exact hk₀
    · exact hC k' (hs'C hk')
  · have hZ : Z' = (Ideal.span ((z ∘ σ) '' {i | i.val < l}) ⊔
        Ideal.span (z '' (k₀.succAbove '' ↑s'))).map φ := by
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, hZ']
      congr 1
      · congr 1
        rw [← Set.image_comp]
        exact Set.image_congr fun i _ => by simp [hσ]
      · congr 1
        rw [← Set.image_comp, ← Set.image_comp]
        rfl
    rw [hZ, comap_map_eq_sup_span hφ hker, Finset.coe_insert, Finset.coe_image,
      Set.image_insert_eq, Ideal.span_insert, sup_assoc, sup_comm (Ideal.span {z k₀})]
  · intro hl0'
    obtain ⟨k, hk, hb⟩ := hl0 hl0'
    exact ⟨k₀.succAbove k, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hk), hb⟩
  · intro hpos
    obtain ⟨k, hk, ha⟩ := hlpos hpos
    exact ⟨k₀.succAbove k, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hk), ha⟩

/-- The lift of a terminal-normal stratum. -/
theorem terminalIn_comap_of_terminalIn {n : ℕ} {z : Fin (n + 1) → R} {k₀ : Fin (n + 1)}
    {φ : R →+* S} (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {z k₀})
    {C : Set (Fin (n + 1))} (hk₀ : k₀ ∈ C) {C' : Set (Fin n)} (hC : ∀ k ∈ C', k₀.succAbove k ∈ C)
    {r : ℕ} {σ : Fin (r + 1) → Fin (n + 1)} {σ' : Fin (r + 1) → Fin n}
    (hσ : ∀ i, k₀.succAbove (σ' i) = σ i) {Z' : Ideal S}
    (h : TerminalIn (fun i => φ (z (k₀.succAbove i))) C' σ' Z') :
    TerminalIn z C σ (Z'.comap φ) := by
  obtain ⟨s', hs'C, hne, hZ'⟩ := h
  classical
  refine ⟨insert k₀ (s'.image k₀.succAbove), ?_, Finset.insert_nonempty _ _, ?_⟩
  · intro k hk
    rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image] at hk
    rcases hk with rfl | ⟨k', hk', rfl⟩
    · exact hk₀
    · exact hC k' (hs'C hk')
  · have hZ : Z' = (Ideal.span (Set.range (z ∘ σ)) ⊔
        Ideal.span (z '' (k₀.succAbove '' ↑s'))).map φ := by
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, hZ']
      congr 1
      · congr 1
        rw [← Set.range_comp]
        exact congrArg Set.range (funext fun i => by simp [hσ])
      · congr 1
        rw [← Set.image_comp, ← Set.image_comp]
        rfl
    rw [hZ, comap_map_eq_sup_span hφ hker, Finset.coe_insert, Finset.coe_image,
      Set.image_insert_eq, Ideal.span_insert, sup_assoc, sup_comm (Ideal.span {z k₀})]

/-- The lift of the absorption `Z' = (f̄)`: the
preimage is the terminal-normal stratum `(f, z_{k₀})`. -/
theorem terminalIn_comap_of_eq_span {n : ℕ} {z : Fin (n + 1) → R} {k₀ : Fin (n + 1)}
    {φ : R →+* S} (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {z k₀})
    {C : Set (Fin (n + 1))} (hk₀ : k₀ ∈ C) {r : ℕ} {σ : Fin (r + 1) → Fin (n + 1)}
    {σ' : Fin (r + 1) → Fin n} (hσ : ∀ i, k₀.succAbove (σ' i) = σ i) {Z' : Ideal S}
    (h : Z' = Ideal.span (Set.range ((fun i => φ (z (k₀.succAbove i))) ∘ σ'))) :
    TerminalIn z C σ (Z'.comap φ) := by
  refine ⟨{k₀}, by simpa using hk₀, Finset.singleton_nonempty _, ?_⟩
  have hZ : Z' = (Ideal.span (Set.range (z ∘ σ))).map φ := by
    rw [Ideal.map_span, h, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext fun i => by simp [hσ]))
  rw [hZ, comap_map_eq_sup_span hφ hker, Finset.coe_singleton, Set.image_singleton]

omit [CommRing R] in
/-- Truncated images: the image of the indices below
`l ≤ l₀` through `castLE` is the image of the indices below `l`. -/
theorem image_castLE_lt_eq {r l₀ : ℕ} (h : l₀ + 1 ≤ r + 1) {F : Fin (r + 1) → R} {l : ℕ}
    (hl : l ≤ l₀ + 1) :
    (fun i : Fin (l₀ + 1) => F (Fin.castLE h i)) '' {i | i.val < l} =
      F '' {i : Fin (r + 1) | i.val < l} := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Fin.castLE h i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : i.val < l := hi
    exact ⟨⟨i.val, by omega⟩, hi', rfl⟩

omit [CommRing R] in
/-- The range of the truncated family is the image of
the indices below `l₀ + 1`. -/
theorem range_castLE_eq {r l₀ : ℕ} (h : l₀ + 1 ≤ r + 1) (F : Fin (r + 1) → R) :
    Set.range (fun i : Fin (l₀ + 1) => F (Fin.castLE h i)) =
      F '' {i : Fin (r + 1) | i.val < l₀ + 1} := by
  rw [← Set.image_univ, ← image_castLE_lt_eq h le_rfl]
  congr 1
  ext i
  exact ⟨fun _ => i.isLt, fun _ => Set.mem_univ i⟩

omit [CommRing R] in
/-- The indices below `l + 1` are the `succAbove
t`-images of the indices below `l` together with `t`, when `t ≤ l`. -/
theorem image_succAbove_lt_union {r l : ℕ} (t : Fin (r + 2)) (hl : t.val ≤ l) :
    t.succAbove '' {i : Fin (r + 1) | i.val < l} ∪ {t} = {i : Fin (r + 2) | i.val < l + 1} := by
  ext i
  constructor
  · rintro (⟨j, hj, rfl⟩ | hi)
    · have hj' : j.val < l := hj
      change (t.succAbove j).val < l + 1
      rcases lt_or_ge (Fin.castSucc j) t with hlt | hge
      · rw [Fin.succAbove_of_castSucc_lt _ _ hlt, Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ hge, Fin.val_succ]
        omega
    · have hit : i = t := hi
      rw [hit]
      change t.val < l + 1
      omega
  · intro hi
    have hi' : i.val < l + 1 := hi
    by_cases hit : i = t
    · exact Or.inr hit
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hit
      refine Or.inl ⟨j, ?_, rfl⟩
      change j.val < l
      rcases lt_or_ge (Fin.castSucc j) t with hlt | hge
      · have := Fin.lt_def.mp hlt
        rw [Fin.val_castSucc] at this
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ hge, Fin.val_succ] at hi'
        omega

/-- The flag span of the shortened chain, with the
killed coordinate adjoined, is the flag span of the full chain (`t ≤ l`). -/
theorem span_image_succAbove_sup {r l : ℕ} (F : Fin (r + 2) → R) (t : Fin (r + 2))
    (hl : t.val ≤ l) :
    Ideal.span ((F ∘ t.succAbove) '' {i : Fin (r + 1) | i.val < l}) ⊔ Ideal.span {F t} =
      Ideal.span (F '' {i : Fin (r + 2) | i.val < l + 1}) := by
  rw [Set.image_comp, ← Set.image_singleton, ← Ideal.span_union, ← Set.image_union,
    image_succAbove_lt_union t hl]

/-- The chain span of the shortened chain, with the
killed coordinate adjoined, is the full chain span. -/
theorem span_range_comp_succAbove_sup {r : ℕ} (F : Fin (r + 2) → R) (t : Fin (r + 2)) :
    Ideal.span (Set.range (F ∘ t.succAbove)) ⊔ Ideal.span {F t} = Ideal.span (Set.range F) := by
  rw [Set.range_comp, ← Set.image_singleton, ← Ideal.span_union, ← Set.image_union,
    Fin.range_succAbove, Set.compl_union_self, Set.image_univ]

/-- The lift of a stratum of the TRUNCATED chain (the restriction to a member with a first level
carrying the killed coordinate): a stratum at level `l ≤ l₀` of the truncated chain, or its
absorption, lifts to a stratum of the full chain; the absorption lifts to level `l₀ + 1` with
`s = {k₀}`, admissible by `a l₀ k₀ ≠ 0`. -/
theorem stratumIn_comap_of_stratumIn_castLE {n : ℕ} {z : Fin (n + 1) → R} {k₀ : Fin (n + 1)}
    {φ : R →+* S} (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {z k₀})
    {C : Set (Fin (n + 1))} (hk₀ : k₀ ∈ C) {C' : Set (Fin n)} (hC : ∀ k ∈ C', k₀.succAbove k ∈ C)
    {r : ℕ} {σ : Fin (r + 1) → Fin (n + 1)} {σ' : Fin (r + 1) → Fin n}
    (hσ : ∀ i, k₀.succAbove (σ' i) = σ i) {a : Fin (r + 1) → Fin (n + 1) → ℕ} {b : Fin (n + 1) → ℕ}
    {l₀ : ℕ} (hl : l₀ < r) (ha : a ⟨l₀, by omega⟩ k₀ ≠ 0) {Z' : Ideal S}
    (h : StratumIn (fun i => φ (z (k₀.succAbove i))) C'
        (fun i : Fin (l₀ + 1) => σ' (Fin.castLE (by omega) i))
        (fun i : Fin (l₀ + 1) => a (Fin.castLE (by omega) i) ∘ k₀.succAbove) (b ∘ k₀.succAbove) Z' ∨
      TerminalIn (fun i => φ (z (k₀.succAbove i))) C'
        (fun i : Fin (l₀ + 1) => σ' (Fin.castLE (by omega) i)) Z' ∨
      Z' = Ideal.span (Set.range ((fun i => φ (z (k₀.succAbove i))) ∘
        fun i : Fin (l₀ + 1) => σ' (Fin.castLE (by omega) i)))) :
    StratumIn z C σ a b (Z'.comap φ) := by
  classical
  have e1 : ((fun i => φ (z (k₀.succAbove i))) ∘
      fun i : Fin (l₀ + 1) => σ' (Fin.castLE (by omega) i)) =
      fun i : Fin (l₀ + 1) => (φ ∘ z ∘ σ) (Fin.castLE (by omega) i) :=
    funext fun i => by simp [hσ]
  have himg : ∀ l ≤ l₀ + 1, ((fun i => φ (z (k₀.succAbove i))) ∘
      fun i : Fin (l₀ + 1) => σ' (Fin.castLE (by omega) i)) '' {i | i.val < l} =
        φ '' ((z ∘ σ) '' {i : Fin (r + 1) | i.val < l}) := by
    intro l hl'
    rw [e1, image_castLE_lt_eq (by omega) hl', Set.image_comp]
  have hrng : Set.range ((fun i => φ (z (k₀.succAbove i))) ∘
      fun i : Fin (l₀ + 1) => σ' (Fin.castLE (by omega) i)) =
        φ '' ((z ∘ σ) '' {i : Fin (r + 1) | i.val < l₀ + 1}) := by
    rw [e1, range_castLE_eq, Set.image_comp]
  have hs : ∀ s' : Finset (Fin n), (fun i => φ (z (k₀.succAbove i))) '' ↑s' =
      φ '' (z '' (k₀.succAbove '' ↑s')) := fun s' => by
    rw [← Set.image_comp, ← Set.image_comp]
    rfl
  rcases h with ⟨l, hl', s', hs'C, hZ', hl0, hlpos⟩ | ⟨s', hs'C, hne, hZ'⟩ | hZ'
  · refine ⟨l, by omega, insert k₀ (s'.image k₀.succAbove), ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image] at hk
      rcases hk with rfl | ⟨k', hk', rfl⟩
      · exact hk₀
      · exact hC k' (hs'C hk')
    · have hZ : Z' = (Ideal.span ((z ∘ σ) '' {i : Fin (r + 1) | i.val < l}) ⊔
          Ideal.span (z '' (k₀.succAbove '' ↑s'))).map φ := by
        rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, hZ', himg l (by omega), hs]
      rw [hZ, comap_map_eq_sup_span hφ hker, Finset.coe_insert, Finset.coe_image,
        Set.image_insert_eq, Ideal.span_insert, sup_assoc, sup_comm (Ideal.span {z k₀})]
    · intro hl0'
      obtain ⟨k, hk, hb⟩ := hl0 hl0'
      exact ⟨k₀.succAbove k, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hk), hb⟩
    · intro hpos
      obtain ⟨k, hk, ha'⟩ := hlpos hpos
      exact ⟨k₀.succAbove k, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hk), ha'⟩
  · refine ⟨l₀ + 1, by omega, insert k₀ (s'.image k₀.succAbove), ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image] at hk
      rcases hk with rfl | ⟨k', hk', rfl⟩
      · exact hk₀
      · exact hC k' (hs'C hk')
    · have hZ : Z' = (Ideal.span ((z ∘ σ) '' {i : Fin (r + 1) | i.val < l₀ + 1}) ⊔
          Ideal.span (z '' (k₀.succAbove '' ↑s'))).map φ := by
        rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, hZ', hs, hrng]
      rw [hZ, comap_map_eq_sup_span hφ hker, Finset.coe_insert, Finset.coe_image,
        Set.image_insert_eq, Ideal.span_insert, sup_assoc, sup_comm (Ideal.span {z k₀})]
    · intro h0
      omega
    · intro _
      exact ⟨k₀, Finset.mem_insert_self _ _, ha⟩
  · refine ⟨l₀ + 1, by omega, {k₀}, by simpa using hk₀, ?_, ?_, ?_⟩
    · have hZ : Z' = (Ideal.span ((z ∘ σ) '' {i : Fin (r + 1) | i.val < l₀ + 1})).map φ := by
        rw [Ideal.map_span, hZ', hrng]
      rw [hZ, comap_map_eq_sup_span hφ hker, Finset.coe_singleton, Set.image_singleton]
    · intro h0
      omega
    · intro _
      exact ⟨k₀, Finset.mem_singleton_self _, ha⟩

/-- The lift along the descent to a chain
hypersurface (`k₀ = σ t`, the flag shortened, the monomials shifted): a stratum of the shortened
chain lifts to a stratum of the full chain. -/
theorem stratumIn_comap_of_stratumIn_succAbove {n : ℕ} {z : Fin (n + 1) → R} {k₀ : Fin (n + 1)}
    {φ : R →+* S} (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {z k₀})
    {C : Set (Fin (n + 1))} {C' : Set (Fin n)} (hC : ∀ k ∈ C', k₀.succAbove k ∈ C)
    {r : ℕ} {σ : Fin (r + 2) → Fin (n + 1)} {t : Fin (r + 2)} (hk₀ : σ t = k₀)
    {σ' : Fin (r + 1) → Fin n} (hσ : ∀ i, k₀.succAbove (σ' i) = σ (t.succAbove i))
    {a : Fin (r + 2) → Fin (n + 1) → ℕ} (ht : ∀ i : Fin (r + 2), i.val < t.val → a i = 0)
    {b : Fin (n + 1) → ℕ} {Z' : Ideal S}
    (h : StratumIn (fun i => φ (z (k₀.succAbove i))) C' σ' (fun i => a (Fin.succ i) ∘ k₀.succAbove)
      (a 0 ∘ k₀.succAbove) Z') :
    StratumIn z C σ a b (Z'.comap φ) := by
  classical
  obtain ⟨l, hl, s', hs'C, hZ', hl0, hlpos⟩ := h
  -- `t ≤ l` from (★) and the trivial block
  have htl : t.val ≤ l := by
    by_contra hcon
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · obtain ⟨k, -, hk⟩ := hl0 h0
      exact hk (by simp [ht 0 (by rw [Fin.val_zero]; omega)])
    · obtain ⟨k, -, hk⟩ := hlpos hpos
      refine hk ?_
      simp only [Function.comp_apply]
      rw [ht (Fin.succ ⟨l - 1, by omega⟩) (by rw [Fin.val_succ]; simp; omega)]
      rfl
  refine ⟨l + 1, by omega, s'.image k₀.succAbove, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [Finset.coe_image] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    exact hC k' (hs'C hk')
  · have hZ : Z' = (Ideal.span ((z ∘ σ ∘ t.succAbove) '' {i : Fin (r + 1) | i.val < l}) ⊔
        Ideal.span (z '' (k₀.succAbove '' ↑s'))).map φ := by
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, hZ']
      congr 1
      · congr 1
        rw [← Set.image_comp]
        exact Set.image_congr fun i _ => by simp [hσ]
      · congr 1
        rw [← Set.image_comp, ← Set.image_comp]
        rfl
    rw [hZ, comap_map_eq_sup_span hφ hker, Finset.coe_image, ← hk₀, sup_right_comm]
    have key : Ideal.span ((z ∘ σ ∘ t.succAbove) '' {i : Fin (r + 1) | i.val < l}) ⊔
        Ideal.span {z (σ t)} = Ideal.span ((z ∘ σ) '' {i : Fin (r + 2) | i.val < l + 1}) := by
      have h := span_image_succAbove_sup (z ∘ σ) t htl
      rw [Function.comp_assoc] at h
      exact h
    rw [key]
  · intro h0
    omega
  · intro _
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · subst h0
      obtain ⟨k, hk, hk'⟩ := hl0 rfl
      exact ⟨k₀.succAbove k, Finset.mem_image_of_mem _ hk, hk'⟩
    · obtain ⟨k, hk, hk'⟩ := hlpos hpos
      refine ⟨k₀.succAbove k, Finset.mem_image_of_mem _ hk, ?_⟩
      have : Fin.succ (⟨l - 1, by omega⟩ : Fin (r + 1)) = ⟨l + 1 - 1, by omega⟩ := by
        ext
        rw [Fin.val_succ]
        simp
        omega
      rw [← this]
      exact hk'

/-- The descent lift for a terminal-normal stratum of
the shortened chain: adjoining the killed chain coordinate restores the full chain. -/
theorem terminalIn_comap_of_terminalIn_succAbove {n : ℕ} {z : Fin (n + 1) → R} {k₀ : Fin (n + 1)}
    {φ : R →+* S} (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {z k₀})
    {C : Set (Fin (n + 1))} {C' : Set (Fin n)} (hC : ∀ k ∈ C', k₀.succAbove k ∈ C)
    {r : ℕ} {σ : Fin (r + 2) → Fin (n + 1)} {t : Fin (r + 2)} (hk₀ : σ t = k₀)
    {σ' : Fin (r + 1) → Fin n} (hσ : ∀ i, k₀.succAbove (σ' i) = σ (t.succAbove i)) {Z' : Ideal S}
    (h : TerminalIn (fun i => φ (z (k₀.succAbove i))) C' σ' Z') :
    TerminalIn z C σ (Z'.comap φ) := by
  classical
  obtain ⟨s', hs'C, hne, hZ'⟩ := h
  refine ⟨s'.image k₀.succAbove, ?_, hne.image _, ?_⟩
  · intro k hk
    rw [Finset.coe_image] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    exact hC k' (hs'C hk')
  · have hZ : Z' = (Ideal.span (Set.range (z ∘ σ ∘ t.succAbove)) ⊔
        Ideal.span (z '' (k₀.succAbove '' ↑s'))).map φ := by
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, hZ']
      congr 1
      · congr 1
        rw [← Set.range_comp]
        exact congrArg Set.range (funext fun i => by simp [hσ])
      · congr 1
        rw [← Set.image_comp, ← Set.image_comp]
        rfl
    rw [hZ, comap_map_eq_sup_span hφ hker, Finset.coe_image, ← hk₀, sup_right_comm]
    have key : Ideal.span (Set.range (z ∘ σ ∘ t.succAbove)) ⊔ Ideal.span {z (σ t)} =
        Ideal.span (Set.range (z ∘ σ)) := by
      have h := span_range_comp_succAbove_sup (z ∘ σ) t
      rw [Function.comp_assoc] at h
      exact h
    rw [key]

/-- The descent lift for the absorption of the
shortened chain: the preimage is the full chain. -/
theorem comap_eq_span_range_of_eq_span_range_succAbove {n : ℕ} {z : Fin (n + 1) → R}
    {k₀ : Fin (n + 1)} {φ : R →+* S} (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {z k₀}) {r : ℕ} {σ : Fin (r + 2) → Fin (n + 1)}
    {t : Fin (r + 2)} (hk₀ : σ t = k₀) {σ' : Fin (r + 1) → Fin n}
    (hσ : ∀ i, k₀.succAbove (σ' i) = σ (t.succAbove i)) {Z' : Ideal S}
    (h : Z' = Ideal.span (Set.range ((fun i => φ (z (k₀.succAbove i))) ∘ σ'))) :
    Z'.comap φ = Ideal.span (Set.range (z ∘ σ)) := by
  have hZ : Z' = (Ideal.span (Set.range (z ∘ σ ∘ t.succAbove))).map φ := by
    rw [Ideal.map_span, h, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext fun i => by simp [hσ]))
  rw [hZ, comap_map_eq_sup_span hφ hker, ← hk₀]
  have h := span_range_comp_succAbove_sup (z ∘ σ) t
  rw [Function.comp_assoc] at h
  exact h

end Algebra

end Hironaka.Resolution
