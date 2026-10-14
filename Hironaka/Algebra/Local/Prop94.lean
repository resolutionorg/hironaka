/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Taylor
public import Hironaka.Algebra.Local.MaximalContact
public import Hironaka.Algebra.Local.PowerSeries
public import Hironaka.Algebra.Local.PowerSeriesRegular
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Kollár's Proposition 94: ideals invariant under the automorphisms of the form `1 + B`

For `R = K⟦x₁, …, xₙ⟧`, `B ⊂ 𝔪` an ideal and `I` any ideal, the following are equivalent
[Kol07, Proposition 94]: (1) `I` is invariant under every automorphism of the form `1 + B`
(`IsInvariantOnePlus I B`, `Hironaka/Algebra/Local/FormalAut.lean`); (2) `B · D(I) ⊂ I`; (3)
`Bʲ · Dʲ(I) ⊂ I` for every `j ≥ 1`.  Kollár's motivation: derivations are "essentially the first
order automorphisms", so an ideal should be invariant under a subgroup of automorphisms exactly
when it is invariant to first order; the setting being infinite-dimensional, he works out the
details.

The proof follows Kollár's: (3) ⇒ (1) by the Taylor expansion modulo `𝔪^{s+1}`
(`Hironaka/Algebra/Local/Taylor.lean`) and Krull's intersection theorem; (1) ⇒ (2) by the
one-direction expansion along `xᵢ ↦ xᵢ + λ b` for `s` admissible values of `λ` (the shift
automorphisms of `Hironaka/Algebra/Local/FormalAut.lean`) and the invertibility of the Vandermonde
matrix `(λᵢʲ)`; (2) ⇒ (3) by induction on `j` with the product rule.  The derivative ideals are
those of the standard coordinate structure `RegularCoords.stdMvPowerSeries` on `K⟦X⟧`.  The
proposition is applied, through the Cohen isomorphism, to the completed local rings in the proof
of the formal equivalence of hypersurfaces of maximal contact [Kol07, Theorem 92].
-/

public section

namespace IsLocalRing

open IsLocalRing

/-! ### The product rule read backwards, and (2) ⇒ (3) for any coordinate ring -/

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n)

/-- `J · D(K) ≤ D(J K) + K · D(J)` (the product rule `a ∂h = ∂(a h) - h ∂a`, as in the last step
of the proof of [Kol07, Proposition 94]). -/
theorem mul_D_le (J K : Ideal R) : J * c.D K ≤ c.D (J * K) ⊔ K * c.D J := by
  have hcol : c.D K ≤ (c.D (J * K) ⊔ K * c.D J).colon (J : Set R) := by
    refine c.D_le_iff.mpr ⟨fun h hh => Submodule.mem_colon.mpr fun a ha => ?_,
      fun i h hh => Submodule.mem_colon.mpr fun a ha => ?_⟩
    · rw [smul_eq_mul, mul_comm h a]
      exact Ideal.mem_sup_left (c.le_D _ (Ideal.mul_mem_mul ha hh))
    · rw [smul_eq_mul]
      have : c.pderiv i h * a = c.pderiv i (a * h) - h * c.pderiv i a := by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (c.pderiv_mem_D (Ideal.mul_mem_mul ha hh) i))
        (Ideal.mem_sup_right (Ideal.mul_mem_mul hh (c.pderiv_mem_D ha i)))
  refine Ideal.mul_le.mpr fun a ha h hh => ?_
  have := Submodule.mem_colon.mp (hcol hh) a ha
  rwa [smul_eq_mul, mul_comm h a] at this

/-- The implication (2) ⇒ (3) of [Kol07, Proposition 94]: if `B · D(I) ≤ I` then `Bʲ · Dʲ(I) ≤ I`
for every `j ≥ 1`, by induction with the product rule. -/
theorem pow_mul_Dpow_le (I B : Ideal R) (h2 : B * c.D I ≤ I) :
    ∀ j : ℕ, 1 ≤ j → B ^ j * c.Dpow j I ≤ I := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simpa using h2
  | succ j hj ih =>
    rw [Dpow_succ, pow_succ]
    refine (c.mul_D_le _ _).trans (sup_le ?_ ?_)
    · have h1 : B ^ j * B * c.Dpow j I ≤ B * I := by
        rw [mul_comm (B ^ j) B, mul_assoc]
        exact Ideal.mul_mono le_rfl ih
      exact (c.D_mono h1).trans ((c.D_mul_le B I).trans (sup_le Ideal.mul_le_right h2))
    · have h1 : c.D (B ^ j * B) ≤ B ^ j := by
        rw [← pow_succ]
        refine (c.D_pow_le B (by omega)).trans ?_
        rw [Nat.add_sub_cancel]
        exact Ideal.mul_le_right
      calc c.Dpow j I * c.D (B ^ j * B) ≤ c.Dpow j I * B ^ j := Ideal.mul_mono le_rfl h1
        _ = B ^ j * c.Dpow j I := mul_comm _ _
        _ ≤ I := ih

end RegularCoords

/-! ### Proposition 94 on `K⟦X⟧` -/

section PowerSeries

open MvPowerSeries

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
/-- `b^α ∈ B^{|α|}` for `bᵢ ∈ B`. -/
theorem prod_pow_mem_pow {B : Ideal (MvPowerSeries (Fin n) K)} {b : Fin n → MvPowerSeries (Fin n) K}
    (hb : ∀ i, b i ∈ B) (α : Fin n →₀ ℕ) : ∏ i, b i ^ α i ∈ B ^ α.degree := by
  rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hb i) _

theorem pderivEnd'_pow_mem_Dpow {I : Ideal (MvPowerSeries (Fin n) K)}
    {f : MvPowerSeries (Fin n) K} (hf : f ∈ I) (i : Fin n) (b : ℕ) :
    (pderivEnd' i ^ b) f ∈ (RegularCoords.stdMvPowerSeries K n).Dpow b I := by
  induction b with
  | zero => simpa using hf
  | succ b ih =>
    rw [pow_succ', Module.End.mul_apply, RegularCoords.Dpow_succ]
    exact (RegularCoords.stdMvPowerSeries K n).pderiv_mem_D ih i

/-- `∂^α f ∈ D^{|α|}(I)` for `f ∈ I` (each Taylor term lies in `D^{|α|}(I) B^{|α|}`). -/
theorem pderivPowSeries_mem_Dpow {I : Ideal (MvPowerSeries (Fin n) K)} (α : Fin n →₀ ℕ)
    {f : MvPowerSeries (Fin n) K} (hf : f ∈ I) :
    pderivPowSeries α f ∈ (RegularCoords.stdMvPowerSeries K n).Dpow α.degree I := by
  induction α using Finsupp.induction generalizing f with
  | zero => simpa [pderivPowSeries_zero] using hf
  | single_add a b g _ _ ih =>
    rw [pderivPowSeries_add, Module.End.mul_apply, pderivPowSeries_single, map_add,
      Finsupp.degree_single, ← RegularCoords.Dpow_Dpow]
    exact pderivEnd'_pow_mem_Dpow (ih hf) a b

omit [CharZero K] in
/-- An automorphism `g` of the form `1 + B` is the substitution `Xᵢ ↦ Xᵢ + bᵢ` with
`bᵢ := g(Xᵢ) - Xᵢ ∈ B`. -/
theorem IsOnePlus.eq_substAlgHom {B : Ideal (MvPowerSeries (Fin n) K)}
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K))
    {g : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K} (hg : IsOnePlus B g)
    (f : MvPowerSeries (Fin n) K) :
    g f = substAlgHom (R := K)
      (hasSubst_add (b := fun i => g (X (R := K) i) - X (R := K) i) fun i => hB (hg.2 i)) f := by
  obtain ⟨⟨a, ha, hga⟩, hgB⟩ := hg
  have h1 : (g : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K) f =
      substAlgHom ha f := by
    rw [hga]
  have h2 : a = fun i => X (R := K) i + (g (X (R := K) i) - X (R := K) i) := by
    funext i
    have : (g : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K) (X (R := K) i) =
        substAlgHom ha (X (R := K) i) := by rw [hga]
    rw [coe_substAlgHom, subst_X ha] at this
    rw [add_sub_cancel]
    exact this.symm
  rw [show g f = (g : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K) f from rfl, h1,
    coe_substAlgHom, coe_substAlgHom, h2]

/-- If `Bʲ Dʲ(I) ≤ I` for all `j ≥ 1`, `bᵢ ∈ B` and `f ∈ I`, then each Taylor term
`(1/α!) (∂^α f) b^α` lies in `D^{|α|}(I) B^{|α|} ≤ I` (the proof of [Kol07, Proposition 94]). -/
theorem taylor_term_mem {I B : Ideal (MvPowerSeries (Fin n) K)}
    (h3 : ∀ j : ℕ, 1 ≤ j → B ^ j * (RegularCoords.stdMvPowerSeries K n).Dpow j I ≤ I)
    {b : Fin n → MvPowerSeries (Fin n) K} (hbB : ∀ i, b i ∈ B) {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ I) (α : Fin n →₀ ℕ) :
    ((multiFactorial α : ℚ)⁻¹ • pderivPowSeries α f) * ∏ i, b i ^ α i ∈ I := by
  rcases Nat.eq_zero_or_pos α.degree with h0 | hpos
  · have hα : α = 0 := by
      ext i
      have := Finsupp.le_degree i α
      rw [h0] at this
      simpa using this
    subst hα
    simpa [pderivPowSeries_zero, multiFactorial] using hf
  · rw [Algebra.smul_def, mul_assoc]
    refine Ideal.mul_mem_left _ _ (h3 α.degree hpos ?_)
    rw [mul_comm]
    exact Ideal.mul_mem_mul (pderivPowSeries_mem_Dpow α hf) (prod_pow_mem_pow hbB α)

/-- The implication (3) ⇒ (1) of [Kol07, Proposition 94]: if `Bʲ Dʲ(I) ≤ I` for all `j ≥ 1`, then
`I` is invariant under the automorphisms of the form `1 + B` — `g(f) ∈ I + 𝔪^{s+1}` for every `s`
by the Taylor expansion and `taylor_term_mem`, and Krull's intersection theorem finishes. -/
theorem isInvariantOnePlus_of_forall_pow_mul_Dpow_le (I B : Ideal (MvPowerSeries (Fin n) K))
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K))
    (h3 : ∀ j : ℕ, 1 ≤ j → B ^ j * (RegularCoords.stdMvPowerSeries K n).Dpow j I ≤ I) :
    IsInvariantOnePlus I B := by
  classical
  intro g hg
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap]
  change g f ∈ I
  rw [hg.eq_substAlgHom hB f]
  have hb : ∀ i, g (X (R := K) i) - X (R := K) i ∈ maximalIdeal (MvPowerSeries (Fin n) K) :=
    fun i => hB (hg.2 i)
  refine mem_of_forall_mem_sup_pow fun s => ?_
  rcases s with _ | s
  · simp
  · have hd := substAlgHom_add_sub_taylor_mem f hb s
    have hsum := Ideal.sum_mem I fun α (_ : α ∈ degreeLE n s) =>
      taylor_term_mem h3 hg.2 hf α
    have := Ideal.add_mem _ (Ideal.mem_sup_left hsum) (Ideal.mem_sup_right hd)
    rwa [add_sub_cancel] at this

/-- The admissible, nonzero, pairwise distinct scalars `λ₁, …, λ_N ∈ ℚ` of Kollár's Vandermonde
argument ("use `s` different values", the proof of [Kol07, Proposition 94]): all of `1, …, N + 1`
except the one excluded value. -/
theorem exists_admissible_scalars (q₀ : ℚ) (N : ℕ) :
    ∃ lam : Fin N → ℚ, Function.Injective lam ∧ ∀ i, lam i ≠ q₀ ∧ lam i ≠ 0 := by
  classical
  refine ⟨fun i => if ((i : ℕ) + 1 : ℚ) = q₀ then (N : ℚ) + 1 else (i : ℕ) + 1, ?_, ?_⟩
  · intro i j hij
    simp only at hij
    have key : ∀ {p q : ℕ}, ((p : ℚ) + 1 = (q : ℚ) + 1) → p = q := fun h => by
      exact_mod_cast add_right_cancel h
    split_ifs at hij with hi hj hj
    · exact Fin.ext (key (hi.trans hj.symm))
    · exfalso
      have hj' : ((j : ℕ) : ℚ) = N := by linarith
      have hj'' : (j : ℕ) = N := by exact_mod_cast hj'
      have := j.isLt
      omega
    · exfalso
      have hi' : ((i : ℕ) : ℚ) = N := by linarith
      have hi'' : (i : ℕ) = N := by exact_mod_cast hi'
      have := i.isLt
      omega
    · exact Fin.ext (key hij)
  · intro i
    simp only
    split_ifs with hi
    · refine ⟨fun h => ?_, by positivity⟩
      have : ((i : ℕ) : ℚ) + 1 = N + 1 := hi.trans h.symm
      have hi' : ((i : ℕ) : ℚ) = N := by linarith
      have hi'' : (i : ℕ) = N := by exact_mod_cast hi'
      have := i.isLt
      omega
    · exact ⟨hi, by positivity⟩

/-- If `I` is invariant under the automorphisms of the form `1 + B`, `b ∈ B`, `f ∈ I` and `λ` is
admissible (`exists_onePlus_shift`), then `∑_{j=0}^{s} λʲ uⱼ ∈ I + 𝔪^{s+1}` with
`uⱼ := (bʲ/j!) ∂ᵢʲ f` (the `range` form). -/
theorem taylor_shift_range_mem {I B : Ideal (MvPowerSeries (Fin n) K)}
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K)) (h1 : IsInvariantOnePlus I B)
    {b : MvPowerSeries (Fin n) K} (hb : b ∈ B) {f : MvPowerSeries (Fin n) K} (hf : f ∈ I)
    (i : Fin n) {q : ℚ}
    (hq : ∃ g : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K,
      IsOnePlus B g ∧ ∀ f, g f = subst (shiftSubst i (q • b)) f) (s : ℕ) :
    ∑ j ∈ Finset.range (s + 1), q ^ j • (((j.factorial : ℚ)⁻¹ • (pderivEnd' i ^ j) f) * b ^ j) ∈
      I ⊔ maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) := by
  obtain ⟨g, hg, hgf⟩ := hq
  have hgI : g f ∈ I := by
    have := h1 g hg (Ideal.mem_map_of_mem _ hf)
    simpa using this
  have hd := substAlgHom_shift_sub_taylor_mem f i (hB hb) q s
  rw [coe_substAlgHom, ← hgf] at hd
  have := Ideal.sub_mem _ (Ideal.mem_sup_left hgI) (Ideal.mem_sup_right hd)
  rwa [sub_sub_cancel] at this

theorem sum_range_succ_eq_add_sum_Icc {M : Type*} [AddCommMonoid M] (F : ℕ → M) (s : ℕ) :
    ∑ j ∈ Finset.range (s + 1), F j = F 0 + ∑ j ∈ Finset.Icc 1 s, F j := by
  have h : Finset.Icc 1 s = Finset.Ico 1 (s + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Finset.sum_range_succ', add_comm, Finset.range_eq_Ico, Finset.sum_Ico_add', zero_add, h]

/-- The first step of (1) ⇒ (2) in the proof of [Kol07, Proposition 94]: if `I` is invariant under
the automorphisms of the form `1 + B`, `b ∈ B`, `f ∈ I` and `λ` is admissible, then
`∑_{j=1}^{s} λʲ uⱼ ∈ I + 𝔪^{s+1}` with `uⱼ := (bʲ/j!) ∂ᵢʲ f` (from the one-direction Taylor
formula and `g_λ(f) ∈ I`). -/
theorem taylor_shift_sum_mem {I B : Ideal (MvPowerSeries (Fin n) K)}
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K)) (h1 : IsInvariantOnePlus I B)
    {b : MvPowerSeries (Fin n) K} (hb : b ∈ B) {f : MvPowerSeries (Fin n) K} (hf : f ∈ I)
    (i : Fin n) {q : ℚ}
    (hq : ∃ g : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K,
      IsOnePlus B g ∧ ∀ f, g f = subst (shiftSubst i (q • b)) f) (s : ℕ) :
    ∑ j ∈ Finset.Icc 1 s, q ^ j • (((j.factorial : ℚ)⁻¹ • (pderivEnd' i ^ j) f) * b ^ j) ∈
      I ⊔ maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) := by
  have h := taylor_shift_range_mem hB h1 hb hf i hq s
  rw [sum_range_succ_eq_add_sum_Icc] at h
  have := Ideal.sub_mem _ h (Ideal.mem_sup_left hf)
  simpa using this

/-- The second step of (1) ⇒ (2) in the proof of [Kol07, Proposition 94]: choosing `s` distinct
admissible `λ₁, …, λ_s ∈ ℚ`, the Vandermonde matrix `(λᵢʲ)` is invertible over `ℚ`, hence
`u₁ = b ∂ᵢ f ∈ I + 𝔪^{s+1}`. -/
theorem mul_pderiv_mem_sup_pow {I B : Ideal (MvPowerSeries (Fin n) K)}
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K)) (h1 : IsInvariantOnePlus I B)
    {b : MvPowerSeries (Fin n) K} (hb : b ∈ B) {f : MvPowerSeries (Fin n) K} (hf : f ∈ I)
    (i : Fin n) {N : ℕ} (hN : 1 ≤ N) :
    b * MvPowerSeries.pderiv (R := K) i f ∈
      I ⊔ maximalIdeal (MvPowerSeries (Fin n) K) ^ (N + 1) := by
  classical
  obtain ⟨q₀, hq₀⟩ := exists_onePlus_shift B hB i hb
  -- `u j = (b^j / j!) ∂ᵢ^j f`
  set u : ℕ → MvPowerSeries (Fin n) K := fun j =>
    ((j.factorial : ℚ)⁻¹ • (pderivEnd' i ^ j) f) * b ^ j with hu
  have hu0 : u 0 = f := by simp [hu]
  have hu1 : u 1 = b * MvPowerSeries.pderiv (R := K) i f := by simp [hu, mul_comm]
  set J := I ⊔ maximalIdeal (MvPowerSeries (Fin n) K) ^ (N + 1) with hJ
  obtain ⟨lam, hinj, hlam⟩ := exists_admissible_scalars q₀ N
  -- the Taylor sums `w k := ∑_{j=1}^{N} lam k ^ j • u j` lie in `J`
  have hw : ∀ k : Fin N, ∑ j : Fin N, lam k ^ ((j : ℕ) + 1) • u ((j : ℕ) + 1) ∈ J := by
    intro k
    have hfull := taylor_shift_range_mem hB h1 hb hf i (hq₀ (lam k) (hlam k).1) N
    change ∑ j ∈ Finset.range (N + 1), lam k ^ j • u j ∈ J at hfull
    rw [Finset.sum_range_succ', pow_zero, one_smul, hu0, Finset.sum_range] at hfull
    have := Ideal.sub_mem _ hfull (Ideal.mem_sup_left hf)
    rwa [add_sub_cancel_right] at this
  -- the Vandermonde matrix `V k j = lam k ^ (j + 1)` is invertible over `ℚ`
  set V : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun k j => lam k ^ ((j : ℕ) + 1) with hV
  have hVdet : V.det ≠ 0 := by
    have hV' : V = Matrix.diagonal lam * Matrix.vandermonde lam := by
      ext k j
      rw [hV, Matrix.of_apply, Matrix.diagonal_mul, Matrix.vandermonde_apply, pow_succ']
    rw [hV', Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => (hlam k).2)
      (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  set V' : Matrix (Fin N) (Fin N) (MvPowerSeries (Fin n) K) :=
    V.map (algebraMap ℚ (MvPowerSeries (Fin n) K)) with hV'
  have hV'det : IsUnit V'.det := by
    have : V'.det = algebraMap ℚ (MvPowerSeries (Fin n) K) V.det := by
      rw [hV', RingHom.map_det, RingHom.mapMatrix_apply]
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hVdet).map _
  -- `w = V' *ᵥ u'` with `u' j = u (j + 1)`, hence `u' = V'⁻¹ *ᵥ w`
  set u' : Fin N → MvPowerSeries (Fin n) K := fun j => u ((j : ℕ) + 1) with hu'
  set w : Fin N → MvPowerSeries (Fin n) K := fun k =>
    ∑ j : Fin N, lam k ^ ((j : ℕ) + 1) • u ((j : ℕ) + 1) with hw'
  have hVu : V'.mulVec u' = w := by
    funext k
    simp only [Matrix.mulVec, dotProduct, hV', hV, Matrix.map_apply, Matrix.of_apply, hu', hw',
      Algebra.smul_def]
  have hu'eq : u' = V'⁻¹.mulVec w := by
    rw [← hVu, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hV'det, Matrix.one_mulVec]
  have h0 : (0 : ℕ) < N := hN
  have : u' ⟨0, h0⟩ ∈ J := by
    rw [hu'eq]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hw k)
  rw [← hu1]
  simpa [hu'] using this

/-- The third step of (1) ⇒ (2) in the proof of [Kol07, Proposition 94]: by Krull's intersection
theorem, `b ∂ᵢ f ∈ I` for `b ∈ B`, `f ∈ I` and every coordinate `i`. -/
theorem mul_pderiv_mem_of_isInvariantOnePlus {I B : Ideal (MvPowerSeries (Fin n) K)}
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K)) (h1 : IsInvariantOnePlus I B)
    {b : MvPowerSeries (Fin n) K} (hb : b ∈ B) {f : MvPowerSeries (Fin n) K} (hf : f ∈ I)
    (i : Fin n) : b * MvPowerSeries.pderiv (R := K) i f ∈ I := by
  refine mem_of_forall_mem_sup_pow fun s => ?_
  rcases s with _ | s
  · simp
  · exact (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ _)) I)
      (mul_pderiv_mem_sup_pow hB h1 hb hf i (N := s + 1) (by omega))

/-- The implication (1) ⇒ (2) of [Kol07, Proposition 94]: since `D(I)` is generated by the `f`
and `∂ᵢ f` (`f ∈ I`) and `b f, b ∂ᵢ f ∈ I`, `B · D(I) ≤ I`. -/
theorem mul_D_le_of_isInvariantOnePlus {I B : Ideal (MvPowerSeries (Fin n) K)}
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K)) (h1 : IsInvariantOnePlus I B) :
    B * (RegularCoords.stdMvPowerSeries K n).D I ≤ I := by
  have hcol : (RegularCoords.stdMvPowerSeries K n).D I ≤ I.colon (B : Set _) := by
    refine (RegularCoords.stdMvPowerSeries K n).D_le_iff.mpr
      ⟨fun f hf => Submodule.mem_colon.mpr fun b hb => ?_,
        fun i f hf => Submodule.mem_colon.mpr fun b hb => ?_⟩
    · rw [smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hf
    · rw [smul_eq_mul, mul_comm _ b]
      exact mul_pderiv_mem_of_isInvariantOnePlus hB h1 hb hf i
  refine Ideal.mul_le.mpr fun b hb h hh => ?_
  have := Submodule.mem_colon.mp (hcol hh) b hb
  rwa [smul_eq_mul, mul_comm h b] at this

/-- **Kollár's Proposition 94**, first form [Kol07, Proposition 94, (1) ⟺ (2)]: `I` is invariant
under the automorphisms of the form `1 + B` iff `B · D(I) ≤ I`. -/
theorem isInvariantOnePlus_iff_mul_D_le (I B : Ideal (MvPowerSeries (Fin n) K))
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K)) :
    IsInvariantOnePlus I B ↔ B * (RegularCoords.stdMvPowerSeries K n).D I ≤ I :=
  ⟨mul_D_le_of_isInvariantOnePlus hB, fun h2 =>
    isInvariantOnePlus_of_forall_pow_mul_Dpow_le I B hB
      ((RegularCoords.stdMvPowerSeries K n).pow_mul_Dpow_le I B h2)⟩

/-- **Kollár's Proposition 94**, second form [Kol07, Proposition 94, (1) ⟺ (3)]: `I` is invariant
under the automorphisms of the form `1 + B` iff `Bʲ · Dʲ(I) ≤ I` for every `j ≥ 1`. -/
theorem isInvariantOnePlus_iff_forall_pow_mul_Dpow_le (I B : Ideal (MvPowerSeries (Fin n) K))
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K)) :
    IsInvariantOnePlus I B ↔
      ∀ j : ℕ, 1 ≤ j → B ^ j * (RegularCoords.stdMvPowerSeries K n).Dpow j I ≤ I :=
  ⟨fun h1 => (RegularCoords.stdMvPowerSeries K n).pow_mul_Dpow_le I B
      ((isInvariantOnePlus_iff_mul_D_le I B hB).mp h1),
    isInvariantOnePlus_of_forall_pow_mul_Dpow_le I B hB⟩

/-- `I` is MC-invariant with respect to `m` iff it is invariant under every automorphism of the
form `1 + MC_m(I)` (for `MC_m(I) ≤ 𝔪`, e.g. `ord I = m ≥ 1`): [Kol07, Proposition 94] with
`B = MC(I)`, read against the definition (53.1) of [Kol07, 53]. -/
theorem isMCInvariant_iff_isInvariantOnePlus (I : Ideal (MvPowerSeries (Fin n) K)) (m : ℕ)
    (hB : (RegularCoords.stdMvPowerSeries K n).MC I m ≤
      maximalIdeal (MvPowerSeries (Fin n) K)) :
    (RegularCoords.stdMvPowerSeries K n).IsMCInvariant I m ↔
      IsInvariantOnePlus I ((RegularCoords.stdMvPowerSeries K n).MC I m) :=
  (isInvariantOnePlus_iff_mul_D_le I _ hB).symm

end PowerSeries

end IsLocalRing
