/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.MaximalContact
public import Hironaka.Algebra.Local.PowerSeries
public import Hironaka.Algebra.Local.PowerSeriesRegular
import Hironaka.Algebra.Local.Taylor
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Coordinate derivations over the coefficient field

Kollár's derivations are `k`-derivations ("`Der_X` … a `k`-bilinear map", [Kol07, Definition 73];
Włodarczyk's `Der_K(𝒪_X)`, [Wlo05, Definition 2.6.1]), while the coordinate structure
`RegularCoords` of `Hironaka/Algebra/Local/Coords.lean` carries the `∂ᵢ` as `ℚ`-derivations.  The
spanning condition `SpansDerivations` must be read over the coefficient field `k` of the ring at
hand: `SpansDerivations ℚ` is strictly stronger and fails for `ℝ⟦X⟧`, `ℂ⟦X⟧` and the stalks of
smooth varieties over `ℝ` or `ℂ` (a nonzero `ℚ`-derivation of the coefficient field, applied
coefficientwise, is a `ℚ`-derivation killing every `xᵢ`; not formalized).

This file provides the `k`-linear theory: `IsLinearOver k` (the `∂ᵢ` kill `algebraMap k R`),
`SpansDerivations ℚ → SpansDerivations k`, the spanning identity in transported coordinates over
`k`, the commutation of the transported derivations and the change of coordinates over `k`, the
maximal-contact coordinate over `k`, and the two properties for `K⟦X⟧` (`IsLinearOver K` from
`pderiv_C`, `SpansDerivations K` by uniqueness of Taylor coefficients through Krull's
intersection theorem, `Hironaka/Algebra/Local/Taylor.lean`).  The `ℚ`-forms `transportPderiv_comm`,
`changeCoordsOfSpans`, `exists_coords_x_zero_eq`, `exists_maximalContact` of
`Hironaka/Algebra/Local/Coords.lean` and `MaximalContact.lean` remain valid with the stronger
hypothesis.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

variable {R : Type*} [CommRing R]

/-- A `ℚ`-derivation of `R` killing the image of `k` is a `k`-derivation (`∂ᵢ(af) = a ∂ᵢf` by
Leibniz). -/
def derivationOver {k : Type*} [CommRing k] [Algebra k R] [Algebra ℚ R] (D : Derivation ℚ R R)
    (hD : ∀ a : k, D (algebraMap k R a) = 0) : Derivation k R R where
  toLinearMap :=
    { toFun := D
      map_add' := fun f g => map_add D f g
      map_smul' := fun a f => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Derivation.leibniz, hD a, smul_zero, add_zero, smul_eq_mul,
          Algebra.smul_def] }
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := fun f g => D.leibniz f g

@[simp] theorem derivationOver_apply {k : Type*} [CommRing k] [Algebra k R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (hD : ∀ a : k, D (algebraMap k R a) = 0) (f : R) :
    derivationOver D hD f = D f :=
  rfl

namespace RegularCoords

variable [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ} (c : RegularCoords R n)

section Linear

variable (k : Type*) [CommRing k] [Algebra k R]

/-- The coordinate structure is **`k`-linear** if every `∂ᵢ` kills the image of the coefficient
field `k` (so that the `∂ᵢ` are `k`-derivations, as in [Kol07, Definition 73]). -/
def IsLinearOver : Prop := ∀ (i : Fin n) (a : k), c.pderiv i (algebraMap k R a) = 0

variable {k}

/-- `∂ᵢ` as a `k`-derivation. -/
def pderivOver (hk : c.IsLinearOver k) (i : Fin n) : Derivation k R R :=
  derivationOver (c.pderiv i) (hk i)

@[simp] theorem pderivOver_apply (hk : c.IsLinearOver k) (i : Fin n) (f : R) :
    c.pderivOver hk i f = c.pderiv i f :=
  rfl

/-- Every `R`-combination of the `∂ᵢ` is again `k`-linear. -/
theorem isLinearOver_sum_smul (hk : c.IsLinearOver k) (r : Fin n → R) (a : k) :
    (∑ l, r l • c.pderiv l) (algebraMap k R a) = 0 := by
  rw [derivation_sum_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [Derivation.smul_apply, hk l a, smul_zero]

/-- `SpansDerivations ℚ` implies `SpansDerivations k` (a `k`-derivation is a `ℚ`-derivation).  The
converse fails for `k = ℝ, ℂ` (not formalized). -/
theorem SpansDerivations.of_rat [Algebra ℚ k] [IsScalarTower ℚ k R] (hs : c.SpansDerivations ℚ) :
    c.SpansDerivations k :=
  fun δ f => hs (δ.restrictScalars ℚ) f

/-- The transported derivations are `k`-linear when the `∂ₗ` are. -/
theorem transportPderiv_isLinearOver (hk : c.IsLinearOver k) (x' : Fin n → R) (j : Fin n) (a : k) :
    c.transportPderiv x' j (algebraMap k R a) = 0 := by
  rw [transportPderiv_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hk l a, mul_zero]

/-- The spanning identity in transported coordinates, `δ f = ∑ⱼ δ(x'ⱼ) ∂'ⱼ f` for every
`k`-derivation `δ` (the argument of `SpansDerivations.transport` read over `k`; no linearity
hypothesis is needed here). -/
theorem SpansDerivations.transport_over (hs : c.SpansDerivations k) (x' : Fin n → R)
    (hx' : maximalIdeal R = Ideal.span (Set.range x')) (δ : Derivation k R R) (f : R) :
    δ f = ∑ j, δ (x' j) * c.transportPderiv x' j f := by
  classical
  have hdet : IsUnit (c.jacobian x').det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (c.isUnit_jacobian x' hx')
  have hmul := Matrix.mul_nonsing_inv _ hdet
  have h1 : ∀ j, δ (x' j) = ∑ l, δ (c.x l) * c.jacobian x' l j := fun j => hs δ (x' j)
  calc δ f = ∑ l, δ (c.x l) * c.pderiv l f := hs δ f
    _ = ∑ l, ∑ p, δ (c.x l) * ((c.jacobian x' * (c.jacobian x')⁻¹) l p * c.pderiv p f) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hmul]
        simp [Matrix.one_apply]
    _ = ∑ l, ∑ p, ∑ j, δ (c.x l) * c.jacobian x' l j * ((c.jacobian x')⁻¹ j p * c.pderiv p f) := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun p _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ l, ∑ j, ∑ p, δ (c.x l) * c.jacobian x' l j * ((c.jacobian x')⁻¹ j p * c.pderiv p f) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ p, δ (c.x l) * c.jacobian x' l j * ((c.jacobian x')⁻¹ j p * c.pderiv p f) :=
        Finset.sum_comm
    _ = ∑ j, δ (x' j) * c.transportPderiv x' j f := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h1, transportPderiv_apply, Finset.sum_mul_sum]

/-- The transported derivation as a `k`-derivation. -/
noncomputable def transportPderivOver (hk : c.IsLinearOver k) (x' : Fin n → R) (j : Fin n) :
    Derivation k R R :=
  derivationOver (c.transportPderiv x' j) (c.transportPderiv_isLinearOver hk x' j)

/-- Under `IsLinearOver k` and `SpansDerivations k` the transported derivations commute — their
commutator is a `k`-derivation killing every `x'ₗ`, hence zero by the spanning identity over
`k` (the `k`-linear form of `transportPderiv_comm`). -/
theorem transportPderiv_comm_over (hk : c.IsLinearOver k) (hs : c.SpansDerivations k)
    (x' : Fin n → R) (hx' : maximalIdeal R = Ideal.span (Set.range x')) (i j : Fin n) (f : R) :
    c.transportPderiv x' i (c.transportPderiv x' j f) =
      c.transportPderiv x' j (c.transportPderiv x' i f) := by
  have hδ : ∀ l, ⁅c.transportPderivOver hk x' i, c.transportPderivOver hk x' j⁆ (x' l) = 0 := by
    intro l
    rw [Derivation.commutator_apply]
    change c.transportPderiv x' i (c.transportPderiv x' j (x' l)) -
      c.transportPderiv x' j (c.transportPderiv x' i (x' l)) = 0
    rw [c.transportPderiv_x x' hx', c.transportPderiv_x x' hx']
    split_ifs <;> simp
  have := SpansDerivations.transport_over c hs x' hx'
    ⁅c.transportPderivOver hk x' i, c.transportPderivOver hk x' j⁆ f
  simp only [hδ, zero_mul, Finset.sum_const_zero] at this
  rw [Derivation.commutator_apply] at this
  exact sub_eq_zero.mp this

/-- The change of coordinates over `k` (no commutation hypothesis needed): the form of the change
of coordinates used for the stalks of smooth varieties and the rings of analytic germs. -/
noncomputable def changeCoordsOfLinearSpans (hk : c.IsLinearOver k) (hs : c.SpansDerivations k)
    (x' : Fin n → R) (hx' : maximalIdeal R = Ideal.span (Set.range x')) : RegularCoords R n :=
  c.changeCoords x' hx' (c.transportPderiv_comm_over hk hs x' hx')

theorem changeCoordsOfLinearSpans_x (hk : c.IsLinearOver k) (hs : c.SpansDerivations k)
    (x' : Fin n → R) (hx' : maximalIdeal R = Ideal.span (Set.range x')) :
    (c.changeCoordsOfLinearSpans hk hs x' hx').x = x' :=
  rfl

theorem changeCoordsOfLinearSpans_pderiv (hk : c.IsLinearOver k) (hs : c.SpansDerivations k)
    (x' : Fin n → R) (hx' : maximalIdeal R = Ideal.span (Set.range x')) :
    (c.changeCoordsOfLinearSpans hk hs x' hx').pderiv = c.transportPderiv x' :=
  rfl

/-- The transported structure is again `k`-linear. -/
theorem changeCoordsOfLinearSpans_isLinearOver (hk : c.IsLinearOver k) (hs : c.SpansDerivations k)
    (x' : Fin n → R) (hx' : maximalIdeal R = Ideal.span (Set.range x')) :
    (c.changeCoordsOfLinearSpans hk hs x' hx').IsLinearOver k :=
  fun j a => c.transportPderiv_isLinearOver hk x' j a

/-- The transported structure again spans the `k`-derivations. -/
theorem changeCoordsOfLinearSpans_spansDerivations (hk : c.IsLinearOver k)
    (hs : c.SpansDerivations k) (x' : Fin n → R)
    (hx' : maximalIdeal R = Ideal.span (Set.range x')) :
    (c.changeCoordsOfLinearSpans hk hs x' hx').SpansDerivations k :=
  fun δ f => SpansDerivations.transport_over c hs x' hx' δ f

theorem reindex_isLinearOver (hk : c.IsLinearOver k) (σ : Equiv.Perm (Fin n)) :
    (c.reindex σ).IsLinearOver k :=
  fun i a => hk (σ i) a

theorem reindex_spansDerivations (hs : c.SpansDerivations k) (σ : Equiv.Perm (Fin n)) :
    (c.reindex σ).SpansDerivations k := fun δ f => by
  rw [hs δ f]
  exact (Equiv.sum_comp σ fun i => δ (c.x i) * c.pderiv i f).symm

/-- Under `IsLinearOver k` and `SpansDerivations k`, an element of order `1` is the first
coordinate of a `k`-linear, `k`-spanning coordinate system `x'` with `∂'₁ h = 1` (the coordinate
half of the local construction of maximal contact, [Kol07, 51.2], over `k`). -/
theorem exists_coords_x_zero_eq_over (hk : c.IsLinearOver k) (hs : c.SpansDerivations k) {h : R}
    (hh : ordElem h = 1) :
    ∃ (hn : 0 < n) (c' : RegularCoords R n), c'.x ⟨0, hn⟩ = h ∧ c'.pderiv ⟨0, hn⟩ h = 1 ∧
      c'.IsLinearOver k ∧ c'.SpansDerivations k := by
  classical
  obtain ⟨hh1, hh2⟩ := ordElem_eq_one_iff.mp hh
  obtain ⟨i, hi⟩ := c.exists_span_update hh1 hh2
  have hx : (c.changeCoordsOfLinearSpans hk hs (Function.update c.x i h) hi).x i = h := by
    rw [changeCoordsOfLinearSpans_x, Function.update_self]
  refine ⟨i.pos, (c.changeCoordsOfLinearSpans hk hs _ hi).reindex (Equiv.swap ⟨0, i.pos⟩ i),
    ?_, ?_, reindex_isLinearOver _ (c.changeCoordsOfLinearSpans_isLinearOver hk hs _ hi) _,
    reindex_spansDerivations _ (c.changeCoordsOfLinearSpans_spansDerivations hk hs _ hi) _⟩
  · rw [reindex_x, Equiv.swap_apply_left, hx]
  · have := ((c.changeCoordsOfLinearSpans hk hs _ hi).reindex
      (Equiv.swap ⟨0, i.pos⟩ i)).pderiv_x ⟨0, i.pos⟩ ⟨0, i.pos⟩
    rwa [ite_eq_left rfl, reindex_x, Equiv.swap_apply_left, hx] at this

/-- The local construction of maximal contact [Kol07, 51.2] over `k`: for `ord I = m ≥ 1` some
`h ∈ MC_m(I)` of order `1` is the first coordinate of a coordinate system `x'` with `∂'₁ h = 1`. -/
theorem exists_maximalContact_over (hk : c.IsLinearOver k) (hs : c.SpansDerivations k)
    {I : Ideal R} {m : ℕ} (hm : 1 ≤ m) (hI : ord I = m) :
    ∃ h ∈ c.MC I m, ordElem h = 1 ∧
      ∃ (hn : 0 < n) (c' : RegularCoords R n), c'.x ⟨0, hn⟩ = h ∧ c'.pderiv ⟨0, hn⟩ h = 1 := by
  obtain ⟨h, hmem, hh⟩ := c.exists_mem_MC_ordElem_eq_one hm hI
  obtain ⟨hn, c', hx, hd, -, -⟩ := c.exists_coords_x_zero_eq_over hk hs hh
  exact ⟨h, hmem, hh, hn, c', hx, hd⟩

end Linear

end RegularCoords

/-! ### The two properties for `K⟦X⟧` -/

section PowerSeries

open MvPowerSeries

variable {K : Type*} [Field K] {n : ℕ}

/-- A `K`-derivation of `K⟦X⟧` lowers the `𝔪`-adic order by at most one (Leibniz on a product of
elements of `𝔪`). -/
theorem derivation_mem_maximalIdeal_pow
    (δ : Derivation K (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K)) (N : ℕ)
    {f : MvPowerSeries (Fin n) K} (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ (N + 1)) :
    δ f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
  induction N generalizing f with
  | zero => simp
  | succ N ih =>
    rw [pow_succ'] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha (ih hb)
    · rw [map_add]
      exact Ideal.add_mem _ hx hy

/-- A `K`-derivation of `K⟦X⟧` agrees with `∑ᵢ δ(Xᵢ) ∂ᵢ` on polynomials (Leibniz). -/
theorem derivation_coe_eq_sum
    (δ : Derivation K (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K))
    (P : MvPolynomial (Fin n) K) :
    δ (P : MvPowerSeries (Fin n) K) =
      ∑ i, δ (X i) * MvPowerSeries.pderiv (R := K) i (P : MvPowerSeries (Fin n) K) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    have hC : ((MvPolynomial.C a : MvPolynomial (Fin n) K) : MvPowerSeries (Fin n) K) =
        algebraMap K (MvPowerSeries (Fin n) K) a := by
      rw [MvPolynomial.coe_C, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    rw [hC, Derivation.map_algebraMap]
    simp [Derivation.map_algebraMap]
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add]
    ring
  | mul_X p i hp =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp]
    have hpd : ∀ j, MvPowerSeries.pderiv (R := K) j ((p : MvPowerSeries (Fin n) K) * X i) =
        (p : MvPowerSeries (Fin n) K) * (if i = j then 1 else 0) +
          X i * MvPowerSeries.pderiv (R := K) j (p : MvPowerSeries (Fin n) K) := fun j => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPowerSeries.pderiv_X, Pi.single_apply]
    simp only [hpd, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ i, ite_eq_left (Finset.mem_univ i), Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring

variable (K n) [CharZero K]

/-- The coordinate structure `RegularCoords.mvPowerSeries` on `K⟦X⟧` is `K`-linear
(`MvPowerSeries.pderiv_C`). -/
theorem mvPowerSeries_isLinearOver :
    (RegularCoords.stdMvPowerSeries K n).IsLinearOver K := by
  intro i a
  change (MvPowerSeries.pderiv (R := K) i).restrictScalars ℚ
    (algebraMap K (MvPowerSeries (Fin n) K) a) = 0
  rw [Derivation.restrictScalars_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, MvPowerSeries.pderiv_C]

/-- The coordinate structure on `K⟦X⟧` spans the `K`-derivations — a `K`-derivation agrees with
`∑ᵢ δ(Xᵢ) ∂ᵢ` on polynomials, both sides lower the `𝔪`-adic order by at most one, and Krull's
intersection theorem (`Hironaka/Algebra/Local/Taylor.lean`) finishes: the uniqueness of Taylor
coefficients. -/
theorem mvPowerSeries_spansDerivations :
    (RegularCoords.stdMvPowerSeries K n).SpansDerivations K := by
  intro δ f
  change δ f = ∑ i, δ (X i) * MvPowerSeries.pderiv (R := K) i f
  have hmem : ∀ N : ℕ, δ f - ∑ i, δ (X i) * MvPowerSeries.pderiv (R := K) i f ∈
      maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
    intro N
    have hr := sub_truncTotal_mem f N
    have hP := derivation_coe_eq_sum δ (truncTotal (N + 1) f)
    have h1 : δ f - δ (truncTotal (N + 1) f : MvPolynomial (Fin n) K) ∈
        maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
      rw [← map_sub]
      exact derivation_mem_maximalIdeal_pow δ N hr
    have h2 : ∑ i, δ (X i) * MvPowerSeries.pderiv (R := K) i f -
        ∑ i, δ (X i) *
          MvPowerSeries.pderiv (R := K) i (truncTotal (N + 1) f : MvPolynomial (Fin n) K) ∈
        maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [← mul_sub, ← map_sub]
      exact Ideal.mul_mem_left _ _
        (derivation_mem_maximalIdeal_pow (MvPowerSeries.pderiv (R := K) i) N hr)
    have := Ideal.sub_mem _ h1 h2
    rwa [hP, sub_sub_sub_cancel_right] at this
  have := mem_of_forall_mem_sup_pow (I := (⊥ : Ideal (MvPowerSeries (Fin n) K)))
    fun s => Ideal.mem_sup_right (hmem s)
  rw [Ideal.mem_bot, sub_eq_zero] at this
  exact this

end PowerSeries

end IsLocalRing
