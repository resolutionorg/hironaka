/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Oka.DegLt
public import Hironaka.AnalyticSpace.Coherent
public import Hironaka.Analytic.ConvSeries.ConvNorm
import Hironaka.Analytic.ConvSeries.Units
import Hironaka.Analytic.Rueckert.Quotient
import Hironaka.Analytic.Weierstrass.Division
import Hironaka.Analytic.Weierstrass.Preparation
import Hironaka.Analytic.Weierstrass.Tail
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Oka's lemma on relations with polynomial coefficients

Oka's lemma [Fre17, Ch. I, 10.4] is the algebraic heart of the coherence of the structure sheaf:
for an `𝒪_n`-linear map `F : 𝒪_n^p → 𝒪_n` whose matrix entries are normalized polynomials in
`𝒪_{n−1}[z_n]` of degree `< d`, the kernel of `F` is generated, as an `𝒪_n`-module, by the
relations whose components are polynomials in `z_n` of degree `< 3d`.

Here `𝒪_n` is the ring `Conv K (m + 1)` of convergent power series in `m + 1` variables over
`K ∈ {ℝ, ℂ}`, the distinguished variable is `x_0` (`splitFirst`, `liftTail`, `weierstrassPoly`),
and `𝒪_{n−1}[x_0 : N]` is the set of series of `x_0`-degree `< N` (`DegLt N`, `DegLt.lean`). The
statement `rowKer_le_span_degLt` says: every relation `P` (`∑_j F_j P_j = 0`) with `F_0` a monic
polynomial in `x_0` of degree `< d` and the other `F_j` of `x_0`-degree `< d` lies in the
`𝒪_n`-span of the relations whose components have `x_0`-degree `< 3d`. The proof follows the two
steps of Freitag's:

* Case A (`rowKer_le_span_degLt_of_weierstrass`), `F_0 = Q` a Weierstrass polynomial of degree
  `d' < d`: divide the other components of a relation by `Q` (Weierstrass division,
  `Hironaka/Analytic/Weierstrass/Division.lean`), subtract the trivial relations
  `H^{(j)} = (−F_j, 0, …, Q, …, 0)`, and read the first component off the polynomial division of
  `∑_j F_j r_j` by the monic `Q` through the uniqueness of Weierstrass division (this gives the
  bound `d`, sharper than the `2d` of the printed proof).
* Case B (`rowKer_le_span_degLt`), `F_0` monic: the preparation `F_0 = u · Q`
  (`Hironaka/Analytic/Weierstrass/Preparation.lean`), where the unit `u` is itself a
  polynomial of degree `≤ e − d'` (`degLt_unit_of_monic`: polynomial division of `F_0` by `Q` and
  uniqueness of Weierstrass division); the relations of `(Q, F_1, …)` are carried to those of
  `(F_0, F_1, …)` by `(b_0, b_1, …) ↦ (b_0, u b_1, …, u b_p)`, which raises the degree bound by
  less than `d`.

The real and complex cases have the same proof. The lemma feeds the coherence of the ideal of
relations (`Hironaka/AnalyticSpace/Oka`).
-/

@[expose] public section

open MvPowerSeries Manifold

noncomputable section

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

local notation "𝒪" => Conv K (m + 1)

/-- The relations of a row `G` over `𝒪_n`: `{P ∣ ∑_j G j * P j = 0}` (the relation module of a
system at one point, `relationSubmodule` of `Hironaka/AnalyticSpace/Coherent.lean`, is this with the
germs of the entries). -/
abbrev rowKer {p : ℕ} (G : Fin p → 𝒪) : Submodule 𝒪 (Fin p → 𝒪) :=
  relKer fun _ : Fin 1 => G

theorem mem_rowKer_iff {p : ℕ} (G : Fin p → 𝒪) (P : Fin p → 𝒪) :
    P ∈ rowKer G ↔ ∑ j, G j * P j = 0 := by
  rw [rowKer, mem_relKer_iff]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- The relations of `G` whose components have `x_0`-degree `< N`: the submodule `K_N` of
[Fre17, Ch. I, 10.4]. -/
def degLtRel {p : ℕ} (N : ℕ) (G : Fin p → 𝒪) : Set (Fin p → 𝒪) :=
  {b | (∀ j, DegLt N (b j : MvPowerSeries (Fin (m + 1)) K)) ∧ b ∈ rowKer G}

theorem degLtRel_mono {p : ℕ} {N N' : ℕ} (h : N ≤ N') (G : Fin p → 𝒪) :
    degLtRel N G ⊆ degLtRel N' G :=
  fun _ hb => ⟨fun j => (hb.1 j).mono h, hb.2⟩

section CaseA

variable {p d d' : ℕ}

/-- The trivial relation `H^{(j)} = (−F_j, 0, …, 0, Q, 0, …, 0)` (`Q` in slot `j + 1`). -/
def trivialRel (Q : 𝒪) (F : Fin p → 𝒪) (j : Fin p) : Fin (p + 1) → 𝒪 :=
  Fin.cons (-F j) (Pi.single j Q)

/-- `c • H`, written componentwise (definitionally `c • H`; avoids the `Pi.smul` simp set on the
subtype
ring). -/
def scaled (c : 𝒪) (H : Fin (p + 1) → 𝒪) : Fin (p + 1) → 𝒪 := fun i => c * H i

theorem scaled_eq_smul (c : 𝒪) (H : Fin (p + 1) → 𝒪) : scaled c H = c • H := rfl

theorem trivialRel_mem_rowKer (Q : 𝒪) (F : Fin p → 𝒪) (j : Fin p) :
    trivialRel Q F j ∈ rowKer (Fin.cons Q F) := by
  rw [mem_rowKer_iff, Fin.sum_univ_succ]
  simp only [trivialRel, Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp only [Pi.single_eq_same]
  ring

/-- Case A of Oka's lemma (the first step of the proof of [Fre17, Ch. I, 10.4]): for `Q` a
Weierstrass polynomial of degree `d' < d` and `F_1, …, F_p` of `x_0`-degree `< d`, every relation
of `(Q, F_1, …, F_p)` is an `𝒪_n`-combination of relations whose components have `x_0`-degree
`< d`. -/
theorem rowKer_le_span_degLt_of_weierstrass (hd' : d' < d) {c : Fin d' → MvPowerSeries (Fin m) K}
    (hc0 : ∀ k, constantCoeff (c k) = 0) (Q : 𝒪)
    (hQ : (Q : MvPowerSeries (Fin (m + 1)) K) = weierstrassPoly d' c)
    (F : Fin p → 𝒪) (hF : ∀ j, DegLt d (F j : MvPowerSeries (Fin (m + 1)) K)) :
    rowKer (Fin.cons Q F) ≤ Submodule.span 𝒪 (degLtRel d (Fin.cons Q F)) := by
  have hreg : IsRegularIn (Q : MvPowerSeries (Fin (m + 1)) K) d' := by
    rw [hQ]; exact isRegularIn_weierstrassPoly hc0
  have hQdeg : DegLt d (Q : MvPowerSeries (Fin (m + 1)) K) := by
    rw [hQ]; exact (degLt_weierstrassPoly d' c).mono hd'
  intro P hP
  rw [mem_rowKer_iff, Fin.sum_univ_succ] at hP
  simp only [Fin.cons_zero, Fin.cons_succ] at hP
  -- divide the components `P (j.succ)` by `Q`
  choose! q r hq hr hrdeg heq _ using fun j : Fin p =>
    exists_unique_weierstrassDivision (P j.succ).2 Q.2 hreg
  obtain ⟨qs, hqs⟩ : ∃ qs : Fin p → 𝒪, ∀ j, (qs j : MvPowerSeries (Fin (m + 1)) K) = q j :=
    ⟨fun j => ⟨q j, hq j⟩, fun j => rfl⟩
  obtain ⟨rs, hrs⟩ : ∃ rs : Fin p → 𝒪, ∀ j, (rs j : MvPowerSeries (Fin (m + 1)) K) = r j :=
    ⟨fun j => ⟨r j, hr j⟩, fun j => rfl⟩
  have hrdeg' : ∀ j, DegLt d' (rs j : MvPowerSeries (Fin (m + 1)) K) := fun j => by
    rw [hrs]; exact hrdeg j
  have heq' : ∀ j, P j.succ = qs j * Q + rs j := fun j => Subtype.ext (by
    rw [Subalgebra.coe_add, Subalgebra.coe_mul, hqs, hrs]; exact heq j)
  -- the corrected relation `P' = P − Σ q_j H^{(j)}`
  obtain ⟨P', hP'def⟩ : ∃ P' : Fin (p + 1) → 𝒪,
      P' = P - ∑ j, scaled (qs j) (trivialRel Q F j) := ⟨_, rfl⟩
  have hP'0 : P' 0 = P 0 + ∑ j, qs j * F j := by
    rw [hP'def, Pi.sub_apply, Finset.sum_apply]
    have hneg : ∀ x, scaled (qs x) (trivialRel Q F x) 0 = -(qs x * F x) := fun x => by
      simp only [scaled, trivialRel, Fin.cons_zero]
      exact mul_neg (qs x) (F x)
    simp only [hneg, Finset.sum_neg_distrib, sub_neg_eq_add]
  have hP'succ : ∀ j, P' j.succ = rs j := by
    intro j
    rw [hP'def, Pi.sub_apply, Finset.sum_apply]
    have hcomp : ∀ i, scaled (qs i) (trivialRel Q F i) j.succ = if i = j then qs j * Q else 0 := by
      intro i
      simp only [scaled, trivialRel, Fin.cons_succ]
      by_cases hij : i = j
      · subst hij; simp only [Pi.single_eq_same, ite_true]
      · simp only [Pi.single_eq_of_ne (Ne.symm hij), mul_zero, ite_eq_right hij]
    simp only [hcomp, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [heq' j]; ring
  have hP'mem : P' ∈ rowKer (Fin.cons Q F) := by
    have hPmem : P ∈ rowKer (Fin.cons Q F) := by
      rw [mem_rowKer_iff, Fin.sum_univ_succ]; simpa using hP
    rw [hP'def]
    refine Submodule.sub_mem _ hPmem (Submodule.sum_mem _ fun j _ => ?_)
    rw [scaled_eq_smul]
    exact Submodule.smul_mem _ _ (trivialRel_mem_rowKer Q F j)
  -- `Q * P' 0 = −T` with `T = Σ_j F_j r_j` of `x_0`-degree `< d + d'`
  obtain ⟨T, hTdef⟩ : ∃ T : 𝒪, T = ∑ j, F j * rs j := ⟨_, rfl⟩
  have hTdeg : DegLt (d + d') (T : MvPowerSeries (Fin (m + 1)) K) := by
    rw [hTdef, AddSubmonoidClass.coe_finsetSum]
    exact DegLt.sum _ fun j _ => by
      rw [Subalgebra.coe_mul]; exact (hF j).mul (hrdeg' j)
  have hQP' : Q * P' 0 = -T := by
    have := (mem_rowKer_iff _ _).1 hP'mem
    rw [Fin.sum_univ_succ] at this
    simp only [Fin.cons_zero, Fin.cons_succ, hP'succ] at this
    rw [hTdef]; exact eq_neg_of_add_eq_zero_left this
  have hQP'c : (Q : MvPowerSeries (Fin (m + 1)) K) * (P' 0 : MvPowerSeries (Fin (m + 1)) K) =
      -(T : MvPowerSeries (Fin (m + 1)) K) := by
    have := congrArg Subtype.val hQP'
    rwa [Subalgebra.coe_mul, Subalgebra.coe_neg] at this
  -- polynomial division of `T` by the monic `Q`, read back through the uniqueness of Weierstrass
  -- division
  have hP'0deg : DegLt d (P' 0 : MvPowerSeries (Fin (m + 1)) K) := by
    obtain ⟨Tp, hTp⟩ : ∃ Tp, Tp = toPoly (d + d') (T : MvPowerSeries (Fin (m + 1)) K) := ⟨_, rfl⟩
    obtain ⟨Qp, hQp⟩ : ∃ Qp, Qp = weierstrassPolynomial d' c := ⟨_, rfl⟩
    have hQpm : Qp.Monic := by rw [hQp]; exact monic_weierstrassPolynomial d' c
    have hQpdeg : Qp.natDegree = d' := by rw [hQp]; exact natDegree_weierstrassPolynomial d' c
    have hQpoly : ofPoly Qp = (Q : MvPowerSeries (Fin (m + 1)) K) := by
      rw [hQp, ofPoly_weierstrassPolynomial, hQ]
    have hTpdeg : Tp.natDegree < d + d' := by rw [hTp]; exact natDegree_toPoly_lt _ _ (by omega)
    have hdiv := Polynomial.modByMonic_add_div Tp Qp
    have hqdeg : (Tp /ₘ Qp).natDegree < d := by
      rw [Polynomial.natDegree_divByMonic _ hQpm, hQpdeg]
      omega
    have hrdegp : DegLt d' (ofPoly (Tp %ₘ Qp) : MvPowerSeries (Fin (m + 1)) K) := by
      rcases eq_or_ne (Tp %ₘ Qp) 0 with h0 | h0
      · rw [h0, ofPoly_zero]; exact DegLt.zero _
      · apply degLt_ofPoly_of_natDegree_lt
        have := Polynomial.degree_modByMonic_lt Tp hQpm
        rw [Polynomial.degree_eq_natDegree hQpm.ne_zero, hQpdeg] at this
        exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 this
    have hT : (T : MvPowerSeries (Fin (m + 1)) K) =
        ofPoly (Tp %ₘ Qp) + (Q : MvPowerSeries (Fin (m + 1)) K) * ofPoly (Tp /ₘ Qp) := by
      have h1 : (T : MvPowerSeries (Fin (m + 1)) K) = ofPoly Tp := by
        rw [hTp, ofPoly_toPoly hTdeg]
      rw [h1]
      conv_lhs => rw [← hdiv]
      rw [ofPoly_add, ofPoly_mul, hQpoly]
    -- two Weierstrass divisions of `−T` by `Q`
    obtain ⟨q0, r0, -, -, -, -, huniq⟩ :=
      exists_unique_weierstrassDivision (neg_mem T.2) Q.2 hreg
    have h1 := huniq (P' 0 : MvPowerSeries (Fin (m + 1)) K) 0 (fun _ _ => by simp)
      (by rw [add_zero, mul_comm]; exact hQP'c.symm)
    have hT' : -(T : MvPowerSeries (Fin (m + 1)) K) =
        (-(ofPoly (Tp /ₘ Qp))) * (Q : MvPowerSeries (Fin (m + 1)) K) + (-(ofPoly (Tp %ₘ Qp))) := by
      rw [hT]; ring
    have h2 := huniq (-(ofPoly (Tp /ₘ Qp))) (-(ofPoly (Tp %ₘ Qp))) hrdegp.neg hT'
    have : (P' 0 : MvPowerSeries (Fin (m + 1)) K) = -(ofPoly (Tp /ₘ Qp)) := h1.1.trans h2.1.symm
    rw [this]
    exact (degLt_ofPoly_of_natDegree_lt hqdeg).neg
  -- assemble
  have hP'set : P' ∈ degLtRel d (Fin.cons Q F) := by
    refine ⟨fun j => ?_, hP'mem⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hP'0deg
    · rw [hP'succ]; exact (hrdeg' i).mono hd'.le
  have hHset : ∀ j, trivialRel Q F j ∈ degLtRel d (Fin.cons Q F) := by
    intro j
    refine ⟨fun i => ?_, trivialRel_mem_rowKer Q F j⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [trivialRel, Fin.cons_zero]
      rw [Subalgebra.coe_neg]; exact (hF j).neg
    · simp only [trivialRel, Fin.cons_succ]
      by_cases hij : i = j
      · subst hij; simp only [Pi.single_eq_same]; exact hQdeg
      · simp only [Pi.single_eq_of_ne hij]; exact DegLt.zero _
  have : P = P' + ∑ j, scaled (qs j) (trivialRel Q F j) := by rw [hP'def]; abel
  rw [this]
  refine Submodule.add_mem _ (Submodule.subset_span hP'set) (Submodule.sum_mem _ fun j _ => ?_)
  rw [scaled_eq_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hHset j))

end CaseA

section CaseB

variable {p d e : ℕ}

/-- A monic polynomial in `x_0` with convergent tail coefficients is convergent. -/
theorem weierstrassPoly_mem_conv {n : ℕ} {c : Fin n → MvPowerSeries (Fin m) K}
    (hc : ∀ j, c j ∈ Conv K m) :
    (weierstrassPoly n c : MvPowerSeries (Fin (m + 1)) K) ∈ Conv K (m + 1) := by
  unfold weierstrassPoly
  refine Subalgebra.add_mem _ (Subalgebra.pow_mem _ (X_mem_conv 0) _)
    (Subalgebra.sum_mem _ fun j _ => ?_)
  exact Subalgebra.mul_mem _ (liftTail_mem_conv (hc j)) (Subalgebra.pow_mem _ (X_mem_conv 0) _)

/-- The second step of the proof of [Fre17, Ch. I, 10.4]: for `F₀ = ofPoly Q` with `Q` monic in
`x_0` of degree `e`, regular of order `d'`, the unit `u` of its Weierstrass preparation
`F₀ = u · Q'` is itself a polynomial in `x_0` of degree `≤ e − d'`, by the polynomial division of
`Q` by the monic Weierstrass polynomial `Q'` and the uniqueness of the Weierstrass division. -/
theorem degLt_unit_of_monic {Q : Polynomial (MvPowerSeries (Fin m) K)}
    (hF : ofPoly Q ∈ Conv K (m + 1))
    {d' : ℕ} {u : MvPowerSeries (Fin (m + 1)) K} {c' : Fin d' → MvPowerSeries (Fin m) K}
    (hc' : ∀ j, c' j ∈ Conv K m) (hc'0 : ∀ j, constantCoeff (c' j) = 0)
    (hprep : ofPoly Q = u * weierstrassPoly d' c') :
    DegLt (Q.natDegree - d' + 1) u := by
  obtain ⟨Qp, hQp⟩ : ∃ Qp, Qp = weierstrassPolynomial d' c' := ⟨_, rfl⟩
  have hQpm : Qp.Monic := by rw [hQp]; exact monic_weierstrassPolynomial d' c'
  have hQpdeg : Qp.natDegree = d' := by rw [hQp]; exact natDegree_weierstrassPolynomial d' c'
  have hdiv := Polynomial.modByMonic_add_div Q Qp
  have hqdeg : (Q /ₘ Qp).natDegree < Q.natDegree - d' + 1 := by
    rw [Polynomial.natDegree_divByMonic _ hQpm, hQpdeg]; omega
  have hrdeg : DegLt d' (ofPoly (Q %ₘ Qp) : MvPowerSeries (Fin (m + 1)) K) := by
    rcases eq_or_ne (Q %ₘ Qp) 0 with h0 | h0
    · rw [h0, ofPoly_zero]; exact DegLt.zero _
    · apply degLt_ofPoly_of_natDegree_lt
      have := Polynomial.degree_modByMonic_lt Q hQpm
      rw [Polynomial.degree_eq_natDegree hQpm.ne_zero, hQpdeg] at this
      exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 this
  have hQreg : IsRegularIn (weierstrassPoly d' c' : MvPowerSeries (Fin (m + 1)) K) d' :=
    isRegularIn_weierstrassPoly hc'0
  have hF' : ofPoly Q = ofPoly (Q /ₘ Qp) * weierstrassPoly d' c' + ofPoly (Q %ₘ Qp) := by
    conv_lhs => rw [← hdiv]
    rw [ofPoly_add, ofPoly_mul, hQp, ofPoly_weierstrassPolynomial]; ring
  obtain ⟨q0, r0, -, -, -, -, huniq⟩ :=
    exists_unique_weierstrassDivision hF (weierstrassPoly_mem_conv hc') hQreg
  have h1 := huniq u 0 (fun _ _ => by simp) (by rw [add_zero]; exact hprep)
  have h2 := huniq (ofPoly (Q /ₘ Qp)) (ofPoly (Q %ₘ Qp)) hrdeg hF'
  have : u = ofPoly (Q /ₘ Qp) := h1.1.trans h2.1.symm
  rw [this]
  exact degLt_ofPoly_of_natDegree_lt hqdeg

/-- **Oka's lemma** [Fre17, Ch. I, 10.4]: for `F₀` a monic polynomial in `x_0` of degree `e < d`
and `F_1, …, F_p` of `x_0`-degree `< d`, every relation of `(F₀, F_1, …, F_p)` is an
`𝒪_n`-combination of relations whose components have `x_0`-degree `< 3d` (the proof gives `< 2d`).
The hypothesis is weaker than the printed one, where `F₀` is a Weierstrass polynomial (monic with
coefficients in the maximal ideal): only monicity of `F₀` is used. -/
theorem rowKer_le_span_degLt (he : e < d) {Q : Polynomial (MvPowerSeries (Fin m) K)} (hQ : Q.Monic)
    (hQe : Q.natDegree = e) (F0 : 𝒪) (hF0 : (F0 : MvPowerSeries (Fin (m + 1)) K) = ofPoly Q)
    (F : Fin p → 𝒪) (hF : ∀ j, DegLt d (F j : MvPowerSeries (Fin (m + 1)) K)) :
    rowKer (Fin.cons F0 F) ≤ Submodule.span 𝒪 (degLtRel (3 * d) (Fin.cons F0 F)) := by
  obtain ⟨d', hd'e, hreg⟩ := exists_isRegularIn_ofPoly hQ
  rw [hQe] at hd'e
  have hregF : IsRegularIn (F0 : MvPowerSeries (Fin (m + 1)) K) d' := by rw [hF0]; exact hreg
  obtain ⟨u, c', hu, hu0, hc', hprep, -⟩ := exists_unique_weierstrassPreparation F0.2 hregF
  have hprep' : ofPoly Q = u * weierstrassPoly d' c' := by rw [← hF0]; exact hprep
  have hFconv : ofPoly Q ∈ Conv K (m + 1) := hF0 ▸ F0.2
  have hudeg : DegLt d u :=
    (degLt_unit_of_monic hFconv (fun j => (hc' j).1) (fun j => (hc' j).2) hprep').mono
      (by omega)
  obtain ⟨Q, hQ⟩ : ∃ Q : 𝒪, (Q : MvPowerSeries (Fin (m + 1)) K) = weierstrassPoly d' c' :=
    ⟨⟨_, weierstrassPoly_mem_conv fun j => (hc' j).1⟩, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : 𝒪, (U : MvPowerSeries (Fin (m + 1)) K) = u := ⟨⟨u, hu⟩, rfl⟩
  have hUdeg : DegLt d (U : MvPowerSeries (Fin (m + 1)) K) := by rw [hU]; exact hudeg
  have hF0eq : F0 = U * Q := Subtype.ext (by rw [Subalgebra.coe_mul, hU, hQ, hF0]; exact hprep')
  have hUunit : IsUnit U := by
    have h := (isUnit_iff_constantCoeff_ne_zero hu).2 hu0
    have hUeq : U = ⟨u, hu⟩ := Subtype.ext hU
    rw [hUeq]; exact h
  -- Case A for the `Q`-system
  have hA :=
    rowKer_le_span_degLt_of_weierstrass (show d' < d by omega) (fun j => (hc' j).2) Q hQ F hF
  intro P hP
  have hP' := (mem_rowKer_iff _ _).1 hP
  rw [Fin.sum_univ_succ] at hP'
  simp only [Fin.cons_zero, Fin.cons_succ, hF0eq] at hP'
  -- `P̃ = (U P₀, P₁, …)` is a relation of the `Q`-system
  have hPt : Fin.cons (U * P 0) (fun j => P j.succ) ∈ rowKer (Fin.cons Q F) := by
    rw [mem_rowKer_iff, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hP']; ring
  have hspan := hA hPt
  -- the `𝒪_n`-linear map `Φ b = (b₀, U b₁, …, U b_p)`
  obtain ⟨Φ, hΦ0, hΦs⟩ : ∃ Φ : (Fin (p + 1) → 𝒪) →ₗ[𝒪] (Fin (p + 1) → 𝒪),
      (∀ b, Φ b 0 = b 0) ∧ ∀ b (j : Fin p), Φ b j.succ = U * b j.succ :=
    ⟨{ toFun := fun b => Fin.cons (b 0) fun j => U * b j.succ
       map_add' := fun a b => by
         funext i
         refine Fin.cases ?_ (fun i => ?_) i
         · simp only [Fin.cons_zero, Pi.add_apply]
         · simp only [Fin.cons_succ, Pi.add_apply, mul_add]
       map_smul' := fun r b => by
         funext i
         refine Fin.cases ?_ (fun i => ?_) i
         · simp only [Fin.cons_zero, Pi.smul_apply, RingHom.id_apply]
         · simp only [Fin.cons_succ, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_left_comm] },
      fun b => rfl, fun b j => rfl⟩
  have hΦP : Φ (Fin.cons (U * P 0) fun j => P j.succ) = U • P := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hΦ0]; simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul]
    · rw [hΦs]; simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
  have hΦS : Φ '' degLtRel d (Fin.cons Q F) ⊆ degLtRel (3 * d) (Fin.cons F0 F) := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [hΦ0]; exact (hb.1 0).mono (by omega)
      · rw [hΦs, Subalgebra.coe_mul]
        exact (hUdeg.mul (hb.1 i.succ)).mono (by omega)
    · rw [mem_rowKer_iff, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hΦ0, hΦs, hF0eq]
      have hb2 := (mem_rowKer_iff _ _).1 hb.2
      rw [Fin.sum_univ_succ] at hb2
      simp only [Fin.cons_zero, Fin.cons_succ] at hb2
      calc U * Q * b 0 + ∑ j, F j * (U * b j.succ) = U * (Q * b 0 + ∑ j, F j * b j.succ) := by
            rw [mul_add, Finset.mul_sum]
            congr 1
            · ring
            · exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hb2, mul_zero]
  have hUP : U • P ∈ Submodule.span 𝒪 (degLtRel (3 * d) (Fin.cons F0 F)) := by
    rw [← hΦP]
    have hmem : Φ (Fin.cons (U * P 0) fun j => P j.succ) ∈
        Submodule.map Φ (Submodule.span 𝒪 (degLtRel d (Fin.cons Q F))) :=
      Submodule.mem_map_of_mem hspan
    rw [Submodule.map_span] at hmem
    exact Submodule.span_mono hΦS hmem
  obtain ⟨V, hV⟩ := hUunit.exists_left_inv
  have : P = V • (U • P) := by rw [smul_smul, hV, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ hUP

end CaseB

end Analytic
