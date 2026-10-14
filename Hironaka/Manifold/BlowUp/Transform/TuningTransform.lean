/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Basic
public import Hironaka.Manifold.IdealSheaf.Tuning
import Hironaka.Algebra.Local.CohenIso
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.MarkedAlgebra
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.IdealSheaf.TuningLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The tuning ideal under one blowing-up: orders along the centre and the transform

The order bookkeeping of the tuning theorem [Kol07, Theorem 100] on analytic manifolds, for one
blowing-up `π : M' → M` with centre the closed submanifold `Y`:

* at the stalk, `ord_x (J^s) = s · ord_x J` for `s ≥ 1` (`IdealSheaf.ord_pow`): the stalk
  `𝒪_{M,x}` is a regular local ring containing `ℚ`, so the order is multiplicative on its elements
  (`ordElem_mul_of_algebraRat`, `ord_pow_of_ordElem_mul`); the finite-dimensional model space is
  the setting;
* the converse direction of the theorem ("if `ord_Z J_{r−1} ≥ ms` then `ord_Z I_{r−1} ≥ m`"): for
  `s ≥ 1` and `I^s ⊆ J`, `ord_Y J ≥ ms` at a point of `Y` gives `ord_Y I ≥ m` there
  (`le_ordAlong_of_pow_le`). The order along `Y` is locally constant on `Y` and bounded by the
  pointwise order, so `ms ≤ ord_y J ≤ ord_y (I^s) = s · ord_y I` at the points `y` of `Y` near
  `a`, whence `m ≤ ord_y I` there, and the pointwise bound on `Y` near `a` gives the stalk
  containment `I_a ⊆ I_{Y,a}^m` (`stalkIdeal_le_pow_of_eventually_le_ord`);
* the direct direction (from `ord_Z I_{r−1} ≥ m` Kollár derives `ord_Z D^j(I_{r−1}) ≥ m − j` and
hence `ord_Z ∏_j D^j(I_{r−1}, m)^{c_j} ≥ ∑ (m − j) c_j ≥ ms`): `ord_Y I ≥ m` at a point of `Y` gives
  `ord_Y W_s(I) ≥ s` there (`le_ordAlong_tuning`): each generating product of `stalkIdeal_tuning`
  has order `≥ wt(e) ≥ s` along `Y` (`le_ordAlongIdeal_iteratedDeriv` for the factors, the product
  and power rules of `Hironaka.Manifold.BlowUp.Transform.MarkedAlgebra`), and the sum keeps it;
* the displayed chain of the proof for one blowing-up, read as the inclusion
  `π_*^{-1}(W_s(I), s) ⊆ W_s(π_*^{-1}(I, m))` (`birationalTransform_tuning_le`): with
  `W_s(I) = ∑_e P_e`, `P_e = ∏_j (D^j I)^{e_j}` over the finite exponent set of
  `tuning_eq_finset_sum`, each `P_e` has `m − j ≤ ord_Y D^j I` on its factors, so
  `π_*^{-1}(P_e, s) ⊆ π_*^{-1}(P_e, wt e) = ∏_j π_*^{-1}(D^j I, m − j)^{e_j} ⊆
  ∏_j D^j(π_*^{-1}(I, m))^{e_j} ⊆ W_s(π_*^{-1}(I, m))` (the mark comparison, the product and power
  rules, the derivative rule `markedTransform_iteratedDeriv_le` of [Kol07, Theorem 76], and the
  definition of `W_s`), and the sum rule assembles the summands.

The counterparts for schemes are in `Hironaka.Resolution.Algebraic.Kol07.Tuning` and
`Hironaka.Resolution.Algebraic.Tuning.Transform`.
-/

public noncomputable section

open TopologicalSpace Opposite CategoryTheory IsLocalRing Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section OrderAlongCentre

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ}

/-- At every point
`x` of a manifold modelled on a finite-dimensional space, `ord_x (J^s) = s · ord_x J` for `s ≥ 1` —
the stalk `𝒪_{M,x}` is a regular local ring containing `ℚ`, so the order is
multiplicative on its elements (`ordElem_mul_of_algebraRat`). -/
theorem IdealSheaf.ord_pow [FiniteDimensional 𝕜 E] (J : IdealSheaf (structureSheaf 𝕜 E M)) {s : ℕ}
    (hs : 1 ≤ s) (x : M) : (J ^ s).ord x = (s : ℕ∞) * J.ord x := by
  have hφ : chartAt E x ∈ maximalAtlas 𝓘(𝕜, E) ω M := IsManifold.chart_mem_maximalAtlas x
  have := isRegularLocalRing_stalk_of_chart E (modelCoord (𝕜 := 𝕜) (E := E)) (chartAt E x)
    (mem_chart_source E x) hφ
  unfold IdealSheaf.ord
  rw [IdealSheaf.stalkIdeal_pow]
  exact ord_pow_of_ordElem_mul
    (ordElem_mul_of_algebraRat ((structureSheaf 𝕜 E M).presheaf.stalk x)) _ hs

/-- For `s ≥ 1` and `I^s ⊆ J`, `ord_Y J ≥ ms` at a point of `Y` gives `ord_Y I ≥ m` there. -/
theorem le_ordAlong_of_pow_le (hY : IsClosedSubmanifold ψ Y c)
    {I J : IdealSheaf (structureSheaf 𝕜 E M)} {m s : ℕ} (hs : 1 ≤ s) (hIJ : I ^ s ≤ J) {a : M}
    (ha : a ∈ Y) (hJ : ((m * s : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a) :
    (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a := by
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  rw [IdealSheaf.le_ordAlongIdeal_iff]
  refine stalkIdeal_le_pow_of_eventually_le_ord hY I ha ?_
  obtain ⟨W, hWo, haW, hW⟩ := exists_open_ordAlong_eq hY J ha
  filter_upwards [hWo.mem_nhds haW] with y hy
  have h1 : ((m * s : ℕ) : ℕ∞) ≤ (I ^ s).ord (y : M) := by
    calc ((m * s : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a := hJ
      _ = IdealSheaf.ordAlongIdeal hY.idealSheaf J (y : M) := (hW y hy).symm
      _ ≤ J.ord (y : M) := ordAlong_le_ord hY J y.2
      _ ≤ (I ^ s).ord (y : M) := IdealSheaf.ord_anti hIJ _
  rw [IdealSheaf.ord_pow I hs, Nat.cast_mul, mul_comm (m : ℕ∞) (s : ℕ∞)] at h1
  exact (ENat.mul_le_mul_left_iff (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hs))
    (ENat.natCast_ne_top s)).mp h1

variable [FiniteDimensional 𝕜 E]

/-- `ord_Y I ≥ m` at a point of `Y` gives `ord_Y W_s(I) ≥ s` there — each
generating product `∏_j (D^j I)^{e_j}` with `∑ (m − j) e_j ≥ s` has order `≥ s` along `Y`
(`le_ordAlongIdeal_iteratedDeriv` for the factors), and the sum keeps it. -/
theorem le_ordAlong_tuning (hY : IsClosedSubmanifold ψ Y c) (I : IdealSheaf (structureSheaf 𝕜 E M))
    (m s : ℕ) {a : M} (ha : a ∈ Y)
    (hm : (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) :
    (s : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf (I.tuning m s) a := by
  rw [IdealSheaf.le_ordAlongIdeal_iff, IdealSheaf.stalkIdeal_tuning]
  refine iSup₂_le fun e he => ?_
  have hj : ∀ j : Fin (m + 1), (I.iteratedDeriv (j : ℕ)).stalkIdeal a ^ e j ≤
      hY.idealSheaf.stalkIdeal a ^ ((m - (j : ℕ)) * e j) := fun j => by
    rw [pow_mul]
    refine Ideal.pow_right_mono ?_ _
    exact (IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp
      (le_ordAlongIdeal_iteratedDeriv hY I ha (Nat.lt_succ_iff.mp j.2) hm)
  calc ∏ j : Fin (m + 1), (I.iteratedDeriv (j : ℕ)).stalkIdeal a ^ e j
      ≤ ∏ j : Fin (m + 1), hY.idealSheaf.stalkIdeal a ^ ((m - (j : ℕ)) * e j) :=
        Finset.prod_le_prod fun j _ => hj j
    _ = hY.idealSheaf.stalkIdeal a ^ wt m e := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ hY.idealSheaf.stalkIdeal a ^ s := Ideal.pow_le_pow_right he

end OrderAlongCentre

/-! ### The transform of the tuning ideal under one blowing-up -/

section TuningOneBlowUp

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] {Y : Set M} {c : ℕ} {M' : Type u}
  [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M} (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)

/-- For a blowing-up `π` with
centre `Y` and `ord_Y I ≥ m` at every point of `Y`, `π_*^{-1}(W_s(I), s) ⊆ W_s(π_*^{-1}(I, m))`:
each generating product `P_e = ∏_j (D^j I)^{e_j}` with `∑ (m − j) e_j ≥ s` has `m − j ≤ ord_Y D^j I`
(`le_ordAlongIdeal_iteratedDeriv`), so `π_*^{-1}(P_e, s) ⊆ π_*^{-1}(P_e, ∑ (m − j) e_j) = ∏_j
π_*^{-1}(D^j I, m − j)^{e_j} ⊆ ∏_j D^j(π_*^{-1}(I, m))^{e_j} ⊆ W_s(π_*^{-1}(I, m))` (the mark
comparison, the product and power rules, `markedTransform_iteratedDeriv_le` of [Kol07, Theorem 76],
the definition of `W_s`), and the sum rule assembles the summands of `tuning_eq_finset_sum`. -/
theorem birationalTransform_tuning_le (I : IdealSheaf (structureSheaf 𝕜 E M)) (m s : ℕ)
    (hm : ∀ x ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I x) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨I.tuning m s, s⟩).I ≤
      (MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I.tuning m s := by
  have hdef : ∀ j : Fin (m + 1), ∀ x ∈ Y, ((m - (j : ℕ) : ℕ) : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal hY.idealSheaf (I.iteratedDeriv (j : ℕ)) x := fun j x hx =>
    le_ordAlongIdeal_iteratedDeriv hY I hx (Nat.lt_succ_iff.mp j.2) (hm x hx)
  have hpow : ∀ (e : Fin (m + 1) → ℕ) (j : Fin (m + 1)), ∀ x ∈ Y,
      (((m - (j : ℕ)) * e j : ℕ) : ℕ∞) ≤
        IdealSheaf.ordAlongIdeal hY.idealSheaf (I.iteratedDeriv (j : ℕ) ^ e j) x :=
    fun e j x hx => le_ordAlongIdeal_pow _ (hdef j x hx) (e j)
  have hP : ∀ e : Fin (m + 1) → ℕ, ∀ x ∈ Y, ((wt m e : ℕ) : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal hY.idealSheaf (∏ j : Fin (m + 1), I.iteratedDeriv (j : ℕ) ^ e j) x :=
    fun e x hx => le_ordAlongIdeal_finset_prod _ Finset.univ
      (fun j : Fin (m + 1) => I.iteratedDeriv (j : ℕ) ^ e j)
      (fun j : Fin (m + 1) => (m - (j : ℕ)) * e j) fun j _ => hpow e j x hx
  have hPs : ∀ e ∈ tuningExponents m s, ∀ x ∈ Y, (s : ℕ∞) ≤
      IdealSheaf.ordAlongIdeal hY.idealSheaf (∏ j : Fin (m + 1), I.iteratedDeriv (j : ℕ) ^ e j) x :=
    fun e he x hx => (Nat.cast_le.mpr (mem_tuningExponents.mp he).2.1).trans (hP e x hx)
  rw [IdealSheaf.tuning_eq_finset_sum, birationalTransform_finset_sum hY h _ _ s hPs,
    IdealSheaf.le_def]
  intro p
  rw [IdealSheaf.stalkIdeal_finset_sum, IdealSheaf.stalkIdeal_tuning]
  refine Finset.sum_induction _ (fun A : Ideal _ => A ≤ _)
    (fun A B hA hB => by rw [Submodule.add_eq_sup]; exact sup_le hA hB) bot_le fun e he => ?_
  have hse : s ≤ wt m e := (mem_tuningExponents.mp he).2.1
  refine le_iSup₂_of_le e hse ?_
  have hwt : wt m e = ∑ j : Fin (m + 1), (m - (j : ℕ)) * e j := rfl
  refine (birationalTransform_le_of_le_mark hY h _ hse (hP e) p).trans ?_
  rw [hwt, birationalTransform_finset_prod hY h Finset.univ _ _ fun j _ => hpow e j,
    IdealSheaf.stalkIdeal_finset_prod]
  refine Finset.prod_le_prod fun j _ => ?_
  rw [birationalTransform_pow hY h _ _ _ (hdef j), IdealSheaf.stalkIdeal_pow]
  exact Ideal.pow_right_mono
    (markedTransform_iteratedDeriv_le hY h I hm (Nat.lt_succ_iff.mp j.2) p) _

end TuningOneBlowUp

end Manifold
