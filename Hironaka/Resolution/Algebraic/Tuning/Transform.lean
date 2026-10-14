/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
import Hironaka.Resolution.Algebraic.Kol07.Tuning
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.Theorem88Basic
import Hironaka.Scheme.BlowUpSequence.TransformDerivative
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 100, the direction `⟹`: the transform of the tuning ideal under one blow-up

The proof of [Kol07, Theorem 100] shows, by induction along the sequence, that the marked transforms
`J_i` of `(J, ms)` stay inside the tuning ideals `W_{ms}(I_i)` of the marked transforms of `(I, m)`.
This module is the one-blow-up step of that induction, the displayed chain of Kollár's proof for a
single smooth blow-up `π : B_Z X → X` with `ord_Z I ≥ m`:

* **The product rule** (Kollár's product of marked ideals `(I₁, m₁) · (I₂, m₂) := (I₁ I₂, m₁ + m₂)`,
  [Kol07, Definition 59], under the birational transform of marked ideals, [Kol07, Definition 60]):
  when `F^a ∣ π^* K₁` and `F^b ∣ π^* K₂`,
  `π_*^{-1}(K₁ K₂, a + b) = π_*^{-1}(K₁, a) · π_*^{-1}(K₂, b)` —
  `π^*(K₁ K₂) = F^a π_*^{-1}(K₁, a) · F^b π_*^{-1}(K₂, b) = F^{a+b} · (product)`
  (`pow_mul_colon_of_dvd`), and the quotient by the invertible `F^{a+b}` is unique
  (`colon_pow_eq_of_mul_eq`) (`markedTransform_mul`); iterated over a finite product
  (`markedTransform_finset_prod`), with `markedTransform_pow` of
  `Hironaka.Resolution.Algebraic.Kol07.Tuning` for the powers.
* **The sum rule for an arbitrary family** (`markedTransform_iSup_le` of `Hironaka.Sequence` for an
  `ℕ`-indexed family, here for any index and as an equality): when every `π^* K_i` is divisible by
  `F^c`, `π_*^{-1}(⨆ K_i, c) = ⨆ π_*^{-1}(K_i, c)`, because `π^*(⨆ K_i) = ⨆ F^c T_i = F^c · ⨆ T_i`
  (`markedTransform_iSup_eq`).
* **The transform of the tuning ideal** (Kollár's chain read as the inclusion `⊆`):
  `π_*^{-1}(W_s(I), s) ⊆ W_s(π_*^{-1}(I, m))`. Every generating product `P_e = ∏_j (D^j I)^{e_j}` of
  weight `wt(e) ≥ s` has `F^{wt(e)} ∣ π^* P_e` ([Kol07, Corollary 77]: `F^{m-j} ∣ π^* D^j I` from
  `ord_Z D^j I ≥ m − j`), so `π_*^{-1}(P_e, s) ⊆ π_*^{-1}(P_e, wt(e))` (the colon by the smaller
  power `F^s` is the smaller ideal, `controlledTransformAlong_mono`)
  `= ∏_j π_*^{-1}(D^j I, m − j)^{e_j}` (the product rule) `⊆ ∏_j D^j(π_*^{-1}(I, m))^{e_j}`
  ([Kol07, Theorem 76] for one blow-up) `⊆ W_s(π_*^{-1}(I, m))`; the sum rule assembles the summands
  (`markedTransform_W_le`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme.BlowUpSequence IsLocalRing

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The pull-back of a finite product of ideal sheaves is the product of the pull-backs
(`comap_mul` iterated; the empty product is the unit ideal, `comap_top`). -/
theorem comap_finset_prod {ι : Type*} (s : Finset ι) (g : ι → X.IdealSheafData) (π : Y ⟶ X) :
    (∏ i ∈ s, g i).comap π = ∏ i ∈ s, (g i).comap π := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    exact comap_top π
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, comap_mul, ih]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The product rule for marked transforms -/

section ProductRule

variable (D : X.IdealSheafData)

/-- The product rule for marked transforms (Kollár's product of marked ideals,
[Kol07, Definition 59], under the birational transform of [Kol07, Definition 60]): for marked ideals
`(K₁, a)`, `(K₂, b)` whose transforms are defined, `F^a ∣ π^* K₁` and `F^b ∣ π^* K₂`, the marked
transform of `(K₁ K₂, a + b)` is the product of the marked transforms:
`π^*(K₁ K₂) = π^* K₁ · π^* K₂ = F^a π_*^{-1}(K₁, a) · F^b π_*^{-1}(K₂, b)`, and the quotient by the
invertible `F^{a+b}` is unique. -/
theorem markedTransform_mul (K₁ K₂ : X.IdealSheafData) (a b : ℕ)
    (h₁ : D.exceptionalDivisor ^ a ∣ K₁.comap D.blowUpπ)
    (h₂ : D.exceptionalDivisor ^ b ∣ K₂.comap D.blowUpπ) :
    (K₁ * K₂).markedTransform D (a + b) = K₁.markedTransform D a * K₂.markedTransform D b := by
  have hF : D.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π D
  change ((K₁ * K₂).comap D.blowUpπ).colon (D.exceptionalDivisor ^ (a + b)) =
    (K₁.comap D.blowUpπ).colon (D.exceptionalDivisor ^ a) *
      (K₂.comap D.blowUpπ).colon (D.exceptionalDivisor ^ b)
  refine colon_pow_eq_of_mul_eq (I := (K₁ * K₂).comap D.blowUpπ) hF (a + b) _ ?_
  rw [comap_mul, pow_add, mul_mul_mul_comm, pow_mul_colon_of_dvd _ _ a h₁,
    pow_mul_colon_of_dvd _ _ b h₂]

/-- The marked transform of the unit ideal with the mark `0` is the unit ideal (the empty
product of the product rule). -/
theorem markedTransform_one : Scheme.IdealSheafData.markedTransform 1 D 0 = 1 := by
  change ((⊤ : X.IdealSheafData).comap D.blowUpπ).colon
      (D.exceptionalDivisor ^ 0) = ⊤
  rw [pow_zero, comap_top]
  exact colon_top ⊤

/-- Definedness of the transform of a finite product: if `F^{c_i} ∣ π^* g_i` for every factor, then
`F^{∑ c_i} ∣ π^* ∏ g_i`. -/
theorem pow_sum_dvd_comap_finset_prod {ι : Type*} (s : Finset ι) (g : ι → X.IdealSheafData)
    (c : ι → ℕ) (h : ∀ i ∈ s, D.exceptionalDivisor ^ c i ∣ (g i).comap D.blowUpπ) :
    D.exceptionalDivisor ^ (∑ i ∈ s, c i) ∣ (∏ i ∈ s, g i).comap D.blowUpπ := by
  rw [comap_finset_prod, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_dvd_prod_of_dvd _ _ h

/-- The product rule iterated (Kollár's `∏_j (D^j I, m − j)^{c_j}` with the markings added): for
marked ideals `(g_i, c_i)` whose transforms are defined, the marked transform of `(∏ g_i, ∑ c_i)` is
the product of the marked transforms. -/
theorem markedTransform_finset_prod {ι : Type*} (s : Finset ι) (g : ι → X.IdealSheafData)
    (c : ι → ℕ) (h : ∀ i ∈ s, D.exceptionalDivisor ^ c i ∣ (g i).comap D.blowUpπ) :
    (∏ i ∈ s, g i).markedTransform D (∑ i ∈ s, c i) = ∏ i ∈ s, (g i).markedTransform D (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, Finset.prod_empty]
    exact markedTransform_one D
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
      markedTransform_mul D _ _ _ _ (h a (Finset.mem_insert_self a s))
        (pow_sum_dvd_comap_finset_prod D s g c fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-! ### The sum rule for an arbitrary family -/

/-- The sum rule for marked transforms (`markedTransform_iSup_le`, for a family indexed by any Sort
and as an equality): for marked ideals `(K_i, c)` of the same mark whose transforms are defined, the
marked transform of the sum is the sum of the marked transforms:
`π^*(⨆ K_i) = ⨆ π^* K_i = ⨆ F^c π_*^{-1}(K_i, c) = F^c · ⨆ π_*^{-1}(K_i, c)`, and the quotient by
the invertible `F^c` is unique. -/
theorem markedTransform_iSup_eq {ι : Sort*} (K : ι → X.IdealSheafData) (c : ℕ)
    (hK : ∀ i, D.exceptionalDivisor ^ c ∣ (K i).comap D.blowUpπ) :
    (⨆ i, K i).markedTransform D c = ⨆ i, (K i).markedTransform D c := by
  have hF : D.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π D
  change ((⨆ i, K i).comap D.blowUpπ).colon (D.exceptionalDivisor ^ c) =
    ⨆ i, ((K i).comap D.blowUpπ).colon (D.exceptionalDivisor ^ c)
  refine colon_pow_eq_of_mul_eq (I := (⨆ i, K i).comap D.blowUpπ) hF c _ ?_
  rw [comap_iSup, mul_iSup']
  exact iSup_congr fun i => pow_mul_colon_of_dvd _ _ c (hK i)

end ProductRule

/-! ### The transform of the tuning ideal under one blow-up -/

section OneBlowUp

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]
  (I : X.IdealSheafData) (m s : ℕ)

include n

/-- The one-blow-up step of the proof of [Kol07, Theorem 100] (the displayed chain, read as the
inclusion `⊆`): for a smooth blow-up with `ord_Z I ≥ m` along every component of the centre,
`π_*^{-1}(W_s(I), s) ⊆ W_s(π_*^{-1}(I, m))`. Each generating product `P_e = ∏_j (D^j I)^{e_j}` with
`wt(e) ≥ s` has `F^{wt(e)} ∣ π^* P_e` ([Kol07, Corollary 77]: `F^{m−j} ∣ π^* D^j I`), so
`π_*^{-1}(P_e, s) ⊆ π_*^{-1}(P_e, wt(e))` (mark comparison) `= ∏_j π_*^{-1}(D^j I, m − j)^{e_j}`
(the product rule) `⊆ ∏_j D^j(π_*^{-1}(I, m))^{e_j}` ([Kol07, Theorem 76] for one blow-up)
`⊆ W_s(π_*^{-1}(I, m))` (the definition of `W`); the sum rule assembles the summands. -/
theorem markedTransform_W_le (hm : I.LeOrdAlong Z.support (m : ℕ∞)) :
    (W f I m s).markedTransform Z s ≤ W (Z.blowUpπ ≫ f) (I.markedTransform Z m) m s := by
  have hdef : ∀ j : Fin (m + 1),
      Z.exceptionalDivisor ^ (m - (j : ℕ)) ∣ (I.derivativeIter f j).comap
          Z.blowUpπ :=
    fun j => pow_dvd_comap_of_leOrdAlong f n Z _
      (leOrdAlong_derivativeIter f n Z I hm (Nat.lt_succ_iff.mp j.2))
  have hpow : ∀ (e : Fin (m + 1) → ℕ) (j : Fin (m + 1)),
      Z.exceptionalDivisor ^ ((m - (j : ℕ)) * e j) ∣
        (I.derivativeIter f j ^ e j).comap Z.blowUpπ := fun e j => by
    rw [comap_pow, pow_mul]
    exact pow_dvd_pow_of_dvd (hdef j) _
  have hPdvd : ∀ e : Fin (m + 1) → ℕ, Z.exceptionalDivisor ^ wt m e ∣
      (∏ j : Fin (m + 1), I.derivativeIter f j ^ e j).comap Z.blowUpπ := fun e =>
    pow_sum_dvd_comap_finset_prod Z Finset.univ _ _ fun j _ => hpow e j
  have hPtr : ∀ e : Fin (m + 1) → ℕ,
      (∏ j : Fin (m + 1), I.derivativeIter f j ^ e j).markedTransform Z (wt m e) =
        ∏ j : Fin (m + 1), (I.derivativeIter f j).markedTransform Z (m - (j : ℕ)) ^ e j :=
      fun e => by
    unfold wt
    rw [markedTransform_finset_prod Z Finset.univ _ _ fun j _ => hpow e j]
    exact Finset.prod_congr rfl fun j _ => markedTransform_pow Z _ _ _ (hdef j)
  have h1 : W f I m s = ⨆ x : {e : Fin (m + 1) → ℕ // s ≤ wt m e},
      ∏ j : Fin (m + 1), I.derivativeIter f j ^ x.1 j := by
    rw [W_eq]
    exact iSup_subtype'
  have h2 : (W f I m s).markedTransform Z s =
      ⨆ x : {e : Fin (m + 1) → ℕ // s ≤ wt m e},
        (∏ j : Fin (m + 1), I.derivativeIter f j ^ x.1 j).markedTransform Z s :=
    (congrArg (fun K : X.IdealSheafData => K.markedTransform Z s) h1).trans
      (markedTransform_iSup_eq Z _ s fun x =>
        (pow_dvd_pow Z.exceptionalDivisor x.2).trans (hPdvd x.1))
  refine h2.le.trans (iSup_le fun x => ?_)
  calc (∏ j : Fin (m + 1), I.derivativeIter f j ^ x.1 j).markedTransform Z s
      ≤ (∏ j : Fin (m + 1), I.derivativeIter f j ^ x.1 j).markedTransform Z (wt m x.1) :=
        controlledTransformAlong_mono _ _ _ x.2
    _ = ∏ j : Fin (m + 1), (I.derivativeIter f j).markedTransform Z (m - (j : ℕ)) ^ x.1 j :=
        hPtr x.1
    _ ≤ ∏ j : Fin (m + 1),
          (I.markedTransform Z m).derivativeIter (Z.blowUpπ ≫ f) j ^ x.1 j :=
        Finset.prod_le_prod₀ (fun j _ => bot_le) fun j _ =>
          pow_le_pow_left₀ bot_le
            (markedTransform_derivativeIter_le f n Z I hm (Nat.lt_succ_iff.mp j.2)) _
    _ ≤ W (Z.blowUpπ ≫ f) (I.markedTransform Z m) m s := prod_le_W _ x.2

end OneBlowUp

end Hironaka.Sequence
