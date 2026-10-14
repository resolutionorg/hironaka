/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Chart
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Wlo05.ChainRelativeLift
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.ParameterAlgebra
import Hironaka.Scheme.Snc.ParameterSubset
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The new chain coordinates at a point of the blow-up

The second half of the local computation for the statement CP4 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) at a point `q` of the blow-up, on the
chart datum `ChartAt` of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Chart`:

* **the new parameters** (`newExp`, `exists_isUnit_mul_monomialOf_newExp`): an `ε`-power times a
  monomial in the ε-free induced coordinates is a unit times a monomial in the new regular system
  of parameters `z'`, the exponents transported along `τ` (the ratio coordinates of members whose
  strict transform misses `q` are units and drop);
* **the members' strict transforms** at `q` (`stalkIdeal_strictTransformAlong_eq_span_w`,
  `stalkIdeal_strictTransformAlong_eq_top_of_isUnit`, the dichotomy
  `mem_support_strictTransformAlong_iff`);
* **the assembly** (`chainCoords_totalTransform`): the new members' coordinates `newMemberIdx`, the
  new chain `newChain = τ ∘ σ`, snc data for the total transform (`isSncAt_totalTransform`), the
  support of the new exponents — chain coordinates at `q` for the total transform of the boundary
  and the strict transform of `Γ`;
* **the transforms in the new parameters** (`stalkIdeal_markedTransform_chainKIdeal`,
  `stalkIdeal_markedTransform_chainIdeal`): the K-shape and the un-isolated form at `q`;
* **off the exceptional divisor** (`chainRelativeKAt_totalTransform_of_notMem`,
  `chainRelativeAt_totalTransform_of_notMem`, `exists_isSncAt_totalTransform_of_notMem`): the
  forms transport along the stalk isomorphism `π^*`.

The chart is that of [Kol07, Definition 60]. The pointwise statements are assembled into CP4 in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4`;
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Sheaf` uses them for the un-isolated ideal.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Ideal Scheme.IdealSheafData
  Scheme IdealSheafData

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

namespace ChartAt

/-! ### From the induced coordinates to the new regular system of parameters -/

section NewCoords

variable {Z : X.IdealSheafData} {q : blowUp Z} {n : ℕ}
  {z : Fin n → X.presheaf.stalk (blowUpπ Z q)} {C : Finset (Fin n)} (D : ChartAt Z q z C)

/-- The pivot's entry among the parameters. -/
noncomputable def pivotIdx (hq : q ∈ (Z.comap (blowUpπ Z)).support) : Fin D.m :=
  D.τ ⟨D.c₀, D.w_c₀ ▸ D.ε_mem_maximalIdeal hq⟩

theorem z'_pivotIdx (hq : q ∈ (Z.comap (blowUpπ Z)).support) : D.z' (D.pivotIdx hq) = D.ε := by
  rw [pivotIdx, D.hτ, D.w_c₀]

/-- The exponent vector on the new parameters: the entry `t` at the pivot, the entries of `c` at the
vanishing induced coordinates, `0` elsewhere. -/
noncomputable def newExp (t : ℕ) (c : Fin n → ℕ) : Fin D.m → ℕ :=
  Function.extend D.τ (fun k => if k.1 = D.c₀ then t else c k.1) 0

open Classical in
/-- A monomial in the new parameters with exponents extended along `τ` is the product over the
vanishing induced coordinates. -/
theorem monomialOf_z'_extend
    (g : {i : Fin n // D.w i ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)} → ℕ) :
    monomialOf D.z' (Function.extend D.τ g 0) = ∏ k, D.w k.1 ^ g k := by
  classical
  unfold monomialOf
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image D.τ)) fun i _ hi => ?_]
  · rw [Finset.prod_image fun k _ k' _ h => D.τ_injective h]
    exact Finset.prod_congr rfl fun k _ => by rw [D.τ_injective.extend_apply, D.hτ]
  · have : Function.extend D.τ g 0 i = 0 := by
      rw [Function.extend_apply' _ _ _
        fun ⟨k, hk⟩ => hi (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)]
      rfl
    rw [this, pow_zero]

/-- **Units drop**: `ε^t · ŵ^c` is a unit times the monomial in the new parameters with the
exponents `newExp t c`. -/
theorem exists_isUnit_mul_monomialOf_newExp (hq : q ∈ (Z.comap (blowUpπ Z)).support) (t : ℕ)
    (c : Fin n → ℕ) :
    ∃ u : (blowUp Z).presheaf.stalk q, IsUnit u ∧
      D.ε ^ t * monomialOf D.wHat c = u * monomialOf D.z' (D.newExp t c) := by
  classical
  set 𝔪 := maximalIdeal ((blowUp Z).presheaf.stalk q) with h𝔪
  have hεm : D.w D.c₀ ∈ 𝔪 := D.w_c₀ ▸ D.ε_mem_maximalIdeal hq
  -- the monomial in the new parameters as a product over the vanishing coordinates
  have h1 : monomialOf D.z' (D.newExp t c) =
      ∏ k : Fin n, if D.w k ∈ 𝔪 then D.w k ^ (if k = D.c₀ then t else c k) else 1 := by
    rw [newExp, D.monomialOf_z'_extend, ← Finset.prod_filter,
      Finset.prod_subtype (p := fun k => D.w k ∈ 𝔪) (Finset.univ.filter fun k => D.w k ∈ 𝔪)
        (fun k => by simp)]
  -- the left side, term by term
  have h2 : D.ε ^ t * monomialOf D.wHat c = ∏ k : Fin n,
      (if D.w k ∈ 𝔪 then D.w k ^ (if k = D.c₀ then t else c k) else 1) *
        (if D.w k ∈ 𝔪 then 1 else D.w k ^ c k) := by
    unfold monomialOf
    have hε : D.ε ^ t = ∏ k : Fin n, if k = D.c₀ then D.ε ^ t else 1 := by
      rw [Finset.prod_ite_eq' Finset.univ D.c₀ fun _ => D.ε ^ t, ite_eq_left (Finset.mem_univ _)]
    rw [hε, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : k = D.c₀
    · subst hk
      rw [ite_eq_left rfl, ite_eq_left hεm, ite_eq_left hεm, ChartAt.wHat, Function.update_self,
        one_pow, mul_one, mul_one, ite_eq_left rfl, D.w_c₀]
    · rw [ite_eq_right hk, one_mul, D.wHat_of_ne hk, ite_eq_right hk]
      by_cases hkm : D.w k ∈ 𝔪
      · rw [ite_eq_left hkm, ite_eq_left hkm, mul_one]
      · rw [ite_eq_right hkm, ite_eq_right hkm, one_mul]
  refine ⟨∏ k : Fin n, if D.w k ∈ 𝔪 then 1 else D.w k ^ c k, ?_, ?_⟩
  · refine isUnit_prod_of_forall_isUnit _ fun k => ?_
    by_cases hkm : D.w k ∈ 𝔪
    · rw [ite_eq_left hkm]
      exact isUnit_one
    · rw [ite_eq_right hkm]
      exact (D.isUnit_w_of_notMem hkm).pow _
  · rw [h2, h1, Finset.prod_mul_distrib, mul_comm]

end NewCoords

/-! ### The strict transforms of the members in the chart -/

section Members

variable {Z : X.IdealSheafData} {q : blowUp Z} {n : ℕ}
  {z : Fin n → X.presheaf.stalk (blowUpπ Z q)} {C : Finset (Fin n)} (D : ChartAt Z q z C)

/-- **A member through `q`**: for a member `Y = (z_c = 0)` at `p` whose coordinate is not the pivot
and whose induced coordinate vanishes at `q`, the strict transform has stalk `(w_c)` at `q`. -/
theorem stalkIdeal_strictTransformAlong_eq_span_w
    [IsRegularLocalRing ((blowUp Z).presheaf.stalk q)]
        (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    {c : Fin n} (hc : c ≠ D.c₀)
    (hcm : D.w c ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)) (Y : X.IdealSheafData)
    (hY : Y.stalkIdeal (blowUpπ Z q) = span {z c}) :
    (Y.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).stalkIdeal q = span {D.w c} := by
  classical
  rw [D.stalkIdeal_strictTransformAlong_eq Y, hY, Ideal.map_span, Set.image_singleton,
    D.stalkMap_eq_pow c, D.wHat_of_ne hc, mul_comm]
  have hprime : Prime (D.w c) := by
    have := prime_of_parameters D.hz'.1.symm D.hz'.2 (D.τ ⟨c, hcm⟩)
    rwa [D.hτ] at this
  have hεP : D.ε ∉ span {D.w c} := by
    rw [← D.z'_pivotIdx hq, ← D.hτ ⟨c, hcm⟩, ← Set.image_singleton, ← Finset.coe_singleton]
    refine notMem_span_image_of_notMem D.hz'.1.symm D.hz'.2 fun h => ?_
    rw [Finset.mem_singleton, ChartAt.pivotIdx] at h
    exact hc (Subtype.mk.inj (D.τ_injective h)).symm
  exact iSup_colon_pow_span_singleton_mul_pow hprime hεP _

/-- **A member missing `q`**: a member `Y = (z_c = 0)` of the centre (`c ∈ C`, not the pivot) whose
induced coordinate is a unit at `q` has strict transform missing `q`. -/
theorem stalkIdeal_strictTransformAlong_eq_top_of_isUnit {c : Fin n} (hc : c ≠ D.c₀) (hcC : c ∈ C)
    (hcu : IsUnit (D.w c)) (Y : X.IdealSheafData) (hY : Y.stalkIdeal (blowUpπ Z q) = span {z c}) :
    (Y.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).stalkIdeal q = ⊤ := by
  classical
  rw [D.stalkIdeal_strictTransformAlong_eq Y, hY, Ideal.map_span, Set.image_singleton,
    D.stalkMap_eq c, D.wHat_of_ne hc, ite_eq_left hcC]
  exact iSup_colon_pow_eq_top_of_pow_mem (t := 1)
    (by rw [pow_one, span_singleton_mul_left_unit hcu]; exact mem_span_singleton_self _)

/-- Off the centre every coordinate's induced coordinate vanishes at `q`. -/
theorem w_mem_maximalIdeal_of_notMem' [IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z q))]
    (hz : IsRegularSystemOfParameters z) {c : Fin n} (hcC : c ∉ C) :
    D.w c ∈ maximalIdeal ((blowUp Z).presheaf.stalk q) :=
  D.w_mem_maximalIdeal_of_notMem hcC (x_mem_maximalIdeal_of_span_eq z hz.1.symm c)

/-- **The dichotomy for a member `Y = (z_c = 0)` through `p`**: `q` lies on its strict transform iff
`c` is not the pivot and `w_c` vanishes at `q`; then the stalk is `(w_c)`. -/
theorem mem_support_strictTransformAlong_iff
    [IsRegularLocalRing ((blowUp Z).presheaf.stalk q)]
        (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    [IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z q))]
    (hz : IsRegularSystemOfParameters z) {c : Fin n} (Y : X.IdealSheafData)
    (hY : Y.stalkIdeal (blowUpπ Z q) = span {z c}) :
    q ∈ (Y.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).support ↔
      c ≠ D.c₀ ∧ D.w c ∈ maximalIdeal ((blowUp Z).presheaf.stalk q) := by
  classical
  constructor
  · intro hqY
    have hle := (mem_support_iff_stalkIdeal_le_maximalIdeal (I := _) (x := q)).mp hqY
    have hc : c ≠ D.c₀ := by
      rintro rfl
      rw [D.stalkIdeal_strictTransformAlong_eq_top_of_mem Y (hY ▸ mem_span_singleton_self _)]
        at hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)
    refine ⟨hc, ?_⟩
    by_contra hcm
    by_cases hcC : c ∈ C
    · rw [D.stalkIdeal_strictTransformAlong_eq_top_of_isUnit hc hcC
        (IsLocalRing.notMem_maximalIdeal.mp hcm) Y hY] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)
    · exact hcm (D.w_mem_maximalIdeal_of_notMem' hz hcC)
  · rintro ⟨hc, hcm⟩
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal (I := _) (x := q),
      D.stalkIdeal_strictTransformAlong_eq_span_w hq hc hcm Y hY, span_singleton_le_iff_mem]
    exact hcm

end Members

/-! ### The new chain coordinates at a point of the exceptional divisor -/

section Assembly

variable {Z : X.IdealSheafData} {q : blowUp Z} {n : ℕ}
  {z : Fin n → X.presheaf.stalk (blowUpπ Z q)} {C : Finset (Fin n)} (D : ChartAt Z q z C)
  (E : DivisorFamily X) (Γ : X.IdealSheafData)
  (c : {j : E.ι // blowUpπ Z q ∈ (E.component j).support} → Fin n)
  {r : ℕ} (σ : Fin (r + 1) → Fin n) (a : Fin (r + 1) → Fin n → ℕ)

open Classical in
/-- The coordinate assigned to a member of the total transform at `q`: the parameter of the induced
coordinate of a strict transform through `q`, the pivot's parameter for `F` (and, irrelevantly,
for a strict transform missing `q`). -/
noncomputable def newMemberIdx (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (j' : (E.totalTransform Z).ι) : Fin D.m :=
  match ofLex j' with
  | Sum.inl j =>
    if h : ∃ hj : blowUpπ Z q ∈ (E.component j).support,
        D.w (c ⟨j, hj⟩) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q) then
      D.τ ⟨c ⟨j, h.fst⟩, h.snd⟩
    else D.pivotIdx hq
  | Sum.inr _ => D.pivotIdx hq

open Classical in
theorem newMemberIdx_inl (hq : q ∈ (Z.comap (blowUpπ Z)).support) (j : E.ι) :
    D.newMemberIdx E c hq (toLex (Sum.inl j)) =
      if h : ∃ hj : blowUpπ Z q ∈ (E.component j).support,
          D.w (c ⟨j, hj⟩) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q) then
        D.τ ⟨c ⟨j, h.fst⟩, h.snd⟩
      else D.pivotIdx hq := rfl

theorem newMemberIdx_inr (hq : q ∈ (Z.comap (blowUpπ Z)).support) (u : PUnit.{u + 1}) :
    D.newMemberIdx E c hq (toLex (Sum.inr u)) = D.pivotIdx hq := rfl

/-- The pivot is not a chain coordinate when `q` lies on the strict transform of `Γ`. -/
theorem σ_ne_c₀ (hΓ : Γ.stalkIdeal (blowUpπ Z q) = span (Set.range (z ∘ σ)))
    (hqΓ : q ∈ (Γ.strictTransform Z).support) (i : Fin (r + 1)) : σ i ≠ D.c₀ := by
  intro h
  have hle := (mem_support_iff_stalkIdeal_le_maximalIdeal (I := _) (x := q)).mp hqΓ
  rw [strictTransform_eq_strictTransformAlong, D.stalkIdeal_strictTransformAlong_eq_top_of_mem Γ
    (by rw [hΓ, ← h]; exact subset_span ⟨i, rfl⟩)] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

/-- The chain coordinates vanish at `q` and generate the strict transform of `Γ` there. -/
theorem w_σ_mem_and_stalkIdeal_strictTransform [IsRegularLocalRing ((blowUp Z).presheaf.stalk q)]
    (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hΓ : Γ.stalkIdeal (blowUpπ Z q) = span (Set.range (z ∘ σ)))
    (hqΓ : q ∈ (Γ.strictTransform Z).support) :
    (∀ i, D.w (σ i) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)) ∧
      (Γ.strictTransform Z).stalkIdeal q = span (Set.range fun i => D.w (σ i)) :=
  D.stalkIdeal_strictTransformAlong_eq_span_range hq σ (D.σ_ne_c₀ Γ σ hΓ hqΓ) Γ hΓ hqΓ

/-- The new chain: the parameters of the chain coordinates. -/
noncomputable def newChain
    (hmem : ∀ i, D.w (σ i) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q))
    (i : Fin (r + 1)) : Fin D.m :=
  D.τ ⟨σ i, hmem i⟩

theorem z'_newChain (hmem : ∀ i, D.w (σ i) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q))
    (i : Fin (r + 1)) : D.z' (D.newChain σ hmem i) = D.w (σ i) :=
  D.hτ _

theorem newChain_injective (hσ : Function.Injective σ)
    (hmem : ∀ i, D.w (σ i) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)) :
    Function.Injective (D.newChain σ hmem) := by
  intro i₁ i₂ h
  exact hσ (Subtype.mk.inj (D.τ_injective h))

variable [IsRegularLocalRing ((blowUp Z).presheaf.stalk q)]
  [IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z q))]

/-- A member of the total transform through `q` of the form `inl j`: `j` passes through `p`, its
coordinate is not the pivot and its induced coordinate vanishes at `q`. -/
theorem exists_of_mem_support_inl (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hz : IsRegularSystemOfParameters z)
    (hc : ∀ j, (E.component j.1).stalkIdeal (blowUpπ Z q) = span {z (c j)}) (j : E.ι)
    (hj' : q ∈ ((E.totalTransform Z).component (toLex (Sum.inl j))).support) :
    ∃ hj : blowUpπ Z q ∈ (E.component j).support,
      c ⟨j, hj⟩ ≠ D.c₀ ∧ D.w (c ⟨j, hj⟩) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q) := by
  rw [totalTransform_component_inl, strictTransform_eq_strictTransformAlong] at hj'
  have hj : blowUpπ Z q ∈ (E.component j).support :=
    π_mem_support_of_mem_support_strictTransformAlong Z _ q hj'
  exact ⟨hj, (D.mem_support_strictTransformAlong_iff hq hz _ (hc ⟨j, hj⟩)).mp hj'⟩

/-- The coordinate of a strict transform through `q`. -/
theorem newMemberIdx_inl_of_mem (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hz : IsRegularSystemOfParameters z)
    (hc : ∀ j, (E.component j.1).stalkIdeal (blowUpπ Z q) = span {z (c j)}) (j : E.ι)
    (hj' : q ∈ ((E.totalTransform Z).component (toLex (Sum.inl j))).support) :
    ∃ (hj : blowUpπ Z q ∈ (E.component j).support)
      (hm : D.w (c ⟨j, hj⟩) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)),
      c ⟨j, hj⟩ ≠ D.c₀ ∧ D.newMemberIdx E c hq (toLex (Sum.inl j)) = D.τ ⟨c ⟨j, hj⟩, hm⟩ := by
  classical
  obtain ⟨hj, hne, hm⟩ := D.exists_of_mem_support_inl E c hq hz hc j hj'
  refine ⟨hj, hm, hne, ?_⟩
  rw [newMemberIdx_inl, dite_eq_left ⟨hj, hm⟩]

/-- The stalk of a strict transform through `q` is generated by its new coordinate. -/
theorem stalkIdeal_component_inl (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hz : IsRegularSystemOfParameters z)
    (hc : ∀ j, (E.component j.1).stalkIdeal (blowUpπ Z q) = span {z (c j)}) (j : E.ι)
    (hj' : q ∈ ((E.totalTransform Z).component (toLex (Sum.inl j))).support) :
    ((E.totalTransform Z).component (toLex (Sum.inl j))).stalkIdeal q =
      span {D.z' (D.newMemberIdx E c hq (toLex (Sum.inl j)))} := by
  obtain ⟨hj, hm, hne, heq⟩ := D.newMemberIdx_inl_of_mem E c hq hz hc j hj'
  rw [heq, D.hτ, totalTransform_component_inl, strictTransform_eq_strictTransformAlong,
    D.stalkIdeal_strictTransformAlong_eq_span_w hq hne hm _ (hc ⟨j, hj⟩)]

omit [IsRegularLocalRing ((blowUp Z).presheaf.stalk q)]
  [IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z q))] in
/-- The stalk of the exceptional divisor is generated by the pivot's parameter. -/
theorem stalkIdeal_component_inr (hq : q ∈ (Z.comap (blowUpπ Z)).support) (u : PUnit.{u + 1}) :
    ((E.totalTransform Z).component (toLex (Sum.inr u))).stalkIdeal q =
      span {D.z' (D.newMemberIdx E c hq (toLex (Sum.inr u)))} := by
  rw [newMemberIdx_inr, D.z'_pivotIdx, totalTransform_component_toLex_inr,
    exceptionalDivisor_eq_comap, D.hF_ε]

/-- The new coordinates of the members through `q` are distinct. -/
theorem newMemberIdx_injective (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hz : IsRegularSystemOfParameters z) (hcinj : Function.Injective c)
    (hc : ∀ j, (E.component j.1).stalkIdeal (blowUpπ Z q) = span {z (c j)}) :
    Function.Injective fun j' : {j' : (E.totalTransform Z).ι //
      q ∈ ((E.totalTransform Z).component j').support} => D.newMemberIdx E c hq j'.1 := by
  classical
  rintro ⟨j₁, h₁⟩ ⟨j₂, h₂⟩ heq
  apply Subtype.ext
  change D.newMemberIdx E c hq j₁ = D.newMemberIdx E c hq j₂ at heq
  rcases eq_toLex_inl_or_inr E Z j₁ with ⟨i₁, rfl⟩ | ⟨u₁, rfl⟩ <;>
    rcases eq_toLex_inl_or_inr E Z j₂ with ⟨i₂, rfl⟩ | ⟨u₂, rfl⟩
  · obtain ⟨hj₁, hm₁, -, e₁⟩ := D.newMemberIdx_inl_of_mem E c hq hz hc i₁ h₁
    obtain ⟨hj₂, hm₂, -, e₂⟩ := D.newMemberIdx_inl_of_mem E c hq hz hc i₂ h₂
    have heq' : D.τ ⟨c ⟨i₁, hj₁⟩, hm₁⟩ = D.τ ⟨c ⟨i₂, hj₂⟩, hm₂⟩ := e₁.symm.trans (heq.trans e₂)
    have := hcinj (Subtype.mk.inj (D.τ_injective heq'))
    change toLex (Sum.inl i₁) = toLex (Sum.inl i₂)
    exact congrArg (fun j => toLex (Sum.inl j)) (Subtype.mk.inj this)
  · obtain ⟨hj₁, hm₁, hne₁, e₁⟩ := D.newMemberIdx_inl_of_mem E c hq hz hc i₁ h₁
    have heq' : D.τ ⟨c ⟨i₁, hj₁⟩, hm₁⟩ = D.pivotIdx hq :=
      e₁.symm.trans (heq.trans (D.newMemberIdx_inr E c hq u₂))
    exact absurd (Subtype.mk.inj (D.τ_injective heq')) hne₁
  · obtain ⟨hj₂, hm₂, hne₂, e₂⟩ := D.newMemberIdx_inl_of_mem E c hq hz hc i₂ h₂
    have heq' : D.pivotIdx hq = D.τ ⟨c ⟨i₂, hj₂⟩, hm₂⟩ :=
      (D.newMemberIdx_inr E c hq u₁).symm.trans (heq.trans e₂)
    exact absurd (Subtype.mk.inj (D.τ_injective heq')).symm hne₂
  · rfl

/-- Every member of the total transform through `q` is generated by its new coordinate. -/
theorem stalkIdeal_component (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hz : IsRegularSystemOfParameters z)
    (hc : ∀ j, (E.component j.1).stalkIdeal (blowUpπ Z q) = span {z (c j)})
    (j' : {j' : (E.totalTransform Z).ι // q ∈ ((E.totalTransform Z).component j').support}) :
    ((E.totalTransform Z).component j'.1).stalkIdeal q =
      span {D.z' (D.newMemberIdx E c hq j'.1)} := by
  obtain ⟨j', hj'⟩ := j'
  rcases eq_toLex_inl_or_inr E Z j' with ⟨j, rfl⟩ | ⟨u, rfl⟩
  · exact D.stalkIdeal_component_inl E c hq hz hc j hj'
  · exact D.stalkIdeal_component_inr E c hq u

/-- The new coordinates form snc data for the total transform at `q`. -/
theorem isSncAt_totalTransform (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hz : IsRegularSystemOfParameters z) (hcinj : Function.Injective c)
    (hc : ∀ j, (E.component j.1).stalkIdeal (blowUpπ Z q) = span {z (c j)}) :
    (E.totalTransform Z).IsSncAt q D.z' :=
  ⟨D.hz', fun j' => D.newMemberIdx E c hq j'.1, D.newMemberIdx_injective E c hq hz hcinj hc,
    D.stalkIdeal_component E c hq hz hc⟩

omit [IsRegularLocalRing ((blowUp Z).presheaf.stalk q)]
  [IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z q))] in
/-- A nonzero entry of `newExp t c` sits at the parameter of a vanishing induced coordinate. -/
theorem exists_of_newExp_ne_zero (t : ℕ) (cc : Fin n → ℕ) {k' : Fin D.m}
    (h : D.newExp t cc k' ≠ 0) :
    ∃ (kk : Fin n) (hk : D.w kk ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)),
      k' = D.τ ⟨kk, hk⟩ ∧ (if kk = D.c₀ then t else cc kk) ≠ 0 := by
  classical
  by_cases hr : ∃ kk : {i : Fin n // D.w i ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)},
      D.τ kk = k'
  · obtain ⟨⟨kk, hk⟩, rfl⟩ := hr
    refine ⟨kk, hk, rfl, ?_⟩
    rwa [newExp, D.τ_injective.extend_apply] at h
  · exfalso
    apply h
    rw [newExp, Function.extend_apply' _ _ _ hr]
    rfl

/-- The new exponents are supported on the new members' coordinates. -/
theorem newExp_support (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hz : IsRegularSystemOfParameters z)
    (hc : ∀ j, (E.component j.1).stalkIdeal (blowUpπ Z q) = span {z (c j)}) (t : ℕ)
    (cc : Fin n → ℕ) (hcc : ∀ kk, cc kk ≠ 0 → kk ∈ Set.range c) (k' : Fin D.m)
    (h : D.newExp t cc k' ≠ 0) :
    k' ∈ Set.range fun j' : {j' : (E.totalTransform Z).ι //
      q ∈ ((E.totalTransform Z).component j').support} => D.newMemberIdx E c hq j'.1 := by
  classical
  obtain ⟨kk, hk, rfl, hne⟩ := D.exists_of_newExp_ne_zero t cc h
  by_cases hkc : kk = D.c₀
  · subst hkc
    refine ⟨⟨toLex (Sum.inr PUnit.unit), hq⟩, ?_⟩
    change D.newMemberIdx E c hq (toLex (Sum.inr PUnit.unit)) = D.τ ⟨D.c₀, hk⟩
    rw [newMemberIdx_inr, ChartAt.pivotIdx]
  · rw [ite_eq_right hkc] at hne
    obtain ⟨⟨j, hj⟩, rfl⟩ := hcc kk hne
    have hqj : q ∈ ((E.totalTransform Z).component (toLex (Sum.inl j))).support := by
      rw [totalTransform_component_inl, strictTransform_eq_strictTransformAlong,
        D.mem_support_strictTransformAlong_iff hq hz _ (hc ⟨j, hj⟩)]
      exact ⟨hkc, hk⟩
    refine ⟨⟨toLex (Sum.inl j), hqj⟩, ?_⟩
    obtain ⟨hj', hm', -, e⟩ := D.newMemberIdx_inl_of_mem E c hq hz hc j hqj
    change D.newMemberIdx E c hq (toLex (Sum.inl j)) = D.τ ⟨c ⟨j, hj⟩, hk⟩
    rw [e]

/-- The new chain avoids the new members' coordinates. -/
theorem newChain_ne_newMemberIdx (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hz : IsRegularSystemOfParameters z)
    (hc : ∀ j, (E.component j.1).stalkIdeal (blowUpπ Z q) = span {z (c j)})
    (hσc : ∀ i j, σ i ≠ c j) (hσc₀ : ∀ i, σ i ≠ D.c₀)
    (hmem : ∀ i, D.w (σ i) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)) (i : Fin (r + 1))
    (j' : {j' : (E.totalTransform Z).ι // q ∈ ((E.totalTransform Z).component j').support}) :
    D.newChain σ hmem i ≠ D.newMemberIdx E c hq j'.1 := by
  classical
  obtain ⟨j', hj'⟩ := j'
  rcases eq_toLex_inl_or_inr E Z j' with ⟨j, rfl⟩ | ⟨u, rfl⟩
  · obtain ⟨hj, hm, -, e⟩ := D.newMemberIdx_inl_of_mem E c hq hz hc j hj'
    change D.newChain σ hmem i ≠ D.newMemberIdx E c hq (toLex (Sum.inl j))
    rw [e, newChain]
    intro h
    exact hσc i ⟨j, hj⟩ (Subtype.mk.inj (D.τ_injective h))
  · change D.newChain σ hmem i ≠ D.newMemberIdx E c hq (toLex (Sum.inr u))
    rw [newMemberIdx_inr, ChartAt.pivotIdx, newChain]
    intro h
    exact hσc₀ i (Subtype.mk.inj (D.τ_injective h))

/-- **The new chain coordinates at `q`**: the parameters `z'`, the members' coordinates, the chain
`τ ∘ σ` and the exponents `newExp (D_i) (a_i)`. -/
theorem chainCoords_totalTransform (hq : q ∈ (Z.comap (blowUpπ Z)).support)
    (hcoords : ChainCoords E Γ (blowUpπ Z q) z c σ a) (hqΓ : q ∈ (Γ.strictTransform Z).support)
    (Dexp : Fin (r + 1) → ℕ) :
    ChainCoords (E.totalTransform Z) (Γ.strictTransform Z) q D.z'
      (fun j' => D.newMemberIdx E c hq j'.1)
      (D.newChain σ (D.w_σ_mem_and_stalkIdeal_strictTransform Γ σ hq
        hcoords.2.2.2.2.2.2 hqΓ).1)
      (fun i => D.newExp (Dexp i) (a i)) := by
  obtain ⟨hz, hcinj, hc, hσinj, hσc, ha, hΓ⟩ := hcoords
  refine ⟨D.hz', D.newMemberIdx_injective E c hq hz hcinj hc, D.stalkIdeal_component E c hq hz hc,
    D.newChain_injective σ hσinj _,
    fun i j' => D.newChain_ne_newMemberIdx E c σ hq hz hc hσc (D.σ_ne_c₀ Γ σ hΓ hqΓ) _ i j',
    fun i k' h => D.newExp_support E c hq hz hc _ _ (ha i) k' h, ?_⟩
  exact (D.w_σ_mem_and_stalkIdeal_strictTransform Γ σ hq hΓ hqΓ).2.trans
    (congrArg span (congrArg Set.range (funext fun i => (D.z'_newChain σ _ i).symm)))

end Assembly

/-! ### The transforms in the new parameters -/

section Conversion

variable {Z : X.IdealSheafData} {q : blowUp Z} {n : ℕ}
  {z : Fin n → X.presheaf.stalk (blowUpπ Z q)} {C : Finset (Fin n)} (D : ChartAt Z q z C)
  {r : ℕ} (σ : Fin (r + 1) → Fin n) (a : Fin (r + 1) → Fin n → ℕ)

/-- The ε-free chain equations are the new chain's parameters. -/
theorem wHat_comp_eq (hσc₀ : ∀ i, σ i ≠ D.c₀)
    (hmem : ∀ i, D.w (σ i) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)) :
    (fun i => D.wHat (σ i)) = D.z' ∘ D.newChain σ hmem :=
  funext fun i => by rw [D.wHat_of_ne (hσc₀ i), Function.comp_apply, D.z'_newChain]

/-- **The K-shape in the new parameters**: under the ε-order conditions (the admissibility
condition (★)), the mark-`1` transform of a K-shape is the K-shape with chain `τ ∘ σ`, level
exponents `newExp (D_i) (a_i)` and top exponents `newExp (E_0 − 1) b`. -/
theorem stalkIdeal_markedTransform_chainKIdeal [IsRegularLocalRing ((blowUp Z).presheaf.stalk q)]
    (hq : q ∈ (Z.comap (blowUpπ Z)).support) (hσc₀ : ∀ i, σ i ≠ D.c₀)
    (hmem : ∀ i, D.w (σ i) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)) (b : Fin n → ℕ)
    (K : X.IdealSheafData)
    (hK : K.stalkIdeal (blowUpπ Z q) =
      span {monomialOf z b} * chainKIdeal (z ∘ σ) fun i => monomialOf z (a i))
    (δ : Fin (r + 1) → ℕ) (hδ : ∀ i, δ i = if σ i ∈ C then 1 else 0)
    (hpos : 1 ≤ epsOrderC C a b (Function.update δ (Fin.last r) 0) 0)
    (hmono : ∀ i : Fin r, epsOrderC C a b (Function.update δ (Fin.last r) 0) i.castSucc ≤
      epsOrderC C a b (Function.update δ (Fin.last r) 0) i.succ)
    (Dexp : Fin (r + 1) → ℕ)
    (hD : ∀ i : Fin r, Dexp i.castSucc =
      epsOrderC C a b (Function.update δ (Fin.last r) 0) i.succ -
        epsOrderC C a b (Function.update δ (Fin.last r) 0) i.castSucc) :
    (K.markedTransform Z 1).stalkIdeal q =
      span {monomialOf D.z'
          (D.newExp (epsOrderC C a b (Function.update δ (Fin.last r) 0) 0 - 1) b)} *
        chainKIdeal (D.z' ∘ D.newChain σ hmem)
          fun i => monomialOf D.z' (D.newExp (Dexp i) (a i)) := by
  rw [markedTransform_one_eq,
    D.stalkIdeal_controlledTransformAlong_chainKIdeal σ a b K hK δ hδ hpos hmono Dexp hD]
  obtain ⟨u₀, hu₀, e₀⟩ := D.exists_isUnit_mul_monomialOf_newExp hq _ b
  choose u hu e using fun i => D.exists_isUnit_mul_monomialOf_newExp hq (Dexp i) (a i)
  have hM : (fun i => D.ε ^ Dexp i * monomialOf D.wHat (a i)) =
      fun i => u i * monomialOf D.z' (D.newExp (Dexp i) (a i)) := funext e
  rw [e₀, hM, D.wHat_comp_eq σ hσc₀ hmem, span_singleton_mul_left_unit hu₀,
    chainKIdeal_isUnit_mul _ _ hu]

/-- **The un-isolated form in the new parameters**. -/
theorem stalkIdeal_markedTransform_chainIdeal [IsRegularLocalRing ((blowUp Z).presheaf.stalk q)]
    (hq : q ∈ (Z.comap (blowUpπ Z)).support) (hσc₀ : ∀ i, σ i ≠ D.c₀)
    (hmem : ∀ i, D.w (σ i) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q)) (b : Fin n → ℕ)
    (I : X.IdealSheafData)
    (hI : I.stalkIdeal (blowUpπ Z q) =
      span {monomialOf z b} * chainIdeal (z ∘ σ) fun i => monomialOf z (a i))
    (δ : Fin (r + 1) → ℕ) (hδ : ∀ i, δ i = if σ i ∈ C then 1 else 0)
    (hpos : 1 ≤ epsOrderC C a b δ 0)
    (hmono : ∀ i : Fin r, epsOrderC C a b δ i.castSucc ≤ epsOrderC C a b δ i.succ)
    (Dexp : Fin (r + 1) → ℕ)
    (hD : ∀ i : Fin r, Dexp i.castSucc = epsOrderC C a b δ i.succ - epsOrderC C a b δ i.castSucc) :
    (I.markedTransform Z 1).stalkIdeal q =
      span {monomialOf D.z' (D.newExp (epsOrderC C a b δ 0 - 1) b)} *
        chainIdeal (D.z' ∘ D.newChain σ hmem)
          fun i => monomialOf D.z' (D.newExp (Dexp i) (a i)) := by
  rw [markedTransform_one_eq,
    D.stalkIdeal_controlledTransformAlong_chainIdeal σ a b I hI δ hδ hpos hmono Dexp hD]
  obtain ⟨u₀, hu₀, e₀⟩ := D.exists_isUnit_mul_monomialOf_newExp hq _ b
  choose u hu e using fun i => D.exists_isUnit_mul_monomialOf_newExp hq (Dexp i) (a i)
  have hM : (fun i => D.ε ^ Dexp i * monomialOf D.wHat (a i)) =
      fun i => u i * monomialOf D.z' (D.newExp (Dexp i) (a i)) := funext e
  rw [e₀, hM, D.wHat_comp_eq σ hσc₀ hmem, span_singleton_mul_left_unit hu₀,
    chainIdeal_isUnit_mul _ _ hu]

end Conversion

end ChartAt

/-! ### Off the exceptional divisor: transport along the stalk isomorphism -/

section OffCentre

variable (E : DivisorFamily X) (Z : X.IdealSheafData) {q : blowUp Z}
  (hq : q ∉ (Z.comap (blowUpπ Z)).support)

variable {n : ℕ} {z : Fin n → X.presheaf.stalk (blowUpπ Z q)}
  (c : {j : E.ι // blowUpπ Z q ∈ (E.component j).support} → Fin n) {r : ℕ}
  (σ : Fin (r + 1) → Fin n)

open Classical in
/-- The members' coordinates transported to the total transform (the exceptional divisor and the
strict transforms missing `q` receive an irrelevant value). -/
noncomputable def offCentreIdx (j' : (E.totalTransform Z).ι) : Fin n :=
  Sum.elim (fun j => if h : blowUpπ Z q ∈ (E.component j).support then c ⟨j, h⟩ else σ 0)
    (fun _ => σ 0) (ofLex j')

theorem offCentreIdx_inl_of_mem (j : E.ι) (hj : blowUpπ Z q ∈ (E.component j).support) :
    offCentreIdx E Z c σ (toLex (Sum.inl j)) = c ⟨j, hj⟩ := by
  classical
  change (if h : blowUpπ Z q ∈ (E.component j).support then c ⟨j, h⟩ else σ 0) = _
  rw [dite_eq_left hj]

include hq

/-- Off the exceptional divisor a strict transform passes through `q` iff the member passes through
`π(q)`; the exceptional divisor misses `q`. -/
theorem mem_support_totalTransform_component_iff (j : E.ι) :
    q ∈ ((E.totalTransform Z).component (toLex (Sum.inl j))).support ↔
      blowUpπ Z q ∈ (E.component j).support :=
  mem_support_strictTransformAlong_iff_of_notMem_support Z (E.component j) hq

theorem not_mem_support_totalTransform_component_inr (u : PUnit.{u + 1}) :
    q ∉ ((E.totalTransform Z).component (toLex (Sum.inr u))).support := hq

/-- The stalk of a strict transform off the exceptional divisor is the image of the member's
stalk under the stalk isomorphism. -/
theorem stalkIdeal_totalTransform_component_inl (j : E.ι) :
    ((E.totalTransform Z).component (toLex (Sum.inl j))).stalkIdeal q =
      ((E.component j).stalkIdeal (blowUpπ Z q)).map ((blowUpπ Z).stalkMap q).hom :=
  stalkIdeal_strictTransformAlong_of_notMem_support Z (E.component j) hq

/-- The stalk of the strict transform of `Γ` off the exceptional divisor. -/
theorem stalkIdeal_strictTransform_eq_map_of_notMem (Γ : X.IdealSheafData) :
    (Γ.strictTransform Z).stalkIdeal q =
      (Γ.stalkIdeal (blowUpπ Z q)).map ((blowUpπ Z).stalkMap q).hom :=
  stalkIdeal_strictTransformAlong_of_notMem_support Z Γ hq

/-- The stalk of the mark-`1` transform off the exceptional divisor is the image of the stalk. -/
theorem stalkIdeal_markedTransform_one_of_notMem (K : X.IdealSheafData) :
    (K.markedTransform Z 1).stalkIdeal q =
      (K.stalkIdeal (blowUpπ Z q)).map ((blowUpπ Z).stalkMap q).hom := by
  rw [markedTransform_one_eq, controlledTransformAlong, pow_one,
    stalkIdeal_colon_of_isInvertible _ (blowUp.isInvertible_comap_π Z), stalkIdeal_comap,
    stalkIdeal_eq_top_of_notMem_support _ hq, Ideal.colon_coe_top]

/-- The chain-relative form (K-shape) transports off the exceptional divisor: coordinates `π^* z`,
the same chain and exponents. -/
theorem chainCoords_totalTransform_of_notMem {Γ : X.IdealSheafData}
    {a : Fin (r + 1) → Fin n → ℕ} (hcoords : ChainCoords E Γ (blowUpπ Z q) z c σ a) :
    ChainCoords (E.totalTransform Z) (Γ.strictTransform Z) q
      (fun i => (blowUpπ Z).stalkMap q (z i)) (fun j' => offCentreIdx E Z c σ j'.1) σ a := by
  classical
  set e := stalkMapπEquiv Z hq
  obtain ⟨hz, hcinj, hc, hσinj, hσc, ha, hΓ⟩ := hcoords
  refine ⟨?_, ?_, ?_, hσinj, ?_, ?_, ?_⟩
  · exact Hironaka.Sequence.isRegularSystemOfParameters_comp_ringEquiv e hz
  · rintro ⟨j₁, h₁⟩ ⟨j₂, h₂⟩ heq
    apply Subtype.ext
    change offCentreIdx E Z c σ j₁ = offCentreIdx E Z c σ j₂ at heq
    rcases eq_toLex_inl_or_inr E Z j₁ with ⟨i₁, rfl⟩ | ⟨u₁, rfl⟩
    · rcases eq_toLex_inl_or_inr E Z j₂ with ⟨i₂, rfl⟩ | ⟨u₂, rfl⟩
      · have hp₁ := (mem_support_totalTransform_component_iff E Z hq i₁).mp h₁
        have hp₂ := (mem_support_totalTransform_component_iff E Z hq i₂).mp h₂
        have heq' : c ⟨i₁, hp₁⟩ = c ⟨i₂, hp₂⟩ :=
          (offCentreIdx_inl_of_mem E Z c σ i₁ hp₁).symm.trans
            (heq.trans (offCentreIdx_inl_of_mem E Z c σ i₂ hp₂))
        change toLex (Sum.inl i₁) = toLex (Sum.inl i₂)
        exact congrArg (fun j => toLex (Sum.inl j)) (Subtype.mk.inj (hcinj heq'))
      · exact absurd h₂ (not_mem_support_totalTransform_component_inr E Z hq u₂)
    · exact absurd h₁ (not_mem_support_totalTransform_component_inr E Z hq u₁)
  · rintro ⟨j', hj'⟩
    rcases eq_toLex_inl_or_inr E Z j' with ⟨j, rfl⟩ | ⟨u, rfl⟩
    · have hp := (mem_support_totalTransform_component_iff E Z hq j).mp hj'
      change ((E.totalTransform Z).component (toLex (Sum.inl j))).stalkIdeal q =
        span {(blowUpπ Z).stalkMap q (z (offCentreIdx E Z c σ (toLex (Sum.inl j))))}
      rw [stalkIdeal_totalTransform_component_inl E Z hq, offCentreIdx_inl_of_mem E Z c σ j hp,
        hc ⟨j, hp⟩, Ideal.map_span, Set.image_singleton]
    · exact absurd hj' (not_mem_support_totalTransform_component_inr E Z hq u)
  · intro i j'
    obtain ⟨j', hj'⟩ := j'
    rcases eq_toLex_inl_or_inr E Z j' with ⟨j, rfl⟩ | ⟨u, rfl⟩
    · have hp := (mem_support_totalTransform_component_iff E Z hq j).mp hj'
      change σ i ≠ offCentreIdx E Z c σ (toLex (Sum.inl j))
      rw [offCentreIdx_inl_of_mem E Z c σ j hp]
      exact hσc i ⟨j, hp⟩
    · exact absurd hj' (not_mem_support_totalTransform_component_inr E Z hq u)
  · intro i k hk
    obtain ⟨⟨j, hj⟩, rfl⟩ := ha i k hk
    refine ⟨⟨toLex (Sum.inl j), (mem_support_totalTransform_component_iff E Z hq j).mpr hj⟩, ?_⟩
    exact offCentreIdx_inl_of_mem E Z c σ j hj
  · rw [stalkIdeal_strictTransform_eq_map_of_notMem Z hq, hΓ, Ideal.map_span, ← Set.range_comp]
    rfl

/-- The support of the exponents transports off the exceptional divisor. -/
theorem range_le_range_offCentreIdx (k : Fin n) (hk : k ∈ Set.range c) :
    k ∈ Set.range fun j' : {j' : (E.totalTransform Z).ι //
      q ∈ ((E.totalTransform Z).component j').support} => offCentreIdx E Z c σ j'.1 := by
  obtain ⟨⟨j, hj⟩, rfl⟩ := hk
  exact ⟨⟨toLex (Sum.inl j), (mem_support_totalTransform_component_iff E Z hq j).mpr hj⟩,
    offCentreIdx_inl_of_mem E Z c σ j hj⟩

/-- **CP4 off the exceptional divisor, K-shape**: the K-shape transports along the stalk
isomorphism at a point off the centre. -/
theorem chainRelativeKAt_totalTransform_of_notMem (K Γ : X.IdealSheafData)
    (h : ChainRelativeKAt E K Γ (blowUpπ Z q)) :
    ChainRelativeKAt (E.totalTransform Z) (K.markedTransform Z 1) (Γ.strictTransform Z) q := by
  obtain ⟨n, z, c, r, σ, a, b, hcoords, hb, hK⟩ := h
  refine ⟨n, fun i => (blowUpπ Z).stalkMap q (z i), fun j' => offCentreIdx E Z c σ j'.1, r, σ, a,
    b, chainCoords_totalTransform_of_notMem E Z hq c σ hcoords,
    fun k hk => range_le_range_offCentreIdx E Z hq c σ k (hb k hk), ?_⟩
  rw [stalkIdeal_markedTransform_one_of_notMem Z hq, hK, Ideal.map_mul, Ideal.map_span,
    Set.image_singleton, monomialOf_map, ← chainKIdeal_comp]
  congr 2
  funext i
  rw [Function.comp_apply, monomialOf_map]
  rfl

/-- **CP4 off the exceptional divisor, un-isolated form**. -/
theorem chainRelativeAt_totalTransform_of_notMem (I Γ : X.IdealSheafData)
    (h : ChainRelativeAt E I Γ (blowUpπ Z q)) :
    ChainRelativeAt (E.totalTransform Z) (I.markedTransform Z 1) (Γ.strictTransform Z) q := by
  obtain ⟨n, z, c, r, σ, a, b, hcoords, hb, hI⟩ := h
  refine ⟨n, fun i => (blowUpπ Z).stalkMap q (z i), fun j' => offCentreIdx E Z c σ j'.1, r, σ, a,
    b, chainCoords_totalTransform_of_notMem E Z hq c σ hcoords,
    fun k hk => range_le_range_offCentreIdx E Z hq c σ k (hb k hk), ?_⟩
  rw [stalkIdeal_markedTransform_one_of_notMem Z hq, hI, Ideal.map_mul, Ideal.map_span,
    Set.image_singleton, monomialOf_map, ← chainIdeal_comp]
  congr 2
  funext i
  rw [Function.comp_apply, monomialOf_map]
  rfl

/-- **snc data off the exceptional divisor**: `Γ̃` has snc with the total transform at `q` when
`Γ` has snc with `E` at `π(q)`. -/
theorem exists_isSncAt_totalTransform_of_notMem (Γ : X.IdealSheafData) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (blowUpπ Z q)} (hsnc : E.IsSncAt (blowUpπ Z q) z)
    {s : Finset (Fin n)} (hΓ : Γ.stalkIdeal (blowUpπ Z q) = span (z '' ↑s)) :
    ∃ z' : Fin n → (blowUp Z).presheaf.stalk q, (E.totalTransform Z).IsSncAt q z' ∧
      (Γ.strictTransform Z).stalkIdeal q = span (z' '' ↑s) := by
  obtain ⟨⟨hspan, hdim⟩, c, hcinj, hc⟩ := hsnc
  have h' := exists_snc_data_totalTransform_of_notMem_support Z E.component hq hspan.symm hdim c
    hcinj hc
  refine ⟨fun i => (blowUpπ Z).stalkMap q (z i), ⟨⟨h'.1.1.symm, h'.1.2⟩, h'.2⟩, ?_⟩
  rw [stalkIdeal_strictTransform_eq_map_of_notMem Z hq, hΓ, Ideal.map_span, Set.image_image]

end OffCentre

end Hironaka.Resolution
