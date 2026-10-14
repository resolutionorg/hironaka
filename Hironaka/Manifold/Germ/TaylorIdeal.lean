/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Germ.TaylorHom
public import Hironaka.Analytic.ConvSeries.CoordDivision
public import Mathlib.RingTheory.Valuation.ValuationRing
import Hironaka.Analytic.Rueckert.Subst
import Hironaka.Analytic.Weierstrass.AdicComplete
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Taylor homomorphism and the maximal ideal

The Taylor homomorphism `T_a` of a chart `φ` (coordinates `ψ`) maps onto the ring of convergent
series (`range_taylorHom`), sends the coordinate germ `x_i − x_i(a)` to `X_i`
(`taylorHom_coord_sub`) and the constants to the constants (`taylorHom_const`). With the division
of a series without constant term by the coordinates
(`Hironaka/Analytic/ConvSeries/CoordDivision.lean`) this gives Hadamard's lemma for germs —
a germ vanishing at `a` is `∑_i (x_i − x_i(a)) g_i` (`exists_eq_sum_coord_mul'`) — and, by
induction on `k`, that `T_a` reflects the powers of the maximal ideal: `T_a s ∈ (X)^k ↔ s ∈ 𝔪_a^k`
(`taylorHom_mem_maximalIdeal_pow_iff`), hence `T_a(𝔪_a^k) = (X)^k ∩ T_a(𝒪_{M,a})`
(`IsTaylorHom.image_maximalIdeal_pow`), `𝔪_a = (x_1 − a_1, …, x_n − a_n)`
(`maximalIdeal_eq_span_coord'`) and `𝔪_a^k` spanned by the degree-`k` monomials in the `x_i − a_i`
(`maximalIdeal_pow_eq_span_monomials'`). These are the facts behind the isomorphism
`𝒪̂_{M,a} ≅ 𝕜[[X]]` of [BM97, (0.3)] (`Hironaka/Manifold/Germ/TaylorCompletion.lean`) and
behind the order of a germ at a point (`Hironaka/Manifold/IdealSheaf/Order.lean`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Analytic IsLocalRing MvPowerSeries
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Hub

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- The germ at `b` of the function of a convergent series `c`, read in the coordinates `ψ`:
`z ↦ c(ψ z − ψ b)`. -/
def seriesGerm (b : E) (c : MvPowerSeries (Fin n) 𝕜) : (𝓝 b).Germ 𝕜 :=
  ↑(fun z => evalSeries c (ψ z - ψ b))

theorem isSeriesOf_seriesGerm (b : E) {c : MvPowerSeries (Fin n) 𝕜} (hc : c ∈ Analytic.Conv 𝕜 n) :
    IsSeriesOf ψ b (seriesGerm ψ b c) c := by
  refine ⟨hc, ?_⟩
  rw [seriesGerm, germCompCoord_coe]
  congr 1
  funext y
  simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem seriesGerm_mem (b : E) {c : MvPowerSeries (Fin n) 𝕜} (hc : c ∈ Analytic.Conv 𝕜 n) :
    seriesGerm ψ b c ∈ analyticGermsAt 𝕜 E b := by
  refine ⟨_, rfl, ?_⟩
  have h1 : AnalyticAt 𝕜 (fun z : E => ψ z - ψ b) b := by
    have := (ψ : E →L[𝕜] (Fin n → 𝕜)).analyticAt b
    rw [ContinuousLinearEquiv.coe_coe] at this
    exact this.sub analyticAt_const
  exact (analyticAt_evalSeries_zero hc).comp_of_eq h1 (sub_self _)

/-- Every convergent series is the power series of an analytic germ. -/
theorem taylorGerm_surjective (b : E) : Function.Surjective (taylorGerm ψ b) := by
  intro c
  refine ⟨⟨seriesGerm ψ b c, seriesGerm_mem ψ b c.2⟩, Subtype.ext ?_⟩
  rw [coe_taylorGerm]
  exact taylorGermFun_eq_of_isSeriesOf ψ _ (isSeriesOf_seriesGerm ψ b c.2)

end Hub

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

/-- The range of the Taylor homomorphism is the ring of convergent series. -/
theorem range_taylorHom : Set.range (taylorHom E ψ φ ha hφ) = ↑(Analytic.Conv 𝕜 n) := by
  ext c
  constructor
  · rintro ⟨s, rfl⟩
    exact taylorHom_mem_conv E ψ φ ha hφ s
  · intro hc
    obtain ⟨g, hg⟩ := taylorGerm_surjective ψ (φ a) ⟨c, hc⟩
    refine ⟨(chartTransport E φ ha hφ).symm g, ?_⟩
    rw [taylorHom_apply, RingEquiv.apply_symm_apply, hg]

/-- The Taylor series of a constant is the constant. -/
theorem taylorHom_const (c : 𝕜) : taylorHom E ψ φ ha hφ (const 𝕜 E M a c) = C c := by
  have hT := isTaylorHom_taylorHom E ψ φ ha hφ
  have h1 := hT.2 ⊤ trivial (constSection 𝕜 E M c)
  have h2 : (extendSection 𝕜 E (constSection 𝕜 E M c) ∘ φ.symm ∘ ψ.symm) = fun _ => c :=
    funext fun _ => extendSection_of_mem 𝕜 E (constSection 𝕜 E M c) trivial
  rw [h2] at h1
  refine eq_of_evalSeries_sub_eventuallyEq ψ (φ a) (hT.1 _) (C_mem_conv c) ?_
  refine h1.symm.trans (Eventually.of_forall fun y => ?_)
  simp only [evalSeries_C']

/-- The Taylor series of the coordinate germ `x_i = ψ_i ∘ φ` is `X_i + x_i(a)`. -/
theorem taylorHom_coord (i : Fin n) :
    taylorHom E ψ φ ha hφ (coord E ψ φ hφ ha i) = X i + C (ψ (φ a) i) := by
  have hT := isTaylorHom_taylorHom E ψ φ ha hφ
  have h1 := hT.2 ⟨φ.source, φ.open_source⟩ ha (chartSection E ψ φ hφ i)
  refine eq_of_evalSeries_sub_eventuallyEq ψ (φ a) (hT.1 _)
    (add_mem (X_mem_conv i) (C_mem_conv _)) ?_
  have h2 : ∀ᶠ y in 𝓝 (ψ (φ a)), ψ.symm y ∈ φ.target :=
    (tendsto_coord_symm ψ (φ a)).eventually (φ.open_target.mem_nhds (φ.map_source ha))
  have h3 : ∀ᶠ y in 𝓝 (ψ (φ a)), evalSeries (X i + C (ψ (φ a) i)) (y - ψ (φ a)) =
      evalSeries (X i) (y - ψ (φ a)) + evalSeries (C (ψ (φ a) i)) (y - ψ (φ a)) :=
    (tendsto_sub_nhds_zero_iff.mpr tendsto_id).eventually
      (evalSeries_add_eventually (X_mem_conv i) (C_mem_conv (ψ (φ a) i)))
  refine h1.symm.trans ?_
  filter_upwards [h2, h3] with y hy hy3
  rw [hy3, Function.comp_apply, Function.comp_apply,
    extendSection_of_mem 𝕜 E _ (φ.map_target hy)]
  change ψ (φ (φ.symm (ψ.symm y))) i = _
  rw [φ.right_inv hy, ContinuousLinearEquiv.apply_symm_apply, ← pow_one (X i), evalSeries_X_pow,
    evalSeries_C', pow_one, Pi.sub_apply, sub_add_cancel]

/-- `T_a (x_i − x_i(a)) = X_i`. -/
theorem taylorHom_coord_sub (i : Fin n) :
    taylorHom E ψ φ ha hφ
      (coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) = X i := by
  rw [map_sub, taylorHom_coord, eval_coord, taylorHom_const, add_sub_cancel_right]

/-- Hadamard's lemma at the stalk, through the division of series by the coordinates: a germ
whose Taylor series has no constant term is `∑_i (x_i − x_i(a)) g_i`, where `T_a g_i` is the
`i`-th part of `T_a s`. -/
theorem exists_eq_sum_coord_mul_of_constantCoeff (s : (structureSheaf 𝕜 E M).presheaf.stalk a)
    (hs : constantCoeff (taylorHom E ψ φ ha hφ s) = 0) :
    ∃ g : Fin n → (structureSheaf 𝕜 E M).presheaf.stalk a,
      s = ∑ i, (coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) *
        g i ∧ ∀ i, taylorHom E ψ φ ha hφ (g i) = divPart i (taylorHom E ψ φ ha hφ s) := by
  have hg : ∀ i, ∃ g, taylorHom E ψ φ ha hφ g = divPart i (taylorHom E ψ φ ha hφ s) := fun i =>
    Set.mem_range.mp ((range_taylorHom E ψ φ ha hφ).ge
      (divPart_mem_conv (taylorHom_mem_conv E ψ φ ha hφ s) i))
  choose g hg using hg
  refine ⟨g, ?_, hg⟩
  apply IsTaylorHom.injective' E ψ φ ha (isTaylorHom_taylorHom E ψ φ ha hφ)
  rw [map_sum]
  simp_rw [map_mul, taylorHom_coord_sub, hg]
  exact (sum_X_mul_divPart hs).symm

/-- The Taylor homomorphism reflects the powers of the maximal ideal, `T_a s ∈ (X)^k ↔ s ∈ 𝔪_a^k`
(induction on `k` through the division by the coordinates). -/
theorem taylorHom_mem_maximalIdeal_pow_iff (s : (structureSheaf 𝕜 E M).presheaf.stalk a) (k : ℕ) :
    taylorHom E ψ φ ha hφ s ∈ maximalIdeal (MvPowerSeries (Fin n) 𝕜) ^ k ↔
      s ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k := by
  induction k generalizing s with
  | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ k ih =>
    constructor
    · intro hs
      have hs0 : constantCoeff (taylorHom E ψ φ ha hφ s) = 0 :=
        (mem_maximalIdeal_iff _).mp (Ideal.pow_le_self k.succ_ne_zero hs)
      obtain ⟨g, rfl, hg⟩ := exists_eq_sum_coord_mul_of_constantCoeff E ψ φ ha hφ s hs0
      rw [pow_succ']
      refine Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_mul (coord_sub_mem_maximalIdeal E ψ φ ha hφ i) ?_
      rw [← ih, hg]
      exact divPart_mem_maximalIdeal_pow hs i
    · intro hs
      have h1 : Ideal.map (taylorHom E ψ φ ha hφ)
          (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)) ≤
            maximalIdeal (MvPowerSeries (Fin n) 𝕜) := by
        rw [Ideal.map_le_iff_le_comap]
        intro t ht
        rw [Ideal.mem_comap, mem_maximalIdeal_iff,
          IsTaylorHom.constantCoeff' E ψ φ ha (isTaylorHom_taylorHom E ψ φ ha hφ)]
        exact (mem_maximalIdeal_iff_eval E t).mp ht
      have h2 := Ideal.mem_map_of_mem (taylorHom E ψ φ ha hφ) hs
      rw [Ideal.map_pow] at h2
      exact Ideal.pow_right_mono h1 _ h2

include ha hφ in
/-- The previous statement for any map satisfying the specification `IsTaylorHom`. -/
theorem IsTaylorHom.mem_maximalIdeal_pow_iff
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) (k : ℕ) :
    T s ∈ maximalIdeal (MvPowerSeries (Fin n) 𝕜) ^ k ↔
      s ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k := by
  obtain rfl := IsTaylorHom.eq E ψ φ hT (isTaylorHom_taylorHom E ψ φ ha hφ)
  exact taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ s k

include ha hφ in
/-- `T_a(𝔪_aᵏ) = (X)ᵏ ∩ T_a(𝒪_{M,a})` [BM97, (0.3)]. -/
theorem IsTaylorHom.image_maximalIdeal_pow
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) (k : ℕ) :
    T '' ↑(maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k) =
      ↑(maximalIdeal (MvPowerSeries (Fin n) 𝕜) ^ k) ∩ Set.range T := by
  ext c
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨(hT.mem_maximalIdeal_pow_iff E ψ φ ha hφ s k).mpr hs, s, rfl⟩
  · rintro ⟨hc, s, rfl⟩
    exact ⟨s, (hT.mem_maximalIdeal_pow_iff E ψ φ ha hφ s k).mp hc, rfl⟩

/-- Hadamard's lemma: a germ vanishing at `a` is `∑_i (x_i − x_i(a)) g_i`. -/
theorem exists_eq_sum_coord_mul' (s : (structureSheaf 𝕜 E M).presheaf.stalk a)
    (hs : eval 𝕜 E M a s = 0) :
    ∃ g : Fin n → (structureSheaf 𝕜 E M).presheaf.stalk a,
      s = ∑ i, (coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) *
        g i := by
  obtain ⟨g, hg, -⟩ := exists_eq_sum_coord_mul_of_constantCoeff E ψ φ ha hφ s (by
    rw [IsTaylorHom.constantCoeff' E ψ φ ha (isTaylorHom_taylorHom E ψ φ ha hφ), hs])
  exact ⟨g, hg⟩

/-- `𝔪_a = (x_1 − a_1, …, x_n − a_n)`. -/
theorem maximalIdeal_eq_span_coord' :
    maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) =
      Ideal.span (Set.range fun i =>
        coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) := by
  refine le_antisymm (fun s hs => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨g, rfl⟩ :=
      exists_eq_sum_coord_mul' E ψ φ ha hφ s ((mem_maximalIdeal_iff_eval E s).mp hs)
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact coord_sub_mem_maximalIdeal E ψ φ ha hφ i

/-- A product of powers of elements of `I` lies in the corresponding power of `I`. -/
theorem _root_.Ideal.prod_pow_mem_pow_sum {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*}
    (s : Finset ι) {y : ι → R} (hy : ∀ i, y i ∈ I) (ν : ι → ℕ) :
    ∏ i ∈ s, y i ^ ν i ∈ I ^ (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hy i) _) ih

/-- `𝔪_aᵏ` is generated by the monomials of degree `k` in the `x_i − a_i`. -/
theorem maximalIdeal_pow_eq_span_monomials' (k : ℕ) :
    maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k =
      Ideal.span (Set.range fun ν : {ν : Fin n →₀ ℕ // ν.degree = k} =>
        ∏ i, (coord E ψ φ hφ ha i -
          const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) ^ ν.1 i) := by
  classical
  set y : Fin n → (structureSheaf 𝕜 E M).presheaf.stalk a := fun i =>
    coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i)) with hy
  have hymem : ∀ i, y i ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) := fun i =>
    coord_sub_mem_maximalIdeal E ψ φ ha hφ i
  have hgen : ∀ (k : ℕ) (ν : Fin n →₀ ℕ), ν.degree = k →
      ∏ i, y i ^ ν i ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k := by
    intro k ν hν
    rw [← hν, Finsupp.degree_eq_sum]
    exact Ideal.prod_pow_mem_pow_sum _ _ hymem ν
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, eq_comm, Ideal.eq_top_iff_one]
    refine Ideal.subset_span ⟨⟨0, by simp⟩, ?_⟩
    simp
  | succ k ih =>
    refine le_antisymm (fun s hs => ?_) (Ideal.span_le.mpr ?_)
    · have hs' := (taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ s (k + 1)).mpr hs
      have hs0 : constantCoeff (taylorHom E ψ φ ha hφ s) = 0 :=
        (mem_maximalIdeal_iff _).mp (Ideal.pow_le_self k.succ_ne_zero hs')
      obtain ⟨g, rfl, hg⟩ := exists_eq_sum_coord_mul_of_constantCoeff E ψ φ ha hφ s hs0
      refine Ideal.sum_mem _ fun i _ => ?_
      have hgi : g i ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k := by
        rw [← taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ, hg]
        exact divPart_mem_maximalIdeal_pow hs' i
      rw [ih] at hgi
      change y i * g i ∈ _
      refine Submodule.span_induction (p := fun x _ => y i * x ∈ Ideal.span (Set.range fun
        ν : {ν : Fin n →₀ ℕ // ν.degree = k + 1} => ∏ j, y j ^ ν.1 j)) ?_ ?_ ?_ ?_ hgi
      · rintro _ ⟨ν, rfl⟩
        refine Ideal.subset_span ⟨⟨ν.1 + Finsupp.single i 1, ?_⟩, ?_⟩
        · rw [map_add, ν.2, Finsupp.degree_single]
        · simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
          rw [mul_comm]
          congr 1
          rw [Finset.prod_eq_single i]
          · rw [Finsupp.single_eq_same, pow_one]
          · intro j _ hj
            rw [Finsupp.single_apply, ite_eq_right (fun h => hj h.symm), pow_zero]
          · intro h
            exact absurd (Finset.mem_univ i) h
      · rw [mul_zero]
        exact zero_mem _
      · intro x z _ _ hx hz
        rw [mul_add]
        exact add_mem hx hz
      · intro r x _ hx
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hx
    · rintro _ ⟨ν, rfl⟩
      exact hgen (k + 1) ν.1 ν.2

end Manifold
