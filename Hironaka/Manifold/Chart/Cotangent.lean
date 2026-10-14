/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Chart.Basic
public import Hironaka.Manifold.Germ.CoordDeriv
public import Hironaka.Manifold.Germ.TaylorHom
public import Hironaka.Manifold.Submanifold
import Hironaka.Algebra.Local.PowerSeries
import Hironaka.Manifold.Chart.Adapted
import Hironaka.Manifold.Chart.Independence
import Hironaka.Manifold.Chart.Order
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.IdealSheaf.Order
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Independent differentials and the cotangent space `𝔪_a / 𝔪_a²`

For sections `z_1, …, z_c` of `𝒪_M` near `a`, their differentials at `a` are linearly independent
iff the classes of `z_i − z_i(a)` in `𝔪_a / 𝔪_a²` are linearly independent over `𝕜`
(`hasIndependentDifferentialsAt_iff_linearIndependent_cotangentClass'`). This is the
identification of the differentials of functions with the cotangent space of the local ring, as in
Kollár's local coordinates and their derivations [Kol07, Definition 73] and Bierstone–Milman's
regular coordinate charts [BM97, (0.3)]. The bridge is the *linear part* of a germ in a chart — the
degree-one coefficients of its Taylor series — a `𝕜`-linear map `𝒪_{M,a} → 𝕜^n` which kills the
constants and `𝔪_a²` and detects `𝔪_a²` inside `𝔪_a` (Hadamard: a germ vanishing at `a` with
vanishing first derivatives has Taylor order `≥ 2`, `taylorHom_mem_maximalIdeal_pow_iff`), so that
a `𝕜`-combination of classes vanishes iff the same combination of linear parts does; and the linear
part of the germ of a section is the vector of values of its chart derivative on the basis
`ψ⁻¹(e_j)` (`eval_coordDerivStalk_germ`), whose independence is the independence of the chart
derivatives themselves (`linearIndependent_fderiv_chart_iff'`). This is the form in which the
independence of differentials is passed to the analytic spaces
(`Hironaka/AnalyticSpace/Differential.lean`) and to the common-chart constructions of maximal
contact.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

section LinearPart

variable (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M}
  (ha : a ∈ φ.source)

/-- The linear part of a germ in the chart `φ`: the degree-one coefficients of its Taylor series,
as a `𝕜`-linear map `𝒪_{M,a} → 𝕜^n`. -/
def linearPart : (structureSheaf 𝕜 E M).presheaf.stalk a →ₗ[𝕜] (Fin n → 𝕜) where
  toFun s := fun i => MvPowerSeries.coeff (Finsupp.single i 1) (taylorHom E ψ φ ha hφ s)
  map_add' s t := by
    ext i
    simp [map_add]
  map_smul' c s := by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def, algebraMap_stalk_eq, map_mul, taylorHom_const, MvPowerSeries.coeff_C_mul]

theorem linearPart_apply (s : (structureSheaf 𝕜 E M).presheaf.stalk a) (i : Fin n) :
    linearPart E ψ φ hφ ha s i =
      MvPowerSeries.coeff (Finsupp.single i 1) (taylorHom E ψ φ ha hφ s) :=
  rfl

/-- The linear part kills the constants. -/
theorem linearPart_const (c : 𝕜) : linearPart E ψ φ hφ ha (const 𝕜 E M a c) = 0 := by
  ext i
  rw [linearPart_apply, taylorHom_const, MvPowerSeries.coeff_C, ite_eq_right (by simp)]
  rfl

/-- The linear part kills `𝔪_a²` (the Taylor series has order `≥ 2`). -/
theorem linearPart_eq_zero_of_mem_sq {s : (structureSheaf 𝕜 E M).presheaf.stalk a}
    (hs : s ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ 2) :
    linearPart E ψ φ hφ ha s = 0 := by
  have h2 : ((2 : ℕ) : ℕ∞) ≤ (taylorHom E ψ φ ha hφ s).order := by
    have := (taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ s 2).mpr hs
    rwa [mem_maximalIdeal_pow_iff_le_ordElem, MvPowerSeries.ordElem_eq_order] at this
  ext i
  rw [linearPart_apply, Pi.zero_apply]
  apply MvPowerSeries.coeff_of_lt_order
  rw [Finsupp.degree_single]
  exact lt_of_lt_of_le (by exact_mod_cast one_lt_two) h2

/-- Hadamard: a germ vanishing at `a` with vanishing linear part lies in `𝔪_a²`. -/
theorem mem_sq_of_linearPart_eq_zero {s : (structureSheaf 𝕜 E M).presheaf.stalk a}
    (hs : s ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
    (h : linearPart E ψ φ hφ ha s = 0) :
    s ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ 2 := by
  rw [← taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ s 2,
    mem_maximalIdeal_pow_iff_le_ordElem, MvPowerSeries.ordElem_eq_order]
  apply MvPowerSeries.le_order
  intro d hd
  have hd' : Finsupp.degree d < 2 := by exact_mod_cast hd
  rcases Nat.lt_or_ge (Finsupp.degree d) 1 with h0 | h1
  · rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at h0
    subst h0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      IsTaylorHom.constantCoeff' E ψ φ ha (isTaylorHom_taylorHom E ψ φ ha hφ)]
    exact (mem_maximalIdeal_iff_eval E s).mp hs
  · have h1' : Finsupp.degree d = 1 := by omega
    obtain ⟨i, rfl⟩ := (Finsupp.degree_eq_one_iff d).mp h1'
    exact congrFun h i

/-- `s ↦ [s − s(a)] ∈ 𝔪_a / 𝔪_a²` as a `𝕜`-linear map. -/
def cotangentClassₗ (a : M) :
    (structureSheaf 𝕜 E M).presheaf.stalk a →ₗ[𝕜]
      (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)).Cotangent where
  toFun s := cotangentClass E a s
  map_add' s t := by
    unfold cotangentClass
    rw [← map_add]
    congr 1
    ext
    simp only [Submodule.coe_add, map_add]
    ring
  map_smul' c s := by
    unfold cotangentClass
    rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]
    congr 1
    ext
    simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, algebraMap_stalk_eq, map_mul,
      eval_const]
    ring

theorem cotangentClassₗ_apply (a : M) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    cotangentClassₗ E a s = cotangentClass E a s := rfl

/-- The class of `s − s(a)` vanishes iff `s − s(a) ∈ 𝔪_a²` iff the linear part of `s`
vanishes. -/
theorem cotangentClass_eq_zero_iff_linearPart (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    cotangentClass E a s = 0 ↔ linearPart E ψ φ hφ ha s = 0 := by
  unfold cotangentClass
  rw [Ideal.toCotangent_eq_zero]
  have hmem : s - const 𝕜 E M a (eval 𝕜 E M a s) ∈
      maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
    (mem_maximalIdeal_iff_eval E _).mpr (by simp [map_sub])
  have hlp : linearPart E ψ φ hφ ha (s - const 𝕜 E M a (eval 𝕜 E M a s)) =
      linearPart E ψ φ hφ ha s := by
    rw [map_sub, linearPart_const, sub_zero]
  constructor
  · intro h
    rw [← hlp]
    exact linearPart_eq_zero_of_mem_sq E ψ φ hφ ha h
  · intro h
    exact mem_sq_of_linearPart_eq_zero E ψ φ hφ ha hmem (hlp.trans h)

/-- A family of germs has linearly independent cotangent classes iff it has linearly independent
linear parts. -/
theorem linearIndependent_cotangentClass_iff_linearPart {ι : Type*} [Finite ι]
    (s : ι → (structureSheaf 𝕜 E M).presheaf.stalk a) :
    LinearIndependent 𝕜 (fun i => cotangentClass E a (s i)) ↔
      LinearIndependent 𝕜 (fun i => linearPart E ψ φ hφ ha (s i)) := by
  let _i : Fintype ι := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  refine forall_congr' fun g => imp_congr_left ?_
  have h1 : ∑ i, g i • cotangentClass E a (s i) = cotangentClass E a (∑ i, g i • s i) := by
    rw [← cotangentClassₗ_apply, map_sum]
    simp only [map_smul, cotangentClassₗ_apply]
  have h2 : ∑ i, g i • linearPart E ψ φ hφ ha (s i) = linearPart E ψ φ hφ ha (∑ i, g i • s i) := by
    rw [map_sum]
    simp only [map_smul]
  rw [h1, h2]
  exact cotangentClass_eq_zero_iff_linearPart E ψ φ hφ ha _

end LinearPart

/-- A continuous linear functional on `E` is determined by its values on the basis `ψ⁻¹(e_j)`. -/
theorem _root_.ContinuousLinearMap.ext_of_symm_single {L L' : E →L[𝕜] 𝕜}
    (h : ∀ j, L (ψ.symm (Pi.single j 1)) = L' (ψ.symm (Pi.single j 1))) : L = L' := by
  have hpi : ((L.comp (ψ.symm : (Fin n → 𝕜) →L[𝕜] E) : (Fin n → 𝕜) →L[𝕜] 𝕜) :
      (Fin n → 𝕜) →ₗ[𝕜] 𝕜) = (L'.comp (ψ.symm : (Fin n → 𝕜) →L[𝕜] E) : (Fin n → 𝕜) →ₗ[𝕜] 𝕜) := by
    apply LinearMap.pi_ext
    intro j x
    have : Pi.single j x = x • Pi.single j (1 : 𝕜) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    simp [this, h j]
  have hpi' : L.comp (ψ.symm : (Fin n → 𝕜) →L[𝕜] E) = L'.comp (ψ.symm : (Fin n → 𝕜) →L[𝕜] E) :=
    ContinuousLinearMap.coe_injective hpi
  have e1 : L = (L.comp (ψ.symm : (Fin n → 𝕜) →L[𝕜] E)).comp (ψ : E →L[𝕜] (Fin n → 𝕜)) := by
    ext v
    simp
  have e2 : L' = (L'.comp (ψ.symm : (Fin n → 𝕜) →L[𝕜] E)).comp (ψ : E →L[𝕜] (Fin n → 𝕜)) := by
    ext v
    simp
  rw [e1, e2, hpi']

/-- Evaluation of functionals on the basis `ψ⁻¹(e_j)`, an injective `𝕜`-linear map
`(E →L[𝕜] 𝕜) → 𝕜^n`. -/
def evalBasis : (E →L[𝕜] 𝕜) →ₗ[𝕜] (Fin n → 𝕜) :=
  LinearMap.pi fun j =>
    (ContinuousLinearMap.apply 𝕜 𝕜 (ψ.symm (Pi.single j 1)) : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜)

theorem evalBasis_apply (L : E →L[𝕜] 𝕜) (j : Fin n) :
    evalBasis E ψ L j = L (ψ.symm (Pi.single j 1)) := rfl

theorem ker_evalBasis : LinearMap.ker (evalBasis E ψ) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro L L' h
  exact ContinuousLinearMap.ext_of_symm_single E ψ fun j => congrFun h j

variable [FiniteDimensional 𝕜 E] [IsManifold 𝓘(𝕜, E) ω M]

omit ψ in
/-- For sections of `𝒪_M` near `a`, independence of the differentials at `a` is the linear
independence over `𝕜` of their classes in `𝔪_a / 𝔪_a²` ([BM97, (0.3)]; [Kol07, Definition 73]). -/
theorem hasIndependentDifferentialsAt_iff_linearIndependent_cotangentClass' {U : Opens M}
    {a : M} (ha : a ∈ U) {c : ℕ} (z : Fin c → (structureSheaf 𝕜 E M).presheaf.obj (op U)) :
    HasIndependentDifferentialsAt E (fun i => extendSection 𝕜 E (z i)) a ↔
      LinearIndependent 𝕜 fun i =>
        cotangentClass E a ((structureSheaf 𝕜 E M).presheaf.germ U a ha (z i)) := by
  set χ := chartAt E a with hχdef
  have hχ : χ ∈ maximalAtlas 𝓘(𝕜, E) ω M := IsManifold.chart_mem_maximalAtlas a
  have haχ : a ∈ χ.source := mem_chart_source E a
  set ψ := IdealSheaf.modelCoord (𝕜 := 𝕜) (E := E)
  rw [linearIndependent_cotangentClass_iff_linearPart E ψ χ hχ haχ,
    linearIndependent_fderiv_chart_iff' hχ haχ]
  have hlp : ∀ i, linearPart E ψ χ hχ haχ ((structureSheaf 𝕜 E M).presheaf.germ U a ha (z i)) =
      evalBasis E ψ (fderiv 𝕜 (extendSection 𝕜 E (z i) ∘ χ.symm) (χ a)) := fun i => by
    ext j
    rw [linearPart_apply, ← eval_coordDerivStalk, eval_coordDerivStalk_germ, evalBasis_apply]
  simp_rw [hlp]
  exact (LinearMap.linearIndependent_iff (evalBasis E ψ) (ker_evalBasis E ψ)).symm

end Manifold

end
