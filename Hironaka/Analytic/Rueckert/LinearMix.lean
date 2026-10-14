/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Germ.Coordinate
public import Hironaka.Analytic.Rueckert.Embed
public import Hironaka.Analytic.Rueckert.Subst
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Hironaka.Analytic.Rueckert.Reexpansion
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Mixing the fibre coordinates: a linear change making a linear form a coordinate

The primitive element produced by `PrimitiveRelations.lean` is a `ℂ`-linear combination
`∑ c_j x_j` of the fibre coordinates with `c_{i₀} = 1`, as in the primitive-element step of the
local parametrization theorem [Fre17, Ch. I, 8.2] (see also [GR84, Chapter 3, §1]). The linear
automorphism `mixLinear i₀ c` of `ℂⁿ` replaces the `i₀`-th coordinate by that linear form and
fixes the others; substituting it (`substConv`, `Subst.lean`) sends the coordinate series
`X_{i₀}` to `∑ c_j X_j`, fixes the other coordinate series, and fixes every series embedded from
the base along an injection `e` avoiding `i₀` (`convEmbed e`). These are the three identities the
coordinate transport of the parametrization theorem needs; all proved through the function-level
characterization `Conv.ext_of_evalSeries_eventuallyEq`.
-/

@[expose] public section

open Filter Topology

namespace Analytic

variable {n d : ℕ}

/-- The linear map `x ↦ (x with x_{i₀} replaced by ∑ c_j x_j)`. -/
noncomputable def mixFwd (i₀ : Fin n) (c : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := by
  classical
  exact LinearMap.pi fun i => if i = i₀ then ∑ j, c j • LinearMap.proj j else LinearMap.proj i

/-- The inverse of `mixFwd` when `c i₀ = 1`:
`x ↦ (x with x_{i₀} replaced by x_{i₀} − ∑_{j ≠ i₀} c_j x_j)`. -/
noncomputable def mixBwd (i₀ : Fin n) (c : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := by
  classical
  exact LinearMap.pi fun i =>
    if i = i₀ then LinearMap.proj i₀ - ∑ j ∈ Finset.univ.erase i₀, c j • LinearMap.proj j
    else LinearMap.proj i

/-- The coordinates of `mixFwd`. -/
theorem mixFwd_apply (i₀ : Fin n) (c : Fin n → ℂ) (x : Fin n → ℂ) (i : Fin n) :
    mixFwd i₀ c x i = if i = i₀ then ∑ j, c j * x j else x i := by
  classical
  simp only [mixFwd, LinearMap.pi_apply]
  split_ifs <;> simp

/-- The coordinates of `mixBwd`. -/
theorem mixBwd_apply (i₀ : Fin n) (c : Fin n → ℂ) (x : Fin n → ℂ) (i : Fin n) :
    mixBwd i₀ c x i = if i = i₀ then x i₀ - ∑ j ∈ Finset.univ.erase i₀, c j * x j else x i := by
  classical
  simp only [mixBwd, LinearMap.pi_apply]
  split_ifs <;> simp

/-- The linear automorphism of `ℂⁿ` replacing `x_{i₀}` by the linear form `∑ c_j x_j`
(`c i₀ = 1`) and fixing the other coordinates, as a continuous linear equivalence (the type
`substEquiv` takes). -/
noncomputable def mixLinear (i₀ : Fin n) (c : Fin n → ℂ) (hc : c i₀ = 1) :
    (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofLinearMap (mixFwd i₀ c) (mixBwd i₀ c)
    (LinearMap.ext fun x => funext fun i => by
      classical
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mixFwd_apply, mixBwd_apply]
      by_cases hi : i = i₀
      · subst hi
        simp only [ite_true]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hc, one_mul]
        have : ∀ j ∈ Finset.univ.erase i,
            c j * (if j = i then x i - ∑ k ∈ Finset.univ.erase i, c k * x k else x j) =
              c j * x j :=
          fun j hj => by rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
        rw [Finset.sum_congr rfl this]; simp only [ite_true]; ring
      · simp [hi])
    (LinearMap.ext fun x => funext fun i => by
      classical
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mixFwd_apply, mixBwd_apply]
      by_cases hi : i = i₀
      · subst hi
        simp only [ite_true]
        have : ∀ j ∈ Finset.univ.erase i,
            c j * (if j = i then ∑ k, c k * x k else x j) = c j * x j :=
          fun j hj => by rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
        rw [Finset.sum_congr rfl this, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hc,
          one_mul]
        ring
      · simp [hi]))

/-- The coordinates of `mixLinear`, as a continuous linear map. -/
theorem mixLinear_apply (i₀ : Fin n) (c : Fin n → ℂ) (hc : c i₀ = 1) (x : Fin n → ℂ) (i : Fin n) :
    (mixLinear i₀ c hc : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) x i =
      if i = i₀ then ∑ j, c j * x j else x i := by
  rw [ContinuousLinearEquiv.coe_coe]
  simp only [mixLinear, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_ofLinearMap,
    mixFwd_apply]

/-- Substituting `mixLinear` sends the coordinate series `X_{i₀}` to the linear form
`∑ c_j X_j`. -/
theorem substConv_mixLinear_convX_self (i₀ : Fin n) (c : Fin n → ℂ) (hc : c i₀ = 1) :
    substConv (mixLinear i₀ c hc : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (convX ℂ i₀) =
      ∑ j, algebraMap ℂ (Conv ℂ n) (c j) * convX ℂ j := by
  refine Conv.ext_of_evalSeries_eventuallyEq ((evalSeries_substConv _ _).trans ?_)
  refine EventuallyEq.trans ?_ (evalSeries_conv_sum_eventually Finset.univ _).symm
  have h1 : ∀ j : Fin n, evalSeries ((algebraMap ℂ (Conv ℂ n) (c j) * convX ℂ j : Conv ℂ n) :
      MvPowerSeries (Fin n) ℂ) =ᶠ[𝓝 (0 : Fin n → ℂ)] fun x => c j * x j := fun j =>
    (evalSeries_conv_mul_eventually _ _).trans (Eventually.of_forall fun x => by
      simp only [evalSeries_algebraMap_conv, evalSeries_convX])
  refine ((Filter.eventually_all.2 h1).mono fun x hx => ?_)
  simp only [Function.comp_apply, evalSeries_convX, mixLinear_apply, ite_true]
  exact (Finset.sum_congr rfl fun j _ => (hx j).symm)

/-- Substituting `mixLinear` fixes the coordinate series `X_i`, `i ≠ i₀`. -/
theorem substConv_mixLinear_convX_of_ne (i₀ : Fin n) (c : Fin n → ℂ) (hc : c i₀ = 1) {i : Fin n}
    (hi : i ≠ i₀) :
    substConv (mixLinear i₀ c hc : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (convX ℂ i) = convX ℂ i := by
  refine Conv.ext_of_evalSeries_eventuallyEq
    ((evalSeries_substConv _ _).trans (Eventually.of_forall fun x => ?_))
  simp only [Function.comp_apply, evalSeries_convX, mixLinear_apply, ite_eq_right hi]

/-- Substituting `mixLinear` fixes every series embedded from the base along an injection `e`
whose range avoids `i₀` (the base coordinates are untouched). -/
theorem substConv_mixLinear_convEmbed (i₀ : Fin n) (c : Fin n → ℂ) (hc : c i₀ = 1)
    (e : Fin d ↪ Fin n) (hi₀ : i₀ ∉ Set.range e) (a : Conv ℂ d) :
    substConv (mixLinear i₀ c hc : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (convEmbed ℂ e a) =
      convEmbed ℂ e a := by
  refine Conv.ext_of_evalSeries_eventuallyEq
    ((evalSeries_substConv _ _).trans (Eventually.of_forall fun x => ?_))
  simp only [Function.comp_apply, evalSeries_convEmbed]
  congr 1
  funext j
  simp only [Function.comp_apply, mixLinear_apply]
  rw [ite_eq_right]
  exact fun h => hi₀ ⟨j, h⟩

end Analytic
