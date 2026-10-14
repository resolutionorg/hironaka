/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# The embedding of `Conv K d` along an injection of the coordinates

For an injection `e : Fin d ↪ Fin n` the series in the variables `x_{e 0}, …, x_{e (d-1)}` form
the subring `convEmbed K e (Conv K d) ⊆ Conv K n`: renaming the variables along `e` preserves the
majorant norms (`‖rename e f‖_ρ = ‖f‖_{ρ ∘ e}`, the general form of `convNorm_liftTail`), so a
convergent series stays convergent. This is the inclusion `𝒪_d ⊆ 𝒪_n` of Noether normalization
for analytic algebras (`NoetherNormalization.lean`): after a linear change of coordinates,
`𝒪_d → 𝒪_n / I` is finite and injective for a suitable choice of `d` coordinates. `convTail` is
the case `e = Fin.succ`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MvPowerSeries Finsupp

namespace Analytic

variable {K : Type*} [RCLike K] {d n : ℕ}

/-- Renaming the variables along an injection preserves the majorant norm,
`‖rename e f‖_ρ = ‖f‖_{ρ ∘ e}` (the general form of `convNorm_liftTail`). -/
theorem convNorm_rename (e : Fin d ↪ Fin n) (ρ : Fin n → ℝ≥0) (f : MvPowerSeries (Fin d) K) :
    ConvNorm ρ (rename e f) = ConvNorm (fun i => ρ (e i)) f := by
  unfold ConvNorm
  refine (Function.Injective.tsum_eq (f := fun μ : Fin n →₀ ℕ =>
    ‖coeff μ (rename e f)‖ₑ * (monomialEval ρ μ : ℝ≥0∞)) (embDomain_injective e) ?_).symm.trans
    (tsum_congr fun x => ?_)
  · intro μ hμ
    by_contra hμ'
    apply hμ
    have : coeff μ (rename e f) = 0 := by
      refine coeff_rename_eq_zero e f fun ⟨x, hx⟩ => hμ' ⟨x, ?_⟩
      rw [embDomain_eq_mapDomain, hx]
    simp [this]
  · rw [coeff_embDomain_rename]
    congr 2
    unfold monomialEval
    rw [prod_embDomain]

/-- A convergent series stays convergent under a renaming of the variables along an injection
(extend the radius vector by `1` off the image). -/
theorem rename_mem_conv (e : Fin d ↪ Fin n) {f : MvPowerSeries (Fin d) K} (hf : f ∈ Conv K d) :
    rename e f ∈ Conv K n := by
  classical
  obtain ⟨ρ, hρ⟩ := hf
  let ρ' : Fin n → ℝ≥0 := fun j => if h : ∃ i, e i = j then ρ h.choose else 1
  have hρ' : ∀ i, ρ' (e i) = ρ i := fun i => by
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [ρ', dite_eq_left h]
    rw [e.injective h.choose_spec]
  refine ⟨⟨ρ', fun j => ?_⟩, ?_⟩
  · by_cases h : ∃ i, e i = j
    · simp only [ρ', dite_eq_left h]
      exact ρ.pos _
    · simp only [ρ', dite_eq_right h]
      exact one_pos
  · change ConvNorm ρ' (rename e f) ≠ ⊤
    rw [convNorm_rename]
    have : (fun i => ρ' (e i)) = ⇑ρ := funext hρ'
    rw [this]
    exact hρ

variable (K) in
/-- **The embedding `𝒪_d → 𝒪_n` along an injection of the coordinates**,
`convEmbed K e : Conv K d →ₐ[K] Conv K n`, `f ↦ f(x_{e 0}, …, x_{e (d-1)})`. -/
noncomputable def convEmbed (e : Fin d ↪ Fin n) : Conv K d →ₐ[K] Conv K n :=
  AlgHom.codRestrict ((rename e).comp (Conv K d).val) (Conv K n) fun c => rename_mem_conv e c.2

@[simp] theorem coe_convEmbed (e : Fin d ↪ Fin n) (c : Conv K d) :
    (convEmbed K e c : MvPowerSeries (Fin n) K) = rename e c :=
  rfl

/-- The embedding is injective. -/
theorem convEmbed_injective (e : Fin d ↪ Fin n) : Function.Injective (convEmbed K e) := by
  intro c c' h
  have h' := congrArg (fun c : Conv K n => (c : MvPowerSeries (Fin n) K)) h
  simp only [coe_convEmbed] at h'
  exact Subtype.ext (rename_injective e h')

end Analytic
