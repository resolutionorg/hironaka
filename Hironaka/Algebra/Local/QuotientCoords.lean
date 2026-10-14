/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Coords
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem

/-!
# The hypersurface `x₁ = 0` as a coordinate ring

Kollár picks local coordinates `x₁, …, xₙ` with `S = (x₁ = 0)` and notes that
`∂f/∂xᵢ |_S = ∂(f|_S)/∂xᵢ` for `i > 1`, "but `∂(f|_S)/∂x₁` does not even make sense"
[Kol07, 87].  In the local model: `R̄ := R/⟨x₁⟩` is a regular local ring
(`isRegularLocalRing_quotient_span_image_lt` of `Hironaka/Algebra/Local/RegularSystem.lean`) with
coordinates `x̄₂, …, x̄ₙ` and derivations `∂̄ⱼ` (`j ≥ 2`) induced by `∂ⱼ`, which preserve `⟨x₁⟩`
because `∂ⱼ x₁ = 0`; `∂̄ⱼ x̄ₗ = δⱼₗ`; so `R̄` carries a `RegularCoords` structure on `n − 1`
coordinates, and `(∂ⱼ f)‾ = ∂̄ⱼ f̄`.

Kollár's `x₁` is any coordinate `x_{i₀}`; the other coordinates are enumerated by
`Fin.succAbove i₀`.  The general descent of a derivation to a quotient by an invariant ideal is
`Derivation.quotientOfMapLE`.  The structure `quotientCoords` is the setting of the restriction
(87.1) in `Hironaka/Algebra/Local/LogDeriv.lean`.
-/

@[expose] public section

namespace Derivation

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (D : Derivation k R R) (J : Ideal R)

/-- The `k`-linear map `R/J → R/J` induced by a derivation `D` with `D(J) ⊆ J`. -/
noncomputable def quotientLinear (hJ : ∀ f ∈ J, D f ∈ J) : (R ⧸ J) →ₗ[k] (R ⧸ J) :=
  (Submodule.Quotient.restrictScalarsEquiv k J).toLinearMap ∘ₗ
    (J.restrictScalars k).mapQ (J.restrictScalars k) D.toLinearMap (fun f hf => hJ f hf) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k J).symm.toLinearMap

theorem quotientLinear_mk (hJ : ∀ f ∈ J, D f ∈ J) (f : R) :
    D.quotientLinear J hJ (Ideal.Quotient.mk J f) = Ideal.Quotient.mk J (D f) := by
  simp only [quotientLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, ← Ideal.Quotient.mk_eq_mk,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  rfl

/-- A derivation `D` of `R` with `D(J) ⊆ J` descends to a derivation `D̄` of `R/J` with
`D̄ (f̄) = (D f)‾`. -/
noncomputable def quotientOfMapLE (hJ : ∀ f ∈ J, D f ∈ J) : Derivation k (R ⧸ J) (R ⧸ J) :=
  Derivation.mk' (D.quotientLinear J hJ) fun a b => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, quotientLinear_mk, quotientLinear_mk, quotientLinear_mk, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]

@[simp] theorem quotientOfMapLE_mk (hJ : ∀ f ∈ J, D f ∈ J) (f : R) :
    D.quotientOfMapLE J hJ (Ideal.Quotient.mk J f) = Ideal.Quotient.mk J (D f) :=
  D.quotientLinear_mk J hJ f

end Derivation

namespace IsLocalRing

open IsLocalRing Ideal

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {k : ℕ}
  (c : RegularCoords R (k + 1)) (i₀ : Fin (k + 1))

/-- `∂ⱼ` preserves `⟨x_{i₀}⟩` for `j ≠ i₀`, because `∂ⱼ x_{i₀} = 0`. -/
theorem pderiv_mem_span_x_of_ne {j : Fin (k + 1)} (hj : j ≠ i₀) {f : R}
    (hf : f ∈ span {c.x i₀}) : c.pderiv j f ∈ span {c.x i₀} := by
  obtain ⟨g, rfl⟩ := mem_span_singleton.mp hf
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, c.pderiv_x, ite_eq_right hj, mul_zero, add_zero]
  exact mem_span_singleton.mpr (dvd_mul_right _ _)

/-- The induced derivation `∂̄ⱼ` of `R̄ = R/⟨x_{i₀}⟩`, from `∂_{σ j}` with
`σ = Fin.succAbove i₀`. -/
noncomputable def quotientPderiv (j : Fin k) :
    Derivation ℚ (R ⧸ span {c.x i₀}) (R ⧸ span {c.x i₀}) :=
  (c.pderiv (i₀.succAbove j)).quotientOfMapLE _ fun _ hf =>
    c.pderiv_mem_span_x_of_ne i₀ (Fin.succAbove_ne i₀ j) hf

/-- `(∂_{σ j} f)‾ = ∂̄ⱼ f̄`: Kollár's `∂f/∂xᵢ |_S = ∂(f|_S)/∂xᵢ` for `i > 1` [Kol07, 87]. -/
@[simp] theorem quotientPderiv_mk (j : Fin k) (f : R) :
    c.quotientPderiv i₀ j (Ideal.Quotient.mk (span {c.x i₀}) f) =
      Ideal.Quotient.mk (span {c.x i₀}) (c.pderiv (i₀.succAbove j) f) :=
  Derivation.quotientOfMapLE_mk _ _ _ f

/-- The permutation of the coordinates putting `x_{i₀}` first: `0 ↦ i₀`,
`j.succ ↦ i₀.succAbove j`. -/
def shiftPerm : Equiv.Perm (Fin (k + 1)) := (finSuccEquiv k).trans (finSuccEquiv' i₀).symm

@[simp] theorem shiftPerm_zero : shiftPerm i₀ 0 = i₀ := by
  simp [shiftPerm]

@[simp] theorem shiftPerm_succ (j : Fin k) : shiftPerm i₀ j.succ = i₀.succAbove j := by
  simp [shiftPerm]

theorem span_x_shiftPerm : maximalIdeal R = span (Set.range (c.x ∘ shiftPerm i₀)) := by
  rw [c.span_x, (shiftPerm i₀).surjective.range_comp]

theorem span_image_lt_one :
    span ((c.x ∘ shiftPerm i₀) '' {j : Fin (k + 1) | j.val < 1}) = span {c.x i₀} := by
  have hset : {j : Fin (k + 1) | j.val < 1} = {0} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Fin.ext_iff, Fin.val_zero]
    omega
  rw [hset, Set.image_singleton, Function.comp_apply, shiftPerm_zero]

/-- `R̄ = R/⟨x_{i₀}⟩` is a regular local ring (the quotient by a member of a regular system of
parameters). -/
instance isRegularLocalRing_quotient_span_x : IsRegularLocalRing (R ⧸ span {c.x i₀}) :=
  c.span_image_lt_one i₀ ▸
    isRegularLocalRing_quotient_span_image_lt (c.x ∘ shiftPerm i₀) (c.span_x_shiftPerm i₀) c.card 1

theorem ringKrullDim_quotient_span_x_add_one :
    ringKrullDim (R ⧸ span {c.x i₀}) + 1 = ringKrullDim R := by
  have h := ringKrullDim_quotient_span_image_lt (c.x ∘ shiftPerm i₀) (c.span_x_shiftPerm i₀) c.card
    (i := 1) (by omega)
  rw [c.span_image_lt_one i₀, Nat.cast_one] at h
  exact h

theorem withBot_eq_natCast_of_add_one_eq {d : WithBot ℕ∞} {m : ℕ}
    (h : d + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : d = (m : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← WithBot.coe_natCast] at h
    exact (WithBot.bot_ne_coe h).elim
  | coe e =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    induction e using ENat.recTopCoe with
    | top =>
      rw [top_add] at h
      exact absurd h.symm (ENat.natCast_ne_top _)
    | coe a =>
      have ha : a = m := by
        have h' : a + 1 = m + 1 := by exact_mod_cast h
        omega
      subst ha
      exact WithBot.coe_natCast a

/-- `dim R̄ = n − 1`. -/
theorem card_quotient_span_x : (k : WithBot ℕ∞) = ringKrullDim (R ⧸ span {c.x i₀}) :=
  (withBot_eq_natCast_of_add_one_eq
    ((c.ringKrullDim_quotient_span_x_add_one i₀).trans c.card.symm)).symm

/-- The classes `x̄_{σ j}` generate the maximal ideal of `R̄`. -/
theorem maximalIdeal_quotient_span_x :
    maximalIdeal (R ⧸ span {c.x i₀}) =
      span (Set.range fun j : Fin k =>
        Ideal.Quotient.mk (span {c.x i₀}) (c.x (i₀.succAbove j))) := by
  have h := map_maximalIdeal_quotient_span_image_lt (c.x ∘ shiftPerm i₀) (c.span_x_shiftPerm i₀) 1
  rw [c.span_image_lt_one i₀] at h
  rw [maximalIdeal_quotient_eq_map, h]
  refine congrArg span (Set.ext fun g => ?_)
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj0 : j ≠ 0 := by
      intro h0
      subst h0
      simp at hj
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
    exact ⟨j', by simp⟩
  · rintro ⟨j', rfl⟩
    exact ⟨j'.succ, by simp, by simp⟩

/-- **The coordinate structure on the hypersurface ring** `R̄ = R/⟨x_{i₀}⟩`, with coordinates
`x̄_{σ j}` and derivations `∂̄ⱼ`, where `σ = Fin.succAbove i₀` (Kollár's coordinates on
`S = (x₁ = 0)`, [Kol07, 87]). -/
noncomputable def quotientCoords : RegularCoords (R ⧸ span {c.x i₀}) k where
  x j := Ideal.Quotient.mk (span {c.x i₀}) (c.x (i₀.succAbove j))
  pderiv j := c.quotientPderiv i₀ j
  span_x := c.maximalIdeal_quotient_span_x i₀
  card := c.card_quotient_span_x i₀
  pderiv_x j l := by
    rw [quotientPderiv_mk, c.pderiv_x]
    by_cases hjl : j = l
    · subst hjl
      simp
    · rw [ite_eq_right (fun h => hjl (Fin.succAbove_right_inj.mp h)), ite_eq_right hjl, map_zero]
  pderiv_comm j l f := by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective f
    simp only [quotientPderiv_mk, c.pderiv_comm]

@[simp] theorem quotientCoords_x (j : Fin k) :
    (c.quotientCoords i₀).x j = Ideal.Quotient.mk (span {c.x i₀}) (c.x (i₀.succAbove j)) := rfl

@[simp] theorem quotientCoords_pderiv (j : Fin k) :
    (c.quotientCoords i₀).pderiv j = c.quotientPderiv i₀ j := rfl

/-- The compatibility clause `∂̄ⱼ (f̄) = (∂_{σ j} f)‾`, in the form the restriction of D-balanced
ideals takes as a hypothesis. -/
theorem quotientCoords_pderiv_mk (j : Fin k) (f : R) :
    (c.quotientCoords i₀).pderiv j (Ideal.Quotient.mk (span {c.x i₀}) f) =
      Ideal.Quotient.mk (span {c.x i₀}) (c.pderiv (i₀.succAbove j) f) :=
  c.quotientPderiv_mk i₀ j f

end RegularCoords

end IsLocalRing
