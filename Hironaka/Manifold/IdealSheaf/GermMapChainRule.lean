/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Germ.CoordDerivCoords
import Hironaka.Algebra.Local.Completion
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The chain rule for germs along an analytic map

Kollár computes the derivatives of the transform of an ideal "using the chain rule" [Kol07, 75].
On the stalks this is the following identity: for an analytic map `f : M' → M`, a chart `φ` of
`M` at `f b` with coordinates `x_k` and any `𝕜`-derivation `δ` of `𝒪_{M', b}`,
`δ(s ∘ f) = ∑_k δ((x_k − x_k(f b)) ∘ f) · (∂_k s) ∘ f` for every germ `s` at `f b`
(`derivation_germMap_eq_sum_coordDerivStalk`; `s ∘ f` is the germ map `germMap`).

The proof is the Taylor-uniqueness argument of `derivation_eq_sum_coordDerivStalk`
(`Hironaka/Manifold/Germ/CoordDerivCoords.lean`) rerun for the "derivation along `f`"
`F(s) := δ(s ∘ f) − ∑_k δ(x_k ∘ f) · (∂_k s) ∘ f`: `F` is additive, satisfies the Leibniz rule
`F(st) = (s ∘ f) F(t) + (t ∘ f) F(s)`, kills the constants and the centred coordinates, hence
every polynomial in the coordinates; and `F` lowers the order by one
(`F(𝔪_{f b}^{k+1}) ⊆ 𝔪_b^k`, because the germ map is a local homomorphism and derivations lower
the order). Every germ is a polynomial in the coordinates up to `𝔪^{k+1}`, so
`F(s) ∈ ⋂_k 𝔪_b^k = 0`. Not in the sources as a separate statement. It is used to transport
derivations along germ maps (`Hironaka/Resolution/Analytic/MaximalContact/StalkEquiv.lean`) and to
compute derivative ideals in the charts of a blow-up
(`Hironaka/Manifold/BlowUp/Transform/DerivChart.lean`).
-/

public section

noncomputable section

open TopologicalSpace IsLocalRing
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] (f : M' → M)
  (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω f)

omit ψ in
/-- The germ map of an analytic map is a `𝕜`-algebra map: constants pull back to constants. -/
theorem germMap_algebraMap (b : M') (a : 𝕜) :
    germMap f hf b (algebraMap 𝕜 ((structureSheaf 𝕜 E M).presheaf.stalk (f b)) a) =
      algebraMap 𝕜 ((structureSheaf 𝕜 E M').presheaf.stalk b) a := by
  rw [algebraMap_stalk_eq, algebraMap_stalk_eq]
  apply stalkToGerm_injective 𝓘(𝕜, E) ω M' b
  rw [stalkToGerm_germMap, stalkToGerm_const, stalkToGerm_const, Filter.Germ.coe_compTendsto]
  rfl

omit ψ in
/-- The germ map is a local homomorphism, so it carries `𝔪_{f b}^k` into `𝔪_b^k`. -/
theorem germMap_mem_maximalIdeal_pow {b : M'} {s : (structureSheaf 𝕜 E M).presheaf.stalk (f b)}
    {k : ℕ} (hs : s ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk (f b)) ^ k) :
    germMap f hf b s ∈ maximalIdeal ((structureSheaf 𝕜 E M').presheaf.stalk b) ^ k := by
  have h1 : germMap f hf b s ∈ Ideal.map (germMap f hf b)
      (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk (f b)) ^ k) :=
    Ideal.mem_map_of_mem _ hs
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) k h1

variable [IsManifold 𝓘(𝕜, E) ω M']

/-- **The chain rule for germs along an analytic map** `f : M' → M` (the identity behind Kollár's
computation "using the chain rule" [Kol07, 75]; the Taylor-uniqueness argument of
`derivation_eq_sum_coordDerivStalk` for a derivation along the germ map). For a chart `φ` at `f b`
with coordinates `x_k`, every `𝕜`-derivation `δ` of `𝒪_{M', b}` satisfies, on the germs `s ∘ f`,
`δ(s ∘ f) = ∑_k δ((x_k − x_k(f b)) ∘ f) · (∂_k s) ∘ f`. -/
theorem derivation_germMap_eq_sum_coordDerivStalk (φ : OpenPartialHomeomorph M E)
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {b : M'} (hb : f b ∈ φ.source)
    (δ : Derivation 𝕜 ((structureSheaf 𝕜 E M').presheaf.stalk b)
      ((structureSheaf 𝕜 E M').presheaf.stalk b))
    (s : (structureSheaf 𝕜 E M).presheaf.stalk (f b)) :
    δ (germMap f hf b s) =
      ∑ k, δ (germMap f hf b (centredCoord E ψ φ hφ hb k)) *
        germMap f hf b (coordDerivStalk E ψ φ hφ hb k s) := by
  set ρ := germMap f hf b with hρ
  set c : Fin n → (structureSheaf 𝕜 E M').presheaf.stalk b :=
    fun k => δ (ρ (centredCoord E ψ φ hφ hb k)) with hc
  set F : (structureSheaf 𝕜 E M).presheaf.stalk (f b) → (structureSheaf 𝕜 E M').presheaf.stalk b :=
    fun t => δ (ρ t) - ∑ k, c k * ρ (coordDerivStalk E ψ φ hφ hb k t) with hF
  have hFadd : ∀ t u, F (t + u) = F t + F u := by
    intro t u
    simp only [hF, map_add, mul_add, Finset.sum_add_distrib]
    ring
  have hFmul : ∀ t u, F (t * u) = ρ t * F u + ρ u * F t := by
    intro t u
    simp only [hF, map_mul, Derivation.leibniz, smul_eq_mul, map_add]
    have e1 : ∑ k, c k * (ρ t * ρ (coordDerivStalk E ψ φ hφ hb k u) +
        ρ u * ρ (coordDerivStalk E ψ φ hφ hb k t)) =
        ρ t * ∑ k, c k * ρ (coordDerivStalk E ψ φ hφ hb k u) +
          ρ u * ∑ k, c k * ρ (coordDerivStalk E ψ φ hφ hb k t) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1]
    ring
  have hFx : ∀ j, F (centredCoord E ψ φ hφ hb j) = 0 := by
    intro j
    simp only [hF, coordDerivStalk_centredCoord, apply_ite ρ, map_one, map_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hc, sub_self]
  have hFalg : ∀ a : 𝕜, F (algebraMap 𝕜 _ a) = 0 := by
    intro a
    simp only [hF, hρ, germMap_algebraMap, Derivation.map_algebraMap, map_zero, mul_zero,
      Finset.sum_const_zero, sub_zero]
  have hFpoly : ∀ p ∈ Algebra.adjoin 𝕜 (Set.range (centredCoord E ψ φ hφ hb)), F p = 0 := by
    intro p hp
    induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨j, rfl⟩ := hp
      exact hFx j
    | algebraMap r => exact hFalg r
    | add p q _ _ hp hq => rw [hFadd, hp, hq, add_zero]
    | mul p q _ _ hp hq => rw [hFmul, hp, hq, mul_zero, mul_zero, add_zero]
  have hFpow : ∀ (k : ℕ) (t : (structureSheaf 𝕜 E M).presheaf.stalk (f b)),
      t ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk (f b)) ^ (k + 1) →
        F t ∈ maximalIdeal ((structureSheaf 𝕜 E M').presheaf.stalk b) ^ k := by
    intro k t ht
    refine Ideal.sub_mem _ ?_ (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_)
    · exact Derivation.mem_pow_of_mem_pow_succ _ δ k (germMap_mem_maximalIdeal_pow f hf ht)
    · exact germMap_mem_maximalIdeal_pow f hf
        (Derivation.mem_pow_of_mem_pow_succ _ (coordDerivStalk E ψ φ hφ hb j) k ht)
  have hFs : F s = 0 := by
    refine eq_zero_of_forall_mem_maximalIdeal_pow E ψ (chartAt E b)
      (IsManifold.chart_mem_maximalAtlas b) (mem_chart_source E b) (F s) fun k => ?_
    obtain ⟨p, hp, hsp⟩ := exists_mem_adjoin_sub_mem_maximalIdeal_pow E ψ φ hφ hb (k + 1) s
    have h2 : F s = F p + F (s - p) := by rw [← hFadd, add_sub_cancel]
    rw [h2, hFpoly p hp, zero_add]
    exact hFpow k _ hsp
  exact sub_eq_zero.mp hFs

end Manifold

end
