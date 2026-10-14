/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.BlowUp.CoordGerm
import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Resolution.Analytic.Principalization.MonomialStep
import Hironaka.Resolution.Analytic.Wlo09.HadamardBare
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The pull-back of a monomial along a blow-up chart

If `g = b ∏_k z_k^{e_k}` in adapted coordinates for a simple normal crossings divisor `E` at
`π(a')` and the centre `Y` has simple normal crossings with `E`, then in the induced coordinates
of a blow-up chart at `a'` the pull-back `g ∘ π` is again a unit times a monomial supported on the
coordinates of the total transform of `E`: the coordinate `u_i` of the exceptional divisor to the
sum of the exponents of the coordinates in the centre's block, and each other coordinate to its
own exponent (the computation Bierstone–Milman make for the strict transform in a blow-up chart,
`f'(w', z') = (z'_1)^{-d} f(w', z'_1, z'_1(⋯))` [BM97, §3, "The strict transform"]; Kollár's total
transform of a divisor [Kol07, Definition 25]). In the stalk form of the Jacobian ledger
(`Hironaka/Resolution/Analytic/BM97/Ledger.lean`) the unit `b` is absorbed and the monomial is read
as the product of the powers of the vanishing stalks of the members: the stalk map `germMap π`
carries `∏_{j ∈ s} (vanishing stalk of E^j at π p)^{e_j}` to the product over the strict transforms
of the same members at `p`, each with its exponent (a factor `⊤` where the strict transform misses
`p`), times the vanishing stalk of the exceptional divisor `π⁻¹ Y` to the sum of the `e_j` over the
members whose coordinate lies in the centre's block
(`germMap_prod_vanishingStalk_pow_totalTransform`).
The per-member identity (`germMap_vanishingStalk_hyp`) is the chart law for the coordinate germs
(`z_{σ i} ∘ π = u_{σ i}`, `z_{σ k} ∘ π = u_{σ i} u_{σ k}` for `k ≠ i`, `z_j ∘ π = u_j` off the
block: `IsBlowUpChart.germMap_coord_self`, `germMap_coord_of_ne`, `germMap_coord_off`) together
with the description of the strict transforms in the blow-up chart
(`strictTransform_inter_source_self`, `strictTransform_inter_source_of_ne`,
`strictTransform_inter_source_off`) and the vanishing stalk of a coordinate hyperplane
(`IsClosedSubmanifold.vanishingStalk_eq_span_coord`,
`vanishingStalk_eq_span_coord_of_forall_mem_iff`); the product is assembled by `Ideal.map` of a
finite product (`Ideal.map_finset_prod`). This is the transport of the old monomial in the step
of the ledger (`Hironaka/Resolution/Analytic/BM97/LedgerStep.lean`).
-/

public section

open Set TopologicalSpace Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Hironaka.Manifold

open _root_.Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [hM : IsManifold 𝓘(𝕜, E) ω M] {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M']
  [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] {π : M' → M} {Y : Set M}
  {c : ℕ} {F : HypersurfaceFamily M}

omit hM in
/-- In a simple normal crossings chart at `a`, the vanishing stalk of a component through `a` is
spanned by the component's coordinate (`mem_vanishingStalk_hyp_iff`). -/
theorem _root_.Manifold.HypersurfaceFamily.IsSncChartAt.vanishingStalk_hyp_eq_span (hF : F.IsSnc ψ)
    {φ : OpenPartialHomeomorph M E}
    {a : M} {cidx : {j // a ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ φ a cidx)
    (j : {j // a ∈ F.hyp j}) :
    vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j.1) a =
      Ideal.span {coord E ψ φ hc.1 hc.mem_source (cidx j)} := by
  ext s
  rw [Ideal.mem_span_singleton]
  exact hc.mem_vanishingStalk_hyp_iff hF j hc.mem_source j.2 s

omit hM in
/-- One member: the stalk map of the blow-up carries the vanishing stalk of a member through `π p`
to the exceptional divisor's vanishing stalk (to the power `1` when the member's coordinate lies in
the centre's block, `0` otherwise) times the vanishing stalk of its strict transform — the chart
law for the coordinate germs, case by case on the member's coordinate: `σ i` (the strict transform
misses the chart, `strictTransform_inter_source_self`), `σ k` with `k ≠ i` (`z_{σ k} ∘ π =
u_{σ i} u_{σ k}`, the strict transform `{u_{σ k} = 0}`), off the block (`z_j ∘ π = u_j`). The
vanishing stalk of the strict transform at `p` is read in the chart by
`vanishingStalk_eq_span_coord_of_forall_mem_iff`, which needs no closed-submanifold hypothesis, so
no simple normal crossings hypothesis on the centre enters. -/
theorem germMap_vanishingStalk_hyp (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (hF : F.IsSnc ψ) {φ : OpenPartialHomeomorph M E}
    {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ) {p : M'}
    {cidx : {j // π p ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ φ (π p) cidx) {i : Fin c}
    {Φ : OpenPartialHomeomorph M' E} (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hp : p ∈ Φ.source)
    (j : {j // π p ∈ F.hyp j}) [Decidable (∃ k, σ k = cidx j)] :
    Ideal.map (germMap π h.contMDiff p) (vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j.1) (π p)) =
      (vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p) ^ (if ∃ k, σ k = cidx j then 1 else 0) *
        vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet π Y (F.hyp j.1)) p := by
  have hsub : p ∈ π ⁻¹' φ.source := hΦ.source_subset hp
  have hcφ : (π p) ∈ φ.source := hsub
  -- the exceptional divisor's vanishing stalk is spanned by `u_{σ i}`
  have hexc : vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p =
      Ideal.span {coord E ψ Φ hΦ.mem_maximalAtlas hp (σ i)} :=
    (h.isClosedSubmanifold_preimage hY).vanishingStalk_eq_span_coord
      (hΦ.isAdaptedChart_preimage hφ) hp
  -- the member through `π p` is the hyperplane of its coordinate on `φ.source`
  have hH : ∀ x ∈ φ.source, x ∈ F.hyp j.1 ↔ ψ (φ x) (cidx j) = 0 := fun x hx => hc.mem_iff j hx
  rw [hc.vanishingStalk_hyp_eq_span ψ hF j, Ideal.map_span, Set.image_singleton]
  have hcoord : coord E ψ φ hc.1 hc.mem_source (cidx j) = coord E ψ φ hφ.1 hcφ (cidx j) := rfl
  rw [hcoord]
  by_cases hblock : ∃ k, σ k = cidx j
  · obtain ⟨k, hk⟩ := hblock
    rw [ite_eq_left ⟨k, hk⟩, pow_one, hexc]
    by_cases hki : k = i
    · -- the member with the coordinate `σ i`: its strict transform misses the chart
      subst hki
      rw [← hk, hΦ.germMap_coord_self h.contMDiff hφ.1 hp]
      have hE : strictTransformSet π Y (F.hyp j.1) ∩ Φ.source = ∅ :=
        strictTransform_inter_source_self hφ hΦ (hk ▸ hH)
      have ht : vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet π Y (F.hyp j.1)) p = ⊤ := by
        rw [← vanishingStalk_inter_of_mem_nhds (Φ.open_source.mem_nhds hp), hE]
        exact vanishingStalk_eq_top_of_notMem isClosed_empty (Set.notMem_empty p)
      rw [ht, Ideal.mul_top]
    · -- a member with a block coordinate `σ k`, `k ≠ i`: `z_{σ k} ∘ π = u_{σ i} u_{σ k}`
      rw [← hk, hΦ.germMap_coord_of_ne h.contMDiff hφ.1 hp hki,
        ← Ideal.span_singleton_mul_span_singleton]
      congr 1
      have hset := strictTransform_inter_source_of_ne hφ hΦ (hk ▸ hH) (Ne.symm hki)
      have hS : ∀ x ∈ Φ.source, x ∈ strictTransformSet π Y (F.hyp j.1) ↔ ψ (Φ x) (σ k) = 0 :=
        fun x hx => by
          have h1 : x ∈ strictTransformSet π Y (F.hyp j.1) ↔
              x ∈ strictTransformSet π Y (F.hyp j.1) ∩ Φ.source :=
            ⟨fun hx' => ⟨hx', hx⟩, fun hx' => hx'.1⟩
          rw [h1, hset]
          exact ⟨fun hx' => hx'.2, fun hx' => ⟨hx, hx'⟩⟩
      exact (vanishingStalk_eq_span_coord_of_forall_mem_iff ψ hΦ.mem_maximalAtlas hS hp).symm
  · -- a member off the block: `z_j ∘ π = u_j`
    rw [ite_eq_right hblock, pow_zero, one_mul]
    have hoff : ∀ k, σ k ≠ cidx j := fun k hk => hblock ⟨k, hk⟩
    rw [hΦ.germMap_coord_off h.contMDiff hφ.1 hp hoff]
    have hset := strictTransform_inter_source_off hφ hΦ hoff hH
    have hS : ∀ x ∈ Φ.source, x ∈ strictTransformSet π Y (F.hyp j.1) ↔ ψ (Φ x) (cidx j) = 0 :=
      fun x hx => by
        have h1 : x ∈ strictTransformSet π Y (F.hyp j.1) ↔
            x ∈ strictTransformSet π Y (F.hyp j.1) ∩ Φ.source :=
          ⟨fun hx' => ⟨hx', hx⟩, fun hx' => hx'.1⟩
        rw [h1, hset]
        exact ⟨fun hx' => hx'.2, fun hx' => ⟨hx, hx'⟩⟩
    exact (vanishingStalk_eq_span_coord_of_forall_mem_iff ψ hΦ.mem_maximalAtlas hS hp).symm

open scoped Classical in
/-- **The pull-back of a monomial in the coordinates of a simple normal crossings divisor along a
blow-up chart** ([BM97, §3, "The strict transform"]; [Kol07, Definition 25]): the product of the
per-member identities `germMap_vanishingStalk_hyp`, the exceptional exponents summed
(`Finset.prod_pow_eq_pow_sum`). -/
theorem germMap_prod_vanishingStalk_pow_totalTransform (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
    (hφ : IsAdaptedChart ψ Y φ σ) {p : M'} {cidx : {j // π p ∈ F.hyp j} → Fin n}
    (hc : F.IsSncChartAt ψ φ (π p) cidx) {i : Fin c} {Φ : OpenPartialHomeomorph M' E}
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hp : p ∈ Φ.source) (s : Finset F.ι) (e : F.ι → ℕ)
    (hs : ∀ j ∈ s, π p ∈ F.hyp j) :
    Ideal.map (germMap π h.contMDiff p)
        (∏ j ∈ s, (vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j) (π p)) ^ e j) =
      (∏ j ∈ s, (vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p) ^ e j) *
        (vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Y).hyp (toLex (Sum.inr PUnit.unit))) p) ^
          (∑ j ∈ s.attach, if ∃ k, σ k = cidx ⟨j.1, hs j.1 j.2⟩ then e j.1 else 0) := by
  -- The instance `hM : IsManifold 𝓘(𝕜, E) ω M` is part of the statement because the theorem is
  -- stated in the manifold context of the Jacobian ledger, in which the blow-up `π : M' → M` is a
  -- map of analytic manifolds and its Jacobian ideal is defined, and it is applied in that context
  -- (`Hironaka/Resolution/Analytic/BM97/LedgerStep.lean`). The proof does not need it: it computes
  -- in
  -- the coordinate germs of the blow-up chart at the level of the charted space, exactly as the
  -- per-member identity `germMap_vanishingStalk_hyp` above, which is stated without `hM`.
  have _hM := hM
  rw [← Finset.prod_attach s, ← Finset.prod_attach s
    (fun j => (vanishingStalk (𝕜 := 𝕜) (E := E)
      ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p) ^ e j),
    Ideal.map_finset_prod]
  have key : ∀ j : {x // x ∈ s},
      Ideal.map (germMap π h.contMDiff p)
          ((vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j.1) (π p)) ^ e j.1) =
        ((vanishingStalk (𝕜 := 𝕜) (E := E)
            ((F.totalTransform π Y).hyp (toLex (Sum.inl j.1))) p) ^ e j.1) *
          (vanishingStalk (𝕜 := 𝕜) (E := E)
            ((F.totalTransform π Y).hyp (toLex (Sum.inr PUnit.unit))) p) ^
            (if ∃ k, σ k = cidx ⟨j.1, hs j.1 j.2⟩ then e j.1 else 0) := by
    intro j
    rw [Ideal.map_pow, germMap_vanishingStalk_hyp ψ hY h hF hφ hc hΦ hp ⟨j.1, hs j.1 j.2⟩,
      mul_pow, ← pow_mul, mul_comm]
    congr 2
    split_ifs <;> simp
  rw [Finset.prod_congr rfl fun j _ => key j, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end Hironaka.Manifold
