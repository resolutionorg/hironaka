/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Chart.Cotangent
public import Hironaka.Resolution.Analytic.LocalIsoEquiv
public import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.AdaptedChart
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Two charts `(x₁, y)` and `(x₁', y)` with a common complement

Kollár's coordinates in the proof of the uniqueness of maximal contact [Kol07, 95]: at
`p ∈ H ∩ H'` he picks local sections `x₁, x₁' ∈ MC(I)` with `H = (x₁ = 0)` and `H' = (x₁' = 0)`,
further coordinates `x₂, …, x_{s+1}` with `Eⁱ = (x_{i+1} = 0)`, and observes that "for a general
choice of `x_{s+2}, …, xₙ`" both `x₁, x₂, …, xₙ` and `x₁', x₂, …, xₙ` are local coordinate
systems. The ring-level version of
this linear algebra (`Hironaka/Algebra/Local/RegularSystemCommon.lean`) is carried to the analytic
stalk through the linear parts of germs (`linearPart`, `Hironaka/Manifold/Chart/Cotangent.lean`) in
a base chart:

* the snc chart `φ` of `H + E` at `p` gives coordinates `z = ψ ∘ φ` with `H = {z_{i₀} = 0}` and
  `E^j = {z_{k j} = 0}` on its source (`exists_sncChart_append`); the snc chart `φ'` of `H' + E`
  gives `x₁' = z'_{i₀'}` and the same components as `{z'_{k' j} = 0}`;
* the linear part `v` of `x₁'` in the chart `φ` does not lie in the span of the `e_{k j}`
  (`linearPart_notMem_span_of_isSncChartAt`): the equations `z_{k j}` and `z'_{k' j}` of one
  component generate the same vanishing ideal, so their linear parts are proportional
  (`linearPart_mul_of_mem_maximalIdeal`), and in `φ'` the family `x₁', z'_{k' j}` has
  independent linear parts (distinct coordinates), a property independent of the chart
  (`linearIndependent_cotangentClass_iff_linearPart`);
* hence some free index `m₀ ∉ {k j}` has `v_{m₀} ≠ 0`: if `v_{i₀} ≠ 0` no tilt is needed, otherwise
  the coordinate `z_{m₀}` is tilted to `z_{m₀} + z_{i₀}` (Kollár's "general choice"; the protected
  coordinates `z_{k j}` are untouched); the tilted family and the family with `z_{i₀}` replaced by
  `x₁'` both span the cotangent space, hence have independent differentials, and the
  chart-extension theorem `exists_chart_extending` turns each into a chart of the maximal atlas
  centred at `p`; the second is recoordinatised by a permutation so that the two charts share the
  coordinates `≠ i₀` (`exists_commonCharts`).

The two charts are the input of the coordinate swap that realises the formal equivalence of `H`
and `H'` (`Hironaka/Resolution/Analytic/MaximalContact/SwapRealizes.lean`).
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory IsLocalRing
  Set Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-! ### Linear parts: products with a germ of `𝔪`, and coordinate families -/

section LinearPart

variable (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M}
  (ha : a ∈ φ.source)

/-- The linear part of `r · s` for `s ∈ 𝔪_a` is `r(a)` times the linear part of `s`. -/
theorem linearPart_mul_of_mem_maximalIdeal (r : (structureSheaf 𝕜 E M).presheaf.stalk a)
    {s : (structureSheaf 𝕜 E M).presheaf.stalk a}
    (hs : s ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)) :
    Manifold.linearPart E ψ φ hφ ha (r * s) = Manifold.eval 𝕜 E M a r • Manifold.linearPart E ψ φ
        hφ ha s := by
  have h1 : r * s - Manifold.eval 𝕜 E M a r • s ∈
      maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ 2 := by
    have : r * s - Manifold.eval 𝕜 E M a r • s = (r - const 𝕜 E M a
        (Manifold.eval 𝕜 E M a r)) * s := by
      rw [sub_mul, Algebra.smul_def, algebraMap_stalk_eq]
    rw [this, pow_two]
    refine Ideal.mul_mem_mul ?_ hs
    exact (mem_maximalIdeal_iff_eval E _).mpr (by rw [map_sub, eval_const, sub_self])
  have h2 := linearPart_eq_zero_of_mem_sq E ψ φ hφ ha h1
  rwa [map_sub, map_smul, sub_eq_zero] at h2

/-- The linear part of the coordinate germ `z_k` is the unit vector `e_k`. -/
theorem linearPart_coord_eq_single (k : Fin n) :
    Manifold.linearPart E ψ φ hφ ha (coord E ψ φ hφ ha k) = Pi.single k 1 := by
  funext i
  rw [linearPart_coord, Pi.single_apply]

/-- Distinct coordinate germs of a chart have linearly independent linear parts. -/
theorem linearIndependent_linearPart_coord {ι : Type*} (idx : ι → Fin n)
    (hidx : Function.Injective idx) :
    LinearIndependent 𝕜 fun o => Manifold.linearPart E ψ φ hφ ha (coord E ψ φ hφ ha (idx o)) := by
  have h : (fun o => Manifold.linearPart E ψ φ hφ ha (coord E ψ φ hφ ha (idx o))) =
      (Pi.basisFun 𝕜 (Fin n)) ∘ idx := by
    funext o
    rw [Function.comp_apply, Pi.basisFun_apply, linearPart_coord_eq_single]
  rw [h]
  exact (Pi.basisFun 𝕜 (Fin n)).linearIndependent.comp idx hidx

end LinearPart

/-! ### The snc chart of `E + H` at a point of `H`, unpacked -/

section SncChart

variable {ψ} {F : HypersurfaceFamily M} {H : Set M}

/-- An snc chart of the family `F.append H` at `p ∈ H` reads `H` as the coordinate hyperplane of
an index `i₀` and every component `E^j` through `p` as the hyperplane of an index `k j ≠ i₀`, the
`k j` distinct. -/
theorem exists_sncChart_append (hHF : (F.append H).IsSnc ψ) {p : M} (hpH : p ∈ H) :
    ∃ (φ : OpenPartialHomeomorph M E) (_ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (_ : p ∈ φ.source)
      (i₀ : Fin n) (k : {j : F.ι // p ∈ F.hyp j} → Fin n),
      (∀ x ∈ φ.source, x ∈ H ↔ ψ (φ x) i₀ = 0) ∧
        (∀ j, ∀ x ∈ φ.source, x ∈ F.hyp j.1 ↔ ψ (φ x) (k j) = 0) ∧
        (∀ j, k j ≠ i₀) ∧ Function.Injective k := by
  obtain ⟨φ, c, hc⟩ := hHF.exists_isSncChartAt p
  have hpH' : p ∈ (F.append H).hyp (toLex (Sum.inr PUnit.unit)) := hpH
  refine ⟨φ, hc.mem_maximalAtlas, hc.mem_source, c ⟨_, hpH'⟩,
    fun j => c ⟨toLex (Sum.inl j.1), j.2⟩, fun x hx => hc.mem_iff ⟨_, hpH'⟩ hx,
    fun j x hx => hc.mem_iff ⟨toLex (Sum.inl j.1), j.2⟩ hx, fun j h => ?_, fun j j' h => ?_⟩
  · exact Sum.inl_ne_inr (toLex.injective (congrArg Subtype.val (hc.injective h)))
  · exact Subtype.ext (Sum.inl_injective (toLex.injective (congrArg Subtype.val (hc.injective h))))

end SncChart

/-! ### The linear part of `x₁'` is transverse to the components through `p` -/

section Transverse

variable {ψ} {F : HypersurfaceFamily M} {p : M} {φ φ' : OpenPartialHomeomorph M E}

/-- The equation `z_k` of a component in one adapted chart is a unit multiple of its equation in
another: their linear parts (in any chart) are proportional. Here `span {a} = span {b}` for two
germs of `𝔪_p`, and the linear part of `a` is a multiple of that of `b`. -/
theorem linearPart_mem_span_of_span_singleton_eq (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (hp : p ∈ φ.source) {a b : (structureSheaf 𝕜 E M).presheaf.stalk p}
    (hb : b ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk p))
    (h : Ideal.span {a} = Ideal.span {b}) :
    Manifold.linearPart E ψ φ hφ hp a ∈ Submodule.span 𝕜 {Manifold.linearPart E ψ φ hφ hp b} := by
  have ha : a ∈ Ideal.span {b} := h ▸ Ideal.mem_span_singleton_self a
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [linearPart_mul_of_mem_maximalIdeal E ψ φ hφ hp r hb]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- In the snc chart `φ` of `E + H` at `p` (components `E^j = {z_{k j} = 0}`), the linear part of
the equation `x₁'` of `H'` taken from an snc chart `φ'` of `E + H'` does not lie in the span of the
unit vectors `e_{k j}` (the hypothesis that `H' + E` has simple normal crossings,
[Kol07, Theorem 92]). -/
theorem linearPart_notMem_span_of_isSncChartAt (hF : F.IsSnc ψ)
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hp : p ∈ φ.source) {k : {j : F.ι // p ∈ F.hyp j} → Fin n}
    (hk : ∀ j, ∀ x ∈ φ.source, x ∈ F.hyp j.1 ↔ ψ (φ x) (k j) = 0)
    (hφ' : φ' ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hp' : p ∈ φ'.source) {i₀' : Fin n}
    {k' : {j : F.ι // p ∈ F.hyp j} → Fin n}
    (hk' : ∀ j, ∀ x ∈ φ'.source, x ∈ F.hyp j.1 ↔ ψ (φ' x) (k' j) = 0) (hk'i : ∀ j, k' j ≠ i₀')
    (hk'inj : Function.Injective k') :
    Manifold.linearPart E ψ φ hφ hp (coord E ψ φ' hφ' hp' i₀') ∉
      Submodule.span 𝕜 (Set.range fun j => (Pi.single (k j) 1 : Fin n → 𝕜)) := by
  classical
  have : Finite {j : F.ι // p ∈ F.hyp j} := (hF.locallyFinite.point_finite p).to_subtype
  -- the two equations of `E^j` generate the same vanishing ideal
  have hspan : ∀ j : {j : F.ι // p ∈ F.hyp j}, Ideal.span {coord E ψ φ hφ hp (k j)} =
      Ideal.span {coord E ψ φ' hφ' hp' (k' j)} := by
    intro j
    have hE := hF.isClosedSubmanifold j.1
    have had : IsAdaptedChart ψ (F.hyp j.1) φ
        ⟨fun _ : Fin 1 => k j, fun _ _ _ => Subsingleton.elim _ _⟩ :=
      ⟨hφ, fun x hx => by rw [hk j x hx]; exact ⟨fun h _ => h, fun h => h 0⟩⟩
    have had' : IsAdaptedChart ψ (F.hyp j.1) φ'
        ⟨fun _ : Fin 1 => k' j, fun _ _ _ => Subsingleton.elim _ _⟩ :=
      ⟨hφ', fun x hx => by rw [hk' j x hx]; exact ⟨fun h _ => h, fun h => h 0⟩⟩
    have h1 := hE.isIdealSheafOf_idealSheaf.2 φ _ had p hp j.2
    have h2 := hE.isIdealSheafOf_idealSheaf.2 φ' _ had' p hp' j.2
    rw [Set.range_unique] at h1 h2
    rw [h1] at h2
    exact h2
  have hmem' : ∀ j : {j : F.ι // p ∈ F.hyp j}, coord E ψ φ' hφ' hp' (k' j) ∈
      maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk p) := fun j =>
    (mem_maximalIdeal_iff_eval E _).mpr (by rw [eval_coord]; exact (hk' j p hp').mp j.2)
  -- the span of the `e_{k j}` lies in the span of the linear parts of the `z'_{k' j}`
  have hle : Submodule.span 𝕜 (Set.range fun j => (Pi.single (k j) 1 : Fin n → 𝕜)) ≤
      Submodule.span 𝕜
        (Set.range fun j => Manifold.linearPart E ψ φ hφ hp (coord E ψ φ' hφ' hp' (k' j))) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have := linearPart_mem_span_of_span_singleton_eq E (ψ := ψ) hφ hp (hmem' j) (hspan j)
    rw [linearPart_coord_eq_single] at this
    have hsub : Submodule.span 𝕜 {Manifold.linearPart E ψ φ hφ hp (coord E ψ φ' hφ' hp' (k' j))} ≤
        Submodule.span 𝕜
          (Set.range fun j => Manifold.linearPart E ψ φ hφ hp (coord E ψ φ' hφ' hp' (k' j))) :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self j))
    exact hsub this
  -- in `φ'` the family `x₁', z'_{k' j}` is independent; independence is chart-free
  let idx : Option {j : F.ι // p ∈ F.hyp j} → Fin n := fun o => o.elim i₀' k'
  have hidx : Function.Injective idx := by
    rintro (_ | j) (_ | j') h
    · rfl
    · exact absurd h.symm (hk'i j')
    · exact absurd h (hk'i j)
    · exact congrArg some (hk'inj h)
  have hind' : LinearIndependent 𝕜
      fun o => Manifold.linearPart E ψ φ' hφ' hp' (coord E ψ φ' hφ' hp' (idx o)) :=
    linearIndependent_linearPart_coord E ψ φ' hφ' hp' idx hidx
  have hind : LinearIndependent 𝕜
      fun o => Manifold.linearPart E ψ φ hφ hp (coord E ψ φ' hφ' hp' (idx o)) := by
    rw [← linearIndependent_cotangentClass_iff_linearPart E ψ φ hφ hp]
    rw [← linearIndependent_cotangentClass_iff_linearPart E ψ φ' hφ' hp'] at hind'
    exact hind'
  intro hv
  have hnone : (none : Option {j : F.ι // p ∈ F.hyp j}) ∉ Set.range (some : _ → Option _) := by
    rintro ⟨j, hj⟩
    exact Option.some_ne_none j hj
  have := hind.notMem_span_image hnone
  rw [← Set.range_comp] at this
  exact this (hle hv)

end Transverse

/-! ### The free index: where to tilt -/

/-- Kollár's "general choice" [Kol07, 95]: a vector `v` outside the span of the unit vectors
`e_{k j}` has a nonzero coordinate at some index `m₀` off the `k j`; take `m₀ = i₀` when
`v_{i₀} ≠ 0`. -/
theorem exists_free_index {ι : Type*} (k : ι → Fin n) (i₀ : Fin n) (hk : ∀ j, k j ≠ i₀)
    (v : Fin n → 𝕜)
    (hv : v ∉ Submodule.span 𝕜 (Set.range fun j => (Pi.single (k j) 1 : Fin n → 𝕜))) :
    ∃ m₀, (∀ j, k j ≠ m₀) ∧ v m₀ ≠ 0 ∧ (v i₀ ≠ 0 → m₀ = i₀) := by
  classical
  by_cases h0 : v i₀ = 0
  · by_contra hcon
    apply hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun m _ => ?_
    by_cases hm : ∃ j, k j = m
    · obtain ⟨j, rfl⟩ := hm
      have hs : (Pi.single (k j) (v (k j)) : Fin n → 𝕜) = v (k j) • Pi.single (k j) 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · have hvm : v m = 0 := by
        by_contra hne
        exact hcon ⟨m, fun j hj => hm ⟨j, hj⟩, hne, fun h => absurd h0 h⟩
      rw [hvm, Pi.single_zero]
      exact Submodule.zero_mem _
  · exact ⟨i₀, hk, h0, fun _ => rfl⟩

/-! ### Two families of vectors of `𝕜ⁿ`: the tilted basis and the basis with one vector replaced -/

section Vectors

/-- The tilted family `e_m + [m = m₀ ∧ m₀ ≠ i₀] e_{i₀}` is a basis of `𝕜ⁿ`. -/
theorem linearIndependent_tilt (i₀ m₀ : Fin n) :
    LinearIndependent 𝕜 fun m => (Pi.single m 1 : Fin n → 𝕜) +
      (if m = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0) := by
  classical
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_
    (by rw [Fintype.card_fin, Module.finrank_fin_fun])
  set u : Fin n → Fin n → 𝕜 := fun m => (Pi.single m 1 : Fin n → 𝕜) +
    (if m = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0) with hu
  have hsingle : ∀ m, (Pi.single m 1 : Fin n → 𝕜) ∈ Submodule.span 𝕜 (Set.range u) := by
    have hne : ∀ m, ¬ (m = m₀ ∧ m₀ ≠ i₀) → (Pi.single m 1 : Fin n → 𝕜) ∈
        Submodule.span 𝕜 (Set.range u) := fun m hm => by
      have : u m = Pi.single m 1 := by
        change Pi.single m 1 + (if m = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0) = _
        rw [ite_eq_right hm, add_zero]
      rw [← this]
      exact Submodule.subset_span ⟨m, rfl⟩
    intro m
    by_cases hm : m = m₀ ∧ m₀ ≠ i₀
    · obtain ⟨rfl, hmi⟩ := hm
      have h1 : u m = Pi.single m 1 + Pi.single i₀ 1 := by
        change Pi.single m 1 + (if m = m ∧ m ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0) = _
        rw [ite_eq_left ⟨rfl, hmi⟩]
      have h2 : (Pi.single m 1 : Fin n → 𝕜) = u m - Pi.single i₀ 1 := by rw [h1]; abel
      rw [h2]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨m, rfl⟩)
        (hne i₀ fun h => hmi h.1.symm)
    · exact hne m hm
  rw [← (Pi.basisFun 𝕜 (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  rw [Pi.basisFun_apply]
  exact hsingle m

/-- The tilted family with the vector at `i₀` replaced by `v`, where `v_{m₀} ≠ 0` and `v_{i₀} = 0`
unless `m₀ = i₀`, is a basis of `𝕜ⁿ` (Kollár's "`x₁', x₂, …, xₙ` are local coordinates"). -/
theorem linearIndependent_update_tilt (i₀ m₀ : Fin n) (v : Fin n → 𝕜) (hvm : v m₀ ≠ 0)
    (hvi : m₀ ≠ i₀ → v i₀ = 0) :
    LinearIndependent 𝕜 (Function.update (fun m => (Pi.single m 1 : Fin n → 𝕜) +
      (if m = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0)) i₀ v) := by
  classical
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_
    (by rw [Fintype.card_fin, Module.finrank_fin_fun])
  set u := Function.update (fun m => (Pi.single m 1 : Fin n → 𝕜) +
    (if m = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0)) i₀ v with hu
  set S := Submodule.span 𝕜 (Set.range u) with hS
  have hv : v ∈ S := by
    have : u i₀ = v := Function.update_self _ _ _
    rw [← this]
    exact Submodule.subset_span ⟨i₀, rfl⟩
  -- the untouched vectors
  have hfree : ∀ m, m ≠ i₀ → m ≠ m₀ → (Pi.single m 1 : Fin n → 𝕜) ∈ S := fun m hmi hmm => by
    have : u m = Pi.single m 1 := by
      rw [hu, Function.update_of_ne hmi]
      change Pi.single m 1 + (if m = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0) = _
      rw [ite_eq_right (fun h : m = m₀ ∧ m₀ ≠ i₀ => hmm h.1), add_zero]
    rw [← this]
    exact Submodule.subset_span ⟨m, rfl⟩
  have hsum : v = ∑ m, Pi.single m (v m) := (Finset.univ_sum_single v).symm
  have hsingle_of_mem : ∀ m, m ≠ i₀ → m ≠ m₀ → (Pi.single m (v m) : Fin n → 𝕜) ∈ S :=
    fun m hmi hmm => by
      have : (Pi.single m (v m) : Fin n → 𝕜) = v m • Pi.single m 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (hfree m hmi hmm)
  have hsingle : ∀ m, (Pi.single m 1 : Fin n → 𝕜) ∈ S := by
    by_cases hmi : m₀ = i₀
    · -- no tilt: `v_{i₀} ≠ 0` and `v = single i₀ (v i₀) + ∑_{m ≠ i₀} single m (v m)`
      subst hmi
      have hrest : ∑ m ∈ Finset.univ.erase m₀, Pi.single m (v m) ∈ S :=
        Submodule.sum_mem _ fun m hm => hsingle_of_mem m (Finset.ne_of_mem_erase hm)
          (Finset.ne_of_mem_erase hm)
      have h1 : (Pi.single m₀ (v m₀) : Fin n → 𝕜) = v - ∑ m ∈ Finset.univ.erase m₀,
          Pi.single m (v m) := by
        refine eq_sub_of_add_eq ?_
        have h := Finset.add_sum_erase Finset.univ (fun m => (Pi.single m (v m) : Fin n → 𝕜))
          (Finset.mem_univ m₀)
        beta_reduce at h
        rw [Finset.univ_sum_single] at h
        exact h
      have h2 : (Pi.single m₀ 1 : Fin n → 𝕜) = (v m₀)⁻¹ • Pi.single m₀ (v m₀) := by
        rw [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hvm]
      intro m
      by_cases hm : m = m₀
      · subst hm
        rw [h2, h1]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hv hrest)
      · exact hfree m hm hm
    · -- the tilt: `v_{i₀} = 0`, `u m₀ = e_{m₀} + e_{i₀}`
      have hv0 : v i₀ = 0 := hvi hmi
      have hum₀ : u m₀ = Pi.single m₀ 1 + Pi.single i₀ 1 := by
        rw [hu, Function.update_of_ne hmi]
        change Pi.single m₀ 1 + (if m₀ = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0) = _
        rw [ite_eq_left ⟨rfl, hmi⟩]
      have hm₀mem : (Pi.single m₀ 1 + Pi.single i₀ 1 : Fin n → 𝕜) ∈ S := by
        rw [← hum₀]
        exact Submodule.subset_span ⟨m₀, rfl⟩
      have hrest : ∑ m ∈ (Finset.univ.erase i₀).erase m₀, Pi.single m (v m) ∈ S :=
        Submodule.sum_mem _ fun m hm => hsingle_of_mem m
          (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm)) (Finset.ne_of_mem_erase hm)
      have h1 : (Pi.single m₀ (v m₀) : Fin n → 𝕜) = v - ∑ m ∈ (Finset.univ.erase i₀).erase m₀,
          Pi.single m (v m) := by
        refine eq_sub_of_add_eq ?_
        have h := Finset.add_sum_erase (Finset.univ.erase i₀)
          (fun m => (Pi.single m (v m) : Fin n → 𝕜))
          (Finset.mem_erase.mpr ⟨hmi, Finset.mem_univ m₀⟩)
        have h' := Finset.add_sum_erase Finset.univ (fun m => (Pi.single m (v m) : Fin n → 𝕜))
          (Finset.mem_univ i₀)
        beta_reduce at h h'
        rw [hv0, Pi.single_zero, zero_add, Finset.univ_sum_single] at h'
        rw [h, h']
      have h2 : (Pi.single m₀ 1 : Fin n → 𝕜) = (v m₀)⁻¹ • Pi.single m₀ (v m₀) := by
        rw [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hvm]
      have hm₀ : (Pi.single m₀ 1 : Fin n → 𝕜) ∈ S := by
        rw [h2, h1]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hv hrest)
      have hi₀ : (Pi.single i₀ 1 : Fin n → 𝕜) ∈ S := by
        have : (Pi.single i₀ 1 : Fin n → 𝕜) =
            (Pi.single m₀ 1 + Pi.single i₀ 1) - Pi.single m₀ 1 := by
          abel
        rw [this]
        exact Submodule.sub_mem _ hm₀mem hm₀
      intro m
      by_cases hm : m = i₀
      · subst hm; exact hi₀
      by_cases hm' : m = m₀
      · subst hm'; exact hm₀
      exact hfree m hm hm'
  rw [← (Pi.basisFun 𝕜 (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  rw [Pi.basisFun_apply]
  exact hsingle m

end Vectors

/-! ### Germs of coordinates and of sections, compared through their representatives -/

section Germs

variable {ψ} {p : M}

/-- The germ of a section built from a function is the germ of the function. -/
theorem stalkToGerm_germ_sectionOf {W : Opens M} (hpW : p ∈ W) (f : M → 𝕜)
    (hf : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω f W) :
    stalkToGerm 𝓘(𝕜, E) ω M p
      ((structureSheaf 𝕜 E M).presheaf.germ W p hpW (sectionOfContMDiffOn f W hf)) = ↑f := by
  rw [stalkToGerm_structureSheaf_germ]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [W.2.mem_nhds hpW] with x hx
  rw [extendSection_of_mem 𝕜 E _ hx, sectionOfContMDiffOn_apply]

/-- The germ of a chart coordinate is the germ of the coordinate function. -/
theorem stalkToGerm_coord_eq {e : OpenPartialHomeomorph M E} (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (hpe : p ∈ e.source) (i : Fin n) :
    stalkToGerm 𝓘(𝕜, E) ω M p (coord E ψ e he hpe i) = ↑(fun x => ψ (e x) i) := by
  rw [stalkToGerm_coord]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [e.open_source.mem_nhds hpe] with x hx
  rw [extendSection_of_mem 𝕜 E _ hx]
  rfl

/-- Two chart coordinates whose functions agree near `p` have the same germ. -/
theorem coord_eq_coord_of_eventuallyEq {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hpe : p ∈ e.source)
    (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hpe' : p ∈ e'.source) {i i' : Fin n}
    (h : ∀ᶠ x in 𝓝 p, ψ (e x) i = ψ (e' x) i') :
    coord E ψ e he hpe i = coord E ψ e' he' hpe' i' := by
  apply stalkToGerm_injective 𝓘(𝕜, E) ω M p
  rw [stalkToGerm_coord_eq, stalkToGerm_coord_eq]
  exact Filter.Germ.coe_eq.mpr h

end Germs

/-! ### The charts `(x₁, y)` and `(x₁', y)` -/

section Main

variable [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] {ψ} {F : HypersurfaceFamily M}
  {H H' : Set M} {p : M}

/-- Kollár's two coordinate systems `x₁, x₂, …, xₙ` and `x₁', x₂, …, xₙ` [Kol07, 95]: at
`p ∈ H ∩ H'`, with `E + H` and `E + H'` snc, there are two charts of the maximal atlas centred at
`p` sharing all coordinates except the one of index `i₀`, in which `H` (resp. `H'`) is the
hyperplane `{x_{i₀} = 0}` — its vanishing ideal at `p` is generated by the `i₀`-th coordinate germ
— and every component of `E` through `p` is a coordinate hyperplane of an index `≠ i₀`. -/
theorem exists_commonCharts (hF : F.IsSnc ψ) (hH : IsClosedSubmanifold ψ H 1)
    (hH' : IsClosedSubmanifold ψ H' 1) (hHF : (F.append H).IsSnc ψ) (hH'F : (F.append H').IsSnc ψ)
    (hpH : p ∈ H) (hpH' : p ∈ H') :
    ∃ (e e' : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M)
      (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hpe : p ∈ e.source) (hpe' : p ∈ e'.source)
      (i₀ : Fin n), e p = 0 ∧ e' p = 0 ∧
      (∀ i, i ≠ i₀ → coord E ψ e he hpe i = coord E ψ e' he' hpe' i) ∧
      vanishingStalk (𝕜 := 𝕜) (E := E) H p = Ideal.span {coord E ψ e he hpe i₀} ∧
      vanishingStalk (𝕜 := 𝕜) (E := E) H' p = Ideal.span {coord E ψ e' he' hpe' i₀} ∧
      ∀ j, p ∈ F.hyp j → ∃ l, l ≠ i₀ ∧
        vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j) p = Ideal.span {coord E ψ e he hpe l} := by
  classical
  obtain ⟨φ, hφ, hp, i₀, k, hHiff, hEiff, hki₀, hkinj⟩ := exists_sncChart_append E hHF hpH
  obtain ⟨φ', hφ', hp', i₀', k', hH'iff, hE'iff, hk'i₀', hk'inj⟩ :=
    exists_sncChart_append E hH'F hpH'
  have hH0 : ψ (φ p) i₀ = 0 := (hHiff p hp).mp hpH
  have hH'0 : ψ (φ' p) i₀' = 0 := (hH'iff p hp').mp hpH'
  -- the linear part of `x₁'` in the chart `φ`, and the free index `m₀`
  set v := Manifold.linearPart E ψ φ hφ hp (coord E ψ φ' hφ' hp' i₀') with hv_def
  have hv := linearPart_notMem_span_of_isSncChartAt E hF hφ hp hEiff hφ' hp' hE'iff hk'i₀' hk'inj
  obtain ⟨m₀, hm₀k, hvm₀, hm₀i₀⟩ := exists_free_index k i₀ hki₀ v hv
  have hti₀ : ¬ (i₀ = m₀ ∧ m₀ ≠ i₀) := fun h => h.2 h.1.symm
  -- the coordinate functions on `U₀ = φ.source ∩ φ'.source`
  set U₀ : Opens M := ⟨φ.source ∩ φ'.source, φ.open_source.inter φ'.open_source⟩ with hU₀
  have hpU₀ : p ∈ U₀ := ⟨hp, hp'⟩
  set t : Fin n → 𝕜 := fun i => if i = m₀ ∧ m₀ ≠ i₀ then 1 else 0 with ht
  set wf : Fin n → M → 𝕜 :=
    fun i x => (ψ (φ x) i - ψ (φ p) i) + t i * (ψ (φ x) i₀ - ψ (φ p) i₀) with hwf
  set wf' : Fin n → M → 𝕜 :=
    fun i x => if i = i₀ then ψ (φ' x) i₀' - ψ (φ' p) i₀' else wf i x with hwf'
  have hcφ : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (fun x => ψ (φ x) i) U₀ := fun i =>
    (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i).comp
      (ψ : E →L[𝕜] (Fin n → 𝕜))).contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas (n := ω) hφ).mono Set.inter_subset_left))
  have hcφ' : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (fun x => ψ (φ' x) i₀') U₀ :=
    (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i₀').comp
      (ψ : E →L[𝕜] (Fin n → 𝕜))).contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas (n := ω) hφ').mono Set.inter_subset_right))
  have hwfc : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (wf i) U₀ := fun i =>
    ((hcφ i).sub contMDiffOn_const).add (contMDiffOn_const.mul ((hcφ i₀).sub contMDiffOn_const))
  have hwf'c : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (wf' i) U₀ := fun i => by
    by_cases hi : i = i₀
    · have : wf' i = fun x => ψ (φ' x) i₀' - ψ (φ' p) i₀' := funext fun x => ite_eq_left hi
      rw [this]
      exact hcφ'.sub contMDiffOn_const
    · have : wf' i = wf i := funext fun x => ite_eq_right hi
      rw [this]
      exact hwfc i
  set wS : Fin n → (structureSheaf 𝕜 E M).presheaf.obj (op U₀) :=
    fun i => sectionOfContMDiffOn (wf i) U₀ (hwfc i) with hwS
  set wS' : Fin n → (structureSheaf 𝕜 E M).presheaf.obj (op U₀) :=
    fun i => sectionOfContMDiffOn (wf' i) U₀ (hwf'c i) with hwS'
  -- the germs of the sections
  have hg : ∀ i, (structureSheaf 𝕜 E M).presheaf.germ U₀ p hpU₀ (wS i) =
      (coord E ψ φ hφ hp i - const 𝕜 E M p (ψ (φ p) i)) +
        const 𝕜 E M p (t i) * (coord E ψ φ hφ hp i₀ - const 𝕜 E M p (ψ (φ p) i₀)) := by
    intro i
    apply stalkToGerm_injective 𝓘(𝕜, E) ω M p
    rw [stalkToGerm_germ_sectionOfContMDiffOn, map_add, map_sub, map_mul, map_sub,
      stalkToGerm_coord_eq, stalkToGerm_coord_eq, stalkToGerm_const, stalkToGerm_const,
      stalkToGerm_const]
    rfl
  have hg' : ∀ i, i ≠ i₀ → (structureSheaf 𝕜 E M).presheaf.germ U₀ p hpU₀ (wS' i) =
      (structureSheaf 𝕜 E M).presheaf.germ U₀ p hpU₀ (wS i) := fun i hi => by
    apply stalkToGerm_injective 𝓘(𝕜, E) ω M p
    rw [stalkToGerm_germ_sectionOfContMDiffOn, stalkToGerm_germ_sectionOfContMDiffOn]
    exact Filter.Germ.coe_eq.mpr (Eventually.of_forall fun x => ite_eq_right hi)
  have hg'i₀ : (structureSheaf 𝕜 E M).presheaf.germ U₀ p hpU₀ (wS' i₀) =
      coord E ψ φ' hφ' hp' i₀' - const 𝕜 E M p (ψ (φ' p) i₀') := by
    apply stalkToGerm_injective 𝓘(𝕜, E) ω M p
    rw [stalkToGerm_germ_sectionOfContMDiffOn, map_sub, stalkToGerm_coord_eq, stalkToGerm_const,
      ← Filter.Germ.coe_sub]
    exact Filter.Germ.coe_eq.mpr (Eventually.of_forall fun x => ite_eq_left rfl)
  -- their linear parts in `φ`
  have hmem_i₀ : coord E ψ φ hφ hp i₀ - const 𝕜 E M p (ψ (φ p) i₀) ∈
      maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk p) :=
    (mem_maximalIdeal_iff_eval E _).mpr (by rw [map_sub, eval_coord, eval_const, sub_self])
  have hL : ∀ i, Manifold.linearPart E ψ φ hφ hp ((structureSheaf 𝕜 E M).presheaf.germ U₀ p hpU₀
      (wS i)) =
      (Pi.single i 1 : Fin n → 𝕜) +
        (if i = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0) := by
    intro i
    rw [hg i, map_add, map_sub, linearPart_const, sub_zero,
      linearPart_mul_of_mem_maximalIdeal E ψ φ hφ hp _ hmem_i₀, eval_const, map_sub,
      linearPart_const, sub_zero, linearPart_coord_eq_single, linearPart_coord_eq_single]
    by_cases hi : i = m₀ ∧ m₀ ≠ i₀
    · rw [ite_eq_left hi]
      simp only [ht, ite_eq_left hi, one_smul]
    · rw [ite_eq_right hi]
      simp only [ht, ite_eq_right hi, zero_smul]
  have hL' : ∀ i, Manifold.linearPart E ψ φ hφ hp ((structureSheaf 𝕜 E M).presheaf.germ U₀ p hpU₀
      (wS' i)) =
      Function.update (fun m => (Pi.single m 1 : Fin n → 𝕜) +
        (if m = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0)) i₀ v i := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      rw [hg'i₀, map_sub, linearPart_const, sub_zero, Function.update_self]
    · rw [hg' i hi, hL i, Function.update_of_ne hi]
  -- independent differentials
  have hind : HasIndependentDifferentialsAt E (fun i => extendSection 𝕜 E (wS i)) p := by
    rw [hasIndependentDifferentialsAt_iff_linearIndependent_cotangentClass' E hpU₀,
      linearIndependent_cotangentClass_iff_linearPart E ψ φ hφ hp]
    have : (fun i => Manifold.linearPart E ψ φ hφ hp
        ((structureSheaf 𝕜 E M).presheaf.germ U₀ p hpU₀ (wS i))) =
        fun m => (Pi.single m 1 : Fin n → 𝕜) +
          (if m = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0) := funext hL
    rw [this]
    exact linearIndependent_tilt i₀ m₀
  have hind' : HasIndependentDifferentialsAt E (fun i => extendSection 𝕜 E (wS' i)) p := by
    rw [hasIndependentDifferentialsAt_iff_linearIndependent_cotangentClass' E hpU₀,
      linearIndependent_cotangentClass_iff_linearPart E ψ φ hφ hp]
    have : (fun i => Manifold.linearPart E ψ φ hφ hp
        ((structureSheaf 𝕜 E M).presheaf.germ U₀ p hpU₀ (wS' i))) =
        Function.update (fun m => (Pi.single m 1 : Fin n → 𝕜) +
          (if m = m₀ ∧ m₀ ≠ i₀ then (Pi.single i₀ 1 : Fin n → 𝕜) else 0)) i₀ v := funext hL'
    rw [this]
    exact linearIndependent_update_tilt i₀ m₀ v hvm₀ fun hne => by
      by_contra h'
      exact hne (hm₀i₀ h')
  -- the two charts from the chart-extension theorem, restricted to `U₀`
  obtain ⟨e₁, σ, he₁, hpe₁, he₁0, hc₁⟩ := exists_chart_extending ψ
    (fun i => extendSection 𝕜 E (wS i)) p
    (fun i => (contMDiffOn_extendSection (wS i)).contMDiffAt (U₀.2.mem_nhds hpU₀))
    (fun i => by
      rw [extendSection_of_mem 𝕜 E _ hpU₀, sectionOfContMDiffOn_apply]
      simp only [hwf, sub_self, mul_zero, add_zero]) hind
  obtain ⟨e₂, σ', he₂, hpe₂, he₂0, hc₂⟩ := exists_chart_extending ψ
    (fun i => extendSection 𝕜 E (wS' i)) p
    (fun i => (contMDiffOn_extendSection (wS' i)).contMDiffAt (U₀.2.mem_nhds hpU₀))
    (fun i => by
      rw [extendSection_of_mem 𝕜 E _ hpU₀, sectionOfContMDiffOn_apply]
      simp only [hwf', hwf, sub_self, mul_zero, add_zero, ite_self]) hind'
  set e := e₁.restrOpen (U₀ : Set M) U₀.2 with he_def
  have he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M := by
    rw [he_def, OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ he₁ U₀.2
  have hpe : p ∈ e.source := by
    rw [he_def, OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hpe₁, hpU₀⟩
  have hce : ∀ x ∈ e.source, ∀ i, ψ (e x) (σ i) = wf i x := fun x hx i => by
    rw [he_def, OpenPartialHomeomorph.restrOpen_source] at hx
    change ψ (e₁ x) (σ i) = wf i x
    rw [← hc₁ x hx.1 i, extendSection_of_mem 𝕜 E _ hx.2, sectionOfContMDiffOn_apply]
  set e₂r := e₂.restrOpen (U₀ : Set M) U₀.2 with he₂r_def
  have he₂r : e₂r ∈ maximalAtlas 𝓘(𝕜, E) ω M := by
    rw [he₂r_def, OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ he₂ U₀.2
  have hpe₂r : p ∈ e₂r.source := by
    rw [he₂r_def, OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hpe₂, hpU₀⟩
  have hce₂ : ∀ x ∈ e₂r.source, ∀ i, ψ (e₂r x) (σ' i) = wf' i x := fun x hx i => by
    rw [he₂r_def, OpenPartialHomeomorph.restrOpen_source] at hx
    change ψ (e₂ x) (σ' i) = wf' i x
    rw [← hc₂ x hx.1 i, extendSection_of_mem 𝕜 E _ hx.2, sectionOfContMDiffOn_apply]
  -- recoordinatise the second chart so that the index maps agree
  have hσb : Function.Bijective σ := ⟨σ.injective, Finite.injective_iff_surjective.mp σ.injective⟩
  have hσ'b : Function.Bijective σ' :=
    ⟨σ'.injective, Finite.injective_iff_surjective.mp σ'.injective⟩
  set τ : Fin n ≃ Fin n := (Equiv.ofBijective σ hσb).symm.trans (Equiv.ofBijective σ' hσ'b)
    with hτ_def
  have hτ : ∀ i, τ (σ i) = σ' i := fun i => by
    rw [hτ_def, Equiv.trans_apply, ← Equiv.ofBijective_apply σ hσb i, Equiv.symm_apply_apply,
      Equiv.ofBijective_apply]
  set P₀ : (Fin n → 𝕜) ≃L[𝕜] (Fin n → 𝕜) :=
    (LinearEquiv.funCongrLeft 𝕜 𝕜 τ).toContinuousLinearEquiv with hP₀_def
  have hP₀ : ∀ (f : Fin n → 𝕜) i, P₀ f (σ i) = f (σ' i) := fun f i => by
    change (LinearEquiv.funCongrLeft 𝕜 𝕜 τ) f (σ i) = f (σ' i)
    rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, hτ]
  set P : E ≃L[𝕜] E := (ψ.trans P₀).trans ψ.symm with hP_def
  have hP : ∀ (y : E) i, ψ (P y) (σ i) = ψ y (σ' i) := fun y i => by
    rw [hP_def, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply, hP₀]
  set P₁ : OpenPartialHomeomorph E E := P.toHomeomorph.toOpenPartialHomeomorph with hP₁_def
  have hP₁coe : ∀ z, P₁ z = P z := fun z => by
    rw [hP₁_def, Homeomorph.toOpenPartialHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  have hP₁symm : ∀ z, P₁.symm z = P.symm z := fun z => rfl
  have hP₁ : AnalyticOnNhd 𝕜 P₁ P₁.source := fun y _ =>
    ((P : E →L[𝕜] E).analyticAt y).congr (Eventually.of_forall fun z => by
      rw [hP₁coe, ContinuousLinearEquiv.coe_coe])
  have hP₁' : AnalyticOnNhd 𝕜 P₁.symm P₁.target := fun y _ =>
    ((P.symm : E →L[𝕜] E).analyticAt y).congr (Eventually.of_forall fun z => by
      rw [hP₁symm, ContinuousLinearEquiv.coe_coe])
  set e' := e₂r.trans P₁ with he'_def
  have he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M := trans_mem_maximalAtlas_of_analytic' he₂r hP₁ hP₁'
  have hpe' : p ∈ e'.source := by
    rw [he'_def, OpenPartialHomeomorph.trans_source, hP₁_def,
      Homeomorph.toOpenPartialHomeomorph_source]
    exact ⟨hpe₂r, Set.mem_univ _⟩
  have hce' : ∀ x ∈ e'.source, ∀ i, ψ (e' x) (σ i) = wf' i x := fun x hx i => by
    rw [he'_def, OpenPartialHomeomorph.trans_source] at hx
    rw [he'_def, OpenPartialHomeomorph.trans_apply, hP₁coe, hP, hce₂ x hx.1 i]
  -- the conclusions
  refine ⟨e, e', he, he', hpe, hpe', σ i₀, he₁0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he'_def, OpenPartialHomeomorph.trans_apply, hP₁coe]
    change P (e₂ p) = 0
    rw [he₂0, map_zero]
  · intro l hl
    obtain ⟨i, rfl⟩ := hσb.2 l
    have hi : i ≠ i₀ := fun h => hl (h ▸ rfl)
    refine coord_eq_coord_of_eventuallyEq E he hpe he' hpe' ?_
    filter_upwards [e.open_source.mem_nhds hpe, e'.open_source.mem_nhds hpe'] with x hx hx'
    rw [hce x hx i, hce' x hx' i]
    exact (ite_eq_right hi).symm
  · have had : IsAdaptedChart ψ H φ ⟨fun _ : Fin 1 => i₀, fun _ _ _ => Subsingleton.elim _ _⟩ :=
      ⟨hφ, fun x hx => by rw [hHiff x hx]; exact ⟨fun h _ => h, fun h => h 0⟩⟩
    rw [← hH.ker_restrictStalk_eq_vanishingStalk hpH, ← hH.stalkIdeal_idealSheaf_of_mem hpH,
      hH.isIdealSheafOf_idealSheaf.2 φ _ had p hp hpH, Set.range_unique]
    congr 2
    refine coord_eq_coord_of_eventuallyEq E hφ hp he hpe ?_
    filter_upwards [e.open_source.mem_nhds hpe] with x hx
    rw [hce x hx i₀]
    simp only [hwf, hH0, sub_zero, ht, ite_eq_right hti₀, zero_mul, add_zero]
    rfl
  · have had' : IsAdaptedChart ψ H' φ' ⟨fun _ : Fin 1 => i₀', fun _ _ _ => Subsingleton.elim _ _⟩ :=
      ⟨hφ', fun x hx => by rw [hH'iff x hx]; exact ⟨fun h _ => h, fun h => h 0⟩⟩
    rw [← hH'.ker_restrictStalk_eq_vanishingStalk hpH', ← hH'.stalkIdeal_idealSheaf_of_mem hpH',
      hH'.isIdealSheafOf_idealSheaf.2 φ' _ had' p hp' hpH', Set.range_unique]
    congr 2
    refine coord_eq_coord_of_eventuallyEq E hφ' hp' he' hpe' ?_
    filter_upwards [e'.open_source.mem_nhds hpe'] with x hx
    rw [hce' x hx i₀]
    simp only [hwf', ite_eq_left rfl, hH'0, sub_zero]
    rfl
  · intro j hj
    refine ⟨σ (k ⟨j, hj⟩), fun h => hki₀ _ (σ.injective h), ?_⟩
    have hE := hF.isClosedSubmanifold j
    have had : IsAdaptedChart ψ (F.hyp j) φ
        ⟨fun _ : Fin 1 => k ⟨j, hj⟩, fun _ _ _ => Subsingleton.elim _ _⟩ :=
      ⟨hφ, fun x hx => by rw [hEiff ⟨j, hj⟩ x hx]; exact ⟨fun h _ => h, fun h => h 0⟩⟩
    rw [← hE.ker_restrictStalk_eq_vanishingStalk hj, ← hE.stalkIdeal_idealSheaf_of_mem hj,
      hE.isIdealSheafOf_idealSheaf.2 φ _ had p hp hj, Set.range_unique]
    congr 2
    refine coord_eq_coord_of_eventuallyEq E hφ hp he hpe ?_
    filter_upwards [e.open_source.mem_nhds hpe] with x hx
    rw [hce x hx]
    have h0 : ψ (φ p) (k ⟨j, hj⟩) = 0 := (hEiff ⟨j, hj⟩ p hp).mp hj
    have hkm : ¬ (k ⟨j, hj⟩ = m₀ ∧ m₀ ≠ i₀) := fun h => hm₀k ⟨j, hj⟩ h.1
    simp only [hwf, h0, sub_zero, ht, ite_eq_right hkm, zero_mul, add_zero]
    rfl

end Main

end Hironaka.Manifold

end
