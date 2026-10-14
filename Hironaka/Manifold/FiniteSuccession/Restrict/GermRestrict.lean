/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Nested
public import Hironaka.Manifold.FiniteSuccession.Restrict.Restrict
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Algebra.ColonPow
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Restriction of germs to a closed submanifold: the tools

Three facts used in the analytic form of Kollár's Lemma 62
(`birationalTransform_pullback_restrictMap` in `LemmaSixtyTwo.lean`), the compatibility of the
marked transform with restriction to a hypersurface containing the centre [Kol07, Lemma 62]:

* the germ map of the inclusion `S ↪ M` of a bundled closed submanifold (`inclusionMap`,
  `germMap`) is the restriction of germs `restrictStalk` (`germMap_inclusionMap_eq_restrictStalk`),
  surjective with kernel the ideal of `S`;
* the ideal sheaf of `Y ⊆ S` as a closed submanifold of the bundled `S` is the restriction of the
  ideal sheaf `I_Y` (`idealSheaf_preimageVal_eq_pullback`): a germ on `S` vanishes on `Y` near a
  point iff some (equivalently any) extension to `M` vanishes on `Y` there — `Y` is contained in
  `S`;
* the colon by a power of an element commutes with a ring map into a domain, on ideals divisible
  by that power (`Ideal.map_colon_singleton_pow_eq`) — the algebra behind Kollár's remark that it
  does not matter whether one first sets `x_1 = 0` and computes the transform or first computes
  the transform and then sets `y_1 = 0` [Kol07, Lemma 62, proof]; and a coordinate of a chart lies
  outside the ideal spanned by the other (centred) coordinates
  (`coord_notMem_span_coord_sub_const`), which is why the exceptional coordinate does not vanish
  identically on the strict transform in a good chart.

Not in the sources; routine.
-/

public section

noncomputable section

open TopologicalSpace Filter Set IsLocalRing
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

section Colon

/-- The colon by `f u ^ m` of the image of an ideal `A ⊆ (u ^ m)` under a ring map `f` into a
domain, with `f u ≠ 0`, is the image of the colon `(A : u ^ m)`: `A = (u ^ m) · (A : u ^ m)`
(`span_pow_mul_colon_of_le`) and `(f u) ^ m` cancels in the domain
(`colon_span_pow_mul_self`). -/
theorem Ideal.map_colon_singleton_pow_eq {R R' : Type*} [CommRing R] [CommRing R'] [IsDomain R']
    (f : R →+* R') {A : Ideal R} {u : R} {m : ℕ} (hA : A ≤ Ideal.span {u ^ m}) (hu : f u ≠ 0) :
    (Ideal.map f A).colon {f u ^ m} = Ideal.map f (A.colon {u ^ m}) := by
  conv_lhs => rw [← Ideal.span_pow_mul_colon_of_le A u m hA, Ideal.map_mul, Ideal.map_span,
    Set.image_singleton, map_pow]
  exact Ideal.colon_span_pow_mul_self _ hu m

end Colon

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- A coordinate germ of a chart lies outside the ideal spanned by centred coordinate germs of
other indices: applying the partial derivative `∂_k` to a relation
`x_k = ∑ c_j (x_{v j} − x_{v j}(a))`
gives `1 ∈ (x_{v j} − x_{v j}(a))_j ⊆ 𝔪_a`. -/
theorem coord_notMem_span_coord_sub_const (ψ : E ≃L[𝕜] (Fin n → 𝕜))
    {Φ : OpenPartialHomeomorph M E} (hΦ : Φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M}
    (ha : a ∈ Φ.source) {ι : Type*} [Finite ι] (v : ι → Fin n) {k : Fin n} (hv : ∀ j, v j ≠ k) :
    coord E ψ Φ hΦ ha k ∉ Ideal.span (Set.range fun j => coord E ψ Φ hΦ ha (v j) -
      const 𝕜 E M a (eval 𝕜 E M a (coord E ψ Φ hΦ ha (v j)))) := by
  intro h
  have := Fintype.ofFinite ι
  set y : ι → (structureSheaf 𝕜 E M).presheaf.stalk a := fun j => coord E ψ Φ hΦ ha (v j) -
    const 𝕜 E M a (eval 𝕜 E M a (coord E ψ Φ hΦ ha (v j))) with hy
  obtain ⟨cf, hcf⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
  have h1 : coordDerivStalk E ψ Φ hΦ ha k (coord E ψ Φ hΦ ha k) = 1 := by
    rw [coordDerivStalk_coord_eq_ite, ite_eq_left rfl]
  have hδy : ∀ j, coordDerivStalk E ψ Φ hΦ ha k (y j) = 0 := fun j => by
    rw [hy]
    simp only [map_sub, coordDerivStalk_coord_eq_ite, coordDerivStalk_const,
      ite_eq_right (hv j).symm, sub_zero]
  have h2 : (1 : (structureSheaf 𝕜 E M).presheaf.stalk a) ∈ Ideal.span (Set.range y) := by
    rw [← h1, ← hcf, map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Derivation.leibniz, hδy j, smul_zero, zero_add, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have h3 : Ideal.span (Set.range y) ≤ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_maximalIdeal_iff_eval, hy]
    simp only [map_sub, eval_const, sub_self]
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr (h3 h2))

variable [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {S Y : Set M} {s c : ℕ}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The germ map of the inclusion of a bundled closed submanifold is the restriction of germs
`restrictStalk`. -/
theorem IsClosedSubmanifold.germMap_inclusionMap_eq_restrictStalk (hS : IsClosedSubmanifold ψ S s)
    (p : hS.toAnalyticManifold) (t : (structureSheaf 𝕜 E M).presheaf.stalk (hS.inclusionMap p)) :
    germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p t = hS.restrictStalk p t := by
  let _i := hS.chartedSpace
  apply stalkToGerm_injective 𝓘(𝕜, Fin (n - s) → 𝕜) ω hS.toAnalyticManifold p
  rw [stalkToGerm_germMap]
  refine Eq.trans ?_ (hS.stalkToGerm_restrictStalk p t).symm
  change (stalkToGerm 𝓘(𝕜, E) ω M (hS.inclusionMap p) t).compTendsto ⇑hS.inclusionMap _ =
    germRestrict S p (stalkToGerm 𝓘(𝕜, E) ω M (hS.inclusionMap p) t)
  induction stalkToGerm 𝓘(𝕜, E) ω M (hS.inclusionMap p) t using Filter.Germ.inductionOn with
  | h f => rfl

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The germ map of the inclusion, as a ring map, is `restrictStalk`. -/
theorem IsClosedSubmanifold.germMap_inclusionMap (hS : IsClosedSubmanifold ψ S s)
    (p : hS.toAnalyticManifold) :
    germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p = hS.restrictStalk p :=
  RingHom.ext (hS.germMap_inclusionMap_eq_restrictStalk p)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Neighbourhood filters of `Y ⊆ S` read inside the bundled `S` and of `Y` in `M` correspond: a
property of the ambient points holds eventually in one iff it holds eventually in the other (the
maps `⟨⟨y, _⟩, _⟩ ↦ ⟨y, _⟩` and its inverse are continuous). -/
theorem IsClosedSubmanifold.eventually_preimageVal_iff (hS : IsClosedSubmanifold ψ S s)
    (hYS : Y ⊆ S) {p : hS.toAnalyticManifold} (hp : p ∈ hS.preimageVal Y) (P : M → Prop) :
    (∀ᶠ q : hS.preimageVal Y in 𝓝 ⟨p, hp⟩, P (hS.inclusionMap q)) ↔
      ∀ᶠ y : Y in 𝓝 ⟨hS.inclusionMap p, hp⟩, P (y : M) := by
  constructor
  · intro h
    have hc : Continuous fun y : Y =>
        (⟨((⟨(y : M), hYS y.2⟩ : S) : hS.toAnalyticManifold), y.2⟩ : hS.preimageVal Y) :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _
    exact (hc.tendsto (⟨hS.inclusionMap p, hp⟩ : Y)).eventually h
  · intro h
    have hc : Continuous fun q : hS.preimageVal Y => (⟨hS.inclusionMap q, q.2⟩ : Y) :=
      (hS.inclusionMap.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _
    exact (hc.tendsto (⟨p, hp⟩ : hS.preimageVal Y)).eventually h

/-- A germ on `M` at a point of `Y ⊆ S` restricts (along the inclusion's germ map) to a germ on
`S` vanishing on `Y` iff it vanishes on `Y`. -/
theorem IsClosedSubmanifold.germMap_mem_idealSheaf_preimageVal_iff
    (hS : IsClosedSubmanifold ψ S s) (hY : IsClosedSubmanifold ψ Y c) (hYS : Y ⊆ S)
    {p : hS.toAnalyticManifold} (hp : p ∈ hS.preimageVal Y)
    (t : (structureSheaf 𝕜 E M).presheaf.stalk (hS.inclusionMap p)) :
    germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p t ∈
        (hS.preimage_val_of_subset hY hYS).idealSheaf.stalkIdeal p ↔
      t ∈ hY.idealSheaf.stalkIdeal (hS.inclusionMap p) := by
  have hpY : (hS.inclusionMap p : M) ∈ Y := hp
  obtain ⟨V, hV, g, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq t
  rw [germMap_germ]
  refine ((hS.preimage_val_of_subset hY hYS).germ_mem_stalkIdeal_idealSheaf_iff _ hp _ _).trans
    (Iff.trans ?_ (hY.germ_mem_stalkIdeal_idealSheaf_iff V hpY hV g).symm)
  refine Iff.trans ?_ (hS.eventually_preimageVal_iff hYS hp fun y => extendSection 𝕜 E g y = 0)
  have hV' : ∀ᶠ q : hS.preimageVal Y in 𝓝 ⟨p, hp⟩,
      (hS.inclusionMap (q : hS.toAnalyticManifold)) ∈ V := by
    have hcont :
        Continuous fun q : hS.preimageVal Y => hS.inclusionMap (q : hS.toAnalyticManifold) :=
      hS.inclusionMap.contMDiff.continuous.comp continuous_subtype_val
    exact (hcont.tendsto _).eventually (V.2.mem_nhds hV)
  refine Filter.eventually_congr (hV'.mono fun q hq => ?_)
  have hq' : (q : hS.toAnalyticManifold) ∈
      preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff V :=
    (mem_preimageOpens _ _).mpr hq
  rw [extendSection_of_mem 𝕜 (Fin (n - s) → 𝕜) _ hq', comapSection_apply]
  change g ⟨hS.inclusionMap (q : hS.toAnalyticManifold), hq⟩ = 0 ↔
    extendSection 𝕜 E g (hS.inclusionMap (q : hS.toAnalyticManifold)) = 0
  rw [extendSection_of_mem 𝕜 E g hq]

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The germ map of the inclusion is surjective (`restrictStalk_surjective`). -/
theorem IsClosedSubmanifold.germMap_inclusionMap_surjective (hS : IsClosedSubmanifold ψ S s)
    (p : hS.toAnalyticManifold) :
    Function.Surjective (germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p) := by
  intro x
  obtain ⟨t, ht⟩ := hS.restrictStalk_surjective p x
  exact ⟨t, (hS.germMap_inclusionMap_eq_restrictStalk p t).trans ht⟩

/-- The ideal sheaf of `Y ⊆ S` as a closed submanifold of the bundled `S` is the restriction to
`S` of the ideal sheaf `I_Y` (the centre `Z_i ∩ S_i = Z_i` of a restricted blow-up sequence, read
inside `S_i`, [Kol07, Definition 30.2]). -/
theorem idealSheaf_preimageVal_eq_pullback (hS : IsClosedSubmanifold ψ S s)
    (hY : IsClosedSubmanifold ψ Y c) (hYS : Y ⊆ S) :
    (hS.preimage_val_of_subset hY hYS).idealSheaf =
      hY.idealSheaf.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff := by
  refine IdealSheaf.ext fun (p : hS.toAnalyticManifold) => ?_
  rw [IdealSheaf.stalkIdeal_pullback]
  by_cases hp : p ∈ hS.preimageVal Y
  · apply le_antisymm
    · intro x hx
      obtain ⟨t, rfl⟩ := hS.germMap_inclusionMap_surjective p x
      exact Ideal.mem_map_of_mem _
        ((hS.germMap_mem_idealSheaf_preimageVal_iff hY hYS hp t).mp hx)
    · intro x hx
      obtain ⟨t', ht', rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ (hS.germMap_inclusionMap_surjective p)).mp hx
      exact (hS.germMap_mem_idealSheaf_preimageVal_iff hY hYS hp t').mpr ht'
  · have hpY : (hS.inclusionMap p : M) ∉ Y := hp
    rw [(hS.preimage_val_of_subset hY hYS).stalkIdeal_idealSheaf_of_notMem hp,
      hY.stalkIdeal_idealSheaf_of_notMem hpY, Ideal.map_top]

end Manifold

end
