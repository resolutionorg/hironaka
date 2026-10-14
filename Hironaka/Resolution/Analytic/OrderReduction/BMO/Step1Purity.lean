/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.TotalTransform
public import Hironaka.Manifold.StructureSheaf
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialPart
import Hironaka.Algebra.Local.ChartGenericFibre
import Hironaka.Algebra.Local.TransformOrder
import Hironaka.Manifold.BlowUp.Charts
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.KollarChart
import Hironaka.Manifold.BlowUp.Transform.KollarPerm
import Hironaka.Manifold.BlowUp.Transform.MarkedWeak
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.Weak
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Comap
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1ExistsComap
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Measure
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1MeasureOrder
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1PerBlowUp
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The weak transform of a purely nonmonomial ideal is purely nonmonomial

Step 1 of the proof of [Kol07, Theorem 107] (item 111) rests on the remark that the transform of the
nonmonomial part `N(𝓘)` and the marked transform of `(𝓘, m)` differ by a product of powers of the
exceptional divisors, hence only in their monomial part. Its content for one blow-up is
that the marked transform of `N(𝓘)`, taken at its exact order along the centre, is again purely
nonmonomial for the transformed boundary family. This file proves that statement: for an ideal sheaf
`K` whose exponents along all components of the boundary family `F` vanish, with `ord_Y K = d` along
the centre `Y` and `ord K ≤ d` at every point of `Y`, the weak transform `W = π_*^{-1}(K, d)` has
vanishing exponents along every component of `F' = F.totalTransform π Y`
(`componentExponent_weakTransformOf_eq_zero`), so that `M_{F'}(W) = ⊤` and `N_{F'}(W) = W`. The
components of `F'` are of two kinds.

* Components of the strict transforms of the members. The exponent of `W` along such a component
  `C'` is read at a point of `C'` off the exceptional divisor, which exists because `C'` is
  relatively open in the strict transform of the member and `π⁻¹(E^j \ Y)` is dense there. At such a
  point `W` is the total transform of `K`, the blow-up is a local analytic isomorphism, and the
  exponent is an exponent of `K` along a component of `F`, hence zero.
* Components of the exceptional divisor. The exponent of `W` along such a component `α` is read at a
  point of `α` where `W` is the unit ideal. Such a point exists by Kollár's computation of the
  transform in coordinates [Kol07, Definition 60, (60.3)], as in the proof of [Kol07, Lemma 61]: an
  element `f` of `K` of order `d` at the base point has transform `f / x_r^d = Q(y)`, a polynomial
  in the ratio coordinates `y` with a unit coefficient; the polynomial of values is nonzero, so some
  ratio vector `t` has `Q(t) ≠ 0`, and the slice of the blow-up chart with the scaling and
  off-block coordinates of the base point is connected, so the point with ratios `t` lies in `α`.

The weak transform, the total transform divided by the exact power of the ideal of the exceptional
divisor, is Hironaka's [Hir64, §5, p. 142]; the marked transform at the exact order coincides with
it (`birationalTransform_eq_weakTransformOf_of_ordAlong_eq`).
-/

public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

/-! ### A component contains the connected component of any of its points -/

/-- A point of the connected component of `x` in the member `E^j`, for `x` on the component
`i = ⟨j, C⟩`, lies on `componentSet G i`: the connected component of `x` is the class of `x`. -/
theorem mem_componentSet_of_mem_connectedComponentIn {X : Type u} [TopologicalSpace X]
    (G : HypersurfaceFamily X) (i : ComponentIndex G) {x y : X} (hx : x ∈ componentSet G i)
    (hy : y ∈ connectedComponentIn (G.hyp i.1) x) : y ∈ componentSet G i := by
  obtain ⟨p, hpC, hpx⟩ := hx
  have hxG : x ∈ G.hyp i.1 := by rw [← hpx]; exact p.2
  rw [connectedComponentIn_eq_image hxG] at hy
  obtain ⟨q, hq, hqy⟩ := hy
  refine ⟨q, ?_, hqy⟩
  have h1 : ConnectedComponents.mk q = ConnectedComponents.mk ⟨x, hxG⟩ :=
    ConnectedComponents.coe_eq_coe'.mpr hq
  have h2 : (⟨x, hxG⟩ : G.hyp i.1) = p := Subtype.ext hpx.symm
  change ConnectedComponents.mk q = i.2
  rw [h1, h2]
  exact hpC

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M} (hY : IsClosedSubmanifold ψ Y c)
  (h : IsBlowUp ψ Y c π) (F : HypersurfaceFamily M) (hF : F.IsSnc ψ) (hsnc : F.HasSncWith ψ Y c)

/-! ### Off the exceptional divisor -/

/-- Off the centre the weak transform has the stalk of the total transform: the exponent of the
exceptional ideal that is divided out is the (generic) order of `K` along the empty trace of the
centre, that is `toNat ⊤ = 0`, so the colon is by the unit ideal. -/
theorem weakTransformOf_stalkIdeal_of_notMem [T2Space M] [SecondCountableTopology M]
    (K : IdealSheaf (structureSheaf 𝕜 E M)) {a' : M'}
    (ha' : π a' ∉ Y) :
    (IdealSheaf.weakTransformOf hY h K).stalkIdeal a' =
      (K.pullback π h.contMDiff).stalkIdeal a' := by
  have hexp : (IdealSheaf.genericOrdAlong hY.idealSheaf K (π a')).toNat = 0 := by
    rw [IdealSheaf.genericOrdAlong_def, hY.cosupport_idealSheaf, connectedComponentIn_eq_empty ha']
    simp
  have hcol := isDivExceptional_weakTransformOf hY h K a'
  dsimp only at hcol
  rw [hexp, pow_zero, Ideal.one_eq_top, Ideal.colon_coe_top] at hcol
  exact hcol

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- At a point where the blow-up is a local analytic isomorphism, the order of the total transform
of `J` along the total transform of `D` equals the order of `J` along `D` at the image point: the
germ map is bijective there and carries the stalk ideals, their inclusions and their powers. -/
theorem ordAlongIdeal_totalTransform_of_isLocalDiffeomorphAt
    (D J : IdealSheaf (structureSheaf 𝕜 E M)) {a' : M'}
    (hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω π a') :
    IdealSheaf.ordAlongIdeal (D.pullback π h.contMDiff) (J.pullback π h.contMDiff) a' =
      IdealSheaf.ordAlongIdeal D J (π a') := by
  have hbij : Function.Bijective (germMap π h.contMDiff a') :=
    germMap_bijective_of_isLocalDiffeomorphAt π h.contMDiff hloc
  have hiff : ∀ (A C : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk (π a'))),
      Ideal.map (germMap π h.contMDiff a') A ≤ Ideal.map (germMap π h.contMDiff a') C ↔ A ≤ C :=
    fun A C => by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ hbij]
  simp only [IdealSheaf.ordAlongIdeal, IdealSheaf.stalkIdeal_pullback]
  refine iSup_congr fun p => ?_
  rw [← Ideal.map_pow]
  exact iSup_congr_Prop (hiff _ _) fun _ => rfl

/-! ### A point of a strict-transform component off the centre -/

include hY h hF hsnc in
omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Every component `C'` of the strict transform of a member `E^j` contains a point off the
exceptional divisor: `C'` is the trace on the strict transform `closure (π⁻¹(E^j \ Y))` of an open
set, which therefore meets `π⁻¹(E^j \ Y)`. -/
theorem exists_mem_componentSet_inl_notMem {j : F.ι}
    (C' : ConnectedComponents ((F.totalTransform π Y).hyp (toLex (Sum.inl j)))) :
    ∃ a' : M', a' ∈ componentSet (F.totalTransform π Y) ⟨toLex (Sum.inl j), C'⟩ ∧ π a' ∉ Y := by
  have hF' := HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc
  obtain ⟨W₀, hW₀o, hW₀⟩ := exists_isOpen_componentSet_eq (M := (⟨M'⟩ : AnalyticManifold.{u} 𝕜 E))
    (F.totalTransform π Y) hF' ⟨toLex (Sum.inl j), C'⟩
  have hp := out_mem_componentSet (F.totalTransform π Y) ⟨toLex (Sum.inl j), C'⟩
  rw [hW₀] at hp
  have hcl : (C'.out : (F.totalTransform π Y).hyp (toLex (Sum.inl j))).val ∈
      closure (π ⁻¹' (F.hyp j \ Y)) := hp.1
  obtain ⟨a', haW, ha'⟩ := mem_closure_iff.mp hcl W₀ hW₀o hp.2
  refine ⟨a', ?_, ha'.2⟩
  rw [hW₀]
  exact ⟨subset_closure ha', haW⟩

/-! ### The exponent along a strict-transform component is an exponent below -/

/-- The exponent of the weak transform along a component `⟨inl j, C'⟩` of the strict transform of
`E^j`, read at a point `a'` of it off the centre lying over the component `⟨j, C⟩` of `F`, is the
exponent of `K` along `⟨j, C⟩`: both exponents are orders at the actual points; the weak transform
has the stalk of the total transform there (`weakTransformOf_stalkIdeal_of_notMem`), the ideal of
the component of `F'` is the total transform of the ideal of the component of `F`
(`stalkIdeal_totalTransform_componentIdeal_of_notMem`), and the order transports along the local
analytic isomorphism `π` (`ordAlongIdeal_totalTransform_of_isLocalDiffeomorphAt`). -/
theorem componentExponent_weakTransformOf_inl_eq [T2Space M] [SecondCountableTopology M]
    (K : IdealSheaf (structureSheaf 𝕜 E M)) {j : F.ι}
    (C : ConnectedComponents (F.hyp j))
    (C' : ConnectedComponents ((F.totalTransform π Y).hyp (toLex (Sum.inl j)))) {a' : M'}
    (ha' : a' ∈ componentSet (F.totalTransform π Y) ⟨toLex (Sum.inl j), C'⟩) (hπ : π a' ∉ Y)
    (hC : π a' ∈ componentSet F ⟨j, C⟩) :
    componentExponent (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        (IdealSheaf.weakTransformOf hY h K) ⟨toLex (Sum.inl j), C'⟩ =
      componentExponent F hF K ⟨j, C⟩ := by
  have hF' := HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc
  have hmem := ha'
  obtain ⟨p, hpC, hpa⟩ := hmem
  have hxj : a' ∈ strictTransformSet π Y (F.hyp j) := by
    rw [← hpa]
    exact p.2
  have hC' : ConnectedComponents.mk
      (⟨a', hxj⟩ : (F.totalTransform π Y).hyp (toLex (Sum.inl j))) = C' := by
    have hpe : (⟨a', hxj⟩ : (F.totalTransform π Y).hyp (toLex (Sum.inl j))) = p :=
      Subtype.ext hpa.symm
    rw [hpe]
    exact hpC
  subst hC'
  have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω π a' :=
    h.isLocalDiffeomorphOn_compl ⟨a', hπ⟩
  have hcomp := stalkIdeal_totalTransform_componentIdeal_of_notMem hY h F hF hsnc hπ ⟨j, C⟩ hC hxj
  have hleft : IdealSheaf.ordAlongIdeal (componentIdeal (F.totalTransform π Y) hF'
        ⟨toLex (Sum.inl j), ConnectedComponents.mk ⟨a', hxj⟩⟩) (K.pullback π h.contMDiff) a' =
      IdealSheaf.ordAlongIdeal ((componentIdeal F hF ⟨j, C⟩).pullback π h.contMDiff)
        (K.pullback π h.contMDiff) a' := by
    unfold IdealSheaf.ordAlongIdeal
    rw [hcomp]
  rw [componentExponent_eq_toNat_ordAlongIdeal (F.totalTransform π Y) hF' _ _ ha',
    componentExponent_eq_toNat_ordAlongIdeal F hF K ⟨j, C⟩ hC]
  congr 1
  rw [IdealSheaf.ordAlongIdeal_congr_stalk _ _ _ _ (weakTransformOf_stalkIdeal_of_notMem hY h K hπ),
    hleft, ordAlongIdeal_totalTransform_of_isLocalDiffeomorphAt h _ _ hloc]

/-- If `K` is purely nonmonomial for `F` (every exponent along a component of `F` is `0`, as for
`K = N(𝓘)` by `componentExponent_nonmonomialPart_eq_zero`), then the exponent of its weak transform
along every component `⟨inl j, C'⟩` of a strict transform is `0`: read it at a point of `C'` off the
centre (`exists_mem_componentSet_inl_notMem`) as an exponent of `K`
(`componentExponent_weakTransformOf_inl_eq`). No hypothesis on the order of `K` along the centre is
needed. -/
theorem componentExponent_weakTransformOf_inl [T2Space M] [SecondCountableTopology M]
    (K : IdealSheaf (structureSheaf 𝕜 E M))
    (hpure : ∀ i : ComponentIndex F, componentExponent F hF K i = 0) {j : F.ι}
    (C' : ConnectedComponents ((F.totalTransform π Y).hyp (toLex (Sum.inl j)))) :
    componentExponent (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
      (IdealSheaf.weakTransformOf hY h K) ⟨toLex (Sum.inl j), C'⟩ = 0 := by
  obtain ⟨a', ha', hπ⟩ := exists_mem_componentSet_inl_notMem hY h F hF hsnc C'
  have hxj : a' ∈ strictTransformSet π Y (F.hyp j) := by
    obtain ⟨p, -, hpa⟩ := ha'
    rw [← hpa]
    exact p.2
  have hmem : π a' ∈ F.hyp j :=
    strictTransform_subset_preimage h.contMDiff.continuous (hF.1 j).isClosed hxj
  have hC : π a' ∈ componentSet F ⟨j, ConnectedComponents.mk ⟨π a', hmem⟩⟩ :=
    ⟨⟨π a', hmem⟩, rfl, rfl⟩
  rw [componentExponent_weakTransformOf_inl_eq hY h F hF hsnc K _ C' ha' hπ hC]
  exact hpure _

/-! ### The fibre slice of a blow-up chart lies in one exceptional component -/

omit [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- In a blow-up chart `Φ` of index `i` containing a point `a'` of the exceptional component
`⟨inr (), α⟩`, every vector `t` of ratio coordinates is realised by a point `a''` of the same
component over the same base point, with the scaling and off-block coordinates of `a'`: the slice of
the chart with scaling coordinate `0` and the off-block coordinates of `a'` is the continuous image
of the ratio space, hence connected, lies in `π⁻¹(Y)` and contains `a'`, so it lies in the connected
component of `a'` in the exceptional divisor. -/
theorem exists_mem_componentSet_inr_of_ratios
    (α : ConnectedComponents ((F.totalTransform π Y).hyp (toLex (Sum.inr PUnit.unit))))
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} {i : Fin c}
    {Φ : OpenPartialHomeomorph M' E} (hφ : IsAdaptedChart ψ Y φ σ) (hΦ : IsBlowUpChart ψ π φ σ i Φ)
    {a' : M'} (ha' : a' ∈ Φ.source)
    (hα : a' ∈ componentSet (F.totalTransform π Y) ⟨toLex (Sum.inr PUnit.unit), α⟩)
    (t : Fin n → 𝕜) :
    ∃ a'' ∈ componentSet (F.totalTransform π Y) ⟨toLex (Sum.inr PUnit.unit), α⟩,
      a'' ∈ Φ.source ∧ π a'' = π a' ∧
        ψ (Φ a'') = fun j => if ∃ k, k ≠ i ∧ σ k = j then t j else ψ (Φ a') j := by
  have haE : a' ∈ π ⁻¹' Y := Subtype.coe_image_subset _ _ hα
  have hu0 : ψ (Φ a') (σ i) = 0 := (IsBlowUpChart.mem_preimage_iff hφ hΦ ha').mp haE
  -- the slice, parametrised by the ratio vector
  let g : (Fin n → 𝕜) → (Fin n → 𝕜) := fun s j =>
    if ∃ k, k ≠ i ∧ σ k = j then s j else ψ (Φ a') j
  have hgi : ∀ s, g s (σ i) = ψ (Φ a') (σ i) := fun s => by
    simp only [g]
    rw [ite_eq_right]
    rintro ⟨k, hk, hkσ⟩
    exact hk (σ.injective hkσ)
  have hmap : ∀ s, blowUpChartMap σ i (g s) = blowUpChartMap σ i (ψ (Φ a')) := by
    intro s
    funext j
    by_cases hj : ∃ k, k ≠ i ∧ σ k = j
    · obtain ⟨k, hk, rfl⟩ := hj
      rw [blowUpChartMap_apply_ratio σ _ hk, blowUpChartMap_apply_ratio σ _ hk, hgi, hu0, zero_mul,
        zero_mul]
    · have hgj : g s j = ψ (Φ a') j := by
        simp only [g]
        rw [ite_eq_right hj]
      by_cases hji : j = σ i
      · rw [hji, blowUpChartMap_apply_scaling, blowUpChartMap_apply_scaling, hgi]
      · have hoff : ∀ k, σ k ≠ j := fun k hkj => by
          by_cases hk : k = i
          · exact hji (hk ▸ hkj).symm
          · exact hj ⟨k, hk, hkj⟩
        rw [blowUpChartMap_apply_off σ _ hoff, blowUpChartMap_apply_off σ _ hoff, hgj]
  have htarget : ∀ s, ψ.symm (g s) ∈ Φ.target := fun s => by
    rw [hΦ.mem_target_iff, ψ.apply_symm_apply, hmap]
    exact (hΦ.mem_target_iff (Φ a')).mp (Φ.map_source ha')
  let q : (Fin n → 𝕜) → M' := fun s => Φ.symm (ψ.symm (g s))
  have hqsrc : ∀ s, q s ∈ Φ.source := fun s => Φ.map_target (htarget s)
  have hqΦ : ∀ s, ψ (Φ (q s)) = g s := fun s => by
    simp only [q]
    rw [Φ.right_inv (htarget s), ψ.apply_symm_apply]
  have hqπ : ∀ s, π (q s) = π a' := fun s => by
    have h1 := hΦ.comm _ (hqsrc s)
    have h2 := hΦ.comm _ ha'
    rw [hqΦ, hmap] at h1
    have h3 : φ (π (q s)) = φ (π a') := ψ.injective (h1.trans h2.symm)
    exact φ.injOn (hΦ.source_subset (hqsrc s)) (hΦ.source_subset ha') h3
  have hqY : ∀ s, q s ∈ π ⁻¹' Y := fun s => by
    rw [Set.mem_preimage, hqπ]
    exact haE
  have hg0 : g (ψ (Φ a')) = ψ (Φ a') := by
    funext j
    simp only [g]
    split_ifs <;> rfl
  have hq0 : q (ψ (Φ a')) = a' := by
    simp only [q]
    rw [hg0, ψ.symm_apply_apply, Φ.left_inv ha']
  have hgc : Continuous g := by
    refine continuous_pi fun j => ?_
    by_cases hj : ∃ k, k ≠ i ∧ σ k = j
    · simp only [g, ite_eq_left hj]
      exact continuous_apply j
    · simp only [g, ite_eq_right hj]
      exact continuous_const
  have hqcont : ContinuousOn q univ :=
    Φ.continuousOn_symm.comp (ψ.symm.continuous.comp hgc).continuousOn fun s _ => htarget s
  have hpre : IsPreconnected (q '' univ) := isPreconnected_univ.image q hqcont
  have hsub : q '' univ ⊆ connectedComponentIn (π ⁻¹' Y) a' :=
    hpre.subset_connectedComponentIn ⟨_, trivial, hq0⟩ fun _ ⟨s, _, hs⟩ => hs ▸ hqY s
  exact ⟨q t, mem_componentSet_of_mem_connectedComponentIn (F.totalTransform π Y)
    ⟨toLex (Sum.inr PUnit.unit), α⟩ hα (hsub ⟨t, trivial, rfl⟩), hqsrc t, hqπ t, hqΦ t⟩

/-! ### The unit point: Kollár's expansion in the chart ring -/

/-- For `K` of order exactly `d` along the centre and of order `≤ d` at its points, the marked
transform `π_*^{-1}(K, d)` is the unit ideal at some point of every component of the exceptional
divisor. This is Kollár's computation of the transform in coordinates [Kol07, Definition 60,
(60.3)], as in the proof of [Kol07, Lemma 61]: at a point `a` of the centre an element `f` of `K_a`
of order `d` has transform `f / x_r^d = Q(y)`, a polynomial in the ratio coordinates with a unit
coefficient (`exists_transformElem_eq_chartPresentation`); the polynomial of the coefficients'
values is nonzero, so some ratio vector `t` has a nonzero value (`MvPolynomial.funext`, the field
being infinite); at the point `a''` of the component with ratios `t`
(`exists_mem_componentSet_inr_of_ratios`) the chart-ring map carries `Q(y)` into the stalk of the
marked transform with value `Q(t) ≠ 0`, a unit. -/
theorem exists_mem_componentSet_inr_birationalTransform_stalkIdeal_eq_top
    (K : IdealSheaf (structureSheaf 𝕜 E M)) {d : ℕ}
    (hord : ∀ a ∈ Y, IdealSheaf.ordAlongIdeal hY.idealSheaf K a = d)
    (hle : ∀ a ∈ Y, K.ord a ≤ d)
    (α : ConnectedComponents ((F.totalTransform π Y).hyp (toLex (Sum.inr PUnit.unit)))) :
    ∃ a'' ∈ componentSet (F.totalTransform π Y) ⟨toLex (Sum.inr PUnit.unit), α⟩,
      (MarkedIdealSheaf.birationalTransform hY h ⟨K, d⟩).I.stalkIdeal a'' = ⊤ := by
  obtain ⟨a', hα, ha'E⟩ : ∃ a' : M',
      a' ∈ componentSet (F.totalTransform π Y) ⟨toLex (Sum.inr PUnit.unit), α⟩ ∧ a' ∈ π ⁻¹' Y :=
    ⟨_, out_mem_componentSet (F.totalTransform π Y) ⟨toLex (Sum.inr PUnit.unit), α⟩, α.out.2⟩
  have haY : π a' ∈ Y := ha'E
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart _ haY
  obtain ⟨i, Φ, hΦ, ha'Φ⟩ := h.cover φ σ hφ a' haφ
  obtain ⟨r, τ, hτr, hlt⟩ := exists_kollarPerm σ i
  -- the base point as a variable, to be identified with `π a''` at the end
  generalize hgen : π a' = a at haY haφ
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  obtain ⟨κ, hτ, -, -, -⟩ := exists_regularCoords_reindex (ψ := ψ) φ hφ.1 haφ τ
  have hP := chartCenter_eq_stalkIdeal_idealSheaf hY hφ haY haφ κ.x r τ hτr hτ hlt
  have hKP : K.stalkIdeal a ≤ IsLocalRing.chartCenter κ.x r ^ d := by
    rw [hP]
    exact (IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp (hord a haY).ge
  have hPm : IsLocalRing.chartCenter κ.x r ≤ IsLocalRing.maximalIdeal _ := by
    rw [κ.span_x]
    exact Ideal.span_mono (Set.image_subset_range _ _)
  have hordK : IsLocalRing.ord (K.stalkIdeal a) = d := by
    refine le_antisymm (hle a haY) ?_
    exact IsLocalRing.le_ord_of_le (hKP.trans (Ideal.pow_right_mono hPm d))
  obtain ⟨f, hfK, hf⟩ := IsLocalRing.exists_mem_ordElem_eq_of_ord_eq hordK
  have hfP : f ∈ IsLocalRing.chartCenter κ.x r ^ d := hKP hfK
  obtain ⟨Q, hQ, -, β, hβ⟩ :=
    IsLocalRing.exists_transformElem_eq_chartPresentation κ.x κ.span_x r hfP hf
  -- the polynomial of values and a ratio vector where it does not vanish
  set Qb : MvPolynomial (Fin r) 𝕜 := MvPolynomial.map (eval 𝕜 E M a) Q with hQb
  have hQb0 : Qb ≠ 0 := by
    intro h0
    have hc : Qb.coeff β = 0 := by rw [h0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [hQb, MvPolynomial.coeff_map] at hc
    exact hβ ((mem_maximalIdeal_iff_eval E _).mpr hc)
  obtain ⟨t, ht⟩ : ∃ t : Fin r → 𝕜, MvPolynomial.eval t Qb ≠ 0 := by
    by_contra hcon
    refine hQb0 (MvPolynomial.funext fun t => ?_)
    rw [map_zero]
    exact Classical.byContradiction fun hne => hcon ⟨t, hne⟩
  -- the ratio vector in the chart's coordinates: position `τ j` (`j < r`) carries `t j`
  let t' : Fin n → 𝕜 := fun j => if hj : j.val < r.val then t ⟨j.val, hj⟩ else 0
  let s : Fin n → 𝕜 := fun m => t' (τ.symm m)
  have hs : ∀ j : Fin r, s (τ (Fin.castLE r.2.le j)) = t j := fun j => by
    simp only [s, t', Equiv.symm_apply_apply, Fin.val_castLE]
    rw [dite_eq_left j.2]
  obtain ⟨a'', ha''α, ha''Φ, hπ, hΦa''⟩ :=
    exists_mem_componentSet_inr_of_ratios F α hφ hΦ ha'Φ hα s
  rw [hgen] at hπ
  subst hπ
  obtain ⟨χ, hχ, hχy, -⟩ := exists_chartRing_hom h hφ hΦ ha''Φ haY κ.x r τ hτr hτ hlt
  have hstalk := birationalTransform_stalkIdeal_eq_map_transformIdeal hY h hφ hΦ ha''Φ haY κ.x r
    τ hτr hτ hlt χ hχ K (fun b hb => (hord b hb).ge)
  refine ⟨a'', ha''α, ?_⟩
  rw [hstalk]
  -- the transform of `f` lies in the transform ideal
  have hmul : algebraMap _ (IsLocalRing.chartRing κ.x r) (κ.x r) ^ d *
      IsLocalRing.transformElem κ.x r f hfP = algebraMap _ _ f := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap,
      IsLocalRing.coe_transformElem]
    rw [← map_pow, mul_comm, Localization.mk_eq_mk', IsLocalization.mk'_spec]
  have hmem : IsLocalRing.transformElem κ.x r f hfP ∈
      IsLocalRing.transformIdeal κ.x r (K.stalkIdeal (π a'')) d :=
    Ideal.subset_span ⟨f, hfK, hmul⟩
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem χ hmem) ?_
  rw [hQ, ← IsLocalRing.notMem_maximalIdeal, mem_maximalIdeal_iff_eval E]
  -- its value at `a''` is `Q̄(t)`
  have hlt' : ∀ j : Fin r, Fin.castLE r.2.le j < r := fun j => by
    rw [Fin.lt_def, Fin.val_castLE]
    exact j.2
  have hval : eval 𝕜 E M' a'' (χ (IsLocalRing.chartPresentation κ.x r Q)) =
      MvPolynomial.eval t Qb := by
    rw [IsLocalRing.chartPresentation, MvPolynomial.aeval_def, hQb, MvPolynomial.eval_map,
      ← RingHom.comp_apply (eval 𝕜 E M' a'') χ, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext z
      simp only [RingHom.comp_apply]
      rw [hχ]
      exact eval_germMapOn _ _ _ _ z
    · funext j
      simp only [Function.comp_apply, RingHom.comp_apply]
      rw [hχy _ (hlt' j), eval_coord, hΦa'']
      have hj : ∃ k, k ≠ i ∧ σ k = τ (Fin.castLE r.2.le j) := by
        obtain ⟨k, hk, hkτ⟩ := (hlt _).mp (hlt' j)
        exact ⟨k, hk, hkτ.symm⟩
      simp only [ite_eq_left hj]
      exact hs j
  rw [hval]
  exact ht

/-! ### The exceptional components, and the corollaries -/

/-- With `ord K ≤ d` on the centre, the exponent of the weak transform along every component of the
exceptional divisor is `0`: read it at the point where the marked transform is the unit ideal
(`exists_mem_componentSet_inr_birationalTransform_stalkIdeal_eq_top`), the marked transform being
the weak transform at the exact order. -/
theorem componentExponent_weakTransformOf_inr [T2Space M] [SecondCountableTopology M]
    (K : IdealSheaf (structureSheaf 𝕜 E M)) {d : ℕ}
    (hord : ∀ a ∈ Y, IdealSheaf.ordAlongIdeal hY.idealSheaf K a = d)
    (hle : ∀ a ∈ Y, K.ord a ≤ d)
    (α : ConnectedComponents ((F.totalTransform π Y).hyp (toLex (Sum.inr PUnit.unit)))) :
    componentExponent (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
      (IdealSheaf.weakTransformOf hY h K) ⟨toLex (Sum.inr PUnit.unit), α⟩ = 0 := by
  have hF' := HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc
  obtain ⟨a'', ha'', htop⟩ :=
    exists_mem_componentSet_inr_birationalTransform_stalkIdeal_eq_top hY h F K hord hle α
  have haY'' : a'' ∈ π ⁻¹' Y := Subtype.coe_image_subset _ _ ha''
  have hD : (componentIdeal (F.totalTransform π Y) hF'
      ⟨toLex (Sum.inr PUnit.unit), α⟩).stalkIdeal a'' ≠ ⊤ := by
    rw [stalkIdeal_componentIdeal_totalTransform_inr hY h F hF hsnc α ha'']
    have hcos := (isIdealSheafOf_exceptionalIdealSheaf hY h).1
    have hmem : a'' ∈ (hY.idealSheaf.pullback π h.contMDiff).support := by
      rw [hcos]
      exact haY''
    exact hmem
  rw [← birationalTransform_eq_weakTransformOf_of_ordAlong_eq hY h K hord,
    componentExponent_eq_toNat_ordAlongIdeal (F.totalTransform π Y) hF' _ _ ha'',
    IdealSheaf.ordAlongIdeal_eq_zero_of_stalkIdeal_eq_top _ _ _ htop hD]
  rfl

/-- All exponents of the weak transform along the components of the transformed boundary family
vanish: along the strict transforms by `componentExponent_weakTransformOf_inl`, along the
exceptional components by `componentExponent_weakTransformOf_inr`. -/
theorem componentExponent_weakTransformOf_eq_zero [T2Space M] [SecondCountableTopology M]
    (K : IdealSheaf (structureSheaf 𝕜 E M)) {d : ℕ}
    (hord : ∀ a ∈ Y, IdealSheaf.ordAlongIdeal hY.idealSheaf K a = d)
    (hle : ∀ a ∈ Y, K.ord a ≤ d)
    (hpure : ∀ i : ComponentIndex F, componentExponent F hF K i = 0)
    (i' : ComponentIndex (F.totalTransform π Y)) :
    componentExponent (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
      (IdealSheaf.weakTransformOf hY h K) i' = 0 := by
  obtain ⟨k, C⟩ := i'
  obtain j | u := k
  · exact componentExponent_weakTransformOf_inl hY h F hF hsnc K hpure C
  · obtain ⟨⟩ := u
    exact componentExponent_weakTransformOf_inr hY h F hF hsnc K hord hle C

/-- The monomial part of the weak transform with respect to the transformed boundary family is the
unit ideal: every component exponent vanishes. -/
theorem monomialPart_weakTransformOf_eq_top [T2Space M] [SecondCountableTopology M]
    (K : IdealSheaf (structureSheaf 𝕜 E M)) {d : ℕ}
    (hord : ∀ a ∈ Y, IdealSheaf.ordAlongIdeal hY.idealSheaf K a = d)
    (hle : ∀ a ∈ Y, K.ord a ≤ d)
    (hpure : ∀ i : ComponentIndex F, componentExponent F hF K i = 0) :
    monomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
      (IdealSheaf.weakTransformOf hY h K) = ⊤ :=
  monomialPart_eq_top_of_forall_componentExponent_eq_zero (F.totalTransform π Y)
    (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc) _
    (componentExponent_weakTransformOf_eq_zero hY h F hF hsnc K hord hle hpure)

/-- Purity of the weak transform: `N_{F'}(W) = W`, from `M_{F'}(W) · N_{F'}(W) = W` with `M_{F'}(W)`
the unit ideal. -/
theorem nonmonomialPart_weakTransformOf_eq_self [T2Space M] [SecondCountableTopology M]
    (K : IdealSheaf (structureSheaf 𝕜 E M)) {d : ℕ}
    (hord : ∀ a ∈ Y, IdealSheaf.ordAlongIdeal hY.idealSheaf K a = d)
    (hle : ∀ a ∈ Y, K.ord a ≤ d)
    (hpure : ∀ i : ComponentIndex F, componentExponent F hF K i = 0) :
    nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
      (IdealSheaf.weakTransformOf hY h K) = IdealSheaf.weakTransformOf hY h K := by
  have h1 := monomialPart_mul_nonmonomialPart (F.totalTransform π Y)
    (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc) (IdealSheaf.weakTransformOf hY h K)
  rw [monomialPart_weakTransformOf_eq_top hY h F hF hsnc K hord hle hpure] at h1
  have h2 : (⊤ : IdealSheaf (structureSheaf 𝕜 E M')) *
      nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        (IdealSheaf.weakTransformOf hY h K) =
      nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        (IdealSheaf.weakTransformOf hY h K) := by
    refine IdealSheaf.ext fun p => ?_
    rw [IdealSheaf.stalkIdeal_mul, IdealSheaf.stalkIdeal_top, Ideal.top_mul]
  exact h2.symm.trans h1

/-- Purity of the marked transform at the exact order: for `K` purely nonmonomial for `F` (as
`K = N(𝓘)`), `d` the exact order of `K` along the centre and `ord K ≤ d` on the centre, the marked
transform `π_*^{-1}(K, d)` is its own nonmonomial part with respect to the transformed boundary
family. This is the one-blow-up form of the remark of [Kol07, 111, Step 1]. -/
theorem nonmonomialPart_birationalTransform_eq_self [T2Space M] [SecondCountableTopology M]
    (K : IdealSheaf (structureSheaf 𝕜 E M)) {d : ℕ}
    (hord : ∀ a ∈ Y, IdealSheaf.ordAlongIdeal hY.idealSheaf K a = d)
    (hle : ∀ a ∈ Y, K.ord a ≤ d)
    (hpure : ∀ i : ComponentIndex F, componentExponent F hF K i = 0) :
    nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        (MarkedIdealSheaf.birationalTransform hY h ⟨K, d⟩).I =
      (MarkedIdealSheaf.birationalTransform hY h ⟨K, d⟩).I := by
  rw [birationalTransform_eq_weakTransformOf_of_ordAlong_eq hY h K hord]
  exact nonmonomialPart_weakTransformOf_eq_self hY h F hF hsnc K hord hle hpure

end Hironaka.Manifold.BMO
