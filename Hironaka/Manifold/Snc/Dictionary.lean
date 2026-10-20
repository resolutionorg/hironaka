/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.Snc.Basic
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Algebra.Local.PrimeProducts
import Hironaka.Algebra.Local.Regular
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.Snc.Bundled
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Snc.TotalTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Simple normal crossings divisors and Hironaka's Definition 2

The dictionary between Kollár's simple normal crossings divisors (`HypersurfaceFamily.IsSnc`,
`HasSncWith`, [Kol07, Definition 24]) and the stalk-level predicates of Hironaka's Definition 2
[Hir64, Definition 2, p. 141] (`IdealSheaf.IsReduced`, `IdealSheaf.IsInvertible`,
`IdealSheaf.HasOnlyNormalCrossingsWith`) on the reduced ideal sheaf
`F.idealSheaf` of the divisor, whose stalks `Hironaka/Manifold/Snc/Coherence.lean` computed: at
a point `x` with snc chart `φ` and indices `c`, `(F.idealSheaf)_x = (∏_{j : x ∈ E^j} z_{c j})`, a
product of distinct coordinates, each a prime element of the regular local ring `𝒪_{M,x}`; the
algebra of products of primes is `Hironaka/Algebra/Local/PrimeProducts.lean`.

* `E` **reduced** (Hironaka's "no nilpotent elements" [Hir64, p. 111]): a product of pairwise
  non-associated primes generates a radical ideal (a prime dividing a power divides the element).
* `E` **invertible** ("everywhere of codimension one" [Hir64, Definition 2, p. 141]): the product
  is a non-zero-divisor of the domain `𝒪_{M,x}`.
* `E` **has only normal crossings** (Definition 2 with `D = M`): the centred coordinates
  `z_i − z_i(x)` of the snc chart are a regular system of parameters (`𝔪_x = (z_i − z_i(x))`,
  `dim 𝒪_{M,x} = n`), the minimal primes of `(∏ z_{c j})` are the `(z_{c j})` (a prime containing
  the product contains a factor, and `(z_{c j})` is prime), and the ideal of `D = M` is `⊥ = (∅)`.
* **`Y` has simple normal crossings with `F` implies Definition 2 for
  `(E, D) = (F.idealSheaf, 𝓘_Y)`** ([Kol07, Definition 24 (4)] → [Hir64, Definition 2]; the
  converse is `hasOnlyNormalCrossingsWith_idealSheaf_iff` of
  `Hironaka/Manifold/Snc/NormalCrossings.lean`): at `x ∈ Y` the chart adapted to `Y` and snc for
  `F` gives the parameters; `(𝓘_Y)_x = (z_{σ i})` is `(z '' s)` for `s` the image of `σ`.
* **Hironaka's `red(f⁻¹(E) ∪ f⁻¹(D))` is the reduced ideal sheaf of Kollár's total transform**
  ([Hir64, Main Theorem II'(N) (iii), p. 156] and [Kol07, Definition 25] agree): both are the
  vanishing ideal sheaf of the closed set `π⁻¹(|F|) ∪ π⁻¹(Y) = |Π⁻¹_tot(F)|`
  (`support_totalTransform`), whose stalks have local generators because the total transform is
  snc — so the guarded branch of the definition of the reduced transform is taken.

These are the facts that identify the boundary clauses of the main theorems, stated through
`IsSncBoundary` and `IsSncBoundaryWith`, with the boundary families the resolution algorithm
carries (`Hironaka/Manifold/FiniteSuccession/BoundaryFamily.lean`).
-/

public section

open TopologicalSpace Filter Topology IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The coordinates of the components through a point, at that point -/

section Unbundled

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {F : HypersurfaceFamily M}
  {φ : OpenPartialHomeomorph M E} {a : M} {c : {j // a ∈ F.hyp j} → Fin n}

namespace HypersurfaceFamily

/-- The coordinates of the components through `a` vanish at `a`. -/
theorem IsSncChartAt.coord_eq_zero (hc : F.IsSncChartAt ψ φ a c) (j : {j // a ∈ F.hyp j}) :
    ψ (φ a) (c j) = 0 :=
  (hc.mem_iff j hc.2.1).mp j.2

/-- The coordinates of the components through `a` are prime elements of `𝒪_{M,a}`. -/
theorem IsSncChartAt.prime_coord (hc : F.IsSncChartAt ψ φ a c) (j : {j // a ∈ F.hyp j}) :
    Prime (coord E ψ φ hc.1 hc.2.1 (c j)) :=
  prime_coord_of_eq_zero φ hc.1 hc.2.1 (hc.coord_eq_zero j)

/-- The coordinates of two distinct components through `a` do not divide each other. -/
theorem IsSncChartAt.not_coord_dvd (hc : F.IsSncChartAt ψ φ a c) {i j : {j // a ∈ F.hyp j}}
    (hij : i ≠ j) : ¬ coord E ψ φ hc.1 hc.2.1 (c i) ∣ coord E ψ φ hc.1 hc.2.1 (c j) :=
  not_coord_dvd_coord_of_ne φ hc.1 hc.2.1 (hc.coord_eq_zero i) fun h => hij (hc.injective h)

/-- The centred coordinates `z_i − z_i(a)` of a chart: a regular system of parameters of `𝒪_{M,a}`
(they generate `𝔪_a`, and `dim 𝒪_{M,a} = n`). -/
theorem IsSncChartAt.span_range_centred_eq_and_dim (hc : F.IsSncChartAt ψ φ a c) :
    Ideal.span (Set.range fun i => coord E ψ φ hc.1 hc.2.1 i -
        const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hc.1 hc.2.1 i))) =
      maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ∧
    (n : WithBot ℕ∞) = ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  ⟨(maximalIdeal_eq_span_coord' E ψ φ hc.2.1 hc.1).symm,
    (ringKrullDim_stalk_of_chart E ψ φ hc.2.1 hc.1).symm⟩

/-- For a coordinate vanishing at `a`, the centred coordinate is the coordinate itself. -/
theorem centred_coord_eq_of_eq_zero {hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M} {ha : a ∈ φ.source}
    {k : Fin n} (h0 : ψ (φ a) k = 0) :
    coord E ψ φ hφ ha k - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha k)) =
      coord E ψ φ hφ ha k := by
  rw [eval_coord, h0, map_zero, sub_zero]

/-- Hironaka's "`E` reduced" [Hir64, p. 111]: the stalks of the reduced ideal sheaf of an snc
divisor are radical ideals. -/
theorem IsSnc.isRadical_stalkIdeal_idealSheaf (hF : F.IsSnc ψ) (x : M) :
    ((F.idealSheaf (𝕜 := 𝕜) (E := E)).stalkIdeal x).IsRadical := by
  obtain ⟨φ, c, hc⟩ := hF.exists_isSncChartAt x
  rw [hF.stalkIdeal_idealSheaf_eq_span_prod hc]
  refine isRadical_span_prod (fun j _ => hc.prime_coord _) fun i _ j _ hij =>
    hc.not_coord_dvd fun h => hij ?_
  have h2 := congrArg Subtype.val h
  exact Subtype.ext (show i.1 = j.1 from h2)

/-- Hironaka's "everywhere of codimension one" [Hir64, Definition 2, p. 141]: the stalks of the
reduced ideal sheaf of an snc divisor are generated by a single non-zero-divisor. -/
theorem IsSnc.exists_nonZeroDivisor_stalkIdeal_idealSheaf (hF : F.IsSnc ψ) (x : M) :
    ∃ g : (structureSheaf 𝕜 E M).presheaf.stalk x,
      g ∈ nonZeroDivisors ((structureSheaf 𝕜 E M).presheaf.stalk x) ∧
        (F.idealSheaf (𝕜 := 𝕜) (E := E)).stalkIdeal x = Ideal.span {g} := by
  obtain ⟨φ, c, hc⟩ := hF.exists_isSncChartAt x
  refine ⟨_, ?_, hF.stalkIdeal_idealSheaf_eq_span_prod hc⟩
  have hreg := isRegularLocalRing_stalk_of_chart E ψ φ hc.2.1 hc.1
  have hdom : IsDomain ((structureSheaf 𝕜 E M).presheaf.stalk x) := inferInstance
  refine mem_nonZeroDivisors_of_ne_zero ?_
  refine Finset.prod_induction _ (fun g => g ≠ 0) (fun _ _ => mul_ne_zero) one_ne_zero
    fun j _ => (hc.prime_coord _).ne_zero

/-- The minimal primes of Hironaka's Definition 2: in an snc chart at `x`, the minimal primes of
the stalk of the reduced ideal sheaf are the ideals of the coordinates of the components through
`x`, read in the centred coordinates of the chart. -/
theorem IsSncChartAt.minimalPrimes_stalkIdeal_idealSheaf (hF : F.IsSnc ψ)
    (hc : F.IsSncChartAt ψ φ a c) {P : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk a)}
    (hP : P ∈ ((F.idealSheaf (𝕜 := 𝕜) (E := E)).stalkIdeal a).minimalPrimes) :
    ∃ i, P = Ideal.span
      {coord E ψ φ hc.1 hc.2.1 i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hc.1 hc.2.1 i))} := by
  rw [hF.stalkIdeal_idealSheaf_eq_span_prod hc] at hP
  obtain ⟨j, -, hPj⟩ := minimalPrimes_span_prod (fun j _ => hc.prime_coord _) hP
  refine ⟨c ⟨j.1, (hF.2.1.point_finite a).mem_toFinset.mp j.2⟩, ?_⟩
  rw [hPj, centred_coord_eq_of_eq_zero (hc.coord_eq_zero _)]

end HypersurfaceFamily

end Unbundled

/-! ### The predicates of Definition 2 on bundled manifolds -/

section Bundled

variable {N N' : AnalyticManifold.{u} 𝕜 E}

open HypersurfaceFamily

/-- The reduced ideal sheaf of an snc divisor is reduced ([Hir64, Definition 2, p. 141],
"`E` reduced"). -/
theorem isReduced_idealSheaf {F : HypersurfaceFamily N} (hF : F.IsSnc ψ) :
    AnalyticManifold.IdealSheaf.IsReduced (F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
  hF.isRadical_stalkIdeal_idealSheaf

/-- The reduced ideal sheaf of an snc divisor is invertible ([Hir64, Definition 2, p. 141], "the
sheaf of ideals of `E` is invertible"). -/
theorem isInvertible_idealSheaf {F : HypersurfaceFamily N} (hF : F.IsSnc ψ) :
    IdealSheaf.IsInvertible (F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
  hF.exists_nonZeroDivisor_stalkIdeal_idealSheaf

/-- The reduced ideal sheaf of an snc divisor has only normal crossings in Hironaka's sense
([Hir64, Definition 2, p. 141] with `D = M`). -/
theorem hasOnlyNormalCrossings_idealSheaf {F : HypersurfaceFamily N} (hF : F.IsSnc ψ) :
    AnalyticManifold.IdealSheaf.HasOnlyNormalCrossings (F.idealSheaf (𝕜 := 𝕜) (E := E)) := by
  intro x _
  obtain ⟨φ, c, hc⟩ := hF.exists_isSncChartAt x
  refine ⟨n, fun i => coord E ψ φ hc.1 hc.2.1 i -
      const 𝕜 E N x (eval 𝕜 E N x (coord E ψ φ hc.1 hc.2.1 i)),
    hc.span_range_centred_eq_and_dim, fun P hP => hc.minimalPrimes_stalkIdeal_idealSheaf hF hP,
    ∅, ?_⟩
  rw [IdealSheaf.stalkIdeal_bot, Finset.coe_empty, Set.image_empty, Ideal.span_empty]

/-- [Kol07, Definition 24 (4)] → [Hir64, Definition 2, p. 141]: if the closed submanifold `Y` has
simple normal crossings with the snc divisor `F`, the reduced ideal sheaf of `F` has only normal
crossings with the ideal sheaf of `Y` in Hironaka's sense. -/
theorem HasSncWith.hasOnlyNormalCrossingsWith_idealSheaf {F : HypersurfaceFamily N}
    (hF : F.IsSnc ψ) {Y : Set N} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c)
    (hsnc : F.HasSncWith ψ Y c) :
    AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith (F.idealSheaf (𝕜 := 𝕜) (E := E))
      hY.idealSheaf := by
  intro x hx
  have hxY : x ∈ Y := by
    rwa [IsClosedSubmanifold.cosupport_idealSheaf] at hx
  obtain ⟨φ, σ, cidx, hφ, hc⟩ := hsnc x hxY
  refine ⟨n, fun i => coord E ψ φ hc.1 hc.2.1 i -
      const 𝕜 E N x (eval 𝕜 E N x (coord E ψ φ hc.1 hc.2.1 i)),
    hc.span_range_centred_eq_and_dim, fun P hP => hc.minimalPrimes_stalkIdeal_idealSheaf hF hP,
    Finset.univ.map σ, ?_⟩
  rw [hY.isIdealSheafOf_idealSheaf.2 φ σ hφ x hc.2.1 hxY, Finset.coe_map, Finset.coe_univ,
    Set.image_univ, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  change coord E ψ φ hc.1 hc.2.1 (σ i) = _ - _
  rw [centred_coord_eq_of_eq_zero ((hφ.2 x hc.2.1).mp hxY i)]

/-- Hironaka's `E_{λ+1} = red(f⁻¹(E_λ) ∪ f⁻¹(D_λ))` [Hir64, Main Theorem II'(N) (iii), p. 156] is
Kollár's total transform [Kol07, Definition 25]: under the blowing-up of `N` along `Y`, the reduced
transform of the reduced ideal sheaf of an snc divisor `F` having snc with `Y` is the reduced ideal
sheaf of the snc total transform. -/
theorem reducedTransform_eq_idealSheaf_totalTransform {π : N' → N} {Y : Set N} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) {F : HypersurfaceFamily N}
    (hF : F.IsSnc ψ) (hsnc : F.HasSncWith ψ Y c) :
    AnalyticManifold.IdealSheaf.reducedTransform (⟨π, h.contMDiff⟩ : AnalyticMap N'
        N) (F.idealSheaf (𝕜 := 𝕜) (E := E)) hY.idealSheaf =
      (F.totalTransform π Y).idealSheaf (𝕜 := 𝕜) (E := E) := by
  have hT : (F.totalTransform π Y).IsSnc ψ := isSnc_totalTransform hY h hF hsnc
  let f : AnalyticMap N' N := ⟨π, h.contMDiff⟩
  have hset : ⇑f ⁻¹' IdealSheaf.support (F.idealSheaf (𝕜 := 𝕜) (E := E)) ∪
      ⇑f ⁻¹' IdealSheaf.support hY.idealSheaf =
          (F.totalTransform π Y).support := by
    change π ⁻¹' (F.idealSheaf (𝕜 := 𝕜) (E := E)).support ∪ π ⁻¹' hY.idealSheaf.support = _
    rw [hF.cosupport_idealSheaf, hY.cosupport_idealSheaf,
      support_totalTransform π Y F h.contMDiff.continuous fun j => (hF.1 j).isClosed]
  have hgen : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N') fun x : N' =>
      vanishingStalk (𝕜 := 𝕜) (E := E)
        (⇑f ⁻¹' IdealSheaf.support (F.idealSheaf (𝕜 := 𝕜) (E := E)) ∪
          ⇑f ⁻¹' IdealSheaf.support hY.idealSheaf) x := by
    rw [hset]
    exact hT.hasLocalGenerators_vanishingStalk_support
  refine IdealSheaf.ext fun x => ?_
  change (AnalyticManifold.IdealSheaf.reducedTransform f (F.idealSheaf (𝕜 := 𝕜) (E := E))
    hY.idealSheaf).stalkIdeal x = _
  rw [reducedTransform_stalkIdeal_of_hasLocalGenerators f _ _ hgen x, hT.stalkIdeal_idealSheaf,
    hset]

end Bundled

end Manifold
