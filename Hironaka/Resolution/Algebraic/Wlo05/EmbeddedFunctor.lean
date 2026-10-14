/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
public import Hironaka.Scheme.BlowUpSequence.Assignment
public import Hironaka.Scheme.Snc.EmptyFamily
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The embedded desingularization functor

[Wlo05, Theorem 1.0.2] asks for an assignment `Y ↦ S` of a succession of blow-ups to EVERY
reduced closed subscheme `Y` of a smooth equidimensional `k`-scheme `X` of finite type — the
functor type `EmbeddedDesingularizationAssignment k` has the single field `seq`, defined on every
smooth `X` of finite type and every ideal sheaf `Y`. The embedded desingularization sequence `BED`
(`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) runs on a `Triple k`: `X` equidimensional and the
ideal NONZERO ON EVERY IRREDUCIBLE COMPONENT of `X` (Kollár's standing convention, [Kol07, Notation
64]). The theorem's hypotheses have the former (`∃ n, SmoothOfRelativeDimension n (X ↘ Spec k)`) and
not the latter: a reduced `Y` may contain irreducible components of `X` (Włodarczyk's `X` is a
variety, where this means `Y = X`).

**The totalisation.** `EDFunctor k` assigns `BED ⟨X, hX, coreIdeal Y, …, ∅, …⟩` when `X` is
equidimensional (classically decided) and the empty succession otherwise, where the **core** of
`Y` is the reduced ideal sheaf of `V(Y) ∩ X₁`, `X₁ = componentsOutside Y` the (finite, closed)
union of the irreducible components of `X` NOT contained in `V(Y)`:

* `coreIdeal Y` is reduced by construction (`isReduced_subscheme_vanishingIdeal`) and nonzero
  everywhere on any Noetherian space (`isNonzeroEverywhere_coreIdeal`; the scheme is one by
  `noetherianSpace_of_field`): off `V(Y) ∩ X₁` its stalk is the unit ideal; at a point of a
  component `C ⊄ V(Y)` a zero stalk would propagate to the generic point of `C`
  (`stalkIdeal_eq_bot_of_specializes`), putting it — hence `C` — inside `V(Y)`;
* when `Y` is reduced and nonzero everywhere, `coreIdeal Y = Y`
  (`coreIdeal_eq_of_isNonzeroEverywhere`): no component lies in `V(Y)` (at a generic point of a
  component the maximal ideal of the smooth stalk is zero,
  `maximalIdeal_stalk_eq_bot_of_isGenericPoint`), so `X₁ = X` and `V(Y)`'s reduced ideal is `Y`
  (`vanishingIdeal_support_of_isReduced`). Hence on the inputs of the sources
  `(EDFunctor k).seq X Y = BED ⟨X, hX, Y, hY, DivisorFamily.empty X, _⟩` on the nose
  (`EDFunctor_seq_of_isNonzeroEverywhere`); off them the run is `BED` of the core on `X` itself —
  no pushforward, no second scheme — and the clauses about `Y` follow from the clauses about the
  core on the clopen cover `X = X₀ ⊔ X₁`
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorSplit`,
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`).

The functor is the witness of the theorem
`AlgebraicGeometry.exists_functorial_embeddedDesingularization`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`).
For the empty succession on disconnected inputs compare [Kol07, Warning 38].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Scheme Hironaka IdealSheafData
  BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Resolution

/-! ### The core of an ideal sheaf: the reduced ideal of `V(Y)` on the components outside `V(Y)` -/

section Core

variable {X : Scheme.{u}} [NoetherianSpace X]

/-- The union of the irreducible components of `X` NOT contained in `V(Y)` — finitely many closed
sets (`X` a Noetherian space), so closed. Named after Mathlib's `irreducibleComponents`; the
complement is the union of the components inside `V(Y)`. -/
noncomputable def componentsOutside (Y : X.IdealSheafData) : Closeds X :=
  ⟨⋃₀ {C | C ∈ irreducibleComponents X ∧ ¬ C ⊆ (Y.support : Set X)}, by
    rw [Set.sUnion_eq_biUnion]
    exact (NoetherianSpace.finite_irreducibleComponents.subset fun C hC => hC.1).isClosed_biUnion
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1⟩

theorem mem_componentsOutside_iff (Y : X.IdealSheafData) (x : X) :
    x ∈ componentsOutside Y ↔
      ∃ C ∈ irreducibleComponents X, ¬ C ⊆ (Y.support : Set X) ∧ x ∈ C := by
  change x ∈ ⋃₀ {C | C ∈ irreducibleComponents X ∧ ¬ C ⊆ (Y.support : Set X)} ↔ _
  rw [Set.mem_sUnion]
  constructor
  · rintro ⟨C, ⟨hC, hCY⟩, hxC⟩
    exact ⟨C, hC, hCY, hxC⟩
  · rintro ⟨C, hC, hCY, hxC⟩
    exact ⟨C, ⟨hC, hCY⟩, hxC⟩

/-- The **core** of `Y` — the reduced ideal sheaf of `V(Y) ∩ X₁`, `X₁` the components of `X`
outside `V(Y)`; the ideal on which `BED` is run. -/
noncomputable def coreIdeal (Y : X.IdealSheafData) : X.IdealSheafData :=
  vanishingIdeal (Y.support ⊓ componentsOutside Y)

theorem support_coreIdeal (Y : X.IdealSheafData) :
    (coreIdeal Y).support = Y.support ⊓ componentsOutside Y :=
  Hironaka.Sequence.support_vanishingIdeal_eq _

theorem isReduced_subscheme_coreIdeal (Y : X.IdealSheafData) :
    IsReduced (coreIdeal Y).subscheme :=
  isReduced_subscheme_vanishingIdeal _

/-- The core is nonzero on every irreducible component ([Kol07, Notation 64 (2)]): off `V(Y) ∩ X₁`
its stalk is the unit ideal; at `x ∈ X₁`, on a component `C ⊄ V(Y)` through `x` with generic point
`η ⤳ x`, a zero stalk at `x` would be a zero stalk at `η` (`stalkIdeal_eq_bot_of_specializes`), so
`η ∈ V(Y)` and `C = closure {η} ⊆ V(Y)`. -/
theorem isNonzeroEverywhere_coreIdeal (Y : X.IdealSheafData) :
    IsNonzeroEverywhere (coreIdeal Y) := by
  intro x hx
  by_cases hmem : x ∈ (coreIdeal Y).support
  · rw [support_coreIdeal] at hmem
    have hmem' : x ∈ ((Y.support ⊓ componentsOutside Y : Closeds X) : Set X) := hmem
    rw [Closeds.coe_inf] at hmem'
    obtain ⟨C, hC, hCY, hxC⟩ := (mem_componentsOutside_iff Y x).mp hmem'.2
    have hirr : IsIrreducible C := hC.1
    have hgen : IsGenericPoint hirr.genericPoint C :=
      hirr.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    have hη : (coreIdeal Y).stalkIdeal hirr.genericPoint = ⊥ :=
      stalkIdeal_eq_bot_of_specializes _ (hgen.specializes hxC) hx
    have hηsupp : hirr.genericPoint ∈ (coreIdeal Y).support :=
      (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mpr (by rw [hη]; exact bot_le)
    rw [support_coreIdeal] at hηsupp
    have hηsupp' : hirr.genericPoint ∈ ((Y.support ⊓ componentsOutside Y : Closeds X) : Set X) :=
      hηsupp
    rw [Closeds.coe_inf] at hηsupp'
    apply hCY
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηsupp'.1) Y.support.isClosed
  · have hx' : (coreIdeal Y).stalkIdeal x = ⊥ := hx
    rw [stalkIdeal_eq_top_of_notMem_support _ hmem] at hx'
    have h1 : (1 : X.presheaf.stalk x) ∈ (⊥ : Ideal (X.presheaf.stalk x)) := by
      rw [← hx']
      exact Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp h1)

end Core

section Smooth

variable {k : Type u} [Field k] {X : Scheme.{u}} [NoetherianSpace X]
  (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]

include f in
/-- On a smooth `X`, an ideal sheaf nonzero everywhere is contained in no irreducible component's
ideal: at the generic point `η` of a component the smooth stalk is a field
(`maximalIdeal_stalk_eq_bot_of_isGenericPoint`), so `Y_η ≤ 𝔪_η = ⊥` contradicts `Y_η ≠ ⊥`. Hence
every component is outside `V(Y)`. -/
theorem componentsOutside_eq_top_of_isNonzeroEverywhere (Y : X.IdealSheafData)
    (hY : IsNonzeroEverywhere Y) : componentsOutside Y = ⊤ := by
  refine Closeds.ext ?_
  rw [Closeds.coe_top]
  refine Set.eq_univ_of_forall fun x => ?_
  refine (mem_componentsOutside_iff Y x).mpr
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, fun hsub => ?_,
      mem_irreducibleComponent⟩
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hgen : IsGenericPoint hirr.genericPoint (irreducibleComponent x) :=
    hirr.isGenericPoint_genericPoint isClosed_irreducibleComponent
  have hreg := isRegularLocalRing_stalk f hirr.genericPoint
  have hmax : maximalIdeal (X.presheaf.stalk hirr.genericPoint) = ⊥ :=
    maximalIdeal_stalk_eq_bot_of_isGenericPoint
      (irreducibleComponent_mem_irreducibleComponents x) hgen
  have hle := (mem_support_iff_stalkIdeal_le_maximalIdeal Y _).mp (hsub hgen.mem)
  rw [hmax, le_bot_iff] at hle
  exact hY _ hle

include f in
/-- On the inputs of the sources — `Y` reduced and nonzero everywhere on the smooth `X` — the core
is `Y` itself: `X₁ = X` and `V(Y)`'s reduced ideal is `Y`. -/
theorem coreIdeal_eq_of_isNonzeroEverywhere (Y : X.IdealSheafData)
    [IsReduced Y.subscheme] (hY : IsNonzeroEverywhere Y) : coreIdeal Y = Y := by
  rw [coreIdeal, componentsOutside_eq_top_of_isNonzeroEverywhere f Y hY, inf_top_eq,
    vanishingIdeal_support_of_isReduced]

end Smooth

/-! ### The functor -/

section Functor

variable {k : Type u} [Field k] [CharZero k]

/-- `BED` depends on the triple's ideal only through its value: changing the proof-irrelevant fields
and rewriting the ideal along an equation gives the same succession. -/
theorem BED_congr_I (T : Triple k) (I' : T.X.left.IdealSheafData) (hI : T.I = I')
    (hI' : IsNonzeroEverywhere I') :
    BED T = BED { T with I := I', isNonzeroEverywhere := hI' } := by
  subst hI
  rfl

omit [CharZero k] in
/-- A scheme quasi-compact and locally of finite type over a field is Noetherian
(`Scheme.Hom.isNoetherian_of_field`), hence a Noetherian space (Mathlib's
`IsNoetherian.noetherianSpace`). -/
theorem noetherianSpace_of_field {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] : NoetherianSpace X :=
  haveI : IsNoetherian X := f.isNoetherian_of_field
  inferInstance

open Classical in
/-- The **embedded desingularization functor** — the witness of
`AlgebraicGeometry.exists_functorial_embeddedDesingularization` ([Wlo05, Theorem 1.0.2]): on an
equidimensional `X` (classically decided) the embedded desingularization sequence `BED` on the
triple `(X, coreIdeal Y, ∅)`, the empty succession otherwise (the theorem asserts nothing there).
On the inputs of the sources the core is `Y` (`EDFunctor_seq_of_isNonzeroEverywhere`). -/
noncomputable def EDFunctor (k : Type u) [Field k] [CharZero k] :
    EmbeddedDesingularizationAssignment k where
  seq X _ _ _ _ Y :=
    haveI : NoetherianSpace X := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
    if h : ∃ n : ℕ, SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k)) then
      BED (⟨.of X, h, coreIdeal Y, isNonzeroEverywhere_coreIdeal Y, DivisorFamily.empty X,
        isSnc_empty_of_smooth (X ↘ Spec (CommRingCat.of k))⟩ : Triple k)
    else BlowUpSequence.nil X

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k))] [Smooth (X ↘ Spec (CommRingCat.of k))]
  (Y : X.IdealSheafData)

/-- On an equidimensional `X` the functor is `BED` on the core. -/
theorem EDFunctor_seq_of_pos [NoetherianSpace X]
    (hX : ∃ n : ℕ, SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) :
    (EDFunctor k).seq X Y =
      BED (⟨.of X, hX, coreIdeal Y, isNonzeroEverywhere_coreIdeal Y, DivisorFamily.empty X,
        isSnc_empty_of_smooth (X ↘ Spec (CommRingCat.of k))⟩ : Triple k) :=
  dite_eq_left hX

/-- Off the equidimensional schemes the functor assigns the empty succession. -/
theorem EDFunctor_seq_of_neg
    (hX : ¬ ∃ n : ℕ, SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) :
    (EDFunctor k).seq X Y = BlowUpSequence.nil X :=
  dite_eq_right hX

/-- The inputs of the sources: for `Y` reduced and nonzero everywhere on the equidimensional `X`,
the functor is `BED ⟨X, hX, Y, hY, ∅, _⟩` on the nose. -/
theorem EDFunctor_seq_of_isNonzeroEverywhere
    (hX : ∃ n : ℕ, SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k)))
    [IsReduced Y.subscheme] (hY : IsNonzeroEverywhere Y) :
    (EDFunctor k).seq X Y =
      BED (⟨.of X, hX, Y, hY, DivisorFamily.empty X,
        isSnc_empty_of_smooth (X ↘ Spec (CommRingCat.of k))⟩ : Triple k) := by
  have := noetherianSpace_of_field (X ↘ Spec (CommRingCat.of k))
  rw [EDFunctor_seq_of_pos X Y hX]
  exact BED_congr_I
    (⟨.of X, hX, coreIdeal Y, isNonzeroEverywhere_coreIdeal Y, DivisorFamily.empty X,
      isSnc_empty_of_smooth (X ↘ Spec (CommRingCat.of k))⟩ : Triple k) Y
    (coreIdeal_eq_of_isNonzeroEverywhere (X ↘ Spec (CommRingCat.of k)) Y hY) hY

end Functor

end Hironaka.Resolution
