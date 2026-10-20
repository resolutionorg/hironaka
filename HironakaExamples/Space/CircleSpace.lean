/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.JacobianCriterion
public import Hironaka.AnalyticSpace.Complexification
import Hironaka.AnalyticSpace.ModelSupport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The real-analytic space `V(x² + y²) ⊆ ℝ²`

Hironaka's remark that the simple locus of a reduced real-analytic space need not be dense
[Hir64, Introduction], on the example `V(x² + y²) ⊆ ℝ²`: `circleSpace` is the local analytic
`ℝ`-space of the single equation `z₀² + z₁²` on `ℝ²` (`circleEq` of
`HironakaExamples/JacobianCriterion.lean`). Its support is the origin (`circleSpace_eq_zero`,
`subsingleton_circleSpace`, `nonempty_circleSpace`: `x² + y² = 0 ⇒ x = y = 0` over `ℝ`) and its
simple locus is empty (`reg_circleSpace_eq_empty`, from
`circle_setOf_isRegularLocalRing_stalk_eq_empty`); it is reduced
(`HironakaExamples/Space/CircleReduced.lean`).
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold TensorProduct
open scoped Manifold ContDiff

namespace Hironaka.Space

open AnalyticSpace

/-! ### Hironaka's example `V(x² + y²) ⊆ ℝ²` -/

/-- The real-analytic space `V(x² + y²) ⊆ ℝ²`: the local analytic `ℝ`-space of the single equation
`z₀² + z₁²` on `ℝ²` (`circleEq` of `HironakaExamples/JacobianCriterion.lean`). Its underlying
set is the origin, it is reduced (`x² + y²` is irreducible in `ℝ{x, y}`), and its only point is
singular (`𝒪_{X,0} = ℝ{x, y}/(x² + y²)` is not regular): the simple locus is empty although
`X ≠ ∅`: the standard example of the phenomenon Hironaka remarks on, that for a reduced
real-analytic space the simple locus need not be dense [Hir64, Introduction]. -/
def circleSpace : AnalyticSpace.{u} ℝ := localModelSpace ℝ 2 ⊤ circleEq.{u}

theorem circleSpace_toKLocallyRingedSpace :
    circleSpace.{u}.toKLocallyRingedSpace = localModel ℝ 2 ⊤ circleEq.{u} := rfl

/-! ### The circle `V(x² + y²) ⊆ ℝ²`: its points and its simple locus -/

/-- A point of `V(x² + y²)` is a point of `ℝ²` with `x² + y² = 0`. -/
theorem circleSpace_eq_zero (z : circleSpace.{u}) : z.1.1 = (ULift.up 0 : Kn.{u} ℝ 2) := by
  have hz : z.1.1.down 0 * z.1.1.down 0 + z.1.1.down 1 * z.1.1.down 1 = 0 :=
    (mem_cosupport_modelIdeal_iff ℝ 2 ⊤ circleEq z.1).mp z.2 0
  obtain ⟨hx0, hy0⟩ := mul_self_add_mul_self_eq_zero.mp hz
  refine ULift.ext (funext fun i => ?_)
  fin_cases i
  · simpa using hx0
  · simpa using hy0

/-- The underlying set of `V(x² + y²)` is a single point. -/
theorem subsingleton_circleSpace : Subsingleton (circleSpace.{u}) :=
  ⟨fun z w =>
    Subtype.ext (Subtype.ext ((circleSpace_eq_zero z).trans (circleSpace_eq_zero w).symm))⟩

/-- The origin lies on `V(x² + y²)`. -/
theorem nonempty_circleSpace : Nonempty (circleSpace.{u}) :=
  ⟨⟨⟨ULift.up 0, Opens.mem_top _⟩,
    (mem_cosupport_modelIdeal_iff ℝ 2 ⊤ circleEq ⟨ULift.up 0, Opens.mem_top _⟩).mpr fun i => by
      rw [Subsingleton.elim i 0]
      change (0 : ℝ) * 0 + 0 * 0 = 0
      ring⟩⟩

/-- `V(x² + y²) ⊆ ℝ²` has no simple point (`circle_setOf_isRegularLocalRing_stalk_eq_empty`). -/
theorem reg_circleSpace_eq_empty : regularLocus (circleSpace.{u}) = ∅ :=
  circle_setOf_isRegularLocalRing_stalk_eq_empty

end Hironaka.Space
