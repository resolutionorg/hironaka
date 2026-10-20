/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Resolution.Defs

/-!
# Instances for the inputs of the algebraic main theorems

Instances on `AlgebraicGeometry.AlgScheme`, `AlgebraicGeometry.Triple` and
`AlgebraicGeometry.EmbeddedPair` that the proofs of the theorems use and their statements do not:
an algebraic `k`-scheme is separated, a morphism of algebraic `k`-schemes is a `k`-morphism, and
the ambient scheme of a triple or of an embedded pair is smooth. `AlgScheme.of X` is the algebraic
`k`-scheme of a scheme `X` separated and of finite type over `k`, and `AlgScheme.ofHom f` that of
a structure morphism `f`; both unfold to their underlying scheme under reducible transparency.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

namespace AlgScheme

variable {k : Type u} [Field k] (X : AlgScheme k)

instance isSeparated : IsSeparated (X.left ↘ Spec (.of k)) := X.prop.2

/-- A morphism of algebraic `k`-schemes is a `k`-morphism. -/
instance isOver_left {X Y : AlgScheme k} (h : Y ⟶ X) : h.left.IsOver (Spec (.of k)) where
  comp_over := (by simp : h.left ≫ X.hom = Y.hom)

/-- The algebraic `k`-scheme with underlying scheme `X` and structure morphism `f`, of finite type
and separated. It is written as a structure, so that `(ofHom f).left` unfolds to `X` and
`(ofHom f).left ↘ Spec k` to `f` under reducible transparency: instance search and `simp` see
through it. -/
noncomputable abbrev ofHom {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hf : FiniteType f)
    (hs : IsSeparated f) : AlgScheme k where
  left := X
  right := ⟨⟨⟩⟩
  hom := f
  prop := ⟨hf, hs⟩

/-- The algebraic `k`-scheme of a scheme `X` over `Spec k` whose structure morphism is of finite
type and separated; its underlying scheme is `X` (`of_left`), and instance search sees every
instance on `X` at `(of X).left`. -/
noncomputable abbrev of (X : Scheme.{u}) [X.Over (Spec (.of k))] [FiniteType (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] : AlgScheme k :=
  ofHom (X ↘ Spec (.of k)) inferInstance inferInstance

@[simp]
lemma of_left (X : Scheme.{u}) [X.Over (Spec (.of k))] [FiniteType (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] : (of (k := k) X).left = X := rfl

end AlgScheme

namespace Triple

variable {k : Type u} [Field k]

instance smooth (T : Triple k) : Smooth (T.X.left ↘ Spec (.of k)) :=
  T.smoothOfRelativeDimension.elim fun n _ => SmoothOfRelativeDimension.smooth n _

end Triple

namespace EmbeddedPair

variable {k : Type u} [Field k]

instance smooth (P : EmbeddedPair k) : Smooth (P.X.left ↘ Spec (.of k)) :=
  P.smoothOfRelativeDimension.elim fun n _ => SmoothOfRelativeDimension.smooth n _

end EmbeddedPair

end AlgebraicGeometry
