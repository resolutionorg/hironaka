/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The resolution of an affine scheme without a chosen embedding

Once the resolution `BR(X)` of an affine scheme is known to be independent of the embedding
`X ↪ A` used to construct it [Kol07, Theorem 36, proof], it can be defined without a choice.
This file fixes the hypotheses under which Kollár's construction runs and makes that definition.

## Main definitions

* `AdmissibleEmbedding k X TA emb`: `emb : X ⟶ TA.X.left` is a closed immersion over `k` into the
  ambient of a triple `TA = (A, I_X, ∅)` with `A` affine (Kollár's "smooth affine scheme":
  smoothness is part of being a triple), empty boundary, and `I_X = ker emb`. Every use of the
  independence theorem `Hironaka.Resolution.BR_affine_indep` goes through this one predicate.
* `BR_affine' k X : BlowUpSequence X`: Kollár's `BR(X)` for a scheme `X` over `k` without a
  chosen embedding, namely `BR_affine TA emb` for a chosen admissible pair `(TA, emb)` when one
  exists (`Classical.choice`; `Hironaka.Resolution.BR_affine'_eq` shows that the value does not
  depend on the choice), and the empty sequence `nil X` otherwise.

The second branch is never reached for an affine scheme of finite type over `k`, which always
has an admissible embedding (`Hironaka.Resolution.exists_admissibleEmbedding`); the definition
is nevertheless total, so that no existence statement is built into it. The unfolding lemmas
`BR_affine'_of_pos` and `BR_affine'_of_neg` are the two branches of the `if`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence

namespace Hironaka.Resolution

variable (k : Type u) [Field k] [CharZero k]

/-- An **admissible embedding** of the scheme `X` over `k` into the ambient of the triple `TA`:
a closed immersion `emb : X ⟶ TA.X.left` over `k`, with `TA.X.left` affine, the boundary of `TA`
empty and the ideal of `TA` the kernel of `emb`. These are the hypotheses of Kollár's construction
of the resolution of an affine scheme: an embedding `X ↪ A` into a smooth affine scheme and the
blow-up sequence `BP(A, I_X, ∅)` (the proof of [Kol07, Theorem 36]). -/
def AdmissibleEmbedding (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (TA : Triple k)
    (emb : X ⟶ TA.X.left) : Prop :=
  IsClosedImmersion emb ∧ emb.IsOver (Spec (CommRingCat.of k)) ∧ IsAffine TA.X.left ∧
    IsEmpty TA.E.ι ∧ emb.ker = TA.I

open Classical in
/-- Kollár's resolution `BR(X)` of a scheme `X` over `k` without a chosen embedding: `BR_affine
TA emb` for a chosen admissible pair `(TA, emb)` if one exists, the empty sequence otherwise.
`BR_affine'_eq` shows that the value does not depend on the choice [Kol07, Theorem 36, proof]. -/
noncomputable def BR_affine' (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] :
    BlowUpSequence X :=
  if h : ∃ (TA : Triple k) (emb : X ⟶ TA.X.left), AdmissibleEmbedding k X TA emb then
    BR_affine h.choose h.choose_spec.choose
  else nil X

theorem BR_affine'_of_pos (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    (h : ∃ (TA : Triple k) (emb : X ⟶ TA.X.left), AdmissibleEmbedding k X TA emb) :
    BR_affine' k X = BR_affine h.choose h.choose_spec.choose := by
  unfold BR_affine'
  rw [dite_eq_left h]

theorem BR_affine'_of_neg (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    (h : ¬ ∃ (TA : Triple k) (emb : X ⟶ TA.X.left), AdmissibleEmbedding k X TA emb) :
    BR_affine' k X = nil X := by
  unfold BR_affine'
  rw [dite_eq_right h]

end Hironaka.Resolution
