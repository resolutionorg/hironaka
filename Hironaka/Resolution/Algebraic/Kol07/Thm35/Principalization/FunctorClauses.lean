/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Centers
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.ClosedEmbedding
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Functorial
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.IsoLocus
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Monomial
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.BaseChangeParameters
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Scheme.FiniteType
public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.Resolution.Defs
import Hironaka.Scheme.Resolution.Basic

/-!
# Kollár's Theorem 35: functorial principalization

The main theorem `AlgebraicGeometry.exists_functorial_principalization` [Kol07, Theorem 35], with
the principalization sequence `Hironaka.Sequence.BP` as its blow-up sequence functor on the
category `AlgebraicGeometry.Triple k` of the triples of [Kol07, Notation 64]. Each clause is the
corresponding theorem of `Hironaka/Resolution/Algebraic/Kol07/Thm35/Principalization/*.lean`:
(1) the centres are smooth and have simple normal crossings with the total transform of `E`
(`BP_center_smooth_hasSncWith`), (2) the pull-back of `I` is the ideal sheaf of a simple normal
crossing divisor (`BP_isIdealOfSncDivisor`), (3) the sequence is an isomorphism over
`X ∖ (cosupp I ∪ Sing E)` (`BP_isIso_restrict`), (4) it commutes with smooth surjections, with
every smooth morphism up to the deletion of empty blow-ups [Kol07, 34.1]
(`BP_pullback_of_surjective`, `BP_pullback_eraseEmpty`) and with change of fields [Kol07, 34.2]
(`BP_baseChange`), and (5) it commutes with closed embeddings when `E = ∅` [Kol07, 34.3]
(`BP_pushforward_of_closedEmbedding`).

A morphism of triples `h : T' ⟶ T` is a `k`-morphism along which `I` and `E` pull back, so it
carries the pull-back data `Triple.IsPullbackOf` of the functoriality lemmas (the over-`Spec k`
equation is `HomIsOver.comp_over`), and a base change of triples is a cartesian square along which
`I` and `E` pull back, `Triple.IsBaseChangeOf`. In clause (5) the boundary of the embedded triple
`Y` is any family with empty index type; the value of `BP` does not depend on it
(`BP_eq_of_isEmpty`), so it may be replaced by the restriction `E.comap j` of the boundary of the
ambient triple, which is what `Triple.ClosedEmbedding` asks.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme

namespace AlgebraicGeometry

/-- **Kollár's functorial principalization** [Kol07, Theorem 35]. There is a family `BP` of blow-up
sequence functors on triples (`BlowUpSequenceFunctor (Triple k)`), one for each field `k` of
characteristic zero, such that
* every value `BP(X, I, E)`, with composite `Π : X_r → X`, is a principalization of the triple
  (`Triple.IsPrincipalizedBy`): (1) every centre is smooth over `k` and has simple normal
  crossings with the total transform of `E` at its stage; (2) `Π^* I` is the ideal sheaf of a simple
  normal crossing divisor; (3) `Π` is an isomorphism over `X ∖ (cosupp I ∪ Sing E)`;
* (4) `BP` commutes with smooth morphisms [Kol07, 34.1] (`CommutesWithSmoothMorphisms`) and with
  change of fields [Kol07, 34.2] (`CommutesWithChangeOfFields`);
* (5) `BP` commutes with closed embeddings when the boundary is empty [Kol07, 34.3]
  (`CommutesWithClosedEmbeddingsOfEmptyBoundary`).

A triple (`Triple`, [Kol07, Notation 64]) is a smooth, equidimensional algebraic `k`-scheme `X` with
an ideal sheaf `I` nonzero at every point and a simple normal crossing divisor family `E`.

Relation to the source.
* **Translation.** `S.pullback h` is Kollár's pull-back $h^* S$ [Kol07, 30.1],
  `(S.pullback h).eraseEmpty` the same with the blow-ups with empty centre deleted [Kol07, 32], and
  `S.pushforward j` the push-forward $j_* S$ along a closed embedding [Kol07, 30.3];
  `T.I.comap S.composite` is $\Pi^* I$, and `T.E.singularLocus` is $\operatorname{Sing} E$, the set
  of points on at least two components of $E$.
* **Correction.** Clause (3) is stated over
  $X \setminus (\operatorname{cosupp} I \cup \operatorname{Sing} E)$ (`Triple.IsPrincipalizedBy`):
  $\Pi$ is an isomorphism away from the cosupport of $I$ and from the points on at least two
  components of $E$. Kollár prints $X \setminus \operatorname{cosupp} I$, but his functor first
  blows up the intersections of the components of $E$ [Kol07, 72], which need not lie in
  $\operatorname{cosupp} I$; the two loci agree when $E = \emptyset$.
* **Correction.** The order reduction $BMO_1$ of [Kol07, Theorem 107] that the proof runs splits a
  marked ideal as $I = M(I) \cdot N(I)$ with the monomial part
  $M(I) = \prod_D \mathcal{I}_D^{\operatorname{ord}_D I}$ taking one exponent per irreducible
  component $D$ of the boundary members
  (`Hironaka.BMO.monomialPart`; the split of [Wlo05, Section 3, Step 2]). Kollár's construction
  [Kol07, 111] takes one exponent per member, the minimum of $\operatorname{ord}_D I$ over the
  member's components; that split does not commute with open immersions, so clause (2) of
  [Kol07, Theorem 107] fails for it: on $\mathbb{A}^2$ with $E^1 = V(x(x-1))$, $E^2 = V(y(y-1))$ and
  $I = (xy)$ both exponents are $0$, and both are $1$ on the open set $x \ne 1$, $y \ne 1$. The
  fine split commutes with smooth pull-back, since orders at generic points are preserved.
* **Gap.** The inputs are the triples $(X, I, E)$ of [Kol07, Notation 64] (`Triple`), under which
  Kollár proves the theorem: their ambient scheme $X$ is smooth and equidimensional, whereas Theorem
  35 as printed does not ask $X$ to be equidimensional. The base change of a triple along a field
  extension is again a triple.
* **Gap.** Kollár's $E$ is an unordered simple normal crossing divisor. Here it is an ordered family
  (`DivisorFamily`), and clause (4) compares values on families with the induced orders; nothing
  relates the values at two orderings of one divisor.

Source statement: [Kol07, Theorem 35] -/
theorem exists_functorial_principalization :
    ∃ BP : ∀ (k : Type u) [Field k] [CharZero k], BlowUpSequenceFunctor (Triple k),
      -- (1)–(3)
      (∀ (k : Type u) [Field k] [CharZero k] (T : Triple k), T.IsPrincipalizedBy (BP k T)) ∧
      -- (4), 34.1
      (∀ (k : Type u) [Field k] [CharZero k], CommutesWithSmoothMorphisms (BP k)) ∧
      -- (4), 34.2
      CommutesWithChangeOfFields BP ∧
      -- (5), 34.3 with `E = ∅`
      (∀ (k : Type u) [Field k] [CharZero k],
        CommutesWithClosedEmbeddingsOfEmptyBoundary (BP k)) := by
  refine ⟨fun k _ _ T => Hironaka.Sequence.BP T,
    fun _ _ _ T => ⟨Hironaka.Sequence.BP_center_smooth_hasSncWith T,
      Hironaka.Sequence.BP_isIdealOfSncDivisor T, Hironaka.Sequence.BP_isIso_restrict T⟩,
    fun _ _ _ => ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro T T' ⟨h, hI, hE⟩ hs hsurj
    have : Smooth h.left := hs
    exact Hironaka.Sequence.BP_pullback_of_surjective T T' h.left hsurj
      ⟨HomIsOver.comp_over (f := h.left) (S := Spec (.of _)), hI, hE⟩
  · rintro T T' ⟨h, hI, hE⟩ hs
    have : Smooth h.left := hs
    exact Hironaka.Sequence.BP_pullback_eraseEmpty T T' h.left
      ⟨HomIsOver.comp_over (f := h.left) (S := Spec (.of _)), hI, hE⟩
  · rintro k L _ _ _ _ σ T TL p ⟨sq, hI, hE⟩
    exact Hironaka.Sequence.BP_baseChange σ T TL p ⟨sq, hI, hE⟩
  · intro k _ _ T Y j _ hTE hYE hI
    have : IsEmpty (T.E.comap j.left).ι := hTE
    have hE' : (T.E.comap j.left).IsSnc := isSnc_of_isEmpty (Y.X.left ↘ Spec (.of k)) _ hTE
    change Hironaka.Sequence.BP T = (Hironaka.Sequence.BP Y).pushforward j.left
    rw [Hironaka.Sequence.BP_eq_of_isEmpty Y (T.E.comap j.left) hE' hYE]
    exact Hironaka.Sequence.BP_pushforward_of_closedEmbedding T
      { Y with E := T.E.comap j.left, isSnc := hE' } j.left
      ⟨HomIsOver.comp_over (f := j.left) (S := Spec (.of k)), hI, rfl⟩ hTE

end AlgebraicGeometry
