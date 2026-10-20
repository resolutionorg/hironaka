/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Mathlib.Order.Sigma
public import Hironaka.Scheme.Snc.Dictionary
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Monomials of an snc family are ideal sheaves of snc divisors

[Kol07, Theorem 35 (2)] says that `Π^* I` is "the ideal sheaf of a simple normal crossing divisor";
the predicate `IsIdealOfSncDivisor` asks for an snc family `F` and exponents `a` with
`I = ∏_j (F^j)^{a_j}`. The fine monomial `E.monomial a` of
`Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart` ([Kol07, Definition–Lemma 110]
read on the irreducible components) carries one exponent per irreducible component of the members of
`E`; this module realises it as an `IsIdealOfSncDivisor` through **the component family** of `E` —
the family of all irreducible components of all members, indexed by (member, generic point) in the
lexicographic order — which is snc when `E` is ([Kol07, Definition 24]: "each `E^i` is smooth"; a
member may have several irreducible components, [Kol07, Notation 64 (3)]: "Each `E^i` is allowed to
be reducible or empty", and the sentence after [Kol07, Definition–Lemma 110]): a component has the
stalk of its member at each of its points (`stalkIdeal_componentFamily_eq` of
`Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp`), two components of one member never meet
(`eq_of_mem_support_componentFamily`), so the coordinates of `IsSncAt` are those of `E`. This is how
the principalization theorem's clause (2) is verified for the monomial ideal left at the end of
Kollár's order reduction.

* `DivisorFamily.components`, `components_component`, `support_components_component_le`;
* `DivisorFamily.monomial_eq_prod_components`: `E.monomial a = ∏_p (component p)^{a p}`;
* `Snc.isSnc_components`, `Snc.isIdealOfSncDivisor_monomial`;
* `IsIdealOfSncDivisor.comap_of_smooth`: the property pulls back along smooth morphisms
  (`isSnc_comap_of_smooth` of `Hironaka.Scheme.BlowUpSequence.PullbackSnc`; `comap` is
  multiplicative).

Sources: [Kol07, Theorem 35 (2); Definition 24; Notation 64 (3); Definition–Lemma 110];
[BM08, (5.2)]. -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}} [NoetherianSpace X]

/-- **The component family** of `E` — the irreducible components of all the members, indexed by the
member and the generic point of the component (the `componentFamily` of the member), in the
lexicographic order (the members may be reducible, [Kol07, Notation 64 (3)]; the sentence after
[Kol07, Definition–Lemma 110] speaks of the "irreducible components of some of the `E^i`"). -/
noncomputable def components (E : DivisorFamily X) : DivisorFamily X where
  ι := Σₗ i : E.ι, (E.component i).componentFamily.ι
  component := fun p => (E.component (ofLex p).1).componentFamily.component (ofLex p).2

theorem components_component (E : DivisorFamily X) (p : E.components.ι) :
    E.components.component p =
      (E.component (ofLex p).1).componentFamily.component (ofLex p).2 := rfl

/-- A component lies in its member. -/
theorem support_components_component_le (E : DivisorFamily X) (p : E.components.ι) :
    (E.components.component p).support ≤ (E.component (ofLex p).1).support :=
  IsConcreteLE.le_iff.mpr fun x hx =>
    ((Hironaka.Sequence.mem_support_componentFamily_iff _ _ x).mp hx).mem_closed
      (E.component (ofLex p).1).support.isClosed (ofLex p).2.2.1

/-- The fine monomial `𝒪_X(−∑_D a_D D)` is the product over the component family of the powers of
the components. -/
theorem monomial_eq_prod_components (E : DivisorFamily X) (a : X → ℕ) :
    E.monomial a = ∏ p : E.components.ι, E.components.component p ^ a (ofLex p).2.1 := by
  unfold DivisorFamily.monomial
  change _ = ∏ p : (Σ i : E.ι, (E.component i).componentFamily.ι),
    (E.component p.1).componentFamily.component p.2 ^ a p.2.1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← finprod_set_coe_eq_finprod_mem,
    @finprod_eq_prod_of_fintype ((E.component i).support.genericPoints) _ _
      ((E.component i).componentFamily.fintype : Fintype ((E.component i).support.genericPoints))]
  rfl

end AlgebraicGeometry.Scheme.DivisorFamily

namespace Hironaka.Snc

variable {X : Scheme.{u}} [NoetherianSpace X]

/-- [Kol07, Definition 24] for the components of members that may be reducible
([Kol07, Notation 64 (3)]): the component family of a simple normal crossing family is simple normal
crossing — a component is regular with the stalks of its member, and at a point the components
through it are in bijection with the members through it (two components of one member are disjoint),
so Kollár's coordinates for `E` serve. -/
theorem isSnc_components {E : DivisorFamily X} (hE : E.IsSnc) : E.components.IsSnc := by
  refine ⟨fun p => Hironaka.Sequence.isRegular_subscheme_componentFamily _ (hE.1 _) _, fun x => ?_⟩
  obtain ⟨n, z, hz, c, hcinj, hc⟩ := hE.2 x
  have hmem : ∀ p : {p : E.components.ι // x ∈ (E.components.component p).support},
      x ∈ (E.component (ofLex p.1).1).support :=
    fun p => DivisorFamily.support_components_component_le E p.1 p.2
  refine ⟨n, z, hz, fun p => c ⟨(ofLex p.1).1, hmem p⟩, fun p q hpq => ?_, fun p => ?_⟩
  · obtain ⟨⟨i, η⟩, hp⟩ := p
    obtain ⟨⟨j, ζ⟩, hq⟩ := q
    have hij : i = j := congrArg Subtype.val (hcinj hpq)
    subst hij
    have hηζ : η = ζ :=
      Hironaka.Sequence.eq_of_mem_support_componentFamily (E.component i) (hE.1 i) hp hq
    subst hηζ
    rfl
  · exact (Hironaka.Sequence.stalkIdeal_componentFamily_eq _ (hE.1 _) _ p.2).trans
      (hc ⟨(ofLex p.1).1, hmem p⟩)

/-- [Kol07, Theorem 35 (2)] in the vocabulary of `IsIdealOfSncDivisor`: a monomial of a simple
normal crossing family (one exponent per irreducible component) is the ideal sheaf of a simple
normal crossing divisor in the sense of that predicate — of the component family, with the same
exponents. -/
theorem isIdealOfSncDivisor_monomial {E : DivisorFamily X} (hE : E.IsSnc) (a : X → ℕ) :
    IsIdealOfSncDivisor (E.monomial a) :=
  ⟨E.components, fun p => a (ofLex p).2.1, isSnc_components hE, E.monomial_eq_prod_components a⟩

end Hironaka.Snc

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsIdealOfSncDivisor

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}

/-- [Kol07, 34.1] for clause (2) of Theorem 35: the ideal sheaf of an effective divisor supported on
an snc family pulls back along a smooth morphism to one — the family pulls back to an snc family
(`isSnc_comap_of_smooth`) and `comap` is multiplicative (`comap_finset_prod`, `comap_pow`). -/
theorem comap_of_smooth (f : X ⟶ Spec (.of k)) [Smooth f] (h : Y ⟶ X) [Smooth h]
    {I : X.IdealSheafData} (hI : IsIdealOfSncDivisor I) : IsIdealOfSncDivisor (I.comap h) := by
  obtain ⟨F, a, hF, rfl⟩ := hI
  refine ⟨F.comap h, a, isSnc_comap_of_smooth f h hF, ?_⟩
  rw [comap_finset_prod]
  exact Finset.prod_congr rfl fun j _ => comap_pow _ _ _

end AlgebraicGeometry.Scheme.IdealSheafData.IsIdealOfSncDivisor
