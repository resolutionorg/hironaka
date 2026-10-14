/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Disjoint unions of triples and the domain of a blow-up sequence functor

By [Kol07, Warning 38] the domain of a blow-up sequence functor must contain the disconnected
schemes `∐ᵢ Uᵢ`: a resolution functor on connected schemes extends to disconnected ones, a
blow-up sequence functor does not, because the order of the blow-ups on different components is
part of the output. This is expressed as a predicate on triples
(`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean`): `T.IsSigmaOf Ts ι` says that the cofan
`ι i : (Ts i).X.left ⟶ T.X.left` is a coproduct of schemes over
`Spec k` along which the ideal and the divisor family of `T` restrict to those of the `Ts i`, and
`Triple.ClosedUnderSigma Dom` says that the class `Dom` is closed under finite nonempty disjoint
unions. This module proves the elementary facts about these predicates.

* `isSigmaOf_single`: a triple is the disjoint union of itself along the identity: the one-object
  cofan on an isomorphism is a colimit (Mathlib's `Cofan.isColimitMkOfUnique`), and `comap` along
  the identity is the identity on ideal sheaves (Mathlib) and on divisor families
  (`DivisorFamily.comap_id`, componentwise).
* `isIso_sigmaDesc`: a cofan is a colimit iff the induced morphism from the categorical coproduct
  `∐ᵢ (Ts i).X.left` is an isomorphism (Mathlib's `Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`).
* `isOpenImmersion`, `iUnion_range`, `disjoint_range`: the pieces are open, cover, and are
  pairwise disjoint. Each `ι i` factors as `Sigma.ι _ i ≫ Sigma.desc ι`, an open immersion
  (Mathlib's `sigmaOpenCover`) followed by an isomorphism; every point of `∐` is `Sigma.ι _ i z`
  for a unique `⟨i, z⟩` (Mathlib's homeomorphism `sigmaMk` with the disjoint union of the
  underlying spaces, and `sigmaι_eq_iff`), transported along the isomorphism.
* Closure of the classes that occur: affine underlying scheme (Mathlib's `IsAffine (∐ g)` for a
  finite family of affines, transported along the isomorphism; this is the domain of
  [Kol07, Proposition 37], whose proof uses that `X' = ∐ Uᵢ` is affine); `max-ord I ≤ m` (the
  domain of the order reduction functor of [Kol07, Theorem 68]: the order of `I` at a point
  `ι i z` is the order of `I|_{Uᵢ} = (Ts i).I` at `z`, since the order is invariant under open
  immersions); intersections of closed classes; and for marked triples the classes given by a
  condition on the underlying triple and the classes `T.m = m` of [Kol07, Theorem 69] (the marks
  of the pieces agree with the mark of the whole; a nonempty index type is needed here, which is
  why the nullary union is excluded from `ClosedUnderSigma`).
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.DivisorFamily

open Hironaka

variable {X : Scheme.{u}}

/-- Pulling a divisor family back along the identity changes nothing. -/
@[simp]
theorem comap_id (E : DivisorFamily X) : E.comap (𝟙 X) = E := by
  obtain ⟨ι, c⟩ := E
  simp only [DivisorFamily.comap, Scheme.IdealSheafData.comap_id]

end AlgebraicGeometry.Scheme.DivisorFamily

namespace Hironaka

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k] {σ : Type u} {T : Triple k} {Ts : σ → Triple k}
  {ι : ∀ i, (Ts i).X.left ⟶ T.X.left}

/-- A triple is the disjoint union of the one-member family consisting of itself, along the
identity. -/
theorem isSigmaOf_single (T : Triple k) :
    T.IsSigmaOf (fun _ : PUnit.{u + 1} => T) (fun _ => 𝟙 T.X.left) :=
  ⟨⟨Cofan.isColimitMkOfUnique (Iso.refl T.X.left) PUnit.{u + 1}⟩, fun _ => Category.id_comp _,
    fun _ => (Scheme.IdealSheafData.comap_id _).symm, fun _ =>
        (Scheme.DivisorFamily.comap_id _).symm⟩

/-- The canonical morphism from the coproduct scheme to a disjoint union is an isomorphism. -/
theorem IsSigmaOf.isIso_sigmaDesc (h : T.IsSigmaOf Ts ι) : IsIso (Sigma.desc ι) := by
  have := (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk T.X.left ι)).1 h.1
  rw [cofan_mk_inj] at this
  exact this

/-- The pieces of a disjoint union are open subschemes. -/
theorem IsSigmaOf.isOpenImmersion (h : T.IsSigmaOf Ts ι) (i : σ) : IsOpenImmersion (ι i) := by
  have := h.isIso_sigmaDesc
  have : IsOpenImmersion (Sigma.ι (fun i => (Ts i).X.left) i) := (sigmaOpenCover _).map_prop i
  rw [← Sigma.ι_comp_desc ι i]
  infer_instance

/-- The pieces of a disjoint union cover it. -/
theorem IsSigmaOf.iUnion_range (h : T.IsSigmaOf Ts ι) :
    ⋃ i, Set.range (ι i) = Set.univ := by
  have := h.isIso_sigmaDesc
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨y, rfl⟩ := (Sigma.desc ι).homeomorph.surjective x
  obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk fun i => (Ts i).X.left).surjective y
  refine Set.mem_iUnion.2 ⟨i, z, ?_⟩
  simp only [Scheme.Hom.homeomorph_apply, sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]

/-- Distinct pieces of a disjoint union are disjoint. -/
theorem IsSigmaOf.disjoint_range (h : T.IsSigmaOf Ts ι) {i j : σ} (hij : i ≠ j) :
    Disjoint (Set.range (ι i)) (Set.range (ι j)) := by
  have := h.isIso_sigmaDesc
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have e : Sigma.ι (fun i => (Ts i).X.left) j b = Sigma.ι (fun i => (Ts i).X.left) i a := by
    apply (Sigma.desc ι).homeomorph.injective
    simpa only [Scheme.Hom.homeomorph_apply, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] using hb
  exact hij (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 e)).symm

/-- The class of triples with affine underlying scheme is closed under finite disjoint unions
(the disjoint union `X' = ∐ Uᵢ` of the proof of [Kol07, Proposition 37] is affine). -/
theorem closedUnderSigma_isAffine :
    Triple.ClosedUnderSigma (fun T : Triple k => IsAffine T.X.left) := by
  intro σ _ _ Ts T ι h hD
  have := h.isIso_sigmaDesc
  have : ∀ i, IsAffine (Ts i).X.left := hD
  exact IsAffine.of_isIso (inv (Sigma.desc ι))

/-- The class of triples with `max-ord I ≤ m`, the domain of the order reduction functor of
[Kol07, Theorem 68], is closed under finite disjoint unions. -/
theorem closedUnderSigma_maxOrd_le (m : ℕ) :
    Triple.ClosedUnderSigma (fun T : Triple k => T.I.maxOrd ≤ (m : ℕ∞)) := by
  intro σ _ _ Ts T ι h hD
  rw [Scheme.IdealSheafData.maxOrd_le_iff]
  intro x
  have hx : x ∈ ⋃ i, Set.range (ι i) := h.iUnion_range ▸ Set.mem_univ x
  obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.1 hx
  have := h.isOpenImmersion i
  rw [← Scheme.IdealSheafData.ord_comap_of_isOpenImmersion T.I (ι i) z, ← h.2.2.1 i]
  exact (Scheme.IdealSheafData.le_maxOrd (Ts i).I z).trans (hD i)

/-- The intersection of two classes closed under finite disjoint unions is closed. -/
theorem ClosedUnderSigma.and {D₁ D₂ : Triple k → Prop} (h₁ : Triple.ClosedUnderSigma D₁)
    (h₂ : Triple.ClosedUnderSigma D₂) : Triple.ClosedUnderSigma (fun T => D₁ T ∧ D₂ T) := by
  intro σ _ _ Ts T ι h hD
  exact ⟨h₁ Ts T ι h fun i => (hD i).1, h₂ Ts T ι h fun i => (hD i).2⟩

end AlgebraicGeometry.Triple

namespace Hironaka

namespace MarkedTriple

variable {k : Type u} [Field k]

/-- A class of marked triples given by a condition on the underlying triple is closed under
finite disjoint unions when that condition is. -/
theorem closedUnderSigma_of_triple {D : Triple k → Prop} (h : Triple.ClosedUnderSigma D) :
    MarkedTriple.ClosedUnderSigma (fun T : MarkedTriple k => D T.toTriple) := by
  intro σ _ _ Ts T ι hT hD
  exact h (fun i => (Ts i).toTriple) T.toTriple ι hT.1 hD

/-- The class of marked triples with mark `m` (the domain of the marked order reduction functor
of [Kol07, Theorem 69]) is closed under finite nonempty disjoint unions. -/
theorem closedUnderSigma_m_eq (m : ℕ) :
    MarkedTriple.ClosedUnderSigma (fun T : MarkedTriple k => T.m = m) := by
  intro σ _ _ Ts T ι hT hD
  obtain ⟨i⟩ := ‹Nonempty σ›
  exact (hT.2 i).symm.trans (hD i)

/-- The intersection of two classes of marked triples closed under finite disjoint unions is
closed. -/
theorem ClosedUnderSigma.and {D₁ D₂ : MarkedTriple k → Prop}
    (h₁ : MarkedTriple.ClosedUnderSigma D₁) (h₂ : MarkedTriple.ClosedUnderSigma D₂) :
    MarkedTriple.ClosedUnderSigma (fun T => D₁ T ∧ D₂ T) := by
  intro σ _ _ Ts T ι h hD
  exact ⟨h₁ Ts T ι h fun i => (hD i).1, h₂ Ts T ι h fun i => (hD i).2⟩

end MarkedTriple

end Hironaka
