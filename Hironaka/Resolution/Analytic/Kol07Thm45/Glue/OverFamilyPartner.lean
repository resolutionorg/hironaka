/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictInclusion
public import Hironaka.AnalyticSpace.Glue.Over
public import Hironaka.AnalyticSpace.SncFamily
import Hironaka.Algebra.RegularSmooth.ParameterCount
import Hironaka.AnalyticSpace.SncBoundaryChart
import Hironaka.AnalyticSpace.SncFamilyTransport
import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictSetIncl
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The partner of a member of an exceptional family across a gluing transition

Across the transition `ψ : (R i)|_{glueOpens i j} ≅ (R j)|_{glueOpens j i}` of a gluing datum
(`GlueOver`, `Hironaka.AnalyticSpace.Glue.Over`), the members of two simple-normal-crossings
families `H₁`, `H₂` of closed subspaces of the pieces (`ClosedSubspace.IsSncFamily`,
`Hironaka.AnalyticSpace.SncFamily`) are matched by a label `e : Λ₁ → Λ₂`. In the resolution of an
analytic space the label is the stage of the blow-up sequence at which a member is created: the
blow-up sequences of two pieces have the same centres on the overlap at every stage [Kol07,
Proposition 37, (37.2)], so the exceptional divisors created at one stage correspond. Given the
labelled identity locally, an open subset around every point on which the pull-back along `ψ` of the
trace of `H₂ (e σ)` is the trace of `H₁ σ`, it holds on the whole gluing open subset
(`comap_restrict_eq_of_forall_exists_local`: equality of closed subspaces is stalkwise), and for a
member with non-empty trace the partner `e σ` is the unique member of `H₂` whose pull-back is that
trace (`existsUnique_partner_of_forall_exists_local_label`), because two members of a
simple-normal-crossings family with the same stalk ideal at a common point of their supports are the
same member (`IsSncFamily.eq_of_stalkIdeal_eq_of_mem_support`): the chart at the point assigns each
member through it one parameter of a regular system of parameters, distinct members distinct
parameters, and two parameters of a regular system generating the same principal ideal coincide,
their classes in `𝔪/𝔪²` being linearly independent over the residue field
(`IsRegularLocalRing.index_eq_of_span_singleton_eq_of_span_range_eq`, from
`IsRegularLocalRing.linearIndependent_toCotangent_of_span_eq` of
`Hironaka.Algebra.RegularSmooth.ParameterCount`).

A label-free local correspondence does not determine the partner when members are disconnected: for
four disjoint lines `A, A', B, B'` and the families `H₁ = {A ∪ B, A' ∪ B'}`,
`H₂ = {A ∪ B', A' ∪ B}`, the local correspondences match `A ∪ B` to `A ∪ B'` near `A` and to
`A' ∪ B` near `B`. Hence the partner is read as the label.

The two statements about a gluing datum have no code users outside this module: the chain form of
`Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverFamilyChain` restates them in the `restrictOpen`
spelling of the traces (`ClosedSubspace.comap_eq_of_forall_exists_local`,
`existsUnique_comap_eq_of_forall_exists_local`), which is what the gluing along an exhaustion uses.
The rigidity lemma `IsSncFamily.eq_of_stalkIdeal_eq_of_mem_support` is used there too.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set
open Manifold

universe u

namespace IsRegularLocalRing

/-- **Two members of a regular system of parameters of a regular local ring generating the same
principal ideal are the same member** (the classes of a regular system of parameters in `𝔪/𝔪²`
are linearly independent over the residue field,
`IsRegularLocalRing.linearIndependent_toCotangent_of_span_eq`): if `z a = r * z b`, the classes of
`z a` and `z b` in `𝔪/𝔪²` are proportional over the residue field, against their linear
independence. -/
theorem index_eq_of_span_singleton_eq_of_span_range_eq {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {m : ℕ} (z : Fin m → R)
    (hspan : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hdim : (m : WithBot ℕ∞) = ringKrullDim R) {a b : Fin m}
    (h : Ideal.span {z a} = Ideal.span {z b}) : a = b := by
  have hz : ∀ i, z i ∈ IsLocalRing.maximalIdeal R := fun i =>
    hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hli := IsRegularLocalRing.linearIndependent_toCotangent_of_span_eq z hz hspan hdim
  by_contra hab
  have hmem : z a ∈ Ideal.span {z b} := h ▸ Ideal.mem_span_singleton_self (z a)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  -- the cotangent class of `z a` is `r` times that of `z b`
  have hva : (IsLocalRing.maximalIdeal R).toCotangent ⟨z a, hz a⟩ =
      (IsLocalRing.residue R r) • (IsLocalRing.maximalIdeal R).toCotangent ⟨z b, hz b⟩ := by
    have h1 : (IsLocalRing.residue R r) • (IsLocalRing.maximalIdeal R).toCotangent ⟨z b, hz b⟩ =
        r • (IsLocalRing.maximalIdeal R).toCotangent ⟨z b, hz b⟩ := algebraMap_smul _ r _
    rw [h1, ← map_smul]
    exact congrArg _ (Subtype.ext hr.symm)
  -- the linear combination `v a - r • v b = 0` has a nonzero coefficient
  have hsum : ∑ i ∈ ({a, b} : Finset (Fin m)),
      (fun i => if i = a then (1 : IsLocalRing.ResidueField R) else -(IsLocalRing.residue R r)) i •
        (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨z i, hz i⟩) i = 0 := by
    rw [Finset.sum_pair hab]
    beta_reduce
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hab), one_smul, neg_smul, ← hva, add_neg_cancel]
  have h0 := linearIndependent_iff'.mp hli {a, b} _ hsum a (Finset.mem_insert_self a {b})
  rw [ite_eq_left rfl] at h0
  exact one_ne_zero h0

end IsRegularLocalRing

namespace AnalyticSpace.ClosedSubspace

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K}

/-- The stalks of a space carrying a simple-normal-crossings family are regular local rings (the
`∀ x` clause of `IsSncFamily`). -/
theorem IsSncFamily.isRegularLocalRing_stalk_of_isSncFamily {ι : Type u} {H : ι → ClosedSubspace X}
    (h : IsSncFamily H) (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨n, z, ⟨hspan, hdim⟩, -, -⟩ := h.2 x
  have : IsNoetherianRing (X.presheaf.stalk x) := AnalyticSpace.isNoetherianRing_stalk X x
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [← hdim, ← hspan]
  have hle : (Ideal.span (Set.range z)).spanFinrank ≤ n := by
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    calc (Set.range z).ncard = (z '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_image_le Set.finite_univ
      _ = n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact_mod_cast hle

/-- **Rigidity of the members of a simple-normal-crossings family at one point** ([Kol07, Definition
24]): two members of the family with the same stalk ideal at a common point of their supports are
the same member: the chart at the point assigns each member through it one parameter of the regular
system of parameters, injectively. -/
theorem IsSncFamily.eq_of_stalkIdeal_eq_of_mem_support {ι : Type u} {H : ι → ClosedSubspace X}
    (h : IsSncFamily H) {σ τ : ι} {x : X} (hσ : x ∈ (H σ).support) (hτ : x ∈ (H τ).support)
    (hst : (H σ).stalkIdeal x = (H τ).stalkIdeal x) : σ = τ := by
  have _hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    h.isRegularLocalRing_stalk_of_isSncFamily x
  obtain ⟨n, z, ⟨hspan, hdim⟩, c, hc, hH⟩ := h.2 x
  have h1 : Ideal.span {z (c ⟨σ, hσ⟩)} = Ideal.span {z (c ⟨τ, hτ⟩)} :=
    (hH ⟨σ, hσ⟩).symm.trans (hst.trans (hH ⟨τ, hτ⟩))
  exact congrArg Subtype.val
    (hc (IsRegularLocalRing.index_eq_of_span_singleton_eq_of_span_range_eq z hspan hdim h1))

/-- A point of the support of a trace on an open subspace lies in the support of the member
(`QuotientSpace.cosupport_comap`). -/
theorem mem_support_of_comap_restrictInclusion {A : ClosedSubspace X} (S : Set X)
    {p : restrictSet X S}
    (hp : p ∈ (A.comap (restrictInclusion X S)).support) : p.1 ∈ A.support :=
  (Set.ext_iff.mp (QuotientSpace.cosupport_comap
    (restrictInclusion X S).1 A) p).mp hp

/-- Two closed subspaces with the same trace on an open subspace have the same stalk ideal at every
point of the open subset: the stalk map of the open inclusion is an isomorphism
(`KLocallyRingedSpace.isIso_ofRestrict_stalkMap`, `QuotientSpace.stalkIdeal_comap`). -/
theorem stalkIdeal_eq_of_comap_restrictInclusion_eq {A B : ClosedSubspace X} (S : Set X)
    (h :
        A.comap (restrictInclusion X S) =
      B.comap (restrictInclusion X S))
    (p : restrictSet X S) : A.stalkIdeal p.1 =
        B.stalkIdeal p.1 := by
  have hiso : IsIso ((restrictInclusion X S).1.stalkMap p) :=
    KLocallyRingedSpace.isIso_ofRestrict_stalkMap X.toKLocallyRingedSpace
        (AnalyticSpace.openOf X S) p
  have hbij : Function.Bijective
      ((restrictInclusion X S).1.stalkMap p).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hA :=
      QuotientSpace.stalkIdeal_comap (restrictInclusion X S).1 A
          p
  have hB :=
      QuotientSpace.stalkIdeal_comap (restrictInclusion X S).1 B
          p
  have hmap : (A.stalkIdeal p.1).map
        ((restrictInclusion X S).1.stalkMap p).hom =
      (B.stalkIdeal p.1).map
          ((restrictInclusion X S).1.stalkMap p).hom :=
    hA.symm.trans
        ((congrArg (fun D : ClosedSubspace (restrictSet X S) =>
      D.stalkIdeal p) h).trans hB)
  have h2 := congrArg
    (Ideal.comap ((restrictInclusion X S).1.stalkMap p).hom) hmap
  exact (Ideal.comap_map_of_bijective _ hbij).symm.trans
    (h2.trans (Ideal.comap_map_of_bijective _ hbij))

/-- Two members of a simple-normal-crossings family with the same trace on an open subspace, the
trace non-empty, are the same member. -/
theorem IsSncFamily.eq_of_comap_restrictInclusion_eq_of_nonempty {ι : Type u}
    {H : ι → ClosedSubspace X} (h : IsSncFamily H) (S : Set X) {σ τ : ι}
    (heq : (H σ).comap (restrictInclusion X S) = (H τ).comap (restrictInclusion X S))
    (hne : ((H σ).comap (restrictInclusion X S)).support.Nonempty) : σ = τ := by
  obtain ⟨p, hp⟩ := hne
  have hp' := hp
  rw [heq] at hp'
  exact h.eq_of_stalkIdeal_eq_of_mem_support (mem_support_of_comap_restrictInclusion S hp)
    (mem_support_of_comap_restrictInclusion S hp')
    (stalkIdeal_eq_of_comap_restrictInclusion_eq S heq p)

end AnalyticSpace.ClosedSubspace

namespace AnalyticSpace.GlueOver

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K} {ι : Type u}
  {R : ι → AnalyticSpace.{u} K}
  {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace} {dom : ι → Opens X}

/-- **The labelled identity is local** ([Kol07, Proposition 37, (37.2)]: the centres of the blow-up
sequences of two pieces agree on the overlap at every stage): the pull-back along the transition of
the trace of the label-`e σ` member of `H₂` is the trace of `H₁ σ` on the whole gluing open subset
as soon as it is so near every point, for every `σ`, because equality of closed subspaces is
stalkwise. No simple-normal-crossings hypothesis. -/
theorem comap_restrict_eq_of_forall_exists_local {Λ₁ Λ₂ : Type u} (i j : ι)
    (H₁ : Λ₁ → ClosedSubspace (R i)) (H₂ : Λ₂ → ClosedSubspace (R j))
    (ψ : (R i).restrictSet (SetLike.coe (glueOpens X R π dom i j)) ⟶ (R j).restrictSet
        (SetLike.coe (glueOpens X R π dom j i)))
    (e : Λ₁ → Λ₂)
    (hloc : ∀ x : (R i).restrictSet (SetLike.coe (glueOpens X R π dom i j)),
      ∃ V : Set ((R i).restrictSet (SetLike.coe (glueOpens X R π dom i j))),
        IsOpen V ∧ x ∈ V ∧ ∀ σ,
        (((H₂ (e σ)).comap (restrictInclusion (R j) (SetLike.coe (glueOpens X R π dom j i)))).comap
            ψ).comap (restrictInclusion _ V) =
        ((H₁ σ).comap
            (restrictInclusion (R i)
            (SetLike.coe (glueOpens X R π dom i j)))).comap (restrictInclusion _ V)) :
    ∀ σ, ((H₂ (e σ)).comap
        (restrictInclusion (R j) (SetLike.coe (glueOpens X R π dom j i)))).comap ψ =
      (H₁ σ).comap (restrictInclusion (R i) (SetLike.coe (glueOpens X R π dom i j))) := by
  intro σ
  apply IdealSheaf.ext
  intro y
  obtain ⟨V, hVo, hyV, hV⟩ := hloc y
  have hyV' : y ∈ AnalyticSpace.openOf _ V :=
    (AnalyticSpace.mem_openOf_iff_of_isOpen _ hVo y).mpr hyV
  exact ClosedSubspace.stalkIdeal_eq_of_comap_restrictInclusion_eq V (hV σ) ⟨y, hyV'⟩

/-- **The partner is the label, unique among the members of `H₂`**: for a member of `H₁` with
non-empty trace on the gluing open subset, `e σ` is the unique member of `H₂` whose trace pulls back
along the transition to the trace of `H₁ σ`: existence by
`comap_restrict_eq_of_forall_exists_local`, uniqueness by the rigidity of the
simple-normal-crossings family `fun τ => comap ψ (trace of H₂ τ)` (`isSncFamily_comap_of_isIso`,
`IsSncFamily.comap_ofRestrict`) at a point of the non-empty support. -/
theorem existsUnique_partner_of_forall_exists_local_label {Λ₁ Λ₂ : Type u} (i j : ι)
    (H₁ : Λ₁ → ClosedSubspace (R i)) (H₂ : Λ₂ → ClosedSubspace (R j))
    (h₂ : ClosedSubspace.IsSncFamily H₂)
    (ψ : (R i).restrictSet (SetLike.coe (glueOpens X R π dom i j)) ⟶ (R j).restrictSet
        (SetLike.coe (glueOpens X R π dom j i)))
    (hψ : IsIso ψ) (e : Λ₁ → Λ₂)
    (hloc : ∀ x : (R i).restrictSet (SetLike.coe (glueOpens X R π dom i j)),
      ∃ V : Set ((R i).restrictSet (SetLike.coe (glueOpens X R π dom i j))),
        IsOpen V ∧ x ∈ V ∧ ∀ σ,
        (((H₂ (e σ)).comap (restrictInclusion (R j) (SetLike.coe (glueOpens X R π dom j i)))).comap
            ψ).comap (restrictInclusion _ V) =
        ((H₁ σ).comap
            (restrictInclusion (R i)
            (SetLike.coe (glueOpens X R π dom i j)))).comap (restrictInclusion _ V))
    (σ : Λ₁)
    (hσ :
        ((H₁ σ).comap
            (restrictInclusion (R i) (SetLike.coe (glueOpens X R π dom i j)))).support.Nonempty) :
    ∃! τ, ((H₂ τ).comap (restrictInclusion (R j) (SetLike.coe (glueOpens X R π dom j i)))).comap ψ =
      (H₁ σ).comap (restrictInclusion (R i) (SetLike.coe (glueOpens X R π dom i j))) := by
  have hall := comap_restrict_eq_of_forall_exists_local i j H₁ H₂ ψ e hloc
  refine ⟨e σ, hall σ, fun τ hτ => ?_⟩
  -- the pulled-back traces of `H₂` form a simple-normal-crossings family on the gluing open subset
  have hfam : ClosedSubspace.IsSncFamily fun τ =>
      ((H₂ τ).comap (restrictInclusion (R j) (SetLike.coe (glueOpens X R π dom j i)))).comap ψ :=
    ClosedSubspace.isSncFamily_comap_of_isIso ψ hψ
      (h₂.comap_ofRestrict (AnalyticSpace.openOf (R j)
        (SetLike.coe (glueOpens X R π dom j i))))
  obtain ⟨p, hp⟩ := hσ
  have hpτ := hp
  rw [← hτ] at hpτ
  have hpe := hp
  rw [← hall σ] at hpe
  exact hfam.eq_of_stalkIdeal_eq_of_mem_support hpτ hpe
    (congrArg (fun D : ClosedSubspace ((R i).restrictSet
      (SetLike.coe (glueOpens X R π dom i j))) => D.stalkIdeal p)
      (hτ.trans (hall σ).symm))

end AnalyticSpace.GlueOver

end
