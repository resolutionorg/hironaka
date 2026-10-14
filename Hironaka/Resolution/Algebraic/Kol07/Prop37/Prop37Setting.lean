/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The setting of Proposition 37: the affine cover of a triple as one smooth surjection

Kollár's Proposition 37 [Kol07, Proposition 37] extends a blow-up sequence functor from affine
schemes to all schemes of finite type by descent along the smooth surjection
`g : X' = ∐ᵢ Uᵢ → X` from the disjoint union of a finite affine open cover, using the two
projections `τ₁, τ₂ : X'' → X'` of `X'' = X' ×_X X'`. The definitions `Triple.affineCover`,
`coverScheme`, `coverDesc`, `coverPair`, `coverFst`, `coverSnd` and the affine class
`Triple.IsAffineScheme` are in `Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean`; this
module proves the elementary facts about them and defines the triples `coverTriple` and
`coverPairTriple` of `X'` and `X''`.

* **`X'` is affine** (`isAffine_coverScheme`): a finite coproduct of affine schemes (Mathlib's
  instance), the pieces being members of Mathlib's affine cover and the index type the finite
  subcover's.
* **`g` is a smooth surjection** (`smooth_coverDesc`, `surjective_coverDesc`): smoothness is local
  on the source and each piece `Uᵢ → X` is an open immersion (`IsZariskiLocalAtSource.sigmaDesc`);
  the pieces cover `X` (`Cover.iUnion_range`).
* **`X'` is a triple's scheme** (`locallyOfFiniteType_coverScheme`, `quasiCompact_coverScheme`,
  `isSeparated_coverScheme`, `exists_smoothOfRelativeDimension_coverScheme`): `X' → Spec k` factors
  as `g ≫ (X → Spec k)`; finite type by composition, quasi-compact and separated because `X'` is
  affine over the affine base, and smooth of the relative dimension `n` of `X` because each piece
  is an open subscheme of `X` (relative dimension `0 + n`, locality on the source again).
* **`X''` is affine** (`isAffine_coverPair`): `X' → X → Spec k` is an affine morphism and
  `X → Spec k` is separated (a triple's ambient scheme is separated over `k`), so `g` is an affine
  morphism (`IsAffineHom.of_comp`) and the fibre product of `g` with itself is affine. Kollár's
  `X''` is the disjoint union of the `Uᵢ ∩ Uⱼ`; that an intersection of two affine opens is affine
  uses the separatedness of `X`, a point left implicit in his text.
* **`τ₁, τ₂` are smooth surjections** (`smooth_coverFst`, …): base change of `g`; surjectivity
  from the image of a pullback projection (`range_fst_of_isPullback`).
* **The triples** (`coverTriple`, `coverPairTriple`): the pullback triple `Triple.pullback` along
  `g`, resp. along `τ₁`, with the pullback data along `τ₂` as well
  (`coverPairTriple_isPullbackOf_snd`: `τ₁ ≫ g = τ₂ ≫ g` and `comap_comp`); the existence
  statements package them without the constructions.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka

variable {k : Type u} [Field k]

/-- The affine marked triples are closed under finite disjoint unions ([Kol07, Warning 38] for
the domain of Proposition 37): `closedUnderSigma_of_triple` applied to `closedUnderSigma_isAffine`
(the class is `fun T => IsAffine T.X.left` by definition). -/
theorem MarkedTriple.closedUnderSigma_isAffineScheme :
    MarkedTriple.ClosedUnderSigma (MarkedTriple.IsAffineScheme (k := k)) :=
  MarkedTriple.closedUnderSigma_of_triple (D := fun T : Triple k => IsAffine T.X.left)
    Triple.closedUnderSigma_isAffine

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

open Scheme

variable (T : Triple k)

/-- The finite subcover has a finite index type. -/
instance finite_affineCover_I₀ : Finite T.affineCover.I₀ := by
  have : CompactSpace T.X.left :=
    QuasiCompact.compactSpace_of_compactSpace (T.X.left ↘ Spec (CommRingCat.of k))
  delta Triple.affineCover
  infer_instance

/-- The members of the finite affine cover are affine. -/
instance isAffine_affineCover_X (i : T.affineCover.I₀) : IsAffine (T.affineCover.X i) := by
  exact Scheme.isAffine_affineCover T.X.left _

/-- `X'` is affine (the proof of [Kol07, Proposition 37]). -/
theorem isAffine_coverScheme : IsAffine T.coverScheme := by
  delta Triple.coverScheme
  infer_instance

instance : IsAffine T.coverScheme := isAffine_coverScheme T

/-- The piece inclusions: `Sigma.ι i ≫ g` is the member `Uᵢ → X` of the cover. -/
@[reassoc]
theorem ι_comp_coverDesc (i : T.affineCover.I₀) :
    Sigma.ι (fun i => T.affineCover.X i) i ≫ T.coverDesc = T.affineCover.f i :=
  Sigma.ι_comp_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- `g` is smooth: locality on the source (`IsZariskiLocalAtSource.sigmaDesc`; the unifier option
is Mathlib's own idiom for this lemma, cf. `Flat (Sigma.desc f)` in `Morphisms/Flat.lean`). -/
theorem smooth_coverDesc : Smooth T.coverDesc :=
  IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

instance : Smooth T.coverDesc := smooth_coverDesc T

-- Same unifier option as `smooth_coverDesc` above: `IsZariskiLocalAtSource.sigmaDesc` needs the
-- instance `IsZariskiLocalAtSource (@SmoothOfRelativeDimension 0)`, which the
-- transparency-respecting unifier does not find.
set_option backward.isDefEq.respectTransparency.types false in
/-- `g` is smooth of relative dimension `0` (a coproduct of open immersions). -/
theorem smoothOfRelativeDimension_zero_coverDesc : SmoothOfRelativeDimension 0 T.coverDesc :=
  IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

/-- `g` is surjective. -/
theorem surjective_coverDesc : Function.Surjective T.coverDesc :=
  (Surjective.sigmaDesc_of_union_range_eq_univ T.affineCover.iUnion_range).surj

-- Same unifier option as `smooth_coverDesc` above: `IsZariskiLocalAtSource.sigmaDesc` needs the
-- instance `IsZariskiLocalAtSource @LocallyOfFiniteType`, which the transparency-respecting unifier
-- does not find.
set_option backward.isDefEq.respectTransparency.types false in
/-- `X'` is locally of finite type over `Spec k`. -/
theorem locallyOfFiniteType_coverScheme :
    LocallyOfFiniteType (T.coverScheme ↘ Spec (CommRingCat.of k)) := by
  have : LocallyOfFiniteType T.coverDesc := IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  exact inferInstanceAs (LocallyOfFiniteType (T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k))))

instance : LocallyOfFiniteType (T.coverScheme ↘ Spec (CommRingCat.of k)) :=
  locallyOfFiniteType_coverScheme T

/-- `X'` is quasi-compact over `Spec k`. -/
theorem quasiCompact_coverScheme : QuasiCompact (T.coverScheme ↘ Spec (CommRingCat.of k)) :=
  inferInstance

/-- `X'` is separated over `Spec k`. -/
theorem isSeparated_coverScheme : IsSeparated (T.coverScheme ↘ Spec (CommRingCat.of k)) :=
  IsSeparated.of_isAffineHom _

instance : IsSeparated (T.coverScheme ↘ Spec (CommRingCat.of k)) := isSeparated_coverScheme T

/-- `g ≫ (X → Spec k)` as a coproduct morphism. -/
theorem coverDesc_comp :
    T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k)) =
      Sigma.desc fun i => T.affineCover.f i ≫ (T.X.left ↘ Spec (CommRingCat.of k)) :=
  Sigma.hom_ext _ _ fun i => by
    rw [ι_comp_coverDesc_assoc, Sigma.ι_comp_desc]

-- Same unifier option as `smooth_coverDesc` above: `IsZariskiLocalAtSource.sigmaDesc` needs the
-- instance `IsZariskiLocalAtSource (@SmoothOfRelativeDimension n)`, which the
-- transparency-respecting unifier does not find.
set_option backward.isDefEq.respectTransparency.types false in
/-- `X'` is smooth over `k` of the relative dimension of `X` (the equidimensionality required of
a triple, [Kol07, Notation 64]). -/
theorem exists_smoothOfRelativeDimension_coverScheme :
    ∃ n : ℕ, SmoothOfRelativeDimension n (T.coverScheme ↘ Spec (CommRingCat.of k)) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  refine ⟨n, ?_⟩
  change SmoothOfRelativeDimension n (T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k)))
  rw [coverDesc_comp]
  refine IsZariskiLocalAtSource.sigmaDesc fun i => ?_
  simpa using
    smoothOfRelativeDimension_comp 0 n (T.affineCover.f i) (T.X.left ↘ Spec (CommRingCat.of k))

/-- The triple `(X', g^* I, g^{-1} E)` of the proof of [Kol07, Proposition 37]: the pullback of
`T` along `g`. -/
noncomputable def coverTriple [PerfectField k] : Triple k :=
  Triple.pullback T (exists_smoothOfRelativeDimension_coverScheme T) T.coverDesc

theorem coverTriple_X [PerfectField k] : T.coverTriple.X.left = T.coverScheme := rfl

theorem coverTriple_I [PerfectField k] : T.coverTriple.I = T.I.comap T.coverDesc := rfl

theorem coverTriple_E [PerfectField k] : T.coverTriple.E = T.E.comap T.coverDesc := rfl

/-- The triple of `X'` is affine. -/
theorem isAffine_coverTriple [PerfectField k] : T.coverTriple.IsAffineScheme :=
  isAffine_coverScheme T

/-- The triple of `X'` carries the pullback data of `T` along `g`. -/
theorem coverTriple_isPullbackOf [PerfectField k] : T.coverTriple.IsPullbackOf T T.coverDesc :=
  isPullbackOf_pullback T _ _

/-- The setting of the proof of [Kol07, Proposition 37], without the construction: an affine
triple with a smooth surjection to `T.X.left` carrying the pullback data. -/
theorem exists_isAffine_isPullbackOf [PerfectField k] :
    ∃ (T' : Triple k) (g : T'.X.left ⟶ T.X.left), T'.IsAffineScheme ∧ Smooth g ∧
      Function.Surjective g ∧ T'.IsPullbackOf T g :=
  ⟨T.coverTriple, T.coverDesc, isAffine_coverTriple T, smooth_coverDesc T, surjective_coverDesc T,
    coverTriple_isPullbackOf T⟩

/-- `X''` is affine (`g` is an affine morphism since `X → Spec k` is separated). -/
theorem isAffine_coverPair : IsAffine T.coverPair := by
  have : IsAffineHom (T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := inferInstance
  have : IsAffineHom T.coverDesc :=
    IsAffineHom.of_comp (f := T.coverDesc) (g := T.X.left ↘ Spec (CommRingCat.of k))
  delta Triple.coverPair
  infer_instance

instance : IsAffine T.coverPair := isAffine_coverPair T

/-- `τ₁` is smooth (base change of `g`). -/
theorem smooth_coverFst : Smooth T.coverFst :=
  property_of_isPullback _ (IsPullback.of_hasPullback T.coverDesc T.coverDesc)
    (smooth_coverDesc T)

/-- `τ₂` is smooth (base change of `g`). -/
theorem smooth_coverSnd : Smooth T.coverSnd :=
  property_of_isPullback _
    (IsPullback.of_hasPullback T.coverDesc T.coverDesc).flip (smooth_coverDesc T)

instance : Smooth T.coverFst := smooth_coverFst T

instance : Smooth T.coverSnd := smooth_coverSnd T

/-- `τ₁` is smooth of relative dimension `0` (base change of `g`). -/
theorem smoothOfRelativeDimension_zero_coverFst : SmoothOfRelativeDimension 0 T.coverFst := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange 0
  exact property_of_isPullback _
    (IsPullback.of_hasPullback T.coverDesc T.coverDesc) (smoothOfRelativeDimension_zero_coverDesc T)

/-- `τ₁` is surjective. -/
theorem surjective_coverFst : Function.Surjective T.coverFst := by
  have h : Set.range T.coverFst = T.coverDesc ⁻¹' Set.range T.coverDesc :=
    range_fst_of_isPullback (IsPullback.of_hasPullback T.coverDesc T.coverDesc)
  rw [← Set.range_eq_univ, h, Set.range_eq_univ.mpr (surjective_coverDesc T), Set.preimage_univ]

/-- `τ₂` is surjective. -/
theorem surjective_coverSnd : Function.Surjective T.coverSnd := by
  have h : Set.range T.coverSnd = T.coverDesc ⁻¹' Set.range T.coverDesc :=
    range_fst_of_isPullback
      (IsPullback.of_hasPullback T.coverDesc T.coverDesc).flip
  rw [← Set.range_eq_univ, h, Set.range_eq_univ.mpr (surjective_coverDesc T), Set.preimage_univ]

/-- `τ₁ ≫ g = τ₂ ≫ g`. -/
theorem coverFst_comp_coverDesc : T.coverFst ≫ T.coverDesc = T.coverSnd ≫ T.coverDesc :=
  pullback.condition

/-- `X''` is locally of finite type over `Spec k`. -/
instance : LocallyOfFiniteType (T.coverPair ↘ Spec (CommRingCat.of k)) := by
  have : LocallyOfFiniteType T.coverFst :=
    property_of_isPullback _ (IsPullback.of_hasPullback T.coverDesc T.coverDesc)
      (inferInstanceAs (LocallyOfFiniteType T.coverDesc))
  exact inferInstanceAs
    (LocallyOfFiniteType (T.coverFst ≫ (T.coverScheme ↘ Spec (CommRingCat.of k))))

instance : IsSeparated (T.coverPair ↘ Spec (CommRingCat.of k)) := IsSeparated.of_isAffineHom _

/-- `X''` is smooth over `k` of the relative dimension of `X`. -/
theorem exists_smoothOfRelativeDimension_coverPair :
    ∃ n : ℕ, SmoothOfRelativeDimension n (T.coverPair ↘ Spec (CommRingCat.of k)) := by
  obtain ⟨n, hn⟩ := exists_smoothOfRelativeDimension_coverScheme T
  refine ⟨n, ?_⟩
  have := smoothOfRelativeDimension_zero_coverFst T
  change SmoothOfRelativeDimension n (T.coverFst ≫ (T.coverScheme ↘ Spec (CommRingCat.of k)))
  simpa using
    smoothOfRelativeDimension_comp 0 n T.coverFst (T.coverScheme ↘ Spec (CommRingCat.of k))

/-- The triple `(X'', (g τ₁)^* I, (g τ₁)^{-1} E)` of the kernel pair: the pullback of the triple
of `X'` along `τ₁`. -/
noncomputable def coverPairTriple [PerfectField k] : Triple k :=
  haveI : @HomIsOver Scheme.{u} _ T.coverPair T.coverTriple.X.left T.coverFst
      (Spec (CommRingCat.of k)) (instOverCoverPair T) (AlgScheme.over T.coverTriple.X) := ⟨rfl⟩
  haveI : @Smooth T.coverPair T.coverTriple.X.left T.coverFst := smooth_coverFst T
  Triple.pullback T.coverTriple (exists_smoothOfRelativeDimension_coverPair T) T.coverFst

theorem coverPairTriple_X [PerfectField k] : T.coverPairTriple.X.left = T.coverPair := rfl

/-- The triple of `X''` is affine. -/
theorem isAffine_coverPairTriple [PerfectField k] : T.coverPairTriple.IsAffineScheme :=
  isAffine_coverPair T

/-- The triple of `X''` carries the pullback data of the triple of `X'` along `τ₁`. -/
theorem coverPairTriple_isPullbackOf_fst [PerfectField k] :
    T.coverPairTriple.IsPullbackOf T.coverTriple T.coverFst :=
  haveI : @HomIsOver Scheme.{u} _ T.coverPair T.coverTriple.X.left T.coverFst
      (Spec (CommRingCat.of k)) (instOverCoverPair T) (AlgScheme.over T.coverTriple.X) := ⟨rfl⟩
  haveI : @Smooth T.coverPair T.coverTriple.X.left T.coverFst := smooth_coverFst T
  isPullbackOf_pullback T.coverTriple _ _

/-- The triple of `X''` carries the pullback data of the triple of `X'` along `τ₂` as well:
`(g τ₁)^* I = (g τ₂)^* I`. -/
theorem coverPairTriple_isPullbackOf_snd [PerfectField k] :
    T.coverPairTriple.IsPullbackOf T.coverTriple T.coverSnd := by
  have hτ₂ : T.coverSnd ≫ (T.coverScheme ↘ Spec (CommRingCat.of k)) =
      T.coverPair ↘ Spec (CommRingCat.of k) :=
    HomIsOver.comp_over (f := T.coverSnd) (S := Spec (CommRingCat.of k))
  refine ⟨hτ₂, ?_, ?_⟩
  · change (T.I.comap T.coverDesc).comap T.coverFst = (T.I.comap T.coverDesc).comap T.coverSnd
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      coverFst_comp_coverDesc]
  · change (T.E.comap T.coverDesc).comap T.coverFst = (T.E.comap T.coverDesc).comap T.coverSnd
    rw [← DivisorFamily.comap_comp, ← DivisorFamily.comap_comp, coverFst_comp_coverDesc]

/-- The setting of the proof of [Kol07, Proposition 37], without the constructions: the affine
cover triple, the kernel pair triple, and their maps with their properties. -/
theorem exists_prop37Setting [PerfectField k] :
    ∃ (T' : Triple k) (g : T'.X.left ⟶ T.X.left) (T'' : Triple k) (τ₁ τ₂ : T''.X.left ⟶ T'.X.left),
      T'.IsAffineScheme ∧ Smooth g ∧ Function.Surjective g ∧ T'.IsPullbackOf T g ∧
      T''.IsAffineScheme ∧ IsPullback τ₁ τ₂ g g ∧ Smooth τ₁ ∧ Smooth τ₂ ∧
      Function.Surjective τ₁ ∧ Function.Surjective τ₂ ∧
      T''.IsPullbackOf T' τ₁ ∧ T''.IsPullbackOf T' τ₂ :=
  ⟨T.coverTriple, T.coverDesc, T.coverPairTriple, T.coverFst, T.coverSnd, isAffine_coverTriple T,
    smooth_coverDesc T, surjective_coverDesc T, coverTriple_isPullbackOf T,
    isAffine_coverPairTriple T, IsPullback.of_hasPullback T.coverDesc T.coverDesc,
    smooth_coverFst T, smooth_coverSnd T, surjective_coverFst T, surjective_coverSnd T,
    coverPairTriple_isPullbackOf_fst T, coverPairTriple_isPullbackOf_snd T⟩

end AlgebraicGeometry.Triple

namespace Hironaka

variable {k : Type u} [Field k]

namespace MarkedTriple

variable (T : MarkedTriple k)

/-- The marked triple of `X'`. -/
noncomputable def coverTriple [PerfectField k] : MarkedTriple k :=
  MarkedTriple.pullback T (Triple.exists_smoothOfRelativeDimension_coverScheme T.toTriple)
    T.toTriple.coverDesc

theorem coverTriple_toTriple [PerfectField k] : T.coverTriple.toTriple = T.toTriple.coverTriple :=
  rfl

/-- The marked triple of `X'` is affine. -/
theorem isAffine_coverTriple [PerfectField k] : T.coverTriple.IsAffineScheme :=
  Triple.isAffine_coverScheme T.toTriple

/-- The marked triple of `X'` carries the pullback data of `T` along `g`. -/
theorem coverTriple_isPullbackOf [PerfectField k] :
    T.coverTriple.IsPullbackOf T T.toTriple.coverDesc :=
  isPullbackOf_pullback T _ _

/-- The setting of the proof of [Kol07, Proposition 37] for marked triples, without the
construction. -/
theorem exists_isAffine_isPullbackOf [PerfectField k] :
    ∃ (T' : MarkedTriple k) (g : T'.X.left ⟶ T.X.left), T'.IsAffineScheme ∧ Smooth g ∧
      Function.Surjective g ∧ T'.IsPullbackOf T g :=
  ⟨T.coverTriple, T.toTriple.coverDesc, Triple.isAffine_coverScheme T.toTriple,
    Triple.smooth_coverDesc T.toTriple, Triple.surjective_coverDesc T.toTriple,
    coverTriple_isPullbackOf T⟩

/-- The marked triple of `X''`. -/
noncomputable def coverPairTriple [PerfectField k] : MarkedTriple k :=
  haveI : @HomIsOver Scheme.{u} _ T.toTriple.coverPair T.coverTriple.X.left T.toTriple.coverFst
      (Spec (CommRingCat.of k)) (Triple.instOverCoverPair T.toTriple)
      (AlgScheme.over T.coverTriple.toTriple.X) := ⟨rfl⟩
  haveI : @Smooth T.toTriple.coverPair T.coverTriple.X.left T.toTriple.coverFst :=
    Triple.smooth_coverFst T.toTriple
  MarkedTriple.pullback T.coverTriple (Triple.exists_smoothOfRelativeDimension_coverPair T.toTriple)
    T.toTriple.coverFst

/-- The marked triple of `X''` carries the pullback data of the marked triple of `X'` along `τ₁`. -/
theorem coverPairTriple_isPullbackOf_fst [PerfectField k] :
    T.coverPairTriple.IsPullbackOf T.coverTriple T.toTriple.coverFst :=
  haveI : @HomIsOver Scheme.{u} _ T.toTriple.coverPair T.coverTriple.X.left T.toTriple.coverFst
      (Spec (CommRingCat.of k)) (Triple.instOverCoverPair T.toTriple)
      (AlgScheme.over T.coverTriple.toTriple.X) := ⟨rfl⟩
  haveI : @Smooth T.toTriple.coverPair T.coverTriple.X.left T.toTriple.coverFst :=
    Triple.smooth_coverFst T.toTriple
  isPullbackOf_pullback T.coverTriple _ _

/-- … and along `τ₂`. -/
theorem coverPairTriple_isPullbackOf_snd [PerfectField k] :
    T.coverPairTriple.IsPullbackOf T.coverTriple T.toTriple.coverSnd :=
  ⟨Triple.coverPairTriple_isPullbackOf_snd T.toTriple, rfl⟩

/-- The setting of the proof of [Kol07, Proposition 37] for marked triples, without the
constructions. -/
theorem exists_prop37Setting [PerfectField k] :
    ∃ (T' : MarkedTriple k) (g : T'.X.left ⟶ T.X.left) (T'' : MarkedTriple k)
    (τ₁ τ₂ : T''.X.left ⟶ T'.X.left),
      T'.IsAffineScheme ∧ Smooth g ∧ Function.Surjective g ∧ T'.IsPullbackOf T g ∧
      T''.IsAffineScheme ∧ IsPullback τ₁ τ₂ g g ∧ Smooth τ₁ ∧ Smooth τ₂ ∧
      Function.Surjective τ₁ ∧ Function.Surjective τ₂ ∧
      T''.IsPullbackOf T' τ₁ ∧ T''.IsPullbackOf T' τ₂ :=
  ⟨T.coverTriple, T.toTriple.coverDesc, T.coverPairTriple, T.toTriple.coverFst,
    T.toTriple.coverSnd, Triple.isAffine_coverScheme T.toTriple, Triple.smooth_coverDesc T.toTriple,
    Triple.surjective_coverDesc T.toTriple, coverTriple_isPullbackOf T,
    Triple.isAffine_coverPair T.toTriple,
    IsPullback.of_hasPullback T.toTriple.coverDesc T.toTriple.coverDesc,
    Triple.smooth_coverFst T.toTriple, Triple.smooth_coverSnd T.toTriple,
    Triple.surjective_coverFst T.toTriple, Triple.surjective_coverSnd T.toTriple,
    coverPairTriple_isPullbackOf_fst T, coverPairTriple_isPullbackOf_snd T⟩

end MarkedTriple

end Hironaka
