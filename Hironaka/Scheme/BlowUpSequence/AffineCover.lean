/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.AlgebraicGeometry.Morphisms.Etale
/-!
# The finite affine cover of a scheme as one smooth surjection

Kollár's Proposition 37 [Kol07, Proposition 37] extends a blow-up sequence functor from affine
schemes to all schemes of finite type over `k` by descent along the smooth surjection
`g : X' = ∐ᵢ Uᵢ → X` from the disjoint union of a finite affine open cover, using the two
projections `τ₁, τ₂ : X'' → X'` of the kernel pair `X'' = X' ×_X X'`.
`Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Setting.lean` has this setting on a `Triple` (a
smooth `X`); the gluing of the resolution functor of [Kol07, Theorem 36] needs it for an arbitrary
scheme `X` of finite type over `k`, since the input of the resolution functor is not smooth. This
module provides the scheme-level part. The cover and its morphisms depend on `X` alone
(`[CompactSpace X]`, which a quasi-compact `X → Spec k` provides); the field enters only the
structure morphisms and the finite-type, separated and affine statements:

* `finiteAffineCover X`, Mathlib's affine cover refined to a finite subcover;
  `affineCoverScheme X` (`X'`), `affineCoverDesc X` (`g`), `affineCoverPair X` (`X''`),
  `affineCoverFst X`, `affineCoverSnd X` (`τ₁`, `τ₂`);
* `X'` is affine (`isAffine_affineCoverScheme`), `g` is a smooth surjection
  (`smooth_affineCoverDesc`, `surjective_affineCoverDesc`; locality on the source, the pieces
  being open immersions) and a coproduct of open immersions
  (`openImmersionCoprods_affineCoverDesc`, the hypothesis of the descent
  `exists_pullback_eq_of_kernelPair` of
  `Hironaka/Resolution/Algebraic/Kol07/GlobalizeDescent.lean`); `X'` is of finite type,
  quasi-compact and separated over `Spec k` when `X` is of finite type;
* `X''` is affine (`isAffine_affineCoverPair`; `g` is an affine morphism because `X → Spec k` is
  separated), `τ₁, τ₂` are smooth surjections (base change of `g`), `τ₁ ≫ g = τ₂ ≫ g`, and the
  kernel pair is a pullback square (`isPullback_affineCoverFst_affineCoverSnd`).

The `affineCover…` names keep the base names distinct from `Triple.cover…` of
`Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Setting.lean`, whose statements are the instances
of these at `T.X.left`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [CompactSpace X]

/-! ### The finite affine cover and its disjoint union -/

/-- A finite affine open cover of the quasi-compact scheme `X` ("choose an open affine cover
`X = ∪ Uᵢ`", the proof of [Kol07, Proposition 37]): Mathlib's affine cover, refined to a finite
subcover. -/
noncomputable def finiteAffineCover : Scheme.OpenCover.{u} X := X.affineCover.finiteSubcover

/-- The finite subcover has a finite index type. -/
instance finite_finiteAffineCover_I₀ : Finite (finiteAffineCover X).I₀ := by
  delta finiteAffineCover
  infer_instance

/-- The members of the finite affine cover are affine. -/
instance isAffine_finiteAffineCover_X (i : (finiteAffineCover X).I₀) :
    IsAffine ((finiteAffineCover X).X i) :=
  Scheme.isAffine_affineCover X _

/-- `X' := ∐ᵢ Uᵢ`, the disjoint union of the members of the finite affine cover (the proof of
[Kol07, Proposition 37]). -/
noncomputable abbrev affineCoverScheme : Scheme.{u} := ∐ fun i => (finiteAffineCover X).X i

/-- The morphism `g : X' → X` induced by the inclusions of the members of the cover, "a smooth
surjection" in the proof of [Kol07, Proposition 37]. -/
noncomputable def affineCoverDesc : affineCoverScheme X ⟶ X := Sigma.desc (finiteAffineCover X).f

/-- `X'` is affine. -/
theorem isAffine_affineCoverScheme : IsAffine (affineCoverScheme X) := by
  delta affineCoverScheme
  infer_instance

instance instIsAffineAffineCoverScheme : IsAffine (affineCoverScheme X) :=
  isAffine_affineCoverScheme X

/-- The piece inclusions. -/
@[reassoc]
theorem ι_comp_affineCoverDesc (i : (finiteAffineCover X).I₀) :
    Sigma.ι (fun i => (finiteAffineCover X).X i) i ≫ affineCoverDesc X =
      (finiteAffineCover X).f i :=
  Sigma.ι_comp_desc _ _

/-- `g` is smooth: locality on the source, each piece being an open immersion. -/
theorem smooth_affineCoverDesc : Smooth (affineCoverDesc X) := by
  have hloc : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

instance instSmoothAffineCoverDesc : Smooth (affineCoverDesc X) := smooth_affineCoverDesc X

/-- `g` is smooth of relative dimension `0` (a coproduct of open immersions). -/
theorem smoothOfRelativeDimension_zero_affineCoverDesc :
    SmoothOfRelativeDimension 0 (affineCoverDesc X) := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} 0) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

/-- `g` is locally of finite type (a coproduct of open immersions). -/
theorem locallyOfFiniteType_affineCoverDesc : LocallyOfFiniteType (affineCoverDesc X) := by
  have hloc : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

/-- `g` is surjective (the pieces cover `X`). -/
theorem surjective_affineCoverDesc : Function.Surjective (affineCoverDesc X) :=
  (Surjective.sigmaDesc_of_union_range_eq_univ (finiteAffineCover X).iUnion_range).surj

/-- `g` is a coproduct of open immersions: `X'` is the coproduct of the members and each
`Sigma.ι i ≫ g = Uᵢ → X` is an open immersion; the hypothesis of the kernel-pair descent
`exists_pullback_eq_of_kernelPair`. -/
theorem openImmersionCoprods_affineCoverDesc : openImmersionCoprods (affineCoverDesc X) :=
  ⟨(finiteAffineCover X).I₀, fun i => (finiteAffineCover X).X i,
    fun i => Sigma.ι (fun i => (finiteAffineCover X).X i) i,
    ⟨coproductIsCoproduct fun i => (finiteAffineCover X).X i⟩, fun i => by
      rw [ι_comp_affineCoverDesc]
      infer_instance⟩

/-! ### The kernel pair -/

/-- The kernel pair `X'' = X' ×_X X'` (Kollár's `X'' := ∐_{i ≤ j} Uᵢ ∩ Uⱼ`, of which "we can also
think … as the fiber product `X' ×_X X'`", the proof of [Kol07, Proposition 37]). -/
noncomputable abbrev affineCoverPair : Scheme.{u} :=
  pullback (affineCoverDesc X) (affineCoverDesc X)

/-- The first projection `τ₁ : X'' → X'` of the kernel pair. -/
noncomputable def affineCoverFst : affineCoverPair X ⟶ affineCoverScheme X :=
  pullback.fst (affineCoverDesc X) (affineCoverDesc X)

/-- The second projection `τ₂ : X'' → X'` of the kernel pair. -/
noncomputable def affineCoverSnd : affineCoverPair X ⟶ affineCoverScheme X :=
  pullback.snd (affineCoverDesc X) (affineCoverDesc X)

/-- The kernel pair of `g` is a pullback square. -/
theorem isPullback_affineCoverFst_affineCoverSnd :
    IsPullback (affineCoverFst X) (affineCoverSnd X) (affineCoverDesc X) (affineCoverDesc X) :=
  IsPullback.of_hasPullback _ _

/-- `τ₁ ≫ g = τ₂ ≫ g`. -/
theorem affineCoverFst_comp_affineCoverDesc :
    affineCoverFst X ≫ affineCoverDesc X = affineCoverSnd X ≫ affineCoverDesc X :=
  pullback.condition

/-- `τ₁` is smooth (base change of `g`). -/
theorem smooth_affineCoverFst : Smooth (affineCoverFst X) :=
  property_of_isPullback _ (isPullback_affineCoverFst_affineCoverSnd X)
    (smooth_affineCoverDesc X)

/-- `τ₂` is smooth (base change of `g`). -/
theorem smooth_affineCoverSnd : Smooth (affineCoverSnd X) :=
  property_of_isPullback _ (isPullback_affineCoverFst_affineCoverSnd X).flip
    (smooth_affineCoverDesc X)

instance instSmoothAffineCoverFst : Smooth (affineCoverFst X) := smooth_affineCoverFst X

instance instSmoothAffineCoverSnd : Smooth (affineCoverSnd X) := smooth_affineCoverSnd X

/-- `τ₁` is smooth of relative dimension `0` (base change of `g`). -/
theorem smoothOfRelativeDimension_zero_affineCoverFst :
    SmoothOfRelativeDimension 0 (affineCoverFst X) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange 0
  exact property_of_isPullback _ (isPullback_affineCoverFst_affineCoverSnd X)
    (smoothOfRelativeDimension_zero_affineCoverDesc X)

/-- `τ₁` is surjective. -/
theorem surjective_affineCoverFst : Function.Surjective (affineCoverFst X) := by
  have h : Set.range (affineCoverFst X) = affineCoverDesc X ⁻¹' Set.range (affineCoverDesc X) :=
    range_fst_of_isPullback (isPullback_affineCoverFst_affineCoverSnd X)
  rw [← Set.range_eq_univ, h, Set.range_eq_univ.mpr (surjective_affineCoverDesc X),
    Set.preimage_univ]

/-- `τ₂` is surjective. -/
theorem surjective_affineCoverSnd : Function.Surjective (affineCoverSnd X) := by
  have h : Set.range (affineCoverSnd X) = affineCoverDesc X ⁻¹' Set.range (affineCoverDesc X) :=
    range_fst_of_isPullback (isPullback_affineCoverFst_affineCoverSnd X).flip
  rw [← Set.range_eq_univ, h, Set.range_eq_univ.mpr (surjective_affineCoverDesc X),
    Set.preimage_univ]

/-! ### Over the base field -/

section Field

variable {k : Type u} [Field k] [X.Over (Spec (CommRingCat.of k))]

/-- A scheme quasi-compact over `Spec k` is a compact space (the hypothesis of the cover). -/
theorem compactSpace_of_quasiCompact_over (k : Type u) [Field k] (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of k))] [QuasiCompact (Y ↘ Spec (CommRingCat.of k))] :
    CompactSpace Y :=
  QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k))

/-- `X'` is a scheme over `Spec k` through `g`. -/
noncomputable instance instOverAffineCoverScheme :
    (affineCoverScheme X).Over (Spec (CommRingCat.of k)) :=
  ⟨affineCoverDesc X ≫ (X ↘ Spec (CommRingCat.of k))⟩

/-- `g` is a morphism over `Spec k`. -/
instance instIsOverAffineCoverDesc : (affineCoverDesc X).IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩

/-- `X'` is locally of finite type over `Spec k` when `X` is. -/
theorem locallyOfFiniteType_affineCoverScheme (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    LocallyOfFiniteType (affineCoverScheme X ↘ Spec (CommRingCat.of k)) := by
  have := locallyOfFiniteType_affineCoverDesc X
  exact inferInstanceAs
    (LocallyOfFiniteType (affineCoverDesc X ≫ (X ↘ Spec (CommRingCat.of k))))

instance instLocallyOfFiniteTypeAffineCoverScheme
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    LocallyOfFiniteType (affineCoverScheme X ↘ Spec (CommRingCat.of k)) :=
  locallyOfFiniteType_affineCoverScheme X k

/-- `X'` is quasi-compact over `Spec k` (affine over an affine base). -/
theorem quasiCompact_affineCoverScheme (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))] :
    QuasiCompact (affineCoverScheme X ↘ Spec (CommRingCat.of k)) :=
  inferInstance

/-- `X'` is separated over `Spec k` (affine over an affine base). -/
theorem isSeparated_affineCoverScheme (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))] :
    IsSeparated (affineCoverScheme X ↘ Spec (CommRingCat.of k)) :=
  IsSeparated.of_isAffineHom _

instance instIsSeparatedAffineCoverScheme :
    IsSeparated (affineCoverScheme X ↘ Spec (CommRingCat.of k)) :=
  isSeparated_affineCoverScheme X k

/-- `X''` is affine: `g` is an affine morphism because `X' → X → Spec k` is affine and
`X → Spec k` is separated, and the fibre product of `g` with itself is affine. Kollár's `X''` is
a disjoint union of the `Uᵢ ∩ Uⱼ`; that these are affine uses the separatedness of `X`, a point
left implicit in his text. -/
theorem isAffine_affineCoverPair (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))] : IsAffine (affineCoverPair X) := by
  have : IsAffineHom (affineCoverDesc X ≫ (X ↘ Spec (CommRingCat.of k))) := inferInstance
  have : IsAffineHom (affineCoverDesc X) :=
    IsAffineHom.of_comp (f := affineCoverDesc X) (g := X ↘ Spec (CommRingCat.of k))
  delta affineCoverPair
  infer_instance

/-- `X''` is a scheme over `Spec k` through `τ₁`. -/
noncomputable instance instOverAffineCoverPair :
    (affineCoverPair X).Over (Spec (CommRingCat.of k)) :=
  ⟨affineCoverFst X ≫ (affineCoverScheme X ↘ Spec (CommRingCat.of k))⟩

/-- `τ₁` is a morphism over `Spec k`. -/
instance instIsOverAffineCoverFst : (affineCoverFst X).IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩

/-- `τ₂` is a morphism over `Spec k` (`τ₁ ≫ g = τ₂ ≫ g`). -/
theorem affineCoverSnd_comp_over :
    affineCoverSnd X ≫ (affineCoverScheme X ↘ Spec (CommRingCat.of k)) =
      affineCoverPair X ↘ Spec (CommRingCat.of k) := by
  change affineCoverSnd X ≫ affineCoverDesc X ≫ (X ↘ Spec (CommRingCat.of k)) =
    affineCoverFst X ≫ affineCoverDesc X ≫ (X ↘ Spec (CommRingCat.of k))
  rw [← Category.assoc, ← affineCoverFst_comp_affineCoverDesc, Category.assoc]

instance instIsOverAffineCoverSnd : (affineCoverSnd X).IsOver (Spec (CommRingCat.of k)) :=
  ⟨affineCoverSnd_comp_over X⟩

/-- `X''` is locally of finite type over `Spec k` when `X` is. -/
theorem locallyOfFiniteType_affineCoverPair (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    LocallyOfFiniteType (affineCoverPair X ↘ Spec (CommRingCat.of k)) := by
  have : LocallyOfFiniteType (affineCoverFst X) :=
    property_of_isPullback _ (isPullback_affineCoverFst_affineCoverSnd X)
      (locallyOfFiniteType_affineCoverDesc X)
  exact inferInstanceAs
    (LocallyOfFiniteType (affineCoverFst X ≫ (affineCoverScheme X ↘ Spec (CommRingCat.of k))))

/-- `X''` is separated over `Spec k` when `X` is (`X''` is then affine over an affine base). -/
theorem isSeparated_affineCoverPair (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))] :
    IsSeparated (affineCoverPair X ↘ Spec (CommRingCat.of k)) := by
  have := isAffine_affineCoverPair X k
  exact IsSeparated.of_isAffineHom _

end Field

end AlgebraicGeometry
