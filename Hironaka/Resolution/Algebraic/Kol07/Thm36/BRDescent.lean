/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.BR
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AdmissiblePairs
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineFunctoriality
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SigmaCharts
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The descent of the resolution functor and its functoriality under smooth morphisms

The descent of [Kol07, Proposition 37] for the resolution functor `BR`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`), and clause (4a) of the functorial resolution
theorem, commutation with smooth morphisms [Kol07, 34.1], with the relative dimension `d` of the
smooth morphism taken as an input (it is supplied by
`Hironaka.Resolution.Algebraic.Kol07.Thm36.RelativeDimensionConstancy` on the class of the theorem).

## The condition (37.1) and the descent

For a member `X` of the class `IsReducedEquidimensional k X` (quasi-compact, separated over `k`),
the finite affine cover `∐ Uᵢ → X` (`Hironaka.Scheme.BlowUpSequence.AffineCover`) has affine
members of the class as source `X' = ∐ Uᵢ` and kernel pair `X'' = X' ×_X X'`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure`), and the two projections `τ₁, τ₂ : X'' →
X'` are smooth surjective of relative dimension `0`. The affine (34.1) with `d = 0`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineFunctoriality`, the admissible pairs from
`Hironaka.Resolution.Algebraic.Kol07.Thm36.AdmissiblePairs`) gives (37.1): `BRAffine X'' = τᵢ^*
BRAffine X'` on the nose, which is the kernel-pair condition of the descent
(`exists_pullback_eq_of_kernelPair`). Hence `BRDescends k X` holds on every member of the class, `BR
X` is the (deleted) descended sequence, and `g^* BR X = BRAffine X'`
(`BR_pullback_affineCoverDesc`). On an affine member the same (34.1) for `g` itself gives `BRAffine
X' = g^* BRAffine X`, so the descent returns `BRAffine X` and `BR X = BRAffine X`
(`BR_eq_BRAffine_of_isAffine`); on an integral affine `X`, a member
(`isReducedEquidimensional_of_isIntegral`), `BR X` is the embedding-free affine resolution with its
empty steps deleted (`BR_eq_BR_affine'_of_integral`).

## Clause (4a) with the relative dimension as input

For a smooth `q : Z → Y` of relative dimension `d` from an affine member `Z` to a member `Y`, cover
`Y` by its finite affine cover `Uᵢ` and `Z` by the preimages `q⁻¹Uᵢ` (affine, since `q` is an affine
morphism: `Z` affine, `Y` separated). The coproduct `∐ q⁻¹Uᵢ → ∐ Uᵢ` is smooth of relative dimension
`d` between affine members (`sigmaMap_of_isZariskiLocalAtTarget`), so the affine (34.1) computes
`BRAffine (∐ q⁻¹Uᵢ)` from `BRAffine (∐ Uᵢ) = g^* BR Y`; the étale surjection `∐ q⁻¹Uᵢ → Z` computes
it from `BRAffine Z`; comparing and cancelling the flat surjection gives
`BRAffine Z = (q^* BR Y).eraseEmpty` (`BRAffine_eq_eraseEmpty_BR_pullback_of_smooth`). For a smooth
`h : Y → X` of relative dimension `d` between members, apply this to `∐ Uᵢ → Y → X` and cancel
`∐ Uᵢ → Y`: `BR Y = (h^* BR X).eraseEmpty` (`BR_eq_eraseEmpty_pullback_of_smooth`), and on the nose
when `h` is surjective (`BR_eq_pullback_of_smooth_surjective`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- The surjective form of (34.1) for affine members [Kol07, Theorem 36, proof]: a smooth surjective
morphism of relative dimension `d` between affine members of the class pulls `BRAffine` back on the
nose, by `BRAffine_eq_eraseEmpty_pullback_of_smooth` with the admissible pairs of
`exists_admissibleEmbedding`, the deletion of empty steps being trivial along a flat surjection
(`eraseEmpty_pullback_of_flat_surjective`). -/
theorem BRAffine_eq_pullback_of_smooth_surjective (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IsAffine X]
    [Y.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [IsAffine Y]
    (hX : X.IsReducedEquidimensional k) (hY : Y.IsReducedEquidimensional k)
    (h : Y ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] (d : ℕ) [SmoothOfRelativeDimension d h]
    (hs : Function.Surjective h) :
    BRAffine k Y = (BRAffine k X).pullback h := by
  have := SmoothOfRelativeDimension.smooth d h
  obtain ⟨TX, embX, hadmX⟩ := exists_admissibleEmbedding (k := k) X
  obtain ⟨TY, embY, hadmY⟩ := exists_admissibleEmbedding (k := k) Y
  rw [BRAffine_eq_eraseEmpty_pullback_of_smooth X Y hX hY h d TX embX hadmX TY embY hadmY,
    eraseEmpty_pullback_of_flat_surjective _ _ hs, eraseEmpty_BRAffine]

/-- `τ₂` is smooth of relative dimension `0` (the base change of `g`; the counterpart of
`AlgebraicGeometry.smoothOfRelativeDimension_zero_affineCoverFst`). -/
theorem smoothOfRelativeDimension_zero_affineCoverSnd (X : Scheme.{u}) [CompactSpace X] :
    SmoothOfRelativeDimension 0 (affineCoverSnd X) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange 0
  exact property_of_isPullback _ (isPullback_affineCoverFst_affineCoverSnd X).flip
    (smoothOfRelativeDimension_zero_affineCoverDesc X)

/-- The condition (37.1) of [Kol07, Proposition 37]: both projections of the kernel pair
`X'' = X' ×_X X'` are smooth surjective of relative dimension `0` between affine members of the
class, so the affine (34.1) on the nose (`BRAffine_eq_pullback_of_smooth_surjective`) gives both
equalities `BRAffine X'' = τᵢ^* BRAffine X'`. -/
theorem BRAffine_affineCoverPair_eq_pullback_of_class (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) :
    haveI : CompactSpace X := compactSpace_of_quasiCompact_over k X
    BRAffine k (affineCoverPair X) =
        (BRAffine k (affineCoverScheme X)).pullback
          (affineCoverFst X) ∧
      BRAffine k (affineCoverPair X) =
        (BRAffine k (affineCoverScheme X)).pullback
          (affineCoverSnd X) := by
  have hc : CompactSpace X := compactSpace_of_quasiCompact_over k X
  have hA : IsAffine (affineCoverPair X) := isAffine_affineCoverPair X k
  have h1 := smoothOfRelativeDimension_zero_affineCoverFst X
  have h2 := smoothOfRelativeDimension_zero_affineCoverSnd X
  exact ⟨BRAffine_eq_pullback_of_smooth_surjective (affineCoverScheme X) (affineCoverPair X)
      hX.affineCoverScheme hX.affineCoverPair (affineCoverFst X) 0 (surjective_affineCoverFst X),
    BRAffine_eq_pullback_of_smooth_surjective (affineCoverScheme X) (affineCoverPair X)
      hX.affineCoverScheme hX.affineCoverPair (affineCoverSnd X) 0 (surjective_affineCoverSnd X)⟩

/-- The cover descent `BRDescends` holds on every member of the class [Kol07, Proposition 37]:
(37.1) is the kernel-pair condition of `exists_pullback_eq_of_kernelPair`. -/
theorem brDescends_of_isReducedEquidimensional (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) :
    haveI : CompactSpace X := compactSpace_of_quasiCompact_over k X
    BRDescends k X := by
  have hc : CompactSpace X := compactSpace_of_quasiCompact_over k X
  obtain ⟨h1, h2⟩ := BRAffine_affineCoverPair_eq_pullback_of_class (k := k) X hX
  exact exists_pullback_eq_of_kernelPair (affineCoverDesc X)
    (openImmersionCoprods_affineCoverDesc X) (surjective_affineCoverDesc X) (affineCoverFst X)
    (affineCoverSnd X) (isPullback_affineCoverFst_affineCoverSnd X) _ (h1.symm.trans h2)

/-- The defining property of `BR` on every member of the class: its pullback along the finite
affine cover is the affine value on the cover scheme [Kol07, Proposition 37, proof]. -/
theorem BR_pullback_affineCoverDesc (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) :
    haveI : CompactSpace X := compactSpace_of_quasiCompact_over k X
    (BR k X).pullback (affineCoverDesc X) =
      BRAffine k (affineCoverScheme X) := by
  have hc : CompactSpace X := compactSpace_of_quasiCompact_over k X
  exact BR_pullback_affineCoverDesc_of_descends (k := k) X hX
    (brDescends_of_isReducedEquidimensional X hX)

/-- On an affine member of the class the resolution functor is the affine resolution:
`BRAffine (∐ Uᵢ) = g^* BRAffine X` by the affine (34.1) for the étale surjection `g`, so the cover
descent returns `BRAffine X` itself (the uniqueness `BR_eq_eraseEmpty_of_pullback_eq`; the deletion
of empty steps is idempotent). -/
theorem BR_eq_BRAffine_of_isAffine (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IsAffine X]
    (hX : X.IsReducedEquidimensional k) : BR k X = BRAffine k X := by
  have hc : CompactSpace X := compactSpace_of_quasiCompact_over k X
  have h0 := smoothOfRelativeDimension_zero_affineCoverDesc X
  have h := BRAffine_eq_pullback_of_smooth_surjective (k := k) X (affineCoverScheme X) hX
    hX.affineCoverScheme (affineCoverDesc X) 0 (surjective_affineCoverDesc X)
  rw [BR_eq_eraseEmpty_of_pullback_eq (k := k) X hX (BRAffine k X) h.symm, eraseEmpty_BRAffine]

/-- On an integral affine `X`, a member of the class (`isReducedEquidimensional_of_isIntegral`),
the resolution functor is the embedding-free affine resolution `BR_affine' k X`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.Independence`) with its globally empty steps deleted:
`BR X = BRAffine X` (the cover descent), and `BRAffine` is that deletion by definition. -/
theorem BR_eq_BR_affine'_of_integral (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IsAffine X] [IsIntegral X] :
    BR k X = (BR_affine' k X).eraseEmpty :=
  BR_eq_BRAffine_of_isAffine X (isReducedEquidimensional_of_isIntegral X)

section CoverPreimage

variable {Y Z : Scheme.{u}} [CompactSpace Y] (q : Z ⟶ Y)

/-- The preimage in `Z` of the `i`-th member of the finite affine cover of `Y`, as a scheme. -/
noncomputable abbrev coverPreimage (i : (finiteAffineCover Y).I₀) : Scheme.{u} :=
  (q ⁻¹ᵁ ((finiteAffineCover Y).f i).opensRange : Scheme.{u})

/-- The open immersion of the `i`-th preimage into `Z`. -/
noncomputable abbrev coverPreimageι (i : (finiteAffineCover Y).I₀) : coverPreimage q i ⟶ Z :=
  (q ⁻¹ᵁ ((finiteAffineCover Y).f i).opensRange).ι

theorem range_coverPreimageι_comp (i : (finiteAffineCover Y).I₀) :
    Set.range ⇑(coverPreimageι q i ≫ q) ⊆ Set.range ⇑((finiteAffineCover Y).f i) := by
  rintro _ ⟨w, rfl⟩
  have h1 : coverPreimageι q i w ∈ (coverPreimageι q i).opensRange := ⟨w, rfl⟩
  rw [Scheme.Opens.opensRange_ι] at h1
  rw [Scheme.Hom.comp_apply]
  exact h1

/-- The restriction of `q` to the `i`-th preimage, landing in the `i`-th member of the cover. -/
noncomputable def coverPreimageMap (i : (finiteAffineCover Y).I₀) :
    coverPreimage q i ⟶ (finiteAffineCover Y).X i :=
  IsOpenImmersion.lift ((finiteAffineCover Y).f i) (coverPreimageι q i ≫ q)
    (range_coverPreimageι_comp q i)

theorem coverPreimageMap_comp (i : (finiteAffineCover Y).I₀) :
    coverPreimageMap q i ≫ (finiteAffineCover Y).f i = coverPreimageι q i ≫ q :=
  IsOpenImmersion.lift_fac _ _ _

theorem isAffine_coverPreimage [IsAffineHom q] (i : (finiteAffineCover Y).I₀) :
    IsAffine (coverPreimage q i) :=
  (isAffineOpen_opensRange ((finiteAffineCover Y).f i)).preimage q

theorem exists_coverPreimageι_eq (z : Z) : ∃ i w, coverPreimageι q i w = z := by
  have hi := (finiteAffineCover Y).covers (q z)
  have hz : z ∈ (q ⁻¹ᵁ ((finiteAffineCover Y).f ((finiteAffineCover Y).idx (q z))).opensRange :
      Set Z) := hi
  rw [← Scheme.Opens.range_ι] at hz
  obtain ⟨w, hw⟩ := hz
  exact ⟨(finiteAffineCover Y).idx (q z), w, hw⟩

/-- The `i`-th preimage is the fibre product of `Z` and the `i`-th member of the cover over `Y`. -/
theorem isPullback_coverPreimageMap (i : (finiteAffineCover Y).I₀) :
    IsPullback (coverPreimageMap q i) (coverPreimageι q i) ((finiteAffineCover Y).f i) q :=
  IsOpenImmersion.isPullback _ _ _ _ (coverPreimageMap_comp q i).symm
    (Scheme.Opens.opensRange_ι _).symm

theorem smoothOfRelativeDimension_coverPreimageMap (d : ℕ) [SmoothOfRelativeDimension d q]
    (i : (finiteAffineCover Y).I₀) : SmoothOfRelativeDimension d (coverPreimageMap q i) := by
  have hloc : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} d) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ inferInstance
  exact IsZariskiLocalAtTarget.of_isPullback (P := @SmoothOfRelativeDimension.{u} d)
    (isPullback_coverPreimageMap q i).flip ‹_›

theorem sigmaMap_coverPreimageMap_comp_affineCoverDesc :
    Limits.Sigma.map (coverPreimageMap q) ≫ affineCoverDesc Y =
      Sigma.desc (coverPreimageι q) ≫ q :=
  sigmaMap_comp_desc (coverPreimageMap q) (finiteAffineCover Y).f (coverPreimageι q) q
    (coverPreimageMap_comp q)

end CoverPreimage

/-- The affine (34.1) read on the target's resolution functor: for an affine member `Z` of the class
and a smooth `q : Z ⟶ Y` of relative dimension `d` to a member `Y`,
`BRAffine Z = (q^* BR Y).eraseEmpty`, through the coproduct of the preimages of the finite affine
cover of `Y`, the affine (34.1) for `∐ q⁻¹Uᵢ → ∐ Uᵢ`, and the cover descent of `Y`. -/
theorem BRAffine_eq_eraseEmpty_BR_pullback_of_smooth (Y Z : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))] [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    [Z.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [IsAffine Z]
    (hY : Y.IsReducedEquidimensional k) (hZ : Z.IsReducedEquidimensional k)
    (q : Z ⟶ Y) [q.IsOver (Spec (CommRingCat.of k))] (d : ℕ)
    [SmoothOfRelativeDimension d q] :
    BRAffine k Z = ((BR k Y).pullback q).eraseEmpty := by
  have hcY : CompactSpace Y := compactSpace_of_quasiCompact_over k Y
  -- `q` is an affine morphism (`Z` affine, `Y` separated over `k`)
  have hqaff : IsAffineHom q := by
    have h1 : IsAffineHom (q ≫ (Y ↘ Spec (CommRingCat.of k))) := by
      rw [HomIsOver.comp_over (f := q) (S := Spec (CommRingCat.of k))]
      exact isAffineHom_of_isAffine _
    exact IsAffineHom.of_comp (f := q) (g := Y ↘ Spec (CommRingCat.of k))
  have hWaff : ∀ i, IsAffine (coverPreimage q i) := isAffine_coverPreimage q
  have hqq : ∀ i, SmoothOfRelativeDimension d (coverPreimageMap q i) :=
    smoothOfRelativeDimension_coverPreimageMap q d
  have hqqs : ∀ i, Smooth (coverPreimageMap q i) := fun i => SmoothOfRelativeDimension.smooth d _
  -- the coproduct of the preimages over `k`, an affine class member
  let _ : (∐ coverPreimage q).Over (Spec (CommRingCat.of k)) :=
    ⟨Sigma.desc (coverPreimageι q) ≫ (Z ↘ Spec (CommRingCat.of k))⟩
  have hoverE : (Sigma.desc (coverPreimageι q)).IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have hsq := sigmaMap_coverPreimageMap_comp_affineCoverDesc q
  have hoverM : (Limits.Sigma.map (coverPreimageMap q)).IsOver (Spec (CommRingCat.of k)) := by
    constructor
    change Limits.Sigma.map (coverPreimageMap q) ≫ affineCoverDesc Y ≫
        (Y ↘ Spec (CommRingCat.of k)) =
      Sigma.desc (coverPreimageι q) ≫ (Z ↘ Spec (CommRingCat.of k))
    rw [← Category.assoc, hsq, Category.assoc,
      HomIsOver.comp_over (f := q) (S := Spec (CommRingCat.of k))]
  have hlfT : LocallyOfFiniteType ((∐ coverPreimage q) ↘ Spec (CommRingCat.of k)) := by
    change LocallyOfFiniteType (Sigma.desc (coverPreimageι q) ≫ (Z ↘ Spec (CommRingCat.of k)))
    have := locallyOfFiniteType_sigmaDesc (coverPreimageι q)
    infer_instance
  have hZ' : (∐ coverPreimage q).IsReducedEquidimensional k :=
    .sigma _ (coverPreimageι q) (fun i => by
      change Sigma.ι _ i ≫ Sigma.desc (coverPreimageι q) ≫ (Z ↘ Spec (CommRingCat.of k)) = _
      rw [← Category.assoc, Sigma.ι_comp_desc]) hZ
  have hAff : IsAffine (∐ coverPreimage q) := inferInstance
  have hqc : QuasiCompact ((∐ coverPreimage q) ↘ Spec (CommRingCat.of k)) := by
    have := isAffineHom_of_isAffine ((∐ coverPreimage q) ↘ Spec (CommRingCat.of k))
    infer_instance
  have hsurj : Function.Surjective (Sigma.desc (coverPreimageι q)) :=
    surjective_sigmaDesc _ (exists_coverPreimageι_eq q)
  have hflatE : Flat (Sigma.desc (coverPreimageι q)) := flat_sigmaDesc _
  have h0E : SmoothOfRelativeDimension 0 (Sigma.desc (coverPreimageι q)) :=
    smoothOfRelativeDimension_sigmaDesc _ 0
  have hsmE : Smooth (Sigma.desc (coverPreimageι q)) := smooth_sigmaDesc _
  have hMd : SmoothOfRelativeDimension d (Limits.Sigma.map (coverPreimageMap q)) := by
    have hloc : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} d) :=
      @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ inferInstance
    exact sigmaMap_of_isZariskiLocalAtTarget (coverPreimageMap q)
      (@SmoothOfRelativeDimension.{u} d) hqq
  have hMs : Smooth (Limits.Sigma.map (coverPreimageMap q)) := SmoothOfRelativeDimension.smooth d _
  -- the affine 34.1 for `∐ q⁻¹Uᵢ → ∐ Uᵢ` and for `∐ q⁻¹Uᵢ → Z`
  obtain ⟨TA, embA, hadmA⟩ := exists_admissibleEmbedding (k := k) (affineCoverScheme Y)
  obtain ⟨TB, embB, hadmB⟩ := exists_admissibleEmbedding (k := k) (∐ coverPreimage q)
  have hup := BRAffine_eq_eraseEmpty_pullback_of_smooth (affineCoverScheme Y) (∐ coverPreimage q)
    hY.affineCoverScheme hZ' (Limits.Sigma.map (coverPreimageMap q)) d TA embA hadmA TB embB hadmB
  have hdown := BRAffine_eq_pullback_of_smooth_surjective (k := k) Z (∐ coverPreimage q) hZ hZ'
    (Sigma.desc (coverPreimageι q)) 0 hsurj
  have hdesc := BR_pullback_affineCoverDesc (k := k) Y hY
  rw [← hdesc, ← pullback_comp, hsq, pullback_comp,
    eraseEmpty_pullback_of_flat_surjective _ _ hsurj] at hup
  exact pullback_injective_of_surjective (Sigma.desc (coverPreimageι q)) hsurj
    (hdown.symm.trans hup)

/-- Clause (4a) of the functorial resolution theorem with the relative dimension as INPUT [Kol07,
Theorem 36 (4); 34.1]: for a smooth `h : Y ⟶ X` of relative dimension `d` between members of the
class, `BR Y = (h^* BR X).eraseEmpty`, by the affine (34.1) for `∐ Uᵢ → Y → X` read on `BR X`, the
cover descent of `Y`, and the injectivity of the pullback along the flat surjection `∐ Uᵢ → Y`. On
the class of the theorem the relative dimension is supplied by
`Hironaka.Resolution.Algebraic.Kol07.Thm36.RelativeDimensionConstancy`. -/
theorem BR_eq_eraseEmpty_pullback_of_smooth (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))] [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) (hY : Y.IsReducedEquidimensional k)
    (h : Y ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] (d : ℕ)
    [SmoothOfRelativeDimension d h] :
    BR k Y = ((BR k X).pullback h).eraseEmpty := by
  have hcY : CompactSpace Y := compactSpace_of_quasiCompact_over k Y
  have h0 := smoothOfRelativeDimension_zero_affineCoverDesc Y
  have hd : SmoothOfRelativeDimension d (affineCoverDesc Y ≫ h) := by
    have := smoothOfRelativeDimension_comp 0 d (affineCoverDesc Y) h
    rwa [Nat.zero_add] at this
  have hsm : Smooth (affineCoverDesc Y ≫ h) := SmoothOfRelativeDimension.smooth d _
  have hover : (affineCoverDesc Y ≫ h).IsOver (Spec (CommRingCat.of k)) := by
    constructor
    rw [Category.assoc, HomIsOver.comp_over (f := h) (S := Spec (CommRingCat.of k)),
      HomIsOver.comp_over (f := affineCoverDesc Y) (S := Spec (CommRingCat.of k))]
  have hgen := BRAffine_eq_eraseEmpty_BR_pullback_of_smooth (k := k) X (affineCoverScheme Y) hX
    hY.affineCoverScheme (affineCoverDesc Y ≫ h) d
  have hdesc := BR_pullback_affineCoverDesc (k := k) Y hY
  rw [hgen, pullback_comp,
    eraseEmpty_pullback_of_flat_surjective _ _ (surjective_affineCoverDesc Y)] at hdesc
  exact pullback_injective_of_surjective (affineCoverDesc Y) (surjective_affineCoverDesc Y) hdesc

/-- The first part of clause (4a), with the relative dimension as input: along a smooth surjective
`h` the pullback is exact (`eraseEmpty_BR`). -/
theorem BR_eq_pullback_of_smooth_surjective (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))] [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) (hY : Y.IsReducedEquidimensional k)
    (h : Y ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] (d : ℕ) [SmoothOfRelativeDimension d h]
    (hs : Function.Surjective h) :
    BR k Y = (BR k X).pullback h := by
  have := SmoothOfRelativeDimension.smooth d h
  rw [BR_eq_eraseEmpty_pullback_of_smooth (k := k) X Y hX hY h d,
    eraseEmpty_pullback_of_flat_surjective _ _ hs, eraseEmpty_BR]

end Hironaka.Resolution
