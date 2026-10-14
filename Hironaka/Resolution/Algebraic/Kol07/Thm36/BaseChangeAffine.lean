/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.BaseChangeTriple
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.BR
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Functorial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AdmissiblePairs
import Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback
import Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Kol07.Thm36.EqualAbsorbingIndex
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenterPullback
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ReducedComponents
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FlatTransport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SigmaCharts
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.BaseChangeEmbedding
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Base change of the resolution functor

Clause (4b) of the functorial resolution theorem, commutation with change of fields [Kol07, 34.2],
for the resolution functor `BR` (`Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`), following the
proof of [Kol07, Theorem 36]: an embedding `i : X ↪ A` over `K` and `σ : K ↪ L` give the embedding
`i_{σ,L} : X_{σ,L} ↪ A_{σ,L}` of the base changes, and the principalization sequence commutes
with change of fields [Kol07, Theorem 35 (4)].

## The exact two-field form of the pullback lemma

`BRAffine_eq_eraseEmpty_pullback_of_admissible`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback`) compares two admissible pairs over
the SAME field along a smooth `g` of ambients, up to the deletion of empty steps, because `g` need
not be surjective. When the runs are related on the nose, `BP TZ = g^* BP TX`, and the morphism `f :
Z ⟶ X` is flat and SURJECTIVE, no deletion is needed and the fields may differ
(`BRAffine_eq_pullback_of_BP_eq_pullback`): the truncation index of `Z` is the absorbing index of
any component `D` of `Z` (`firstCenterIndex_eq_componentIndex`), which is the absorbing index in
`BP TX` of the component of `X` into which `f` maps `D` (generic points transported along the flat
`f`, `firstCenterIndex_pullback_of_flat_of_le`), the truncation index of `X`; so the affine
resolution of `Z` is the pullback of that of `X`, and the deletion commutes with the flat
surjective pullback.

## The base-changed admissible pair

For an admissible pair `(TA, emb)` of `X` and the pullback square `XL = X ×_{Spec k} Spec L`, the
base-changed triple `Triple.baseChange TA σ` (ambient `TA.X.left ×_{Spec k} Spec L`, ideal and
boundary pulled back) with the embedding `baseChangeEmbedding emb` is an admissible pair of `XL`
(`admissibleEmbedding_baseChange`): the square `XL = X ×_{TA.X.left} (TA.baseChange σ).X.left`
(pasting, `IsPullback.of_right`) makes `emb'` a closed immersion with `emb'.ker = TA.I.comap p_A`
(`ker_eq_comap_of_isPullback`), the ambient is affine (a fibre product of affines), and the
boundary stays empty. Then `BP (TA.baseChange σ) = p_A^* BP TA` (`BP_baseChange`), `p_A` is flat
(`flat_of_isBaseChangeOf`), `p` is flat and surjective (the base change of `Spec L → Spec k`), and
the exact pullback lemma gives `BRAffine L XL = p^* BRAffine k X` for affine members
(`BRAffine_baseChange_of_class`).

## Clause (4b) for the resolution functor

For members `X` over `k` and `XL` over `L` in a pullback square over `Spec σ`
(`BR_baseChange_of_class`): cover `X` by its finite affine cover `Uᵢ` and `XL` by the preimages
`p⁻¹Uᵢ = Uᵢ ×_k L` (`coverPreimage` of `Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent`); the
coproduct `∐ p⁻¹Uᵢ → ∐ Uᵢ` is again a base change over `Spec σ` (a coproduct of pullback squares is
a pullback square, `isPullback_sigmaMap_sigmaDesc`), so the affine (4b) computes `BRAffine L (∐
p⁻¹Uᵢ)` from `BRAffine k (∐ Uᵢ) = g^* BR X`; the affine (34.1) over `L` for the étale surjection `∐
p⁻¹Uᵢ → XL` computes it from `BR XL`; cancelling the flat surjection gives `BR XL = p^* BR X`.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Scheme Hironaka
  BlowUpSequence Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- The exact two-field form of the pullback lemma: for admissible pairs of `X` over `k` and `Z`
over `L` whose global runs are related by `BP TZ = g^* BP TX` along a flat `g`, and a flat
SURJECTIVE `f : Z ⟶ X` compatible with the embeddings, `BRAffine L Z = f^* BRAffine k X` on the
nose. -/
theorem BRAffine_eq_pullback_of_BP_eq_pullback {L : Type u} [Field L] [CharZero L]
    (X Z : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [Z.Over (Spec (CommRingCat.of L))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of L))]
    (hX : X.IsReducedEquidimensional k) (hZ : Z.IsReducedEquidimensional L)
    (TX : Triple k) (TZ : Triple L) (embX : X ⟶ TX.X.left) (embZ : Z ⟶ TZ.X.left)
    (hadmX : AdmissibleEmbedding k X TX embX) (hadmZ : AdmissibleEmbedding L Z TZ embZ)
    (g : TZ.X.left ⟶ TX.X.left) [Flat g]
    (hBP : Hironaka.Sequence.BP TZ = (Hironaka.Sequence.BP TX).pullback g)
    (f : Z ⟶ X) [Flat f] (hs : Function.Surjective f) (hsq : embZ ≫ g = f ≫ embX) :
    BRAffine L Z = (BRAffine k X).pullback f := by
  have hNX : IsNoetherian X := (X ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hNZ : IsNoetherian Z := (Z ↘ Spec (CommRingCat.of L)).isNoetherian_of_field
  have hNTX : IsNoetherian TX.X.left := (TX.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hNTZ : IsNoetherian TZ.X.left := (TZ.X.left ↘ Spec (CommRingCat.of L)).isNoetherian_of_field
  have hclX : IsClosedImmersion embX := hadmX.1
  have hclZ : IsClosedImmersion embZ := hadmZ.1
  have hredX : IsReduced X := hX.1
  have hredZ : IsReduced Z := hZ.1
  obtain ⟨dX, hdX⟩ := hX.2
  obtain ⟨dZ, hdZ⟩ := hZ.2
  rw [BRAffine_eq_eraseEmpty_BR_affine k X TX embX hadmX,
    BRAffine_eq_eraseEmpty_BR_affine L Z TZ embZ hadmZ,
    ← eraseEmpty_pullback_of_flat_surjective _ _ hs]
  rcases isEmpty_or_nonempty Z with hZe | hZn
  · rw [eraseEmpty_eq_nil_of_isEmpty _ hZe, eraseEmpty_eq_nil_of_isEmpty _ hZe]
  · -- a component `D` of `Z` and the component `C` of `X` into which `f` maps it
    set D : Set Z := _root_.irreducibleComponent hZn.some with hDdef
    have hD : D ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents _
    obtain ⟨C, hC, hfC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (f '' D)
      (hD.1.image f f.continuous.continuousOn)
    have hIC : IsIntegral ((X.irreducibleComponentIdeal C hC).map embX).subscheme :=
      isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced C hC embX
    have hID : IsIntegral ((Z.irreducibleComponentIdeal D hD).map embZ).subscheme :=
      isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced D hD embZ
    have hηC : IsGenericPoint hC.1.genericPoint C :=
      hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have hηD : IsGenericPoint hD.1.genericPoint D :=
      hD.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hD)
    have hfη : f hD.1.genericPoint = hC.1.genericPoint :=
      map_genericPoint_eq_of_flat f hD hfC hηC hηD
    have hle : ((X.irreducibleComponentIdeal C hC).map embX).comap g ≤
        (Z.irreducibleComponentIdeal D hD).map embZ := by
      rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, hsq,
        Scheme.IdealSheafData.comap_comp, comap_map_of_isClosedImmersion]
      exact comap_irreducibleComponentIdeal_le f C hC D hD hfC
    have hηη' : g (embZ hD.1.genericPoint) = embX hC.1.genericPoint := by
      rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hfη]
    -- the truncation indices agree
    have hidx : firstCenterIndex (Hironaka.Sequence.BP TZ) TZ.I =
        firstCenterIndex (Hironaka.Sequence.BP TX) TX.I := by
      rw [firstCenterIndex_eq_componentIndex (d := dZ) Z TZ embZ hadmZ D hD, componentIndex_def,
        hBP, firstCenterIndex_eq_componentIndex (d := dX) X TX embX hadmX C hC,
        componentIndex_def]
      exact firstCenterIndex_pullback_of_flat_of_le (Hironaka.Sequence.BP TX) g _
        (isGenericPoint_map_irreducibleComponentIdeal C hC embX hηC) _ hle
        (isGenericPoint_map_irreducibleComponentIdeal D hD embZ hηD) hηη'
    rw [BR_affine_eq, BR_affine_eq, hidx, hBP, ← take_pullback, ← pullback_comp, hsq,
      pullback_comp]

/-- The base change of an embedding (the proof of [Kol07, Theorem 36]: `i : X ↪ A` over `K` and
`σ : K ↪ L` give `i_{σ,L} : X_{σ,L} ↪ A_{σ,L}`): the base change of an admissible pair of
`X` along `σ`, through a pullback square `XL = X ×_{Spec k} Spec L`, is an admissible pair of `XL`
in the base-changed triple, compatible with the projections. -/
theorem admissibleEmbedding_baseChange (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    (L : Type u) [Field L] (σ : k →+* L)
    (XL : Scheme.{u}) [XL.Over (Spec (CommRingCat.of L))] (p : XL ⟶ X)
    (hp : IsPullback p (XL ↘ Spec (CommRingCat.of L)) (X ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom σ)))
    (TA : Triple k) (emb : X ⟶ TA.X.left) (hadm : AdmissibleEmbedding k X TA emb) :
    ∃ emb' : XL ⟶ (TA.baseChange σ).X.left, AdmissibleEmbedding L XL (TA.baseChange σ) emb' ∧
      emb' ≫ pullback.fst (TA.X.left ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom σ)) =
        p ≫ emb := by
  have hcl : IsClosedImmersion emb := hadm.1
  have hemb : emb ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k) :=
    hadm.2.1.comp_over
  have hAaff : IsAffine TA.X.left := hadm.2.2.1
  have hA := (TA.isBaseChangeOf_baseChange σ).1
  let emb' : XL ⟶ (TA.baseChange σ).X.left := baseChangeEmbedding emb hemb hp hA
  have hcomp : emb' ≫ pullback.fst _ _ = p ≫ emb := baseChangeEmbedding_comp emb hemb hp hA
  have hover : emb' ≫ ((TA.baseChange σ).X.left ↘ Spec (CommRingCat.of L)) =
      XL ↘ Spec (CommRingCat.of L) := baseChangeEmbedding_over emb hemb hp hA
  -- the square `XL = X ×_{TA.X.left} (TA.baseChange σ).X.left`
  have hsq : IsPullback emb' p (pullback.fst (TA.X.left ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom σ))) emb := by
    refine IsPullback.of_right ?_ hcomp hA.flip
    rw [hover, hemb]
    exact hp.flip
  refine ⟨emb', ⟨?_, ⟨hover⟩, ?_, ?_, ?_⟩, hcomp⟩
  · exact property_of_isPullback @IsClosedImmersion hsq hcl
  · exact inferInstanceAs (IsAffine (Limits.pullback (TA.X.left ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom σ))))
  · exact hadm.2.2.2.1
  · rw [ker_eq_comap_of_isPullback emb emb' p _ hsq, hadm.2.2.2.2]
    rfl

/-- Clause (4b) for affine members of the class [Kol07, Theorem 36, proof; 34.2]: for affine
members `X` over `k` and `XL` over `L` in a pullback square over `Spec σ`,
`BRAffine L XL = p^* BRAffine k X`. -/
theorem BRAffine_baseChange_of_class (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IsAffine X]
    (_ : X.IsReducedEquidimensional k)
    (L : Type u) [Field L] [CharZero L] (σ : k →+* L)
    (XL : Scheme.{u}) [XL.Over (Spec (CommRingCat.of L))]
    [LocallyOfFiniteType (XL ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (XL ↘ Spec (CommRingCat.of L))]
    (_ : XL.IsReducedEquidimensional L)
    (p : XL ⟶ X) :
    IsPullback p (XL ↘ Spec (CommRingCat.of L)) (X ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom σ)) →
      BRAffine L XL = (BRAffine k X).pullback p := by
  intro hp
  have hX : X.IsReducedEquidimensional k := ‹_›
  have hXL : XL.IsReducedEquidimensional L := ‹_›
  obtain ⟨TA, emb, hadm⟩ := exists_admissibleEmbedding (k := k) X
  obtain ⟨emb', hadm', hcomp⟩ := admissibleEmbedding_baseChange X L σ XL p hp TA emb hadm
  have hflatp : Flat p := flat_of_isPullback_specMap hp
  have hflatA := flat_of_isBaseChangeOf σ TA (TA.baseChange σ) (pullback.fst _ _)
    (TA.isBaseChangeOf_baseChange σ)
  exact BRAffine_eq_pullback_of_BP_eq_pullback X XL hX hXL TA (TA.baseChange σ) emb emb' hadm
    hadm' _ (BP_baseChange σ TA (TA.baseChange σ) _ (TA.isBaseChangeOf_baseChange σ)) p
    (surjective_of_isPullback_specMap hp) hcomp

/-! ### Clause (4b) for the resolution functor -/

/-- Clause (4b) of the functorial resolution theorem [Kol07, Theorem 36 (4); 34.2]: for members `X`
over `k` and `XL` over `L` of the class in a pullback square over `Spec σ`, `BR XL = p^* BR X`,
through the coproduct `∐ p⁻¹Uᵢ` of the preimages of the finite affine cover of `X` (a base change of
`∐ Uᵢ`, the affine (4b)), the cover descent of `X`, the affine (34.1) over `L` for the étale
surjection `∐ p⁻¹Uᵢ → XL`, and the cancellation of that flat surjection. -/
theorem BR_baseChange_of_class (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (_ : X.IsReducedEquidimensional k)
    (L : Type u) [Field L] [CharZero L] (σ : k →+* L)
    (XL : Scheme.{u}) [XL.Over (Spec (CommRingCat.of L))]
    [LocallyOfFiniteType (XL ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (XL ↘ Spec (CommRingCat.of L))]
    [IsSeparated (XL ↘ Spec (CommRingCat.of L))]
    (_ : XL.IsReducedEquidimensional L)
    (p : XL ⟶ X) :
    IsPullback p (XL ↘ Spec (CommRingCat.of L)) (X ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom σ)) →
      (BRFunctor L).seq XL = ((BRFunctor k).seq X).pullback p := by
  intro hp
  have hX : X.IsReducedEquidimensional k := ‹_›
  have hXL : XL.IsReducedEquidimensional L := ‹_›
  change BR L XL = (BR k X).pullback p
  have hcX : CompactSpace X := compactSpace_of_quasiCompact_over k X
  have hcXL : CompactSpace XL := compactSpace_of_quasiCompact_over L XL
  -- `p` is affine and flat (the base change of `Spec L → Spec k`)
  have hpaff : IsAffineHom p :=
    property_of_isPullback @IsAffineHom hp inferInstance
  have hflatp : Flat p := flat_of_isPullback_specMap hp
  have hWaff : ∀ i, IsAffine (coverPreimage p i) := isAffine_coverPreimage p
  -- the coproduct of the preimages, an affine class member over `L`
  let _ : (∐ coverPreimage p).Over (Spec (CommRingCat.of L)) :=
    ⟨Sigma.desc (coverPreimageι p) ≫ (XL ↘ Spec (CommRingCat.of L))⟩
  have hoverE : (Sigma.desc (coverPreimageι p)).IsOver (Spec (CommRingCat.of L)) := ⟨rfl⟩
  have hlfT : LocallyOfFiniteType ((∐ coverPreimage p) ↘ Spec (CommRingCat.of L)) := by
    change LocallyOfFiniteType (Sigma.desc (coverPreimageι p) ≫ (XL ↘ Spec (CommRingCat.of L)))
    have := locallyOfFiniteType_sigmaDesc (coverPreimageι p)
    infer_instance
  have hZ' : (∐ coverPreimage p).IsReducedEquidimensional L :=
    .sigma _ (coverPreimageι p) (fun i => by
      change Sigma.ι _ i ≫ Sigma.desc (coverPreimageι p) ≫ (XL ↘ Spec (CommRingCat.of L)) = _
      rw [← Category.assoc, Sigma.ι_comp_desc]) hXL
  have hAff : IsAffine (∐ coverPreimage p) := inferInstance
  have hAffHom := isAffineHom_of_isAffine ((∐ coverPreimage p) ↘ Spec (CommRingCat.of L))
  have hqc : QuasiCompact ((∐ coverPreimage p) ↘ Spec (CommRingCat.of L)) := inferInstance
  have hsep : IsSeparated ((∐ coverPreimage p) ↘ Spec (CommRingCat.of L)) :=
    IsSeparated.of_isAffineHom _
  -- the coproduct square over `Spec σ`
  have hsqC : IsPullback (Limits.Sigma.map (coverPreimageMap p)) (Sigma.desc (coverPreimageι p))
      (affineCoverDesc X) p :=
    isPullback_sigmaMap_sigmaDesc _ _ _ p (isPullback_coverPreimageMap p)
  have hsq : IsPullback (Limits.Sigma.map (coverPreimageMap p))
      ((∐ coverPreimage p) ↘ Spec (CommRingCat.of L))
      (affineCoverScheme X ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom σ)) :=
    hsqC.paste_vert hp
  -- the affine (4b) on the coproducts
  have h1 := BRAffine_baseChange_of_class (affineCoverScheme X) hX.affineCoverScheme L σ
    (∐ coverPreimage p) hZ' (Limits.Sigma.map (coverPreimageMap p)) hsq
  -- the affine 34.1 over `L` for the étale surjection `∐ p⁻¹Uᵢ → XL`
  have hsurj : Function.Surjective (Sigma.desc (coverPreimageι p)) :=
    surjective_sigmaDesc _ (exists_coverPreimageι_eq p)
  have h0E : SmoothOfRelativeDimension 0 (Sigma.desc (coverPreimageι p)) :=
    smoothOfRelativeDimension_sigmaDesc _ 0
  have hsmE : Smooth (Sigma.desc (coverPreimageι p)) := smooth_sigmaDesc _
  have hflatE : Flat (Sigma.desc (coverPreimageι p)) := flat_sigmaDesc _
  have h2 := BRAffine_eq_eraseEmpty_BR_pullback_of_smooth (k := L) XL (∐ coverPreimage p) hXL hZ'
    (Sigma.desc (coverPreimageι p)) 0
  rw [eraseEmpty_pullback_of_flat_surjective _ _ hsurj, eraseEmpty_BR] at h2
  -- the cover descent of `X` and the square
  have hdesc := BR_pullback_affineCoverDesc (k := k) X hX
  rw [← hdesc, ← pullback_comp, sigmaMap_coverPreimageMap_comp_affineCoverDesc p,
    pullback_comp] at h1
  exact pullback_injective_of_surjective (Sigma.desc (coverPreimageι p)) hsurj (h2.symm.trans h1)

end Hironaka.Resolution
