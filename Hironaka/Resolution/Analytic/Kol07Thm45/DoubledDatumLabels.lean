/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductPadIdentity
public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductSumData
import Hironaka.AnalyticSpace.ClosedSubspaceLemmas
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductLevelPair
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductMixedTransition
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionHomOnComp
import Hironaka.Resolution.Analytic.Kol07Thm45.RunFamilyRestrict
import Hironaka.Resolution.Analytic.OrderReduction.Step22Defs
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The label coherence of the doubled datum

Kollár's agreement of the centres on the overlaps, (37.2) in [Kol07, Proposition 37, proof], for
two runs. The coproduct member of label `l` of a datum `D` is traced on every piece (`pieceTrace`,
`CoproductGluedFamily.lean`), and the gluing of the pieces' local resolutions needs these traces to
be compatible along the transitions WITH THE IDENTITY LABELLING. The transitions come from the
DOUBLED datum `sumPadData D D` — the datum padded to the left and to the right, read on one
coproduct ambient — through the mixed-pair transition `exists_mixedTransition_sumPadData`
(`CoproductMixedTransition.lean`), whose member clause is stated at the labels `σ` of the doubled
run. A label `l` of `D` reaches the doubled run's stage set by TWO routes, `lab₁ ∘ o₁.symm` (the
padding identity of the left copy, then the label embedding at `inl` of `CoproductSumData.lean`)
and `lab₂ ∘ o₂.symm` (the right copy, `inr`), and the identity labelling of the traces needs the
two routes to AGREE — on the labels whose member is not the unit ideal (`⊤` in the closed-subspace
order is the unit ideal, the EMPTY subspace, `isUnit_iff`; the off-range clauses of the label
embeddings say nothing about a label with an empty member, so the routes need not agree there, and
there the traces are all `⊤` and compatibility is trivial).

* `exists_resIn_toFun_eq`: the coproduct local resolution is covered by the summand inclusions
  `resIn i` (`range_toFun_resIn`, `coe_sigmaCoordImage`).
* `exists_mem_support_comap_resIn_of_ne_top`: a non-unit closed subspace of the coproduct local
  resolution has a point on some piece.
* `sumLabelTrace`: the `⊤`-extended piece trace along a label embedding into a common label set,
  with its two evaluation lemmas — the families of the conjugation lemma of
  `CoproductGluedFamilyCompat.lean`.
* `comap_sumInrResIn_sigmaMembers_ne_top_iff`: the POINTWISE STEP — a stage of the doubled run has
  a non-empty trace on the `inr` copy iff on the `inl` copy: a point of one trace lies on a piece,
  its image in `X` lies in both piece domains (`pieceDom_padAlongData`), the mixed-pair transition
  at the same piece on both sides gives an isomorphism over a neighbourhood carrying the one trace
  to the other, and supports transfer along the inverse image (`cosupport_comap`).
* `label_route_eq_of_ne_top`: the two label routes agree on the non-trivial labels — the routes
  restricted to those labels are order embeddings of a finite linear order with equal ranges
  (`OrderEmbedding.range_inj`, `Finite.to_wellFoundedLT`; finiteness through
  `finite_nonempty_totalTransformSeq`).

No swap of the doubled ambient, no transport of the run, no non-emptiness of members is used
anywhere. Not in the sources beyond Kollár's proof; bookkeeping.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace
open KLocallyRingedSpace Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace Manifold.IdealSheaf

/-- A point of the cosupport of an ideal sheaf witnesses that it is not the unit ideal
(`cosupport_top`). -/
theorem ne_top_of_mem_support {X : AlgebraicGeometry.LocallyRingedSpace.{u}}
    {J : IdealSheaf X.𝒪} {z : X} (hz : z ∈ J.support) : J ≠ ⊤ :=
  fun h => by rw [h, support_top] at hz; exact hz

end Manifold.IdealSheaf

section IdealSheafTools

/-! Four bookkeeping facts about the inverse image of ideal sheaves along a morphism of locally
ringed spaces (`QuotientSpace.comap`), stated once here for this module and the modules above it:
the unit ideal pulls back to the unit ideal, a non-unit inverse image comes from a non-unit ideal,
a point of the cosupport witnesses a non-unit ideal, and an isomorphism preserves non-unit ideals
(`cosupport_comap`: the cosupport of the inverse image is the preimage of the cosupport). -/

namespace AnalyticSpace.QuotientSpace

variable {X' X : AlgebraicGeometry.LocallyRingedSpace.{u}}

/-- The inverse image of the unit ideal is the unit ideal (its cosupport is the preimage of the
empty set). -/
theorem comap_top_idealSheaf (φ : X' ⟶ X) :
    comap φ (⊤ : Manifold.IdealSheaf X.𝒪) = ⊤ :=
  Manifold.IdealSheaf.eq_top_of_support_eq_empty (by
    rw [cosupport_comap, Manifold.IdealSheaf.support_top, Set.preimage_empty])

/-- An ideal sheaf whose inverse image is not the unit ideal is not the unit ideal. -/
theorem ne_top_of_comap_ne_top (φ : X' ⟶ X) {J : Manifold.IdealSheaf X.𝒪}
    (h : comap φ J ≠ ⊤) : J ≠ ⊤ :=
  fun hJ => h (by rw [hJ]; exact comap_top_idealSheaf φ)

private theorem exists_base_eq_of_isIso (φ : X' ⟶ X) [IsIso φ] (b : X) : ∃ a, φ.base a = b :=
  ⟨(inv φ).base b, congrArg (fun g : X ⟶ X => g.base b) (IsIso.inv_hom_id φ)⟩

/-- Along an isomorphism the inverse image of a non-unit ideal sheaf is not the unit ideal — a
point of the cosupport has a preimage (`cosupport_comap`). -/
theorem comap_ne_top_of_isIso (φ : X' ⟶ X) [IsIso φ] {J : Manifold.IdealSheaf X.𝒪}
    (hJ : J ≠ ⊤) : comap φ J ≠ ⊤ := by
  obtain ⟨z, hz⟩ : J.support.Nonempty := Set.nonempty_iff_ne_empty.mpr
    (fun h => hJ (Manifold.IdealSheaf.eq_top_of_support_eq_empty h))
  obtain ⟨a, ha⟩ := exists_base_eq_of_isIso φ z
  apply Manifold.IdealSheaf.ne_top_of_mem_support (z := a)
  rw [cosupport_comap]
  change φ.base a ∈ J.support
  rw [ha]
  exact hz

end AnalyticSpace.QuotientSpace

end IdealSheafTools

namespace Hironaka.Manifold.LocalEmbeddingData

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜}

section Cover

variable {U : Set X} (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
  (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
  (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
  (hbed : bed.IsEmbeddedDesing)

/-- **The coproduct local resolution is covered by the summand inclusions** — every point lies in
the range of some `resIn i` (its image in the coproduct ambient lies in one summand of
`ambImage W = ⋃ i, sigmaMk i '' W i`, `coe_sigmaCoordImage`; `range_toFun_resIn`). -/
theorem exists_resIn_toFun_eq
    (y : bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
      (D.isCompact_closure_ambImage W hW)) :
    ∃ (i : D.ι) (y' : (D.embedding i).localResolution bed (W i) (hW i)),
      KLocallyRingedSpace.Hom.toFun (D.resIn bed W hW hbed i) y' = y := by
  set p := (bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW)).toSuccession.stageMap (Fin.last _)
    ((bed.lastIdealOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
        (D.isCompact_closure_ambImage W hW)).toAnalyticSpaceι y) with hp
  have hp2 : (p.1 : D.sigmaAmbient) ∈
      (sigmaCoordImage (fun i => (D.embedding i).G) W : Set D.sigmaAmbient) := p.2
  rw [coe_sigmaCoordImage] at hp2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp2
  have hy : y ∈ Set.range (KLocallyRingedSpace.Hom.toFun (D.resIn bed W hW hbed i)) := by
    rw [D.range_toFun_resIn bed W hW hbed i]
    exact hi
  obtain ⟨y', hy'⟩ := hy
  exact ⟨i, y', hy'⟩

/-- **A non-unit closed subspace of the coproduct local resolution has a point on some piece** —
the unit ideal is the closed subspace with empty support (`isUnit_iff`), and supports transfer
along `resIn i` (`cosupport_comap`). -/
theorem exists_mem_support_comap_resIn_of_ne_top
    (C :
        ClosedSubspace
            (bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple
      (D.ambImage W) (D.isCompact_closure_ambImage W hW)))
    (hC : C ≠ ⊤) :
    ∃ (i : D.ι) (y' : (D.embedding i).localResolution bed (W i) (hW i)),
      y' ∈ IdealSheaf.support (QuotientSpace.comap (D.resIn bed W hW hbed i).1 C) := by
  have hsupp : (IdealSheaf.support C).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hC ((ClosedSubspace.isUnit_iff C).mpr h)
  obtain ⟨y, hy⟩ := hsupp
  obtain ⟨i, y', rfl⟩ := D.exists_resIn_toFun_eq bed W hW hbed y
  refine ⟨i, y', ?_⟩
  rw [QuotientSpace.cosupport_comap]
  exact hy

open Classical in
/-- **The `⊤`-extended piece trace along a label embedding** — for a label `σ` of a common label
set, the trace on piece `i` of the member of `D` carried by `o` from the label `k` with
`lab k = σ`, and the unit ideal off the range of `lab`. -/
def sumLabelTrace {ι' Λ : Type u} [LinearOrder ι'] [LinearOrder Λ]
    (o : ι' ≃o D.sigmaIndex bed W hW) (lab : ι' ↪o Λ)
    (i : D.ι) (σ : Λ) :
    ClosedSubspace ((D.embedding i).localResolution bed (W i) (hW i)) :=
  if h : σ ∈ Set.range lab then
    QuotientSpace.comap (D.resIn bed W hW hbed i).1 (D.sigmaMembers bed W hW hbed (o h.choose))
  else ⊤

/-- The extended trace at a label in the range is the trace of the member (`lab` is injective). -/
theorem sumLabelTrace_lab {ι' Λ : Type u} [LinearOrder ι'] [LinearOrder Λ]
    (o : ι' ≃o D.sigmaIndex bed W hW) (lab : ι' ↪o Λ)
    (i : D.ι) (k : ι') :
    D.sumLabelTrace bed W hW hbed o lab i (lab k) =
      QuotientSpace.comap (D.resIn bed W hW hbed i).1 (D.sigmaMembers bed W hW hbed (o k)) := by
  have h : lab k ∈ Set.range lab := ⟨k, rfl⟩
  rw [sumLabelTrace, dite_eq_left h, lab.injective h.choose_spec]

/-- The extended trace at a label off the range is the unit ideal. -/
theorem sumLabelTrace_of_not_mem_range {ι' Λ : Type u} [LinearOrder ι'] [LinearOrder Λ]
    (o : ι' ≃o D.sigmaIndex bed W hW)
    (lab : ι' ↪o Λ) (i : D.ι) {σ : Λ} (h : σ ∉ Set.range lab) :
    D.sumLabelTrace bed W hW hbed o lab i σ = ⊤ := by
  rw [sumLabelTrace, dite_eq_right h]

end Cover

section Labels

variable {U : Set X} (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
  (hbed : bed.IsEmbeddedDesing)
  (W₁ : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 ((D.padLeftData D.n).embedding i).G))
  (hW₁ : ∀ i, IsCompact (closure (W₁ i : Set (pieceAmbient.{u} 𝕜
    ((D.padLeftData D.n).embedding i).G))))
  (W₂ : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 ((D.padRightData D.n).embedding i).G))
  (hW₂ : ∀ i, IsCompact (closure (W₂ i : Set (pieceAmbient.{u} 𝕜
    ((D.padRightData D.n).embedding i).G))))

local notation "𝒪p" => sumPadOpens D D W₁ W₂
local notation "𝒽p" => isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂

-- The doubled datum's summand embeddings are those of the two padded copies (the cast-free
-- `sumPadData`), definitionally.
example (i : D.ι) :
    (sumPadData D D).embedding (Sum.inl i) = (D.padLeftData D.n).embedding i := rfl
example (i : D.ι) :
    (sumPadData D D).embedding (Sum.inr i) = (D.padRightData D.n).embedding i := rfl

/-- **A stage of the doubled run has a non-empty trace on the `inr` copy iff on the `inl` copy**
((37.2) in [Kol07, Proposition 37, proof], on the diagonal pair) — THE POINTWISE STEP, with no
labels: a point of one trace lies on a piece (`exists_mem_support_comap_resIn_of_ne_top`), its
image lies in both piece domains (`pieceDom_padAlongData` and `hpre`), the mixed-pair transition
at that piece on both sides carries the traces of every stage into each other over a
neighbourhood of the point, and supports transfer along the inverse image (`cosupport_comap`; from
the `inr` side through the inverse of the transition, `comap_ne_top_of_isIso`; the converse because
a non-unit inverse image comes from a non-unit ideal, `ne_top_of_comap_ne_top`). -/
theorem comap_sumInrResIn_sigmaMembers_ne_top_iff
    (hpre : D.padPreimageOpens (Fin.castAddEmb D.n) W₁ =
      D.padPreimageOpens (Fin.natAddEmb D.n) W₂)
    (σ : (sumPadData D D).sigmaIndex bed (sumPadOpens D D W₁ W₂)
      (isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂)) :
    QuotientSpace.comap (sumInrResIn D D W₁ W₂ bed hW₁ hW₂ hbed).1
        ((sumPadData D D).sigmaMembers bed (sumPadOpens D D W₁ W₂)
          (isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂) hbed σ) ≠ ⊤ ↔
      QuotientSpace.comap (sumInlResIn D D W₁ W₂ bed hW₁ hW₂ hbed).1
        ((sumPadData D D).sigmaMembers bed (sumPadOpens D D W₁ W₂)
          (isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂) hbed σ) ≠ ⊤ := by
  have hdom : ∀ i, (sumPadData D D).pieceDom (Sum.inr i) (W₂ i) = (sumPadData D D).pieceDom
      (Sum.inl i) (W₁ i) := fun i => by
    change (D.padAlongData (Fin.natAddEmb D.n)).pieceDom i (W₂ i) =
      (D.padAlongData (Fin.castAddEmb D.n)).pieceDom i (W₁ i)
    rw [D.pieceDom_padAlongData (Fin.natAddEmb D.n) W₂ i,
      D.pieceDom_padAlongData (Fin.castAddEmb D.n) W₁ i, hpre]
  constructor
  · intro hTr
    obtain ⟨i, y', hy'⟩ :=
      (D.padRightData D.n).exists_mem_support_comap_resIn_of_ne_top bed W₂ hW₂ hbed _ hTr
    have hxj : KLocallyRingedSpace.Hom.toFun ((sumPadData D D).pieceToSpace bed (Sum.inr i) (W₂
        i) (hW₂ i)) y' ∈
        (sumPadData D D).pieceDom (Sum.inr i) (W₂ i) :=
      ((sumPadData D D).embedding (Sum.inr i)).range_toFun_toSpaceMap_subset bed (W₂ i) (hW₂ i)
        ⟨y', rfl⟩
    have hxi : KLocallyRingedSpace.Hom.toFun ((sumPadData D D).pieceToSpace bed (Sum.inr i) (W₂
        i) (hW₂ i)) y' ∈
        (sumPadData D D).pieceDom (Sum.inl i) (W₁ i) := by
      rw [← hdom i]; exact hxj
    obtain ⟨P, hxP, -, -, θ, hθ, -, hcl⟩ :=
      exists_mixedTransition_sumPadData D D bed hbed W₁ hW₁ W₂ hW₂ i i _ hxi hxj
    have hcl' := hcl σ
    have hpt : (⟨y', hxP⟩ : ↥(Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
          ((sumPadData D D).pieceToSpace bed (Sum.inr i) (W₂ i) (hW₂ i)), Hom.continuous_toFun
              _⟩ P)) ∈
        (QuotientSpace.comap (ofRestrict (((sumPadData D D).embedding (Sum.inr
            i)).localResolution bed (W₂ i)
            (hW₂ i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
            ((sumPadData D D).pieceToSpace bed (Sum.inr i) (W₂ i) (hW₂ i)),
                Hom.continuous_toFun _⟩ P)).1
          (QuotientSpace.comap ((sumPadData D D).resIn bed 𝒪p 𝒽p hbed (Sum.inr i)).1
            ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed σ))).support := by
      have hJ := comap_resIn_sumPadData_inr D D W₁ W₂ bed hW₁ hW₂ hbed i
        ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed σ)
      have hy'' := (congrArg (fun C => y' ∈ IdealSheaf.support C) hJ).mpr hy'
      exact (congrArg (fun s => _ ∈ s) (QuotientSpace.cosupport_comap _ _)).mpr hy''
    have hne_r := IdealSheaf.ne_top_of_mem_support hpt
    have := hθ
    have : IsIso θ.1 :=
      ⟨⟨(inv θ).1, congrArg (·.1) (IsIso.hom_inv_id θ), congrArg (·.1) (IsIso.inv_hom_id θ)⟩⟩
    have hne_l := hcl' ▸ QuotientSpace.comap_ne_top_of_isIso θ.1 hne_r
    have h2 := QuotientSpace.ne_top_of_comap_ne_top _ hne_l
    have hJ' := comap_resIn_sumPadData_inl D D W₁ W₂ bed hW₁ hW₂ hbed i
      ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed σ)
    exact QuotientSpace.ne_top_of_comap_ne_top _ (fun h => h2 (hJ'.trans h))
  · intro hTl
    obtain ⟨i, y', hy'⟩ :=
      (D.padLeftData D.n).exists_mem_support_comap_resIn_of_ne_top bed W₁ hW₁ hbed _ hTl
    have hxi : KLocallyRingedSpace.Hom.toFun ((sumPadData D D).pieceToSpace bed (Sum.inl i) (W₁
        i) (hW₁ i)) y' ∈
        (sumPadData D D).pieceDom (Sum.inl i) (W₁ i) :=
      ((sumPadData D D).embedding (Sum.inl i)).range_toFun_toSpaceMap_subset bed (W₁ i) (hW₁ i)
        ⟨y', rfl⟩
    have hxj : KLocallyRingedSpace.Hom.toFun ((sumPadData D D).pieceToSpace bed (Sum.inl i) (W₁
        i) (hW₁ i)) y' ∈
        (sumPadData D D).pieceDom (Sum.inr i) (W₂ i) := by
      rw [hdom i]; exact hxi
    obtain ⟨P, hxP, -, -, θ, -, -, hcl⟩ :=
      exists_mixedTransition_sumPadData D D bed hbed W₁ hW₁ W₂ hW₂ i i _ hxi hxj
    have hcl' := hcl σ
    have hpt : (⟨y', hxP⟩ : ↥(Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
          ((sumPadData D D).pieceToSpace bed (Sum.inl i) (W₁ i) (hW₁ i)), Hom.continuous_toFun
              _⟩ P)) ∈
        (QuotientSpace.comap (ofRestrict (((sumPadData D D).embedding (Sum.inl
            i)).localResolution bed (W₁ i)
            (hW₁ i)).toKLocallyRingedSpace (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
            ((sumPadData D D).pieceToSpace bed (Sum.inl i) (W₁ i) (hW₁ i)),
                Hom.continuous_toFun _⟩ P)).1
          (QuotientSpace.comap ((sumPadData D D).resIn bed 𝒪p 𝒽p hbed (Sum.inl i)).1
            ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed σ))).support := by
      have hJ := comap_resIn_sumPadData_inl D D W₁ W₂ bed hW₁ hW₂ hbed i
        ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed σ)
      have hy'' := (congrArg (fun C => y' ∈ IdealSheaf.support C) hJ).mpr hy'
      exact (congrArg (fun s => _ ∈ s) (QuotientSpace.cosupport_comap _ _)).mpr hy''
    have hne_l := IdealSheaf.ne_top_of_mem_support hpt
    have hne_r := QuotientSpace.ne_top_of_comap_ne_top θ.1 (hcl' ▸ hne_l)
    have h2 := QuotientSpace.ne_top_of_comap_ne_top _ hne_r
    have hJ' := comap_resIn_sumPadData_inr D D W₁ W₂ bed hW₁ hW₂ hbed i
      ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed σ)
    exact QuotientSpace.ne_top_of_comap_ne_top _ (fun h => h2 (hJ'.trans h))

variable (V : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
  (hV : ∀ i, IsCompact (closure (V i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))

/-- **The two label routes of the doubled datum agree on the non-trivial labels** ((37.2) in
[Kol07, Proposition 37, proof], on the diagonal pair `(D, D)`) — for a label `l` of `D` whose
coproduct member is not the unit ideal, `lab₁ (o₁.symm l) = lab₂ (o₂.symm l)`, where `o₁`, `ψ₁`
(resp. `o₂`, `ψ₂`) are the coproduct-level conjuncts of the padding identity read at the datum's
reading opens `V` (`exists_padIdentity_of_padPreimageOpens_eq`: the order isomorphism of stage
sets and the isomorphism of coproduct local resolutions carrying the members) and `lab₁` (resp.
`lab₂`) is the label embedding of the left (resp. right) copy into the doubled run with its two
clauses (`CoproductSumData.lean`). The routes restricted to the non-trivial labels are order
embeddings of a finite linear order; by `comap_sumInrResIn_sigmaMembers_ne_top_iff` each has its
range inside the other's; equal ranges force equality (`OrderEmbedding.range_inj`). Off the
non-trivial labels nothing is asserted: the label embeddings' witnesses are not determined at an
empty member. -/
theorem label_route_eq_of_ne_top
    (hpre₁ : D.padPreimageOpens (Fin.castAddEmb D.n) W₁ = V)
    (hpre₂ : D.padPreimageOpens (Fin.natAddEmb D.n) W₂ = V)
    (o₁ : (D.padLeftData D.n).sigmaIndex bed W₁ hW₁ ≃o D.sigmaIndex bed V hV)
    (ψ₁ : bed.localResolutionOn (D.padLeftData D.n).sigmaTriple
        (D.padLeftData D.n).domBEDan_sigmaTriple ((D.padLeftData D.n).ambImage W₁)
        ((D.padLeftData D.n).isCompact_closure_ambImage W₁ hW₁) ⟶
        bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage V)
        (D.isCompact_closure_ambImage V hV))
    (hψ₁ : IsIso ψ₁)
    (hmem₁ : ∀ σp, QuotientSpace.comap ψ₁.1 (D.sigmaMembers bed V hV hbed (o₁ σp)) =
      (D.padLeftData D.n).sigmaMembers bed W₁ hW₁ hbed σp)
    (o₂ : (D.padRightData D.n).sigmaIndex bed W₂ hW₂ ≃o D.sigmaIndex bed V hV)
    (ψ₂ : bed.localResolutionOn (D.padRightData D.n).sigmaTriple
        (D.padRightData D.n).domBEDan_sigmaTriple ((D.padRightData D.n).ambImage W₂)
        ((D.padRightData D.n).isCompact_closure_ambImage W₂ hW₂) ⟶
        bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage V)
        (D.isCompact_closure_ambImage V hV))
    (hψ₂ : IsIso ψ₂)
    (hmem₂ : ∀ σp, QuotientSpace.comap ψ₂.1 (D.sigmaMembers bed V hV hbed (o₂ σp)) =
      (D.padRightData D.n).sigmaMembers bed W₂ hW₂ hbed σp)
    (lab₁ : (D.padLeftData D.n).sigmaIndex bed W₁ hW₁ ↪o
      (sumPadData D D).sigmaIndex bed (sumPadOpens D D W₁ W₂)
        (isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂))
    (hlab₁ : ∀ k, QuotientSpace.comap (sumInlResIn D D W₁ W₂ bed hW₁ hW₂ hbed).1
      ((sumPadData D D).sigmaMembers bed (sumPadOpens D D W₁ W₂)
        (isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂) hbed (lab₁ k)) =
      (D.padLeftData D.n).sigmaMembers bed W₁ hW₁ hbed k)
    (hlab₁' : ∀ σ, σ ∉ Set.range lab₁ →
      QuotientSpace.comap (sumInlResIn D D W₁ W₂ bed hW₁ hW₂ hbed).1
        ((sumPadData D D).sigmaMembers bed (sumPadOpens D D W₁ W₂)
          (isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂) hbed σ) = ⊤)
    (lab₂ : (D.padRightData D.n).sigmaIndex bed W₂ hW₂ ↪o
      (sumPadData D D).sigmaIndex bed (sumPadOpens D D W₁ W₂)
        (isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂))
    (hlab₂ : ∀ k, QuotientSpace.comap (sumInrResIn D D W₁ W₂ bed hW₁ hW₂ hbed).1
      ((sumPadData D D).sigmaMembers bed (sumPadOpens D D W₁ W₂)
        (isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂) hbed (lab₂ k)) =
      (D.padRightData D.n).sigmaMembers bed W₂ hW₂ hbed k)
    (hlab₂' : ∀ σ, σ ∉ Set.range lab₂ →
      QuotientSpace.comap (sumInrResIn D D W₁ W₂ bed hW₁ hW₂ hbed).1
        ((sumPadData D D).sigmaMembers bed (sumPadOpens D D W₁ W₂)
          (isCompact_closure_sumPadOpens D D W₁ W₂ hW₁ hW₂) hbed σ) = ⊤)
    (l : D.sigmaIndex bed V hV) (hl : D.sigmaMembers bed V hV hbed l ≠ ⊤) :
    lab₁ (o₁.symm l) = lab₂ (o₂.symm l) := by
  classical
  have hpre : D.padPreimageOpens (Fin.castAddEmb D.n) W₁ =
      D.padPreimageOpens (Fin.natAddEmb D.n) W₂ := hpre₁.trans hpre₂.symm
  have : IsIso ψ₁ := hψ₁
  have : IsIso ψ₂ := hψ₂
  have : IsIso ψ₁.1 :=
    ⟨⟨(inv ψ₁).1, congrArg (·.1) (IsIso.hom_inv_id ψ₁), congrArg (·.1) (IsIso.inv_hom_id ψ₁)⟩⟩
  have : IsIso ψ₂.1 :=
    ⟨⟨(inv ψ₂).1, congrArg (·.1) (IsIso.hom_inv_id ψ₂), congrArg (·.1) (IsIso.inv_hom_id ψ₂)⟩⟩
  -- the non-trivial labels form a finite linear order
  let A := {l : D.sigmaIndex bed V hV // D.sigmaMembers bed V hV hbed l ≠ ⊤}
  have : Finite A := by
    have := finite_nonempty_totalTransformSeq (D.sigmaRun bed V hV).toSuccession (Fin.last _)
    refine Finite.of_injective (fun a : A => (⟨a.1, ?_⟩ : {k // ((D.sigmaRun bed V
        hV).toSuccession.totalTransformSeq (Fin.last _)).hyp k ≠ ∅}))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
    intro hempty
    apply a.2
    change (HypersurfaceFamily.toClosedSubspaces (D.sigmaFamily bed V hV)
        (D.isClosedSubmanifold_sigmaFamily bed V hV hbed) a.1).comap _ = ⊤
    rw [show HypersurfaceFamily.toClosedSubspaces (D.sigmaFamily bed V hV)
        (D.isClosedSubmanifold_sigmaFamily bed V hV hbed) a.1 = ⊤ from
      IsClosedSubmanifold.idealSheaf_eq_top_of_eq_empty _ hempty]
    exact comap_top_closedSubspace _
  let φ₁ : A ↪o (sumPadData D D).sigmaIndex bed 𝒪p 𝒽p :=
    (OrderEmbedding.subtype _).trans (o₁.symm.toOrderEmbedding.trans lab₁)
  let φ₂ : A ↪o (sumPadData D D).sigmaIndex bed 𝒪p 𝒽p :=
    (OrderEmbedding.subtype _).trans (o₂.symm.toOrderEmbedding.trans lab₂)
  have key₁ : ∀ a : A, φ₁ a ∈ Set.range φ₂ := by
    intro a
    have h1 : QuotientSpace.comap (sumInlResIn D D W₁ W₂ bed hW₁ hW₂ hbed).1
        ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed (φ₁ a)) ≠ ⊤ := by
      change QuotientSpace.comap _ ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed (lab₁ (o₁.symm
          a.1))) ≠ ⊤
      rw [hlab₁ (o₁.symm a.1), ← hmem₁ (o₁.symm a.1), OrderIso.apply_symm_apply]
      exact QuotientSpace.comap_ne_top_of_isIso ψ₁.1 a.2
    have h2 := (D.comap_sumInrResIn_sigmaMembers_ne_top_iff bed hbed W₁ hW₁ W₂ hW₂ hpre
      (φ₁ a)).mpr h1
    have hmem : φ₁ a ∈ Set.range lab₂ := by
      by_contra hn
      exact h2 (hlab₂' _ hn)
    obtain ⟨k₂, hk₂⟩ := hmem
    have h3 : D.sigmaMembers bed V hV hbed (o₂ k₂) ≠ ⊤ := by
      rw [← hk₂, hlab₂ k₂, ← hmem₂ k₂] at h2
      exact QuotientSpace.ne_top_of_comap_ne_top _ h2
    refine ⟨⟨o₂ k₂, h3⟩, ?_⟩
    change lab₂ (o₂.symm (o₂ k₂)) = φ₁ a
    rw [OrderIso.symm_apply_apply]
    exact hk₂
  have key₂ : ∀ a : A, φ₂ a ∈ Set.range φ₁ := by
    intro a
    have h1 : QuotientSpace.comap (sumInrResIn D D W₁ W₂ bed hW₁ hW₂ hbed).1
        ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed (φ₂ a)) ≠ ⊤ := by
      change QuotientSpace.comap _ ((sumPadData D D).sigmaMembers bed 𝒪p 𝒽p hbed (lab₂ (o₂.symm
          a.1))) ≠ ⊤
      rw [hlab₂ (o₂.symm a.1), ← hmem₂ (o₂.symm a.1), OrderIso.apply_symm_apply]
      exact QuotientSpace.comap_ne_top_of_isIso ψ₂.1 a.2
    have h2 := (D.comap_sumInrResIn_sigmaMembers_ne_top_iff bed hbed W₁ hW₁ W₂ hW₂ hpre
      (φ₂ a)).mp h1
    have hmem : φ₂ a ∈ Set.range lab₁ := by
      by_contra hn
      exact h2 (hlab₁' _ hn)
    obtain ⟨k₁, hk₁⟩ := hmem
    have h3 : D.sigmaMembers bed V hV hbed (o₁ k₁) ≠ ⊤ := by
      rw [← hk₁, hlab₁ k₁, ← hmem₁ k₁] at h2
      exact QuotientSpace.ne_top_of_comap_ne_top _ h2
    refine ⟨⟨o₁ k₁, h3⟩, ?_⟩
    change lab₁ (o₁.symm (o₁ k₁)) = φ₂ a
    rw [OrderIso.symm_apply_apply]
    exact hk₁
  have hrange : Set.range φ₁ = Set.range φ₂ :=
    Set.Subset.antisymm (Set.range_subset_iff.mpr key₁) (Set.range_subset_iff.mpr key₂)
  have heq : φ₁ = φ₂ := OrderEmbedding.range_inj_of_wellFoundedLT.mp hrange
  exact DFunLike.congr_fun heq ⟨l, hl⟩

end Labels

end Hironaka.Manifold.LocalEmbeddingData
