/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.ExceptionalChain
public import Hironaka.Resolution.Analytic.Wlo09.Saturation
public import Hironaka.Resolution.Analytic.Wlo09.FamilyExt
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.ModelTransport.Square
import Hironaka.Resolution.Analytic.Wlo09.Clauses

/-!
# Włodarczyk's divisor `E` and strict transform `Ỹ` on the glued space

The global objects of [Wlo09, Theorem 2.0.2] on the glued space `M̃` of a compatible family `C`
(`CompatibleFamily.toExtensionCompatibleFamily`): the exceptional divisor
`gluedExceptionalIdeal`, the reduced ideal sheaf of the exceptional family glued along the
exhaustion (`gluedExceptional`), and the strict transform `globalStrictTransform I`, the
saturation of the total transform `σ^*(I)` by the exceptional divisor (`IdealSheaf.saturation`,
[BM97, Proposition 3.13]). Both pull back along the inclusion of every piece to the per-compact
objects, the last exceptional divisor and the last strict transform of the succession over the
piece (`gluedExceptionalIdeal_pullback_toLimitMap`, `globalStrictTransform_pullback_toLimitMap`,
the latter by the saturation identity
`IsDesingularizedBy.strictTransformSubspaceSeq_last_eq_saturation`), and the clauses of the
theorem hold for them, each read on a piece through the inclusion: `E` has simple normal
crossings (`isSncBoundary_gluedExceptionalIdeal`) with support the preimage of the singular locus
(`support_gluedExceptionalIdeal`); `Ỹ` is smooth (`isNonsingular_globalStrictTransform`) and has
simple normal crossings with `E` transversally
(`isSncBoundaryTransversalTo_globalStrictTransform`); and `σ^*(I) = I_Ỹ · I_Ẽ` pointwise
(`isMulBoundaryMonomial_globalStrictTransform`). The per-piece hypotheses are the clauses of the
embedded desingularization functor on the pieces, with the last exceptional family named
explicitly: its simple normal crossings, its reduced ideal sheaf being the last boundary, the
desingularization clauses (`IsDesingularizedBy`), the transversal chart of (3) and the monomial of
(6) with respect to that family.

Not in the sources beyond the statement cited; bookkeeping.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Filter AnalyticManifold Manifold
open scoped Manifold ContDiff

universe u

/-! ### The image of a product of ideals -/

/-- `Ideal.map` of a finite product of ideals. -/
theorem Ideal.map_finset_prod {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    Ideal.map f (∏ i ∈ s, I i) = ∏ i ∈ s, Ideal.map f (I i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top, Ideal.one_eq_top, Ideal.map_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Ideal.map_mul, ih]

namespace Hironaka.Manifold.CompatibleFamily

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} (C : CompatibleFamily T)

/-! ### The levels of the exhaustion -/

/-- The succession of `C` over the `m`-th member of the exhaustion of `M`. -/
abbrev seqLevel (m : ℕ) : FiniteSuccession (M.restrict (relCompactOpen (exhaustion M) m)) :=
  (C.seqOn (relCompactOpen (exhaustion M) m)
    (isCompact_closure_relCompactOpen (exhaustion M) m)).toSuccession

/-- The last exceptional family of `C` over the `m`-th member of the exhaustion. -/
abbrev excLevel (m : ℕ) : HypersurfaceFamily ((C.seqLevel m).last) :=
  C.exceptionalOn (relCompactOpen (exhaustion M) m)
    (isCompact_closure_relCompactOpen (exhaustion M) m)

/-- The chain of end results along the exhaustion. -/
abbrev chain : OpenEmbeddingChain 𝕜 (Fin n → 𝕜) := C.endResultChain (exhaustion M) C.hemb

/-- The glued blow-down `σ : M̃ → M` (the map of `toExtensionCompatibleFamily`), typed on the limit
manifold of the chain. -/
abbrev glueMap : AnalyticMap C.chain.limitManifold M := C.toExtensionCompatibleFamily.map

theorem space_toExtensionCompatibleFamily :
    C.toExtensionCompatibleFamily.space = C.chain.limitManifold := rfl

theorem toSpace_toExtensionCompatibleFamily (K : Compacts M) :
    C.toExtensionCompatibleFamily.toSpace K =
      C.chain.toLimitMap (relCompactOpenIndex (exhaustion M) K) := rfl

theorem glueMap_toLimit (m : ℕ) (x : (C.seqLevel m).last) :
    C.glueMap (C.chain.toLimit m x) =
      M.inclusion (relCompactOpen (exhaustion M) m) ((C.seqLevel m).composite x) := rfl

/-- The pull-back of `J` along the glued blow-down, read on a piece, is the pull-back of the
restriction of `J` along the composite of the piece. -/
theorem pullback_glueMap_pullback_toLimitMap (J : AnalyticManifold.IdealSheaf M) (m : ℕ) :
    (J.pullback C.glueMap C.glueMap.contMDiff).pullback (C.chain.toLimitMap m)
        (C.chain.toLimitMap m).contMDiff =
      (J.restrict (relCompactOpen (exhaustion M) m)).pullback (C.seqLevel m).composite
        (C.seqLevel m).composite.contMDiff := by
  refine (Manifold.IdealSheaf.pullback_pullback J ⇑C.glueMap C.glueMap.contMDiff
    ⇑(C.chain.toLimitMap m) (C.chain.toLimitMap m).contMDiff).trans ?_
  refine (Manifold.IdealSheaf.pullback_congr J _
    ((M.inclusion (relCompactOpen (exhaustion M) m)).contMDiff.comp
      (C.seqLevel m).composite.contMDiff) (funext fun _ => rfl)).trans ?_
  exact (Manifold.IdealSheaf.pullback_pullback J ⇑(M.inclusion (relCompactOpen (exhaustion M) m))
    (M.inclusion (relCompactOpen (exhaustion M) m)).contMDiff ⇑(C.seqLevel m).composite
    (C.seqLevel m).composite.contMDiff).symm

/-! ### The global objects -/

/-- **Włodarczyk's exceptional divisor `E` on `M̃`**: the reduced ideal sheaf of the exceptional
family glued along the exhaustion. -/
def gluedExceptionalIdeal : AnalyticManifold.IdealSheaf C.chain.limitManifold :=
  (C.gluedExceptional (exhaustion M)).idealSheaf

/-- **Włodarczyk's strict transform `Ỹ` on `M̃`**: the saturation of the total transform of `I`
by the exceptional divisor ([BM97, Proposition 3.13]). -/
def globalStrictTransform (I : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf C.chain.limitManifold :=
  IdealSheaf.saturation (I.pullback C.glueMap C.glueMap.contMDiff) C.gluedExceptionalIdeal

variable (hsnc : ∀ m, (C.excLevel m).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hbd : ∀ m, (C.seqLevel m).boundarySeq ⊤ (Fin.last _) = (C.excLevel m).idealSheaf)

include hsnc in
/-- `E` is a simple normal crossings divisor. -/
theorem isSncBoundary_gluedExceptionalIdeal : C.gluedExceptionalIdeal.IsSncBoundary :=
  ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), _, C.isSnc_gluedExceptional (exhaustion M) hsnc,
    rfl⟩

include hsnc hbd in
/-- `E` pulls back along the inclusion of a piece to the last exceptional divisor of the piece. -/
theorem gluedExceptionalIdeal_pullback_toLimitMap (m : ℕ) :
    C.gluedExceptionalIdeal.pullback (C.chain.toLimitMap m) (C.chain.toLimitMap m).contMDiff =
      (C.seqLevel m).boundarySeq ⊤ (Fin.last _) := by
  rw [hbd]
  exact C.idealSheaf_gluedExceptional_pullback_toLimitMap (exhaustion M) hsnc m

variable (I : AnalyticManifold.IdealSheaf M)
  (hdes : ∀ m, (I.restrict (relCompactOpen (exhaustion M) m)).IsDesingularizedBy (C.seqLevel m))

include hsnc hbd hdes in
/-- `Ỹ` pulls back along the inclusion of a piece to the last strict transform of the piece: the
saturation pulls back to the saturation of the pull-backs, which is the strict transform
(`IsDesingularizedBy.strictTransformSubspaceSeq_last_eq_saturation`). -/
theorem globalStrictTransform_pullback_toLimitMap (m : ℕ) :
    (C.globalStrictTransform I).pullback (C.chain.toLimitMap m) (C.chain.toLimitMap m).contMDiff =
      (C.seqLevel m).strictTransformSubspaceSeq (I.restrict (relCompactOpen (exhaustion M) m))
        (Fin.last _) := by
  rw [globalStrictTransform,
    IdealSheaf.saturation_pullback _ _ _ (C.chain.isLocalDiffeomorph_toLimit m),
    C.pullback_glueMap_pullback_toLimitMap, C.gluedExceptionalIdeal_pullback_toLimitMap hsnc hbd,
    (hdes m).strictTransformSubspaceSeq_last_eq_saturation]
  rfl

include hsnc hbd hdes in
/-- The support of `Ỹ` traces on a piece to the support of the last strict transform. -/
theorem preimage_toLimit_support_globalStrictTransform (m : ℕ) :
    ⇑(C.chain.toLimitMap m) ⁻¹' (C.globalStrictTransform I).support =
      ((C.seqLevel m).strictTransformSubspaceSeq (I.restrict (relCompactOpen (exhaustion M) m))
        (Fin.last _)).support := by
  rw [← C.globalStrictTransform_pullback_toLimitMap hsnc hbd I hdes m]
  exact (Manifold.IdealSheaf.support_pullback _ _ _).symm

include hsnc hbd hdes in
/-- **`|E| = σ⁻¹(Sing Y)`**: on every piece, the support of the last exceptional divisor is the
preimage of the singular locus. -/
theorem support_gluedExceptionalIdeal :
    C.gluedExceptionalIdeal.support = C.glueMap ⁻¹' (I.support \ I.regularLocus) := by
  ext q
  obtain ⟨m, x, rfl⟩ := C.chain.toLimit_surjective q
  have h1 : C.chain.toLimit m x ∈ C.gluedExceptionalIdeal.support ↔
      C.chain.toLimit m x ∈ (C.gluedExceptional (exhaustion M)).support :=
    Set.ext_iff.mp (C.isSnc_gluedExceptional (exhaustion M) hsnc).cosupport_idealSheaf _
  have h2 : C.chain.toLimit m x ∈ (C.gluedExceptional (exhaustion M)).support ↔
      x ∈ (C.excLevel m).support :=
    Set.ext_iff.mp (C.preimage_toLimit_support_gluedExceptional (exhaustion M) m) x
  have h3 : x ∈ (C.excLevel m).support ↔
      x ∈ ((C.seqLevel m).boundarySeq ⊤ (Fin.last _)).support := by
    rw [hbd m]
    exact (Set.ext_iff.mp (hsnc m).cosupport_idealSheaf x).symm
  have h4 : x ∈ ((C.seqLevel m).boundarySeq ⊤ (Fin.last _)).support ↔
      (C.seqLevel m).composite x ∈
        (I.restrict (relCompactOpen (exhaustion M) m)).support \
          (I.restrict (relCompactOpen (exhaustion M) m)).regularLocus :=
    Set.ext_iff.mp (hdes m).support_boundarySeq_last x
  refine (h1.trans (h2.trans (h3.trans h4))).trans ?_
  set U := relCompactOpen (exhaustion M) m
  have key : ∀ y : M.restrict U, y ∈ (I.restrict U).support \ (I.restrict U).regularLocus ↔
      M.inclusion U y ∈ I.support \ I.regularLocus := by
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(mem_cosupport_comap_iff I (M.inclusion U) (isLocalDiffeomorph_inclusion M U) y).mp
        h1, fun h => h2 ?_⟩
      exact (isRegularLocalRing_quotient_stalkIdeal_comap_iff I (M.inclusion U)
        (isLocalDiffeomorph_inclusion M U) y).mpr h
    · rintro ⟨h1, h2⟩
      refine ⟨(mem_cosupport_comap_iff I (M.inclusion U) (isLocalDiffeomorph_inclusion M U) y).mpr
        h1, fun h => h2 ?_⟩
      exact (isRegularLocalRing_quotient_stalkIdeal_comap_iff I (M.inclusion U)
        (isLocalDiffeomorph_inclusion M U) y).mp h
  exact key ((C.seqLevel m).composite x)

include hsnc hbd hdes in
/-- **`Ỹ` is smooth**: at a point of a piece, the local ring of `Ỹ` is that of the last strict
transform of the piece. -/
theorem isNonsingular_globalStrictTransform : (C.globalStrictTransform I).IsNonsingular := by
  intro q hq
  obtain ⟨m, x, rfl⟩ := C.chain.toLimit_surjective q
  have hx : x ∈ ((C.seqLevel m).strictTransformSubspaceSeq
      (I.restrict (relCompactOpen (exhaustion M) m)) (Fin.last _)).support := by
    rw [← C.preimage_toLimit_support_globalStrictTransform hsnc hbd I hdes m]
    exact hq
  have key := (isRegularLocalRing_quotient_stalkIdeal_comap_iff (C.globalStrictTransform I)
    (C.chain.toLimitMap m) (C.chain.isLocalDiffeomorph_toLimit m) x).mp
  rw [C.globalStrictTransform_pullback_toLimitMap hsnc hbd I hdes m] at key
  exact key ((hdes m).isNonsingular_strictTransform x hx)

variable (htr : ∀ m, ∀ a ∈ ((C.seqLevel m).strictTransformSubspaceSeq
    (I.restrict (relCompactOpen (exhaustion M) m)) (Fin.last _)).support,
    ∃ (k : ℕ) (φ : OpenPartialHomeomorph (C.seqLevel m).last (Fin n → 𝕜)) (σ : Fin k ↪ Fin n)
      (cidx : {j // a ∈ (C.excLevel m).hyp j} → Fin n),
      IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((C.seqLevel m).strictTransformSubspaceSeq
          (I.restrict (relCompactOpen (exhaustion M) m)) (Fin.last _)).support φ σ ∧
      (C.excLevel m).IsSncChartAt (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ a cidx ∧
      ∀ j, cidx j ∉ Set.range σ)

include hsnc hbd hdes htr in
/-- **`Ỹ` has simple normal crossings with `E`, transversally**: the transversal chart of a piece,
read on `M̃`, with the glued members through the point indexed by their descendants in the piece
(`FamilyChain.isSncChartAt_glue_limitChart`). -/
theorem isSncBoundaryTransversalTo_globalStrictTransform :
    C.gluedExceptionalIdeal.IsSncBoundaryTransversalTo (C.globalStrictTransform I) := by
  refine ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), _,
    C.isSnc_gluedExceptional (exhaustion M) hsnc, rfl, fun q hq => ?_⟩
  obtain ⟨m, x, rfl⟩ := C.chain.toLimit_surjective q
  have : Nonempty (C.chain.X m) := ⟨x⟩
  have hpre := C.preimage_toLimit_support_globalStrictTransform hsnc hbd I hdes m
  have hx : x ∈ ((C.seqLevel m).strictTransformSubspaceSeq
      (I.restrict (relCompactOpen (exhaustion M) m)) (Fin.last _)).support := by
    rw [← hpre]
    exact hq
  obtain ⟨k, φ, σ, cidx, hadapt, hsnc', hdisj⟩ := htr m x hx
  exact ⟨k, C.chain.limitChart m φ, σ,
    fun p => cidx ((C.exceptionalChain (exhaustion M)).glueIdx p),
    C.chain.isAdaptedChart_limitChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) m hpre hadapt,
    (C.exceptionalChain (exhaustion M)).isSncChartAt_glue_limitChart
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) hsnc', fun p => hdisj _⟩

variable (hmon : ∀ (m : ℕ) (x : (C.seqLevel m).last),
    ∃ (s : Finset (C.excLevel m).ι) (α : (C.excLevel m).ι → ℕ),
      (∀ j ∈ s, x ∈ (C.excLevel m).hyp j) ∧
      ((I.restrict (relCompactOpen (exhaustion M) m)).pullback (C.seqLevel m).composite
          (C.seqLevel m).composite.contMDiff).stalkIdeal x =
        ((C.seqLevel m).strictTransformSubspaceSeq (I.restrict (relCompactOpen (exhaustion M) m))
            (Fin.last _)).stalkIdeal x *
          ∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ((C.excLevel m).hyp j) x ^ α j)

include hsnc hbd hdes hmon in
/-- **`σ^*(I_Y) = I_Ỹ · I_Ẽ` on `M̃`**, pointwise: the monomial of a piece, read on `M̃` through the
bijective germ map of the inclusion, the members of the piece replaced by their born ancestors. -/
theorem isMulBoundaryMonomial_globalStrictTransform :
    IdealSheaf.IsMulBoundaryMonomial (I.pullback C.glueMap C.glueMap.contMDiff)
      (C.globalStrictTransform I) C.gluedExceptionalIdeal := by
  classical
  refine ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), _,
    C.isSnc_gluedExceptional (exhaustion M) hsnc, rfl, fun q => ?_⟩
  obtain ⟨m, x, rfl⟩ := C.chain.toLimit_surjective q
  obtain ⟨s, α, hs, heq⟩ := hmon m x
  set D := C.exceptionalChain (exhaustion M) with hD
  -- the glued members through the point: the births of the members of the piece
  set g : (C.excLevel m).ι → (C.gluedExceptional (exhaustion M)).ι := fun j => toLex (D.birth m j)
    with hg
  have hg_inj : Function.Injective g := fun j₁ j₂ h => D.eq_of_birth_eq (toLex.injective h)
  have hg_hyp : ∀ j, C.chain.toLimit m ⁻¹' (C.gluedExceptional (exhaustion M)).hyp (g j) =
      (C.excLevel m).hyp j := fun j => D.preimage_toLimit_glueHyp_birth m j
  -- the exponents
  set α' : (C.gluedExceptional (exhaustion M)).ι → ℕ := fun p =>
    if h : (ofLex p).1 ≤ m then α (D.iter h (ofLex p).2) else 0 with hα'
  have hα'g : ∀ j, α' (g j) = α j := fun j => by
    change (if h : (D.birth m j).1 ≤ m then α (D.iter h (D.birth m j).2) else 0) = α j
    rw [dite_eq_left (D.birth_le m j)]
    exact congrArg α (D.iter_birth m j)
  refine ⟨s.image g, α', fun p hp => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    exact (Set.ext_iff.mp (hg_hyp j) x).mpr (hs j hj)
  · -- the stalk identity, read in the piece through the bijective germ map
    set f := germMap ⇑(C.chain.toLimitMap m) (C.chain.toLimitMap m).contMDiff x with hf
    have hbij : Function.Bijective f :=
      Manifold.germMap_bijective_of_isLocalDiffeomorphAt _ _
        (C.chain.isLocalDiffeomorph_toLimit m x)
    have hinj : Function.Injective (Ideal.map f) := fun A B h => by
      rw [← Ideal.comap_map_of_bijective f hbij (I := A), h, Ideal.comap_map_of_bijective f hbij]
    apply hinj
    -- the left side
    have hL : Ideal.map f ((I.pullback C.glueMap C.glueMap.contMDiff).stalkIdeal
        (C.chain.toLimit m x)) =
        ((I.restrict (relCompactOpen (exhaustion M) m)).pullback (C.seqLevel m).composite
          (C.seqLevel m).composite.contMDiff).stalkIdeal x :=
      (Manifold.IdealSheaf.stalkIdeal_pullback ⇑(C.chain.toLimitMap m)
        (C.chain.toLimitMap m).contMDiff (I.pullback C.glueMap C.glueMap.contMDiff) x).symm.trans
        (congrArg (fun J => Manifold.IdealSheaf.stalkIdeal J x)
          (C.pullback_glueMap_pullback_toLimitMap I m))
    -- the strict transform
    have hY : Ideal.map f ((C.globalStrictTransform I).stalkIdeal (C.chain.toLimit m x)) =
        ((C.seqLevel m).strictTransformSubspaceSeq (I.restrict (relCompactOpen (exhaustion M) m))
          (Fin.last _)).stalkIdeal x :=
      (Manifold.IdealSheaf.stalkIdeal_pullback ⇑(C.chain.toLimitMap m)
        (C.chain.toLimitMap m).contMDiff (C.globalStrictTransform I) x).symm.trans
        (congrArg (fun J => Manifold.IdealSheaf.stalkIdeal J x)
          (C.globalStrictTransform_pullback_toLimitMap hsnc hbd I hdes m))
    -- the members
    have hV : ∀ j, Ideal.map f (vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜)
        ((C.gluedExceptional (exhaustion M)).hyp (g j)) (C.chain.toLimit m x)) =
        vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ((C.excLevel m).hyp j) x := fun j => by
      have := (Hironaka.Manifold.vanishingStalk_preimage_of_isLocalDiffeomorphAt_models
        (C.chain.toLimitMap m).contMDiff (C.chain.isLocalDiffeomorph_toLimit m x)
        ((C.gluedExceptional (exhaustion M)).hyp (g j))).symm
      exact this.trans
        (congrArg (fun S => vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) S x) (hg_hyp j))
    -- the product of the members
    have hP : Ideal.map f (∏ p ∈ s.image g, vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜)
          ((C.gluedExceptional (exhaustion M)).hyp p) (C.chain.toLimit m x) ^ α' p) =
        ∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ((C.excLevel m).hyp j) x ^ α j := by
      refine (Ideal.map_finset_prod f _ _).trans ?_
      refine (Finset.prod_image hg_inj.injOn).trans ?_
      refine Finset.prod_congr rfl fun j _ => ?_
      refine (Ideal.map_pow f _ _).trans ?_
      exact congrArg₂ (· ^ ·) (hV j) (hα'g j)
    -- the right side
    have hR : Ideal.map f ((C.globalStrictTransform I).stalkIdeal (C.chain.toLimit m x) *
          ∏ p ∈ s.image g, vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜)
            ((C.gluedExceptional (exhaustion M)).hyp p) (C.chain.toLimit m x) ^ α' p) =
        ((C.seqLevel m).strictTransformSubspaceSeq (I.restrict (relCompactOpen (exhaustion M) m))
            (Fin.last _)).stalkIdeal x *
          ∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ((C.excLevel m).hyp j) x ^ α j := by
      refine (Ideal.map_mul f _ _).trans ?_
      exact congrArg₂ (· * ·) hY hP
    exact hL.trans (heq.trans hR.symm)

end Hironaka.Manifold.CompatibleFamily

end

end
