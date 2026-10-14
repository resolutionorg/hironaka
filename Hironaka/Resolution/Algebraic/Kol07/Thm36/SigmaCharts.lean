/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Independence
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The coproduct of fibre-square charts as an admissible pair

Kollár reduces the functoriality of the resolution of an affine scheme under a smooth morphism
`h : Y → X` to the functoriality of the principalization sequence through the charts of
[Kol07, Lemma 41]: near every point of `Y` there is a fibre square in which `Y` is a closed
subscheme of a scheme smooth over the ambient of `X` [Kol07, Theorem 36, proof]. Here the charts
are fibre squares `Wᵢ = Y₀ ×_{T.X.left} Bᵢ`: `jᵢ : Wᵢ ⟶ Bᵢ` a closed immersion into an affine `Bᵢ`
smooth of relative dimension `d` over the ambient `T.X.left` of an admissible pair `(T, emb₀)` of
`Y₀`, `eᵢ : Wᵢ ⟶ Y₀`, with `IsPullback jᵢ eᵢ qᵢ emb₀`. Their coproduct `Z := ∐ Wᵢ` sits in the
coproduct ambient `∐ Bᵢ`, and this file shows that `(sigmaTriple T q d, Sigma.map j)` is an
admissible pair of `Z` (`AdmissibleEmbedding`) carrying the pullback data of `T` along
`Sigma.desc q` (`Triple.IsPullbackOf`): the hypotheses of
`BRAffine_eq_eraseEmpty_pullback_of_admissible`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback`) for `Z` over `Y₀`.

* `Sigma.map j : ∐ W ⟶ ∐ B`, the coproduct of the `jᵢ`, with the pullback squares
  `IsPullback (j i) (Sigma.ι W i) (Sigma.ι B i) (Sigma.map j)`: coproducts of schemes are disjoint
  (`sigmaι_eq_iff`), so the preimage of the `i`-th summand is the `i`-th summand and Mathlib's
  criterion `IsOpenImmersion.isPullback` applies. Hence `Sigma.map j` is a closed immersion (closed
  immersions are local on the target, `IsZariskiLocalAtTarget.iff_of_iSup_eq_top` on the summands)
  and its kernel restricts on each summand to `ker (j i)` (`ker_fst_of_isClosedImmersion`), so it
  is `I.comap (Sigma.desc q)` whenever `ker (j i) = I.comap (q i)` (`eq_of_comap_eq_of_covers`).
* `Sigma.desc` of a family inherits `LocallyOfFiniteType`, `Flat`, `Smooth` and
  `SmoothOfRelativeDimension d` (Zariski-locality on the source, `IsZariskiLocalAtSource.sigmaDesc`)
  and surjectivity from a covering family ("`X' := ∐ Uᵢ`", [Kol07, Proposition 37, proof]).
* `sigmaTriple T q d`: the pullback triple of `T` along `Sigma.desc q` (`Triple.pullback`), the
  coproduct `∐ B` over `k` through `Sigma.desc q` (`sigmaOverOfDesc`): affine, of finite type,
  separated, smooth over `k` of relative dimension `d + n` for `n` the relative dimension of
  `T.X.left` (`smoothOfRelativeDimension_comp`). Its ideal is `T.I.comap (Sigma.desc q)` and its
  boundary `T.E.comap (Sigma.desc q)`, empty when `T.E` is.
* `admissibleEmbedding_sigma`: the admissibility of `(sigmaTriple T q d, Sigma.map j)` for
  `∐ W`, given the fibre squares and the admissibility of `(T, emb₀)`.

The relative dimension `d` common to the charts is that of `h`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.SmoothCharts`, where the charts are constructed); the
charts are assembled in `Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineFunctoriality`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Hironaka
  Scheme.BlowUpSequence Hironaka.Sequence

namespace Hironaka.Resolution

/-! ### The coproduct of a family of closed immersions -/

section SigmaEmb

variable {ι : Type u} {W B : ι → Scheme.{u}} (j : ∀ i, W i ⟶ B i)

/-- Mathlib's `Sigma.map j : ∐ W ⟶ ∐ B` on points: the summand of `j i w`. -/
theorem sigmaMap_apply (i : ι) (w : W i) :
    Limits.Sigma.map j (Sigma.ι W i w) = Sigma.ι B i (j i w) := by
  calc Limits.Sigma.map j (Sigma.ι W i w) = (Sigma.ι W i ≫ Limits.Sigma.map j) w :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = (j i ≫ Sigma.ι B i) w := by rw [Limits.Sigma.ι_map]
    _ = Sigma.ι B i (j i w) := Scheme.Hom.comp_apply _ _ _

/-- The preimage of the `i`-th summand of `∐ B` under the coproduct map is the `i`-th summand of
`∐ W`: coproducts of schemes are disjoint (`sigmaι_eq_iff`). -/
theorem preimage_opensRange_sigmaMap (i : ι) :
    (Limits.Sigma.map j) ⁻¹ᵁ (Sigma.ι B i).opensRange = (Sigma.ι W i).opensRange := by
  ext z
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := Scheme.Hom.mem_opensRange.mp hz
    obtain ⟨⟨i', w⟩, rfl⟩ := (sigmaMk W).surjective z
    rw [sigmaMk_mk] at hb ⊢
    rw [sigmaMap_apply] at hb
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp ((sigmaι_eq_iff B i i' _ _).mp hb)
    exact Scheme.Hom.mem_opensRange.mpr ⟨w, rfl⟩
  · intro hz
    obtain ⟨w, hw⟩ := Scheme.Hom.mem_opensRange.mp hz
    refine Scheme.Hom.mem_opensRange.mpr ⟨j i w, ?_⟩
    rw [← hw, sigmaMap_apply]

/-- The `i`-th summand square of the coproduct map is a pullback (Mathlib's criterion
`IsOpenImmersion.isPullback` on the two summand inclusions). -/
theorem isPullback_sigmaMap (i : ι) :
    IsPullback (j i) (Sigma.ι W i) (Sigma.ι B i) (Limits.Sigma.map j) :=
  IsOpenImmersion.isPullback (j i) (Sigma.ι W i) (Sigma.ι B i) (Limits.Sigma.map j)
    (Limits.Sigma.ι_map j i) (preimage_opensRange_sigmaMap j i)

/-- A coproduct of pullback squares over a common morphism `p` is a pullback square (schemes are
extensive): checked on the open cover of `∐ B` by its summands (`Scheme.isPullback_of_openCover`),
where the canonical pullback of the summand is `W i` (`isPullback_sigmaMap`). -/
theorem isPullback_sigmaMap_sigmaDesc {Y X : Scheme.{u}} (e : ∀ i, W i ⟶ Y) (f : ∀ i, B i ⟶ X)
    (p : Y ⟶ X) (h : ∀ i, IsPullback (j i) (e i) (f i) p) :
    IsPullback (Limits.Sigma.map j) (Sigma.desc e) (Sigma.desc f) p := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (sigmaOpenCover B) fun i => ?_
  have hi := (isPullback_sigmaMap j i).flip
  refine (h i).of_iso hi.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change j i ≫ 𝟙 (B i) = hi.isoPullback.hom ≫ pullback.snd (Limits.Sigma.map j) (Sigma.ι B i)
    rw [Category.comp_id, hi.isoPullback_hom_snd]
  · change e i ≫ 𝟙 Y =
      hi.isoPullback.hom ≫ pullback.fst (Limits.Sigma.map j) (Sigma.ι B i) ≫ Sigma.desc e
    rw [Category.comp_id, ← Category.assoc, hi.isoPullback_hom_fst]
    exact (Sigma.ι_comp_desc e i).symm
  · change f i ≫ 𝟙 X = 𝟙 (B i) ≫ Sigma.ι B i ≫ Sigma.desc f
    rw [Category.comp_id, Category.id_comp]
    exact (Sigma.ι_comp_desc f i).symm
  · simp

/-- The summands cover the coproduct. -/
theorem iSup_opensRange_sigmaι : ⨆ i, (Sigma.ι B i).opensRange = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨i, b⟩, rfl⟩ := (sigmaMk B).surjective z
  rw [sigmaMk_mk]
  exact Opens.mem_iSup.mpr ⟨i, Scheme.Hom.mem_opensRange.mpr ⟨b, rfl⟩⟩

/-- A property local at the target holds for the coproduct of morphisms that have it: on the
summand `Sigma.ι B i` the coproduct restricts to `j i` up to the canonical isomorphism
(`isPullback_morphismRestrict`, `IsPullback.isoIsPullback`). -/
theorem sigmaMap_of_isZariskiLocalAtTarget (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] (hj : ∀ i, P (j i)) : P (Limits.Sigma.map j) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_opensRange_sigmaι (B := B))]
  intro i
  have hpb : IsPullback (j i ≫ (Sigma.ι B i).isoOpensRange.hom) (Sigma.ι W i)
      (Sigma.ι B i).opensRange.ι (Limits.Sigma.map j) :=
    IsOpenImmersion.isPullback _ _ _ _
      (by rw [Limits.Sigma.ι_map, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι])
      (by rw [Scheme.Opens.opensRange_ι, preimage_opensRange_sigmaMap])
  have hres := isPullback_morphismRestrict (Limits.Sigma.map j) (Sigma.ι B i).opensRange
  have hc := IsPullback.isoIsPullback_hom_fst _ _ hpb hres
  rw [← MorphismProperty.cancel_left_of_respectsIso P (IsPullback.isoIsPullback _ _ hpb hres).hom,
    hc]
  exact (MorphismProperty.cancel_right_of_respectsIso P (j i)
    (Sigma.ι B i).isoOpensRange.hom).mpr (hj i)

/-- A coproduct of closed immersions is a closed immersion: local on the target along the
summands, where it is `j i` up to the pullback isomorphism. -/
theorem isClosedImmersion_sigmaMap [∀ i, IsClosedImmersion (j i)] :
    IsClosedImmersion (Limits.Sigma.map j) :=
  sigmaMap_of_isZariskiLocalAtTarget j @IsClosedImmersion fun _ => inferInstance

/-- The kernel of the coproduct of closed immersions restricts on the `i`-th summand to the kernel
of `j i` (`ker_fst_of_isClosedImmersion` on the summand square). -/
theorem ker_sigmaMap_comap_ι [∀ i, IsClosedImmersion (j i)] (i : ι) :
    (Limits.Sigma.map j).ker.comap (Sigma.ι B i) = (j i).ker := by
  have := isClosedImmersion_sigmaMap j
  have hpb := isPullback_sigmaMap j i
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (Limits.Sigma.map j) (Sigma.ι B i),
    ← hpb.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- If every `ker (j i)` is the inverse image of `I` along `q i`, the kernel of the coproduct of the
`j i` is the inverse image of `I` along `Sigma.desc q` (ideal sheaves agreeing on the covering
summands agree). -/
theorem ker_sigmaMap [∀ i, IsClosedImmersion (j i)] {A : Scheme.{u}} (q : ∀ i, B i ⟶ A)
    (I : A.IdealSheafData) (hker : ∀ i, (j i).ker = I.comap (q i)) :
    (Limits.Sigma.map j).ker = I.comap (Sigma.desc q) := by
  refine Scheme.IdealSheafData.eq_of_comap_eq_of_covers (Sigma.ι B) (fun x => ?_) fun i => ?_
  · obtain ⟨⟨i, b⟩, rfl⟩ := (sigmaMk B).surjective x
    exact ⟨i, b, (sigmaMk_mk B i b).symm⟩
  · rw [ker_sigmaMap_comap_ι, hker, ← Scheme.IdealSheafData.comap_comp, Sigma.ι_comp_desc]

/-- Commuting squares on the summands give a commuting square of the coproducts. -/
theorem sigmaMap_comp_desc {A Y₀ : Scheme.{u}} (q : ∀ i, B i ⟶ A) (e : ∀ i, W i ⟶ Y₀)
    (emb₀ : Y₀ ⟶ A) (hsq : ∀ i, j i ≫ q i = e i ≫ emb₀) :
    Limits.Sigma.map j ≫ Sigma.desc q = Sigma.desc e ≫ emb₀ :=
  Sigma.hom_ext _ _ fun i => by
    rw [Limits.Sigma.ι_map_assoc, Sigma.ι_comp_desc, hsq, Sigma.ι_comp_desc_assoc]

end SigmaEmb

/-- The kernel of the closed immersion of a fibre square over a closed immersion `emb₀` is the
inverse image of `ker emb₀`: `j` is `pullback.fst` up to the pullback isomorphism. -/
theorem ker_eq_comap_of_isPullback {A Y₀ W B : Scheme.{u}} (emb₀ : Y₀ ⟶ A)
    [IsClosedImmersion emb₀] (j : W ⟶ B) (e : W ⟶ Y₀) (q : B ⟶ A)
    (sq : IsPullback j e q emb₀) : j.ker = emb₀.ker.comap q := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion emb₀ q, ← sq.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-! ### Properties of `Sigma.desc` -/

section SigmaDesc

variable {ι : Type u} {Y₀ : Scheme.{u}} {W : ι → Scheme.{u}} (e : ∀ i, W i ⟶ Y₀)

theorem locallyOfFiniteType_sigmaDesc [∀ i, LocallyOfFiniteType (e i)] :
    LocallyOfFiniteType (Sigma.desc e) := by
  have hloc : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

theorem flat_sigmaDesc [∀ i, Flat (e i)] : Flat (Sigma.desc e) := by
  have hloc : IsZariskiLocalAtSource @Flat :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

theorem smoothOfRelativeDimension_sigmaDesc (d : ℕ) [∀ i, SmoothOfRelativeDimension d (e i)] :
    SmoothOfRelativeDimension d (Sigma.desc e) := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} d) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

theorem smooth_sigmaDesc [∀ i, Smooth (e i)] : Smooth (Sigma.desc e) := by
  have hloc : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

/-- The coproduct map of a covering family is surjective ("`X' := ∐ Uᵢ` … there is a smooth
surjection `g : X' → X`", [Kol07, Proposition 37, proof]). -/
theorem surjective_sigmaDesc (hcov : ∀ y, ∃ i w, e i w = y) :
    Function.Surjective (Sigma.desc e) := by
  have h : ⋃ i, Set.range (e i) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨i, w, hw⟩ := hcov y
    exact Set.mem_iUnion.mpr ⟨i, w, hw⟩
  exact (Surjective.sigmaDesc_of_union_range_eq_univ h).surj

end SigmaDesc

/-! ### The pull-back triple on a coproduct of charts -/

section SigmaTriple

variable {k : Type u} [Field k] {ι : Type u}

/-- `∐ B` over `k` through the coproduct map `Sigma.desc q`. -/
noncomputable abbrev sigmaOverOfDesc (T : Triple k) {B : ι → Scheme.{u}} (q : ∀ i, B i ⟶ T.X.left) :
    (∐ B).Over (Spec (CommRingCat.of k)) :=
  ⟨Sigma.desc q ≫ (T.X.left ↘ Spec (CommRingCat.of k))⟩

/-- The coproduct is smooth over `k` of relative dimension `d + n` (condition (1) of [Kol07,
Notation 64] for the coproduct triple). -/
theorem exists_smoothOfRelativeDimension_sigmaDesc_comp (T : Triple k) {B : ι → Scheme.{u}}
    (q : ∀ i, B i ⟶ T.X.left) (d : ℕ) [∀ i, SmoothOfRelativeDimension d (q i)] :
    ∃ n : ℕ, SmoothOfRelativeDimension n (Sigma.desc q ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have := smoothOfRelativeDimension_sigmaDesc q d
  exact ⟨d + n, smoothOfRelativeDimension_comp d n _ _⟩

theorem isAffineHom_sigmaDesc_comp [Finite ι] (T : Triple k) {B : ι → Scheme.{u}}
    [∀ i, IsAffine (B i)] (q : ∀ i, B i ⟶ T.X.left) :
    IsAffineHom (Sigma.desc q ≫ (T.X.left ↘ Spec (CommRingCat.of k))) :=
  isAffineHom_of_isAffine _

theorem quasiCompact_sigmaDesc_comp [Finite ι] (T : Triple k) {B : ι → Scheme.{u}}
    [∀ i, IsAffine (B i)] (q : ∀ i, B i ⟶ T.X.left) :
    QuasiCompact (Sigma.desc q ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := by
  have := isAffineHom_sigmaDesc_comp T q
  infer_instance

theorem isSeparated_sigmaDesc_comp [Finite ι] (T : Triple k) {B : ι → Scheme.{u}}
    [∀ i, IsAffine (B i)] (q : ∀ i, B i ⟶ T.X.left) :
    IsSeparated (Sigma.desc q ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := by
  have := isAffineHom_sigmaDesc_comp T q
  exact IsSeparated.of_isAffineHom _

/-- `Sigma.desc q` is over `k` for the structure `sigmaOverOfDesc`. -/
theorem homIsOver_sigmaDesc (T : Triple k) {B : ι → Scheme.{u}} (q : ∀ i, B i ⟶ T.X.left) :
    @HomIsOver Scheme.{u} _ (∐ B) T.X.left (Sigma.desc q) (Spec (CommRingCat.of k))
      (sigmaOverOfDesc T q) (AlgScheme.over T.X) :=
  @HomIsOver.mk Scheme.{u} _ (∐ B) T.X.left (Sigma.desc q) (Spec (CommRingCat.of k))
    (sigmaOverOfDesc T q) (AlgScheme.over T.X) rfl

/-- The pullback triple of `T` on the coproduct `∐ B` of affine schemes smooth of relative dimension
`d` over `T.X.left` (`Triple.pullback` along `Sigma.desc q`): the triple to which the functoriality
of the principalization sequence [Kol07, 34.1] is applied on the coproduct of the charts. -/
noncomputable def sigmaTriple [CharZero k] [Finite ι] (T : Triple k) {B : ι → Scheme.{u}}
    [∀ i, IsAffine (B i)] (q : ∀ i, B i ⟶ T.X.left) (d : ℕ)
    [∀ i, SmoothOfRelativeDimension d (q i)] :
    Triple k :=
  @Triple.pullback k _ _ T (∐ B) (sigmaOverOfDesc T q) (quasiCompact_sigmaDesc_comp T q)
    (isSeparated_sigmaDesc_comp T q)
    (exists_smoothOfRelativeDimension_sigmaDesc_comp T q d) (Sigma.desc q)
    (@SmoothOfRelativeDimension.smooth d _ _ (Sigma.desc q)
      (smoothOfRelativeDimension_sigmaDesc q d))

variable [CharZero k] [Finite ι] (T : Triple k) {B : ι → Scheme.{u}} [∀ i, IsAffine (B i)]
  (q : ∀ i, B i ⟶ T.X.left) (d : ℕ) [∀ i, SmoothOfRelativeDimension d (q i)]

theorem sigmaTriple_X : (sigmaTriple T q d).X.left = ∐ B := rfl

theorem sigmaTriple_I : (sigmaTriple T q d).I = T.I.comap (Sigma.desc q) := rfl

theorem sigmaTriple_E : (sigmaTriple T q d).E = T.E.comap (Sigma.desc q) := rfl

theorem isEmpty_sigmaTriple_E_ι (h : IsEmpty T.E.ι) : IsEmpty (sigmaTriple T q d).E.ι := h

/-- The coproduct triple carries the pull-back data of `T` along `Sigma.desc q`. -/
theorem sigmaTriple_isPullbackOf : (sigmaTriple T q d).IsPullbackOf T (Sigma.desc q) :=
  @Triple.isPullbackOf_pullback k _ _ T (∐ B) (sigmaOverOfDesc T q)
    (quasiCompact_sigmaDesc_comp T q) (isSeparated_sigmaDesc_comp T q)
    (exists_smoothOfRelativeDimension_sigmaDesc_comp T q d)
    (Sigma.desc q) (homIsOver_sigmaDesc T q)
    (@SmoothOfRelativeDimension.smooth d _ _ (Sigma.desc q)
      (smoothOfRelativeDimension_sigmaDesc q d))

theorem isAffine_sigmaTriple_X : IsAffine (sigmaTriple T q d).X.left :=
  inferInstanceAs (IsAffine (∐ B))

/-- The coproduct of fibre-square charts over an admissible pair `(T, emb₀)` of `Y₀` is an
admissible pair of `∐ W` over the pullback triple on `∐ B`: the closed immersion `Sigma.map j`,
over `k` through the squares, into the affine `∐ B` with empty boundary, with kernel the inverse
image of `T.I = ker emb₀` along `Sigma.desc q`. -/
theorem admissibleEmbedding_sigma {Y₀ : Scheme.{u}} [Y₀.Over (Spec (CommRingCat.of k))]
    (emb₀ : Y₀ ⟶ T.X.left) (hadm : AdmissibleEmbedding k Y₀ T emb₀)
    {W : ι → Scheme.{u}} (j : ∀ i, W i ⟶ B i) [∀ i, IsClosedImmersion (j i)]
    (e : ∀ i, W i ⟶ Y₀) (sq : ∀ i, IsPullback (j i) (e i) (q i) emb₀)
    [(∐ W).Over (Spec (CommRingCat.of k))] [HomIsOver (Sigma.desc e) (Spec (CommRingCat.of k))] :
    AdmissibleEmbedding k (∐ W) (sigmaTriple T q d) (Limits.Sigma.map j) := by
  have hcl : IsClosedImmersion emb₀ := hadm.1
  have hover : HomIsOver emb₀ (Spec (CommRingCat.of k)) := hadm.2.1
  refine ⟨isClosedImmersion_sigmaMap j, ?_, isAffine_sigmaTriple_X T q d,
    isEmpty_sigmaTriple_E_ι T q d hadm.2.2.2.1, ?_⟩
  · constructor
    change Limits.Sigma.map j ≫ (Sigma.desc q ≫ (T.X.left ↘ Spec (CommRingCat.of k))) =
      (∐ W) ↘ Spec (CommRingCat.of k)
    rw [← Category.assoc, sigmaMap_comp_desc j q e emb₀ (fun i => (sq i).w), Category.assoc,
      HomIsOver.comp_over (f := emb₀) (S := Spec (CommRingCat.of k)),
      HomIsOver.comp_over (f := Sigma.desc e) (S := Spec (CommRingCat.of k))]
  · rw [sigmaTriple_I]
    exact ker_sigmaMap j q T.I fun i => by
      rw [ker_eq_comap_of_isPullback emb₀ (j i) (e i) (q i) (sq i), hadm.2.2.2.2]

end SigmaTriple

end Hironaka.Resolution
