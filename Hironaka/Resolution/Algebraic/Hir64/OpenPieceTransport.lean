/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransport
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUp.Transform.WeakTransform
import Hironaka.Scheme.BlowUpSequence.ColonComapOpenImmersion
import Hironaka.Scheme.BlowUpSequence.OpenTransport
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.DictionaryOrder

/-!
# Transport of the data of a blow-up sequence along an open immersion, without dimension

Hironaka's Main Theorems II and II(N) and their Corollaries 1 and 3 [Hir64, pp. 142–146, 176] are
stated for a non-singular algebraic scheme, whose irreducible components may have different
dimensions, while the order reduction of the library runs on a scheme smooth of a single relative
dimension. The general case is assembled from the components: a succession on a component, an open
and closed subscheme `U ⊆ X`, is extended to `X` by the unit ideal on the complement
(`Hironaka/Resolution/Algebraic/Hir64/ExtendOpen.lean`), and the clauses are read off the pieces.
The transport lemmas of `Hironaka/Scheme/BlowUpSequence/OpenTransport.lean` do this for the weak
transforms when the ambient scheme is smooth of one relative dimension; this module proves the
transports needed with no smoothness hypothesis at all, for an open immersion `u : Y ⟶ X` and the
stage lifts `u_i` of the pull-back `S.pullback u`:

* the weak transform commutes with the pull-back along `u` when the centre lies inside the range
  of `u` (`weakTransform_comap_blowUpMap_of_subset`: the exceptional orders on the two sides agree,
  since the exceptional ideal is the unit ideal off the centre and divisibility by a power of an
  invertible ideal sheaf is containment, checked on stalks; the colon commutes with the inverse
  image along an open immersion of a locally Noetherian scheme), and also when the pulled-back
  centre is empty (`weakTransform_comap_blowUpMap_of_comap_eq_top`: both sides are the total
  transform); `weakTransformSeq_pullback_mk` iterates this along a sequence each of whose centres
  is inside or outside the range of the stage lift;
* the reduced transform, a vanishing ideal, commutes with every open pull-back
  (`reducedTransform_comap_blowUpMap`, from `vanishingIdeal_comap_of_isOpenImmersion`), hence so
  do Hironaka's boundaries `E_i` (`boundarySeq_pullback_mk`);
* over an open `W` of `X` missing the image of every centre, each stage map restricts to an
  isomorphism (`isIso_stageMap_restrict`), and the weak transforms and boundaries are the inverse
  images of the initial data along the stage maps (`weakTransformSeq_comap_ι_preimage`,
  `boundarySeq_comap_ι_preimage`); over such an open the data is unchanged, the observation Hironaka
  makes in the proof of Corollary 1 [Hir64, p. 144];
* Hironaka's Definition 2 [Hir64, Ch. 0, §5, Definition 2] and the regularity of a point ascend
  along an open immersion (`isSncBoundaryWith_of_comap_of_isOpenImmersion`,
  `exists_isRegularSystemOfParameters_apply_of_comap`,
  `isRegularAt_apply_iff_of_isOpenImmersion`), the converse of the descent lemmas of
  `Hironaka/Resolution/Algebraic/Hir64/ComponentDeletion.lean`.
-/

public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry Scheme Scheme.IdealSheafData
  Scheme.BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry Hironaka.Resolution AlgebraicGeometry.Remark33

variable {X Y : Scheme.{u}}

/-! ### Inverse images along an open immersion -/

/-- The inverse image of a vanishing ideal sheaf along an open immersion is the vanishing ideal
sheaf of the preimage: both are radical with that support. -/
theorem vanishingIdeal_comap_of_isOpenImmersion (u : Y ⟶ X) [IsOpenImmersion u] (Z : Closeds X) :
    (vanishingIdeal Z).comap u = vanishingIdeal (Z.preimage u.continuous) := by
  have : IsReduced ((vanishingIdeal Z).comap u).subscheme :=
    haveI := isReduced_subscheme_vanishingIdeal Z
    isReduced_subscheme_comap_of_isOpenImmersion u _
  rw [← radical_eq_self_of_isReduced_subscheme ((vanishingIdeal Z).comap u),
    ← vanishingIdeal_support, support_comap]
  congr 1

/-- The radical commutes with the inverse image along an open immersion. -/
theorem radical_comap_of_isOpenImmersion (u : Y ⟶ X) [IsOpenImmersion u] (I : X.IdealSheafData) :
    I.radical.comap u = (I.comap u).radical := by
  rw [← vanishingIdeal_support, ← vanishingIdeal_support, vanishingIdeal_comap_of_isOpenImmersion,
    support_comap]

/-- The morphism of blow-ups over an open immersion is an open immersion (the square is
cartesian). -/
theorem isOpenImmersion_blowUpMap (u : Y ⟶ X) [IsOpenImmersion u] (D : X.IdealSheafData) :
    IsOpenImmersion (Scheme.Hom.blowUpMap u D) :=
  isOpenImmersion_pullbackStageHom (cons X D (nil _)) u ⟨1, Nat.one_lt_succ_succ 0⟩

/-! ### The weak transform along an open pull-back -/

/-- The inverse image of the exceptional ideal along the morphism of blow-ups over `u` is the
exceptional ideal of the pulled-back centre. -/
theorem exceptionalDivisor_comap_blowUpMap (u : Y ⟶ X) (D : X.IdealSheafData) :
    D.exceptionalDivisor.comap (Scheme.Hom.blowUpMap u D) = (D.comap u).exceptionalDivisor := by
  rw [Scheme.IdealSheafData.exceptionalDivisor, Scheme.IdealSheafData.exceptionalDivisor,
    ← comap_comp, blowUpMap_π, comap_comp]

/-- The total transform of `J` pulled back along the morphism of blow-ups over `u` is the total
transform of `u⁻¹ J`. -/
theorem comap_blowUpπ_comap_blowUpMap (u : Y ⟶ X) (D J : X.IdealSheafData) :
    (J.comap D.blowUpπ).comap (Scheme.Hom.blowUpMap u D) =
      (J.comap u).comap (D.comap u).blowUpπ := by
  rw [← comap_comp, blowUpMap_π, comap_comp]

/-- If the pulled-back centre is empty, the weak transform along the blow-up pulls back to the
weak transform of the pulled-back ideal: on both sides the exceptional ideal is the unit ideal, so
both are the total transform. -/
theorem weakTransform_comap_blowUpMap_of_comap_eq_top [IsLocallyNoetherian X] (u : Y ⟶ X)
    [IsOpenImmersion u] (D J : X.IdealSheafData) (hD : D.comap u = ⊤) :
    (J.weakTransform D).comap (Scheme.Hom.blowUpMap u D) =
      (J.comap u).weakTransform (D.comap u) := by
  have := isOpenImmersion_blowUpMap u D
  have hLN : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
  have hsupp : (D.comap u).support = ⊥ := (support_eq_bot_iff _).mpr hD
  have hE' : (D.comap u).exceptionalDivisor = ⊤ := by
    rw [← support_eq_bot_iff, Scheme.IdealSheafData.exceptionalDivisor, support_comap, hsupp]
    ext p
    exact ⟨fun h => h, fun h => h.elim⟩
  have hE : D.exceptionalDivisor.comap (Scheme.Hom.blowUpMap u D) = ⊤ := by
    rw [exceptionalDivisor_comap_blowUpMap, hE']
  have htop : ∀ (B : Scheme.{u}) (c : ℕ), (⊤ : B.IdealSheafData) ^ c = ⊤ := fun B c => by
    rw [← one_eq_top, one_pow]
  change (((J.comap D.blowUpπ).colon (D.exceptionalDivisor ^ _)).comap _) =
    ((J.comap u).comap (D.comap u).blowUpπ).colon ((D.comap u).exceptionalDivisor ^ _)
  rw [comap_colon_of_isOpenImmersion_of_isLocallyNoetherian, comap_pow, hE, hE', htop, htop,
    colon_top, colon_top, comap_blowUpπ_comap_blowUpMap]

/-- If the centre lies inside the range of `u`, the exceptional orders of `J` along the blow-up of
`D` and of `u⁻¹ J` along the blow-up of `u⁻¹ D` agree: divisibility by a power of the invertible
exceptional ideal is containment, which holds off the centre (where the exceptional ideal is the
unit ideal) and over the range of `u` exactly when it holds on the pull-back. -/
theorem exceptionalOrderAlong_comap_of_subset [IsLocallyNoetherian X] (u : Y ⟶ X)
    [IsOpenImmersion u] (D J : X.IdealSheafData) (hD : (D.support : Set X) ⊆ Set.range u) :
    exceptionalOrderAlong (D.comap u).blowUpπ (D.comap u).exceptionalDivisor (J.comap u) =
      exceptionalOrderAlong D.blowUpπ D.exceptionalDivisor J := by
  have hφ := isOpenImmersion_blowUpMap u D
  set φ := Scheme.Hom.blowUpMap u D with hφdef
  have hrange : Set.range φ = D.blowUpπ ⁻¹' Set.range u :=
    range_fst_of_isPullback (isPullback_blowUpMap u D)
  have hEinv : D.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π D
  unfold exceptionalOrderAlong
  congr 1
  ext c
  constructor
  · -- from the pull-back to `X`: containment on stalks
    intro h
    have hle : (J.comap u).comap (D.comap u).blowUpπ ≤ (D.comap u).exceptionalDivisor ^ c :=
      le_pow_of_pow_dvd h
    refine pow_dvd_of_le_pow_of_isInvertible hEinv (le_of_stalkIdeal_le fun p => ?_)
    by_cases hp : p ∈ Set.range φ
    · obtain ⟨q, rfl⟩ := hp
      have h1 := stalkIdeal_mono hle q
      rw [← comap_blowUpπ_comap_blowUpMap, ← exceptionalDivisor_comap_blowUpMap, ← comap_pow,
        stalkIdeal_comap (J.comap D.blowUpπ) φ q,
        stalkIdeal_comap (D.exceptionalDivisor ^ c) φ q] at h1
      have h2 := Ideal.map_le_iff_le_comap.mp h1
      rwa [Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso (φ.stalkMap q))]
        at h2
    · have hp' : D.blowUpπ p ∉ D.support := fun hmem => hp (by rw [hrange]; exact hD hmem)
      have hE : D.exceptionalDivisor.stalkIdeal p = ⊤ :=
        stalkIdeal_eq_top_of_notMem_support _ (by
          rw [Scheme.IdealSheafData.exceptionalDivisor, mem_support_comap_iff_apply]
          exact hp')
      rw [stalkIdeal_pow, hE, Ideal.top_pow]
      exact le_top
  · -- from `X` to the pull-back: pull back the quotient
    rintro ⟨K, hK⟩
    refine ⟨K.comap φ, ?_⟩
    rw [← comap_blowUpπ_comap_blowUpMap, hK, comap_mul, comap_pow,
      exceptionalDivisor_comap_blowUpMap]

/-- If the centre lies inside the range of `u`, the weak transform along the blow-up pulls back to
the weak transform of the pulled-back ideal along the pulled-back centre: the exceptional orders
agree (`exceptionalOrderAlong_comap_of_subset`) and the colon commutes with the inverse image along
the open immersion of blow-ups. -/
theorem weakTransform_comap_blowUpMap_of_subset [IsLocallyNoetherian X] (u : Y ⟶ X)
    [IsOpenImmersion u] (D J : X.IdealSheafData) (hD : (D.support : Set X) ⊆ Set.range u) :
    (J.weakTransform D).comap (Scheme.Hom.blowUpMap u D) =
      (J.comap u).weakTransform (D.comap u) := by
  have := isOpenImmersion_blowUpMap u D
  have hLN : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
  change (((J.comap D.blowUpπ).colon (D.exceptionalDivisor ^ _)).comap _) =
    ((J.comap u).comap (D.comap u).blowUpπ).colon ((D.comap u).exceptionalDivisor ^ _)
  rw [comap_colon_of_isOpenImmersion_of_isLocallyNoetherian, comap_pow,
    exceptionalDivisor_comap_blowUpMap, comap_blowUpπ_comap_blowUpMap,
    exceptionalOrderAlong_comap_of_subset u D J hD]

/-- The reduced transform `red(π⁻¹(E) ∪ π⁻¹(D))` [Hir64, Main Theorem II (iii)] commutes with the
pull-back along an open immersion: it is the vanishing ideal sheaf of a closed set, and the
morphism of blow-ups over `u` is an open immersion under which the closed set pulls back to the
corresponding closed set of the blow-up of `u⁻¹ D`. -/
theorem reducedTransform_comap_blowUpMap (u : Y ⟶ X) [IsOpenImmersion u] (E D : X.IdealSheafData) :
    (E.reducedTransform D).comap (Scheme.Hom.blowUpMap u D) =
      (E.comap u).reducedTransform (D.comap u) := by
  have := isOpenImmersion_blowUpMap u D
  rw [Scheme.IdealSheafData.reducedTransform, Scheme.IdealSheafData.reducedTransform,
    vanishingIdeal_comap_of_isOpenImmersion]
  congr 1
  ext p
  have hp : D.blowUpπ (Scheme.Hom.blowUpMap u D p) = u ((D.comap u).blowUpπ p) := by
    rw [← Scheme.Hom.comp_apply, blowUpMap_π, Scheme.Hom.comp_apply]
  change (D.blowUpπ (Scheme.Hom.blowUpMap u D p) ∈ E.support ∨
      D.blowUpπ (Scheme.Hom.blowUpMap u D p) ∈ D.support) ↔
    ((D.comap u).blowUpπ p ∈ (E.comap u).support ∨ (D.comap u).blowUpπ p ∈ (D.comap u).support)
  rw [hp, mem_support_comap_iff_apply, mem_support_comap_iff_apply]

/-! ### Along a pulled-back sequence -/

/-- Hironaka's boundaries of `S.pullback u` are the inverse images of the boundaries of `S` under
the stage lifts (`reducedTransform_comap_blowUpMap` stage by stage). -/
theorem boundarySeq_pullback_mk :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) {Y : Scheme.{u}} (u : Y ⟶ X) [IsOpenImmersion u]
      (E : X.IdealSheafData) (j : ℕ) (hj : j < S.length + 1),
      (S.pullback u).boundarySeq (E.comap u) (S.pullbackStageIdx u ⟨j, hj⟩) =
        (S.boundarySeq E ⟨j, hj⟩).comap (S.pullbackStageHom u ⟨j, hj⟩)
  | _, nil _, _, _, _, _, 0, _ => rfl
  | _, nil _, _, _, _, _, _ + 1, hj => (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | _, cons _ _ _, _, _, _, _, 0, _ => rfl
  | _, cons X D rest, Y, u, _, E, j + 1, hj => by
    have := isOpenImmersion_blowUpMap u D
    have ih := boundarySeq_pullback_mk rest (Scheme.Hom.blowUpMap u D) (E.reducedTransform D) j
      (Nat.lt_of_succ_lt_succ hj)
    rw [reducedTransform_comap_blowUpMap] at ih
    exact ih

/-- The weak transforms of `S.pullback u` are the inverse images of the weak transforms of `S`
under the stage lifts, provided every centre of `S` lies inside the range of its stage lift or
pulls back to the empty centre (`weakTransform_comap_blowUpMap_of_subset`,
`weakTransform_comap_blowUpMap_of_comap_eq_top` stage by stage). -/
theorem weakTransformSeq_pullback_mk :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (S : BlowUpSequence X) {Y : Scheme.{u}} (u : Y ⟶ X)
      [IsOpenImmersion u] (J : X.IdealSheafData),
      (∀ i : Fin S.length,
        ((S.center i).support : Set (S.stage i.castSucc)) ⊆
            Set.range (S.pullbackStageHom u i.castSucc) ∨
          (S.center i).comap (S.pullbackStageHom u i.castSucc) = ⊤) →
      ∀ (j : ℕ) (hj : j < S.length + 1),
        (S.pullback u).weakTransformSeq (J.comap u) (S.pullbackStageIdx u ⟨j, hj⟩) =
          (S.weakTransformSeq J ⟨j, hj⟩).comap (S.pullbackStageHom u ⟨j, hj⟩)
  | _, _, nil _, _, _, _, _, _, 0, _ => rfl
  | _, _, nil _, _, _, _, _, _, _ + 1, hj => (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | _, _, cons _ _ _, _, _, _, _, _, 0, _ => rfl
  | _, _, cons X D rest, Y, u, _, J, hc, j + 1, hj => by
    have := isOpenImmersion_blowUpMap u D
    have hLN : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
    have hw : (J.weakTransform D).comap (Scheme.Hom.blowUpMap u D) =
        (J.comap u).weakTransform (D.comap u) := by
      rcases hc ⟨0, Nat.succ_pos _⟩ with h | h
      · exact weakTransform_comap_blowUpMap_of_subset u D J h
      · exact weakTransform_comap_blowUpMap_of_comap_eq_top u D J h
    have ih := weakTransformSeq_pullback_mk rest (Scheme.Hom.blowUpMap u D) (J.weakTransform D)
      (fun i => hc ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) j (Nat.lt_of_succ_lt_succ hj)
    rw [hw] at ih
    exact ih

/-- `weakTransformSeq_pullback_mk` when every centre lies inside the range of its stage lift. -/
theorem weakTransformSeq_pullback_of_centersInRange [IsLocallyNoetherian X] (S : BlowUpSequence X)
    (u : Y ⟶ X) [IsOpenImmersion u] (hC : S.CentersInRange u) (J : X.IdealSheafData)
    (i : Fin (S.length + 1)) :
    (S.pullback u).weakTransformSeq (J.comap u) (S.pullbackStageIdx u i) =
      (S.weakTransformSeq J i).comap (S.pullbackStageHom u i) := by
  obtain ⟨j, hj⟩ := i
  exact weakTransformSeq_pullback_mk S u J (fun i => Or.inl (hC i)) j hj

/-- `boundarySeq_pullback_mk` in the `Fin` form. -/
theorem boundarySeq_pullback (S : BlowUpSequence X) (u : Y ⟶ X) [IsOpenImmersion u]
    (E : X.IdealSheafData) (i : Fin (S.length + 1)) :
    (S.pullback u).boundarySeq (E.comap u) (S.pullbackStageIdx u i) =
      (S.boundarySeq E i).comap (S.pullbackStageHom u i) := by
  obtain ⟨j, hj⟩ := i
  exact boundarySeq_pullback_mk S u E j hj

/-! ### Over an open missing the centres -/

/-- The blow-up map is an isomorphism over an open `W` on which the centre is the unit ideal
(`blowUp.isIso_π_restrict_compl_support` for a smaller open): the lift of `W.ι` inverts
`π ∣_ W`. -/
theorem isIso_blowUpπ_restrict_of_comap_eq_top (D : X.IdealSheafData) (W : X.Opens)
    (hW : D.comap W.ι = ⊤) : IsIso (D.blowUpπ ∣_ W) := by
  have hadm : (D.comap W.ι).IsInvertible := by
    rw [hW]
    exact isInvertible_top
  set s := blowUp.lift D W.ι hadm with hs_def
  have hrange : Set.range s ⊆ Set.range (D.blowUpπ ⁻¹ᵁ W).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change D.blowUpπ (s w) ∈ W
    rw [← Scheme.Hom.comp_apply, blowUp.lift_π]
    have hw : W.ι w ∈ (W : Set X) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
    exact hw
  set s' := IsOpenImmersion.lift (D.blowUpπ ⁻¹ᵁ W).ι s hrange with hs'_def
  have hs' : s' ≫ (D.blowUpπ ⁻¹ᵁ W).ι = s := IsOpenImmersion.lift_fac _ _ _
  have hadm' : (D.comap ((D.blowUpπ ⁻¹ᵁ W).ι ≫ D.blowUpπ)).IsInvertible := by
    rw [comap_comp]
    exact (blowUp.isInvertible_comap_π D).comap_of_isOpenImmersion _
  refine ⟨⟨s', ?_, ?_⟩⟩
  · rw [← cancel_mono (D.blowUpπ ⁻¹ᵁ W).ι, Category.assoc, hs', Category.id_comp]
    exact blowUp.hom_ext D _ hadm' _ _
      (by rw [Category.assoc, blowUp.lift_π, morphismRestrict_ι]) rfl
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hs',
      blowUp.lift_π, Category.id_comp]

/-- Over an open `W` missing the image of every centre, every stage map of the succession is an
isomorphism: each blow-up map is one over the preimage of `W`, and the restriction of a composite
is the composite of the restrictions (`morphismRestrict_comp`). -/
theorem isIso_stageMap_restrict :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (W : X.Opens),
      (∀ (i : Fin S.length) (y : S.stage i.castSucc), y ∈ (S.center i).support →
        S.stageMap i.castSucc y ∉ W) →
      ∀ i : Fin (S.length + 1), IsIso (S.stageMap i ∣_ W)
  | X, nil _, W, _, ⟨0, _⟩ => by
    change IsIso (𝟙 X ∣_ W)
    rw [morphismRestrict_id]
    exact IsIso.id _
  | _, nil _, _, _, ⟨_ + 1, hj⟩ => (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | X, cons _ _ _, W, _, ⟨0, _⟩ => by
    change IsIso (𝟙 X ∣_ W)
    rw [morphismRestrict_id]
    exact IsIso.id _
  | _, cons X D rest, W, hC, ⟨j + 1, hj⟩ => by
    have hD : D.comap W.ι = ⊤ :=
      comap_ι_eq_top_of_disjoint D W fun x hxW hxD => hC ⟨0, Nat.succ_pos _⟩ x hxD hxW
    have h1 : IsIso (D.blowUpπ ∣_ W) := isIso_blowUpπ_restrict_of_comap_eq_top D W hD
    have h2 : IsIso (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ∣_ (D.blowUpπ ⁻¹ᵁ W)) :=
      isIso_stageMap_restrict rest (D.blowUpπ ⁻¹ᵁ W)
        (fun i y hy => hC ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ y hy) ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    change IsIso ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ) ∣_ W)
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1

/-- The inclusion of the preimage of `W` followed by the blow-up map is an open immersion when the
centre is the unit ideal on `W`: it is the isomorphism `π ∣_ W` followed by the inclusion of
`W`. -/
theorem isOpenImmersion_ι_comp_blowUpπ_of_comap_eq_top (D : X.IdealSheafData) (W : X.Opens)
    (hW : D.comap W.ι = ⊤) : IsOpenImmersion ((D.blowUpπ ⁻¹ᵁ W).ι ≫ D.blowUpπ) := by
  have := isIso_blowUpπ_restrict_of_comap_eq_top D W hW
  rw [← morphismRestrict_ι]
  infer_instance

/-- Over an open `W` on which the centre is the unit ideal, the weak transform is the inverse image
of the ideal: the exceptional ideal is the unit ideal there, so the colon by its powers changes
nothing. -/
theorem weakTransform_comap_ι_preimage [IsLocallyNoetherian X] (D J : X.IdealSheafData)
    (W : X.Opens) (hW : D.comap W.ι = ⊤) :
    (J.weakTransform D).comap (D.blowUpπ ⁻¹ᵁ W).ι = J.comap ((D.blowUpπ ⁻¹ᵁ W).ι ≫ D.blowUpπ) := by
  have hLN : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
  have hE : D.exceptionalDivisor.comap (D.blowUpπ ⁻¹ᵁ W).ι = ⊤ := by
    rw [Scheme.IdealSheafData.exceptionalDivisor, ← comap_comp, ← morphismRestrict_ι, comap_comp,
      hW, comap_top]
  have htop : ∀ (B : Scheme.{u}) (c : ℕ), (⊤ : B.IdealSheafData) ^ c = ⊤ := fun B c => by
    rw [← one_eq_top, one_pow]
  change ((J.comap D.blowUpπ).colon (D.exceptionalDivisor ^ _)).comap _ = _
  rw [comap_colon_of_isOpenImmersion_of_isLocallyNoetherian, comap_pow, hE, htop, colon_top,
    comap_comp]

/-- Over an open `W` on which the centre is the unit ideal, the reduced transform of a reduced
`E` is the inverse image of `E`: the preimage of the centre is empty there, and the vanishing ideal
of the support of the reduced inverse image is that inverse image. -/
theorem reducedTransform_comap_ι_preimage (E D : X.IdealSheafData) [IsReduced E.subscheme]
    (W : X.Opens) (hW : D.comap W.ι = ⊤) :
    (E.reducedTransform D).comap (D.blowUpπ ⁻¹ᵁ W).ι =
      E.comap ((D.blowUpπ ⁻¹ᵁ W).ι ≫ D.blowUpπ) := by
  have hoi := isOpenImmersion_ι_comp_blowUpπ_of_comap_eq_top D W hW
  have hred : IsReduced (E.comap ((D.blowUpπ ⁻¹ᵁ W).ι ≫ D.blowUpπ)).subscheme :=
    isReduced_subscheme_comap_of_isOpenImmersion _ E
  have hDsupp : (D.comap W.ι).support = ⊥ := (support_eq_bot_iff _).mpr hW
  rw [Scheme.IdealSheafData.reducedTransform, vanishingIdeal_comap_of_isOpenImmersion,
    ← radical_eq_self_of_isReduced_subscheme (E.comap ((D.blowUpπ ⁻¹ᵁ W).ι ≫ D.blowUpπ)),
    ← vanishingIdeal_support, support_comap]
  congr 1
  ext p
  change (D.blowUpπ ((D.blowUpπ ⁻¹ᵁ W).ι p) ∈ E.support ∨
      D.blowUpπ ((D.blowUpπ ⁻¹ᵁ W).ι p) ∈ D.support) ↔
    ((D.blowUpπ ⁻¹ᵁ W).ι ≫ D.blowUpπ) p ∈ E.support
  rw [Scheme.Hom.comp_apply]
  refine ⟨fun h => h.resolve_right fun hD => ?_, Or.inl⟩
  have hp : D.blowUpπ ((D.blowUpπ ⁻¹ᵁ W).ι p) ∈ W := by
    have : (D.blowUpπ ⁻¹ᵁ W).ι p ∈ Set.range (D.blowUpπ ⁻¹ᵁ W).ι := ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι] at this
    exact this
  obtain ⟨w, hw⟩ : D.blowUpπ ((D.blowUpπ ⁻¹ᵁ W).ι p) ∈ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact hp
  have : w ∈ (D.comap W.ι).support := by
    rw [mem_support_comap_iff_apply, hw]
    exact hD
  rw [hDsupp] at this
  exact this

/-- Over an open `W` missing the image of every centre, the weak transforms along the succession
are the inverse images of the ideal along the stage maps (`weakTransform_comap_ι_preimage` stage by
stage). -/
theorem weakTransformSeq_comap_ι_preimage :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (S : BlowUpSequence X) (J : X.IdealSheafData)
      (W : X.Opens),
      (∀ (i : Fin S.length) (y : S.stage i.castSucc), y ∈ (S.center i).support →
        S.stageMap i.castSucc y ∉ W) →
      ∀ i : Fin (S.length + 1),
        (S.weakTransformSeq J i).comap (S.stageMap i ⁻¹ᵁ W).ι =
          J.comap ((S.stageMap i ⁻¹ᵁ W).ι ≫ S.stageMap i)
  | X, _, nil _, J, W, _, ⟨0, _⟩ => by
    change J.comap (𝟙 X ⁻¹ᵁ W).ι = J.comap ((𝟙 X ⁻¹ᵁ W).ι ≫ 𝟙 X)
    rw [Category.comp_id]
  | _, _, nil _, _, _, _, ⟨_ + 1, hj⟩ => (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | X, _, cons _ _ _, J, W, _, ⟨0, _⟩ => by
    change J.comap (𝟙 X ⁻¹ᵁ W).ι = J.comap ((𝟙 X ⁻¹ᵁ W).ι ≫ 𝟙 X)
    rw [Category.comp_id]
  | _, _, cons X D rest, J, W, hC, ⟨j + 1, hj⟩ => by
    have hLN : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
    have hD : D.comap W.ι = ⊤ :=
      comap_ι_eq_top_of_disjoint D W fun x hxW hxD => hC ⟨0, Nat.succ_pos _⟩ x hxD hxW
    have ih := weakTransformSeq_comap_ι_preimage rest (J.weakTransform D) (D.blowUpπ ⁻¹ᵁ W)
      (fun i y hy => hC ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ y hy) ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    change (rest.weakTransformSeq (J.weakTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩).comap
        ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ) ⁻¹ᵁ W).ι =
      J.comap (((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ) ⁻¹ᵁ W).ι ≫
        (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ))
    rw [Scheme.Hom.comp_preimage, ih, ← morphismRestrict_ι, ← Category.assoc, comap_comp,
      weakTransform_comap_ι_preimage D J W hD, ← comap_comp, ← Category.assoc, morphismRestrict_ι]

/-- Over an open `W` missing the image of every centre, Hironaka's boundaries along the succession
are the inverse images of the reduced `E₀` along the stage maps (`reducedTransform_comap_ι_preimage`
stage by stage). -/
theorem boundarySeq_comap_ι_preimage :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E : X.IdealSheafData) [IsReduced E.subscheme]
      (W : X.Opens),
      (∀ (i : Fin S.length) (y : S.stage i.castSucc), y ∈ (S.center i).support →
        S.stageMap i.castSucc y ∉ W) →
      ∀ i : Fin (S.length + 1),
        (S.boundarySeq E i).comap (S.stageMap i ⁻¹ᵁ W).ι =
          E.comap ((S.stageMap i ⁻¹ᵁ W).ι ≫ S.stageMap i)
  | X, nil _, E, _, W, _, ⟨0, _⟩ => by
    change E.comap (𝟙 X ⁻¹ᵁ W).ι = E.comap ((𝟙 X ⁻¹ᵁ W).ι ≫ 𝟙 X)
    rw [Category.comp_id]
  | _, nil _, _, _, _, _, ⟨_ + 1, hj⟩ => (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | X, cons _ _ _, E, _, W, _, ⟨0, _⟩ => by
    change E.comap (𝟙 X ⁻¹ᵁ W).ι = E.comap ((𝟙 X ⁻¹ᵁ W).ι ≫ 𝟙 X)
    rw [Category.comp_id]
  | _, cons X D rest, E, _, W, hC, ⟨j + 1, hj⟩ => by
    have hD : D.comap W.ι = ⊤ :=
      comap_ι_eq_top_of_disjoint D W fun x hxW hxD => hC ⟨0, Nat.succ_pos _⟩ x hxD hxW
    have hred : IsReduced (E.reducedTransform D).subscheme := isReduced_subscheme_vanishingIdeal _
    have ih := boundarySeq_comap_ι_preimage rest (E.reducedTransform D) (D.blowUpπ ⁻¹ᵁ W)
      (fun i y hy => hC ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ y hy) ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    change (rest.boundarySeq (E.reducedTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩).comap
        ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ) ⁻¹ᵁ W).ι =
      E.comap (((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ) ⁻¹ᵁ W).ι ≫
        (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ))
    rw [Scheme.Hom.comp_preimage, ih, ← morphismRestrict_ι, ← Category.assoc, comap_comp,
      reducedTransform_comap_ι_preimage E D W hD, ← comap_comp, ← Category.assoc,
      morphismRestrict_ι]

/-- Over an open `W` missing the image of every centre, the inclusion of the preimage of `W`
followed by the stage map is an open immersion (the isomorphism `stageMap ∣_ W` followed by the
inclusion of `W`). -/
theorem isOpenImmersion_ι_preimage_comp_stageMap (S : BlowUpSequence X) (W : X.Opens)
    (hC : ∀ (i : Fin S.length) (y : S.stage i.castSucc), y ∈ (S.center i).support →
      S.stageMap i.castSucc y ∉ W) (i : Fin (S.length + 1)) :
    IsOpenImmersion ((S.stageMap i ⁻¹ᵁ W).ι ≫ S.stageMap i) := by
  have := isIso_stageMap_restrict S W hC i
  rw [← morphismRestrict_ι]
  infer_instance

/-! ### Definition 2 and regularity ascend along an open immersion -/

/-- Hironaka's Definition 2 at a point `u y` in the range of an open immersion, from Definition 2
at `y` for the inverse images: the coordinates at `y` are carried to `u y` by the inverse of the
stalk isomorphism, the minimal primes and the generators with them (the converse of
`IsSncBoundaryWith.comap_of_isOpenImmersion`). -/
theorem exists_isRegularSystemOfParameters_apply_of_comap (u : Y ⟶ X) [IsOpenImmersion u]
    (E D : X.IdealSheafData) (y : Y)
    (h : ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y),
      IsLocalRing.IsRegularSystemOfParameters z ∧
      (∀ P ∈ ((E.comap u).stalkIdeal y).minimalPrimes, ∃ i, P = Ideal.span {z i}) ∧
      ∃ s : Finset (Fin n), (D.comap u).stalkIdeal y = Ideal.span (z '' ↑s)) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk (u y)),
      IsLocalRing.IsRegularSystemOfParameters z ∧
      (∀ P ∈ (E.stalkIdeal (u y)).minimalPrimes, ∃ i, P = Ideal.span {z i}) ∧
      ∃ s : Finset (Fin n), D.stalkIdeal (u y) = Ideal.span (z '' ↑s) := by
  obtain ⟨n, z, hz, hmin, s, hs⟩ := h
  set e : X.presheaf.stalk (u y) ≃+* Y.presheaf.stalk y := stalkEquivOfIsOpenImmersion u y
    with he_def
  set e' : Y.presheaf.stalk y →+* X.presheaf.stalk (u y) :=
    (e.symm : Y.presheaf.stalk y →+* X.presheaf.stalk (u y)) with he'_def
  have hE : E.stalkIdeal (u y) = ((E.comap u).stalkIdeal y).map e' :=
    stalkIdeal_eq_map_symm_stalkIdeal_comap u E y
  have hD : D.stalkIdeal (u y) = ((D.comap u).stalkIdeal y).map e' :=
    stalkIdeal_eq_map_symm_stalkIdeal_comap u D y
  refine ⟨n, fun i => e.symm (z i), isRegularSystemOfParameters_comp_ringEquiv e.symm hz, ?_, s,
    ?_⟩
  · intro P hP
    rw [hE] at hP
    have hP' : P.comap e' ∈ ((E.comap u).stalkIdeal y).minimalPrimes := by
      have h1 := Ideal.comap_minimalPrimes_eq_of_surjective (f := e') e.symm.surjective
        (((E.comap u).stalkIdeal y).map e')
      rw [Ideal.comap_map_of_bijective e' e.symm.bijective] at h1
      rw [h1]
      exact ⟨P, hP, rfl⟩
    obtain ⟨i, hi⟩ := hmin _ hP'
    refine ⟨i, ?_⟩
    rw [← Ideal.map_comap_of_surjective e' e.symm.surjective P, hi, Ideal.map_span,
      Set.image_singleton]
    rfl
  · rw [hD, hs, Ideal.map_span, Set.image_image]
    rfl

/-- Definition 2 ascends along an open immersion whose range contains the support of `D`: `E` has
only normal crossings with `D` if `u⁻¹ E` has only normal crossings with `u⁻¹ D`. -/
theorem isSncBoundaryWith_of_comap_of_isOpenImmersion (u : Y ⟶ X) [IsOpenImmersion u]
    {E D : X.IdealSheafData} (hD : (D.support : Set X) ⊆ Set.range u)
    (h : IsSncBoundaryWith (E.comap u) (D.comap u)) : IsSncBoundaryWith E D := by
  intro x hx
  obtain ⟨y, rfl⟩ := hD hx
  exact exists_isRegularSystemOfParameters_apply_of_comap u E D y
    (h y ((mem_support_comap_iff_apply D u y).mpr hx))

/-- A point in the range of an open immersion is regular iff its preimage is (the stalks are
isomorphic). -/
theorem isRegularAt_apply_iff_of_isOpenImmersion (u : Y ⟶ X) [IsOpenImmersion u] (y : Y) :
    X.IsRegularAt (u y) ↔ Y.IsRegularAt y :=
  ⟨fun h =>
    have : IsRegularLocalRing (X.presheaf.stalk (u y)) := h
    IsRegularLocalRing.of_ringEquiv (stalkEquivOfIsOpenImmersion u y),
  fun h =>
    have : IsRegularLocalRing (Y.presheaf.stalk y) := h
    IsRegularLocalRing.of_ringEquiv (stalkEquivOfIsOpenImmersion u y).symm⟩

/-- Regularity at a point of a closed subscheme `V(Z)` in the range of the open immersion
`V(Z.comap u) → V(Z)` (a point over the range of `u`) is regularity at its preimage. -/
theorem isRegularAt_subscheme_of_comap (u : Y ⟶ X) [IsOpenImmersion u] (Z : X.IdealSheafData)
    (p : (Z.comap u).subscheme)
    (h : (Z.comap u).subscheme.IsRegularAt p) :
    Z.subscheme.IsRegularAt (subschemeMap (Z.comap u) Z u (le_map_comap Z u) p) := by
  have := isOpenImmersion_subschemeMap_comap u Z
  exact (isRegularAt_apply_iff_of_isOpenImmersion _ p).mpr h

end Hironaka.Sequence
