/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSmooth
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.ExceptionalDivisor
import Hironaka.Scheme.Smooth.SubschemeStalk
import Hironaka.Scheme.Snc.ParameterSubset
import Hironaka.Scheme.Snc.TotalTransformChartComputation
import Hironaka.Scheme.Snc.TotalTransformOnCentre
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Restriction of the induced divisors to a hypersurface

Kollár's going up and down [Kol07, Corollary 85] pushes blow-up sequences between a smooth
hypersurface `H` and its ambient `X` when every center lies in the birational transform of `H`
(a hypersurface of maximal contact, [Kol07, Definition 78]); the proof observes that "`E|_H` is
again a divisor with simple normal crossings" and that the restriction to `H` of the divisors
induced on `X` is the family induced on `H` by `E|_H`: `E_i|_{H_i} = (E|_H)_i`. With the
embeddings `H_i ↪ X_i` of `Hironaka/Scheme/BlowUpSequence/Restrict.lean` (closed immersions with
kernels the strict transforms of `H`) and Kollár's `H + E` as `DivisorFamily.append`, this module
proves that identity (`totalTransformSeq_comap_pullback`) from three pieces:

* the point lemma `hasSncWith_append_of_le`: a center `Z ⊆ H` having simple normal crossings with
  `E` has simple normal crossings with `E + H` when `E + H` has simple normal crossings (an
  exchange of coordinates in `𝔪/𝔪²`);
* the stagewise statement: the families `E_i + H_i` keep simple normal crossings along the
  sequence (`AlgebraicGeometry.totalTransform_isSnc` at each stage, up to the reindexing between
  `(E + H)_1` and `E_1 + H_1`), and the centers have simple normal crossings with them;
* the one-step computation `strictTransform_comap_blowUpMap_of_hasSncWith`: strict transforms
  restrict to strict transforms, `(π_*^{-1} K)|_{H'} = (π_H)_*^{-1}(K|_H)`, the chart computation
  of [Hau14, Proposition 5.3] read on the chart shape of the total transform: modulo the
  coordinate of `H'`, the exceptional coordinate is still a member of a regular system of
  parameters, so the two saturations agree (`map_iSup_colon_pow_eq_of_shape`).

The statement carries `[Smooth f]` and `IsSmooth S f` without a relative dimension, so the stages
are shown smooth over `k` by Zariski-locality from the equidimensional statement
(`smooth_blowUpπ_comp_of_smooth'`, `IsSmooth.smooth_stageMap'`). The last section gives the
push-forward of a nonzero ideal sheaf along a closed immersion, used for the intermediate triples
of the chain of hypersurfaces in [Kol07, 108].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme BlowUpSequence
  IsLocalRing Ideal

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Reindexing a divisor family -/

/-- Simple normal crossing data at a point transport along a reindexing of the family with
matching components. -/
theorem isSncAt_of_equiv {E₁ E₂ : DivisorFamily X} (σ : E₁.ι ≃ E₂.ι)
    (hσ : ∀ i, E₂.component (σ i) = E₁.component i) {x : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk x} (h : E₁.IsSncAt x z) : E₂.IsSncAt x z := by
  obtain ⟨hz, c, hc, hcE⟩ := h
  have hcomp : ∀ i₂ : E₂.ι, E₂.component i₂ = E₁.component (σ.symm i₂) := fun i₂ => by
    rw [← hσ (σ.symm i₂), Equiv.apply_symm_apply]
  have hmem : ∀ i₂ : E₂.ι, x ∈ (E₂.component i₂).support →
      x ∈ (E₁.component (σ.symm i₂)).support := fun i₂ hi => by rwa [hcomp] at hi
  refine ⟨hz, fun i₂ => c ⟨σ.symm i₂.1, hmem i₂.1 i₂.2⟩, fun i₂ j₂ hij => ?_, fun i₂ => ?_⟩
  · exact Subtype.ext (σ.symm.injective (congrArg Subtype.val (hc hij)))
  · exact (congrArg (fun Z : X.IdealSheafData => Z.stalkIdeal x) (hcomp i₂.1)).trans
      (hcE ⟨σ.symm i₂.1, hmem i₂.1 i₂.2⟩)

/-- `IsSnc` is invariant under reindexing with matching components. -/
theorem isSnc_of_equiv {E₁ E₂ : DivisorFamily X} (σ : E₁.ι ≃ E₂.ι)
    (hσ : ∀ i, E₂.component (σ i) = E₁.component i) (h : E₁.IsSnc) : E₂.IsSnc := by
  refine ⟨fun i₂ => ?_, fun x => ?_⟩
  · rw [show E₂.component i₂ = E₁.component (σ.symm i₂) by
      rw [← hσ (σ.symm i₂), Equiv.apply_symm_apply]]
    exact h.1 _
  · obtain ⟨n, z, hz⟩ := h.2 x
    exact ⟨n, z, isSncAt_of_equiv σ hσ hz⟩

/-- `HasSncWith` is invariant under reindexing with matching components. -/
theorem hasSncWith_of_equiv {E₁ E₂ : DivisorFamily X} (σ : E₁.ι ≃ E₂.ι)
    (hσ : ∀ i, E₂.component (σ i) = E₁.component i) {Z : X.IdealSheafData}
    (h : E₁.HasSncWith Z) : E₂.HasSncWith Z := by
  intro x hx
  obtain ⟨n, z, hz, s, hs⟩ := h x hx
  exact ⟨n, z, isSncAt_of_equiv σ hσ hz, s, hs⟩

/-! ### Stages smooth over `k`, without a relative dimension -/

section StageSmooth

variable {k : Type u} [Field k]

/-- The blow-up of a scheme smooth over `k` along a center smooth over `k` is smooth over `k`
([Kol07, Notation 19] without the equidimensional convention). Smoothness is Zariski-local on the
source; over an affine open `V` of `X` on which `f` has a relative dimension
(`exists_affineOpen_smoothOfRelativeDimension`) the blow-up restricts to the blow-up of `V`
(`blowUp.restrictIso`), where `smoothOfRelativeDimension_blowUpπ_comp_of_smooth` applies. -/
theorem smooth_blowUpπ_comp_of_smooth' [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : X.IdealSheafData) [Smooth (D.subschemeι ≫ f)] : Smooth
        (D.blowUpπ ≫ f) := by
  classical
  have hloc : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  choose V hxV m hm using fun x : X => exists_affineOpen_smoothOfRelativeDimension f x
  let 𝒰 : D.blowUp.OpenCover := Scheme.Cover.mkOfCovers X
    (fun x => (D.comap (V x).1.ι).blowUp)
    (fun x => Hom.blowUpMap (V x).1.ι D)
    (fun b => ⟨D.blowUpπ b, exists_restrictHom_eq D (V
        (D.blowUpπ b)).1 b
      (hxV (D.blowUpπ b))⟩)
  refine IsZariskiLocalAtSource.of_openCover 𝒰 fun x => ?_
  change Smooth (Hom.blowUpMap (V x).1.ι D ≫ D.blowUpπ ≫ f)
  rw [blowUpMap_π_assoc]
  have := hm x
  have : Smooth ((D.comap (V x).1.ι).subschemeι ≫ (V x).1.ι ≫ f) :=
    smooth_subschemeι_comap_comp D (V x).1.ι f
  exact smooth_blowUpπ_comp_of_smooth ((V x).1.ι ≫ f) (m x) (D.comap (V x).1.ι)

/-- Every stage of a sequence smooth over `k` is smooth over `k` [Kol07, Notation 19], without a
relative dimension. -/
theorem IsSmooth.smooth_stageMap' [PerfectField k] {S : BlowUpSequence X}
    {f : X ⟶ Spec (.of k)} [Smooth f] (h : S.IsSmooth f) (i : Fin (S.length + 1)) :
    Smooth (S.stageMap i ≫ f) := by
  induction S with
  | nil Y =>
    change Smooth (𝟙 Y ≫ f)
    rw [Category.id_comp]
    infer_instance
  | cons Y D rest ih =>
    obtain ⟨hD, ht⟩ := (isSmooth_cons_iff f D rest).1 h
    have hπ : Smooth (D.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth' f D
    rcases i with ⟨_ | j, hi⟩
    · change Smooth (𝟙 Y ≫ f)
      rw [Category.id_comp]
      infer_instance
    · change Smooth ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ)
        ≫ f)
      rw [Category.assoc]
      exact ih ht ⟨j, Nat.lt_of_succ_lt_succ hi⟩

end StageSmooth

/-! ### The stalk map of a closed immersion -/

/-- The stalk map of a closed immersion is surjective with kernel the stalk of its kernel ideal
sheaf (the factorisation through the image, `ker_stalkMap_subschemeι`). -/
theorem ker_stalkMap_of_isClosedImmersion (g : Y ⟶ X) [IsClosedImmersion g] (y : Y) :
    RingHom.ker (g.stalkMap y).hom = g.ker.stalkIdeal (g y) := by
  suffices h : ∀ φ : Y ⟶ X, φ = g.toImage ≫ g.imageι →
      RingHom.ker (φ.stalkMap y).hom = g.ker.stalkIdeal (φ y) from
    h g (Scheme.Hom.toImage_imageι g).symm
  rintro φ rfl
  have hinj : Function.Injective (g.toImage.stalkMap y).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  rw [Scheme.Hom.stalkMap_comp]
  change RingHom.ker ((g.toImage.stalkMap y).hom.comp (g.imageι.stalkMap (g.toImage y)).hom) =
    g.ker.stalkIdeal (g.imageι (g.toImage y))
  rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj,
    ← RingHom.ker_eq_comap_bot]
  exact Scheme.IdealSheafData.ker_stalkMap_subschemeι g.ker (g.toImage y)

/-! ### The algebra: saturation modulo a coordinate -/

section ColonQuotient

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {S : Type*} [CommRing S]
  {φ : R →+* S} {m : ℕ} {z : Fin m → R}
  (hz : span (Set.range z) = maximalIdeal R) (hm : (m : WithBot ℕ∞) = ringKrullDim R)
  (hφ : Function.Surjective φ) {h : Fin m} (hker : RingHom.ker φ = span {z h})

include hz hm hφ hker

/-- The algebra behind [Hau14, Proposition 5.3]: in a regular local ring `R` with regular system of
parameters `z`, for the quotient `φ : R → S = R/(z_h)` and an ideal `T` of one of the four chart
shapes `(z_a z_j)`, `(z_a)`, `(z_j)`, `(1)` with `a, j ≠ h`, saturating by `(z_j)` commutes with
passing to the quotient: the saturation is computed once in `R` and once in `S`, whose regular
system of parameters is the image of the coordinates other than `z_h`
(`span_range_comp_compl_eq_maximalIdeal`). Not in the sources in this form. -/
theorem map_iSup_colon_pow_eq_of_shape {T : Ideal R} {j : Fin m} (hjh : j ≠ h)
    (hT : (∃ a, a ≠ j ∧ a ≠ h ∧ (T = span {z a * z j} ∨ T = span {z a})) ∨
      T = span {z j} ∨ T = ⊤) :
    (⨆ k : ℕ, T.colon (↑(span {z j} ^ k) : Set R)).map φ =
      ⨆ k : ℕ, (T.map φ).colon (↑((span {z j}).map φ ^ k) : Set S) := by
  classical
  have hker' : RingHom.ker φ = span (z '' ↑({h} : Finset (Fin m))) := by
    rw [Finset.coe_singleton, Set.image_singleton]; exact hker
  have hS : IsRegularLocalRing S :=
    isRegularLocalRing_of_ker_eq_span_image hz.symm hm hφ hker'
  set emb := (({h} : Finset (Fin m))ᶜ.orderEmbOfFin rfl) with hemb
  set w : Fin ({h} : Finset (Fin m))ᶜ.card → S := φ ∘ z ∘ emb with hw_def
  have hw : span (Set.range w) = maximalIdeal S :=
    span_range_comp_compl_eq_maximalIdeal hz.symm hφ hker'
  have hwdim : ((({h} : Finset (Fin m))ᶜ.card : ℕ) : WithBot ℕ∞) = ringKrullDim S := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    exact natCast_sub_card_eq_ringKrullDim_of_ker hz.symm hm hφ hker'
  have hidx : ∀ i, i ≠ h → ∃ l, emb l = i := by
    intro i hi
    have hmem : i ∈ Set.range emb := by
      rw [hemb, Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr (Finset.mem_compl.mpr (by simpa using hi))
    exact hmem
  obtain ⟨lj, hlj⟩ := hidx j hjh
  have hwj : w lj = φ (z j) := by simp [hw_def, hlj]
  rw [Ideal.map_span, Set.image_singleton]
  rcases hT with ⟨a, haj, hah, hTa | hTa⟩ | hTj | hTtop
  · obtain ⟨la, hla⟩ := hidx a hah
    have hwa : w la = φ (z a) := by simp [hw_def, hla]
    have hne : la ≠ lj := fun e => haj (by rw [← hla, ← hlj, e])
    subst hTa
    rw [iSup_colon_pow_span_singleton_mul hz hm haj]
    simp only [Ideal.map_span, Set.image_singleton, map_mul]
    rw [← hwa, ← hwj, iSup_colon_pow_span_singleton_mul hw hwdim hne]
  · obtain ⟨la, hla⟩ := hidx a hah
    have hwa : w la = φ (z a) := by simp [hw_def, hla]
    have hne : la ≠ lj := fun e => haj (by rw [← hla, ← hlj, e])
    subst hTa
    rw [iSup_colon_pow_span_singleton_of_ne hz hm haj]
    simp only [Ideal.map_span, Set.image_singleton]
    rw [← hwa, ← hwj, iSup_colon_pow_span_singleton_of_ne hw hwdim hne]
  · subst hTj
    rw [iSup_colon_pow_span_singleton_self, Ideal.map_top, Ideal.map_span,
      Set.image_singleton, iSup_colon_pow_span_singleton_self]
  · subst hTtop
    rw [iSup_colon_pow_top, Ideal.map_top, iSup_colon_pow_top]

end ColonQuotient

/-! ### Strict transforms restrict to strict transforms -/

section OneStep

variable {k : Type u} [Field k] [PerfectField k]

/-- For a closed immersion `g : Y ⟶ X` with image `H = V(g.ker)`, a center `Z = V(D) ⊆ H` having
simple normal crossings with `E + H`, and a component `K` of `E`, the strict transform of `K`
restricted to `B_Z H` (along the closed immersion `blowUpMap g D`) is the strict transform of
`K|_H`: `(π_*^{-1} K)|_{H'} = (π_H)_*^{-1}(K|_H)` ([Kol07, Corollary 85, proof];
[Hau14, Proposition 5.3]). Stalkwise (`ext_stalkIdeal`) at `y'` over `x' = blowUpMap g D y'`: the
stalk map is surjective with kernel the stalk of `H' = V(π_*^{-1} H)`; off the exceptional divisor
both sides are the total transforms; on it, the chart shape for the family `E + H`
(`exists_totalTransformData_of_mem_support`) writes `F = (z'_j)`, the total transform of `K` as
`(z'_a z'_j)`, `(z'_a)`, `(z'_j)` or `(1)`, and that of `H` as `(z'_{a_H} z'_j)` with `a_H ∉ {j, a}`
(`H ⊇ Z` and `x' ∈ H'`), so `H'` has stalk `(z'_{a_H})` and both saturations are computed by
`map_iSup_colon_pow_eq_of_shape`. -/
theorem strictTransform_comap_blowUpMap_of_hasSncWith (f : X ⟶ Spec (.of k)) [Smooth f]
    (g : Y ⟶ X) [IsClosedImmersion g]
    {E : DivisorFamily X} {D : X.IdealSheafData} (hb : (E.append g.ker).HasSncWith D)
    (hle : g.ker ≤ D) (i : E.ι) :
    ((E.component i).comap g).strictTransform (D.comap g) =
      ((E.component i).strictTransform D).comap (Scheme.Hom.blowUpMap g D) := by
  classical
  have hci : IsClosedImmersion (Scheme.Hom.blowUpMap g D) :=
    isClosedImmersion_blowUpMap_of_isClosedImmersion g D
  have hkerg' : (Scheme.Hom.blowUpMap g D).ker = g.ker.strictTransform D :=
    ker_blowUpMap_of_isClosedImmersion g D
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro y'
  set x' := Scheme.Hom.blowUpMap g D y' with hx'
  set φ := ((Scheme.Hom.blowUpMap g D).stalkMap y').hom with hφ
  have hφs : Function.Surjective φ := (Scheme.Hom.blowUpMap g D).stalkMap_surjective y'
  have hφker : RingHom.ker φ = (g.ker.strictTransform D).stalkIdeal x' := by
    rw [hφ, ker_stalkMap_of_isClosedImmersion, hkerg']
  have hT : ((E.component i).comap g).comap (D.comap g).blowUpπ =
      ((E.component i).comap D.blowUpπ).comap (Scheme.Hom.blowUpMap g D) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      blowUpMap_π]
  have hF : (D.comap g).comap (D.comap g).blowUpπ =
      D.exceptionalDivisor.comap (Scheme.Hom.blowUpMap g D) := exceptionalDivisor_comap g D
  have hL : (((E.component i).strictTransform D).comap (Scheme.Hom.blowUpMap g D)).stalkIdeal y' =
      (⨆ n : ℕ, (((E.component i).comap D.blowUpπ).stalkIdeal x').colon
        (↑(D.exceptionalDivisor.stalkIdeal x' ^ n) : Set _)).map φ := by
    rw [Scheme.IdealSheafData.stalkIdeal_comap]
    exact congrArg (Ideal.map φ)
      (stalkIdeal_strictTransformAlong_eq_iSup D (E.component i) x')
  have hR : (((E.component i).comap g).strictTransform (D.comap g)).stalkIdeal y' =
      ⨆ n : ℕ, ((((E.component i).comap D.blowUpπ).stalkIdeal x').map φ).colon
        (↑((D.exceptionalDivisor.stalkIdeal x').map φ ^ n) : Set _) := by
    refine (stalkIdeal_strictTransformAlong_eq_iSup (D.comap g)
      ((E.component i).comap g) y').trans ?_
    refine iSup_congr fun n => ?_
    rw [show ((E.component i).comap g).comap (IdealSheafData.blowUpπ (D.comap g)) =
      ((E.component i).comap D.blowUpπ).comap (Scheme.Hom.blowUpMap g D) from hT,
      show (D.comap g).comap (IdealSheafData.blowUpπ (D.comap g)) =
      D.exceptionalDivisor.comap (Scheme.Hom.blowUpMap g D) from hF,
      Scheme.IdealSheafData.stalkIdeal_comap ((E.component i).comap D.blowUpπ)
        (Scheme.Hom.blowUpMap g D) y',
      Scheme.IdealSheafData.stalkIdeal_comap D.exceptionalDivisor (Scheme.Hom.blowUpMap g D) y']
  rw [hL, hR]
  by_cases hx'F : x' ∈ D.exceptionalDivisor.support
  · obtain ⟨hreg, m, z, ⟨hzspan, hzdim⟩, j, a, hF', hinj, hshape⟩ :=
      (exists_totalTransformData_of_mem_support f (E.append g.ker).component D
        (hasSncWith_data _ _ hb) x' hx'F).1
    set iH : (E.append g.ker).ι := toLex (Sum.inr PUnit.unit) with hiH
    have hF'' : D.exceptionalDivisor.stalkIdeal x' = span {z j} := hF'
    have hshapeH : (a iH ≠ j ∧
        ((g.ker.comap D.blowUpπ).stalkIdeal x' = span {z (a iH) * z j} ∨
          (g.ker.comap D.blowUpπ).stalkIdeal x' = span {z (a iH)})) ∨
        (g.ker.comap D.blowUpπ).stalkIdeal x' = span {z j} ∨
        (g.ker.comap D.blowUpπ).stalkIdeal x' = ⊤ := hshape iH
    have hshapeK : (a (toLex (Sum.inl i)) ≠ j ∧
        (((E.component i).comap D.blowUpπ).stalkIdeal x' = span
          {z (a (toLex (Sum.inl i))) * z j} ∨
          ((E.component i).comap D.blowUpπ).stalkIdeal x' = span
            {z (a (toLex (Sum.inl i)))})) ∨
        ((E.component i).comap D.blowUpπ).stalkIdeal x' = span {z j} ∨
        ((E.component i).comap D.blowUpπ).stalkIdeal x' = ⊤ := hshape (toLex
            (Sum.inl i))
    have hTHle : (g.ker.comap D.blowUpπ).stalkIdeal x' ≤
        D.exceptionalDivisor.stalkIdeal x' :=
      Scheme.IdealSheafData.stalkIdeal_mono (Scheme.IdealSheafData.comap_mono
          D.blowUpπ hle) x'
    have hH1 : (g.ker.strictTransform D).stalkIdeal x' ≠ ⊤ := by
      rw [← hφker]; exact RingHom.ker_ne_top φ
    have hstrictH : (g.ker.strictTransform D).stalkIdeal x' =
        ⨆ n : ℕ, ((g.ker.comap D.blowUpπ).stalkIdeal x').colon
          (↑(D.exceptionalDivisor.stalkIdeal x' ^ n) : Set _) :=
      stalkIdeal_strictTransformAlong_eq_iSup D g.ker x'
    have hFmax : D.exceptionalDivisor.stalkIdeal x' ≤ maximalIdeal _ :=
      (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp hx'F
    have hH : a iH ≠ j ∧ (g.ker.comap D.blowUpπ).stalkIdeal x' = span
      {z (a iH) * z j} := by
      rcases hshapeH with ⟨hne, hTH | hTH⟩ | hTH | hTH
      · exact ⟨hne, hTH⟩
      · exfalso
        have h1 := hTHle
        rw [hTH, hF''] at h1
        exact notMem_span_singleton_of_ne hzspan hzdim hne.symm
          (h1 (Ideal.mem_span_singleton_self _))
      · exfalso
        apply hH1
        rw [hstrictH, iSup_colon_congr hTH hF'',
          iSup_colon_pow_span_singleton_self]
      · exfalso
        have h1 := hTHle
        rw [hTH] at h1
        exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h1.trans hFmax))
    have hkerφ : RingHom.ker φ = span {z (a iH)} := by
      rw [hφker, hstrictH, iSup_colon_congr hH.2 hF'',
        iSup_colon_pow_span_singleton_mul hzspan hzdim hH.1]
    rw [hF'']
    refine (map_iSup_colon_pow_eq_of_shape hzspan hzdim hφs hkerφ hH.1.symm ?_).symm
    rcases hshapeK with ⟨hne, hTK⟩ | hTK | hTK
    · refine Or.inl ⟨a (toLex (Sum.inl i)), hne, fun heq => ?_, hTK⟩
      have := hinj _ _ hne hH.1 heq
      exact Sum.inl_ne_inr (toLex.injective this)
    · exact Or.inr (Or.inl hTK)
    · exact Or.inr (Or.inr hTK)
  · have hFtop : D.exceptionalDivisor.stalkIdeal x' = ⊤ :=
      Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hx'F
    rw [hFtop, Ideal.map_top]
    simp only [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ, iSup_const]

/-- The family form: the total transform of `E` restricted to `B_Z H` is the total transform of
`E|_H` [Kol07, Corollary 85, proof]; componentwise `strictTransform_comap_blowUpMap_of_hasSncWith`,
and the exceptional divisor of `B_Z X` restricts to that of `B_Z H` (`exceptionalDivisor_comap`). -/
theorem totalTransform_comap_blowUpMap_of_hasSncWith (f : X ⟶ Spec (.of k)) [Smooth f]
    (g : Y ⟶ X) [IsClosedImmersion g]
    {E : DivisorFamily X} {D : X.IdealSheafData} (hb : (E.append g.ker).HasSncWith D)
    (hle : g.ker ≤ D) :
    (E.comap g).totalTransform (D.comap g) = (E.totalTransform D).comap (Scheme.Hom.blowUpMap g
        D) := by
  unfold DivisorFamily.totalTransform DivisorFamily.comap
  congr 1
  funext i
  dsimp only
  cases ofLex i with
  | inl j => exact strictTransform_comap_blowUpMap_of_hasSncWith f g hb hle j
  | inr u => exact exceptionalDivisor_comap g D

end OneStep

/-! ### The point lemma -/

/-- Index function for the appended family `E + H` from one for `E` and a coordinate for `H`. -/
def appendIdx {E : DivisorFamily X} {J : X.IdealSheafData} {x : X} {n : ℕ}
    (c : {i : E.ι // x ∈ (E.component i).support} → Fin n) (t₀ : Fin n)
    (i : {i : E.ι ⊕ₗ PUnit.{u + 1} //
      x ∈ (Sum.elim E.component (fun _ => J) (ofLex i)).support}) : Fin n :=
  match hv : ofLex i.1 with
  | Sum.inl i₀ => c ⟨i₀, by
      have hi := i.2
      rwa [hv] at hi⟩
  | Sum.inr _ => t₀

section PointLemma

variable {k : Type u} [Field k]

/-- At `x ∈ Z` with `Z ⊆ H = V(J)`, if `Z` has simple normal crossings with `E` and `H + E` has
simple normal crossings, then `Z` has simple normal crossings with `H + E`
[Kol07, Definition 24]. Not in the sources in this form; the argument: in `E`-adapted coordinates
`z` with `I_Z = (z_s)_{s ∈ S}`, write `I_H = (g)` with `g` a coordinate of the `(E + H)`-adapted
system, and `g = Σ_{s ∈ S} a_s z_s`; if every coefficient at a non-`E` index lay in `𝔪` then `g`
would lie in `𝔪²` plus the span of the `E`-coordinates, contradicting `notMem_sq_sup_span_image`
in the `(E + H)`-adapted system; so some `a_{s₀}` is a unit at a non-`E` index `s₀ ∈ S`, and
exchanging `z_{s₀}` for `g` gives a regular system of parameters adapted to `E`, `H` and `Z`. -/
theorem hasSncWith_append_of_le (f : X ⟶ Spec (.of k)) [Smooth f] {E : DivisorFamily X}
    {J Z : X.IdealSheafData} (hE : (E.append J).IsSnc) (hZ : E.HasSncWith Z) (hle : J ≤ Z) :
    (E.append J).HasSncWith Z := by
  classical
  intro x hx
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f x
  obtain ⟨n, z, ⟨⟨hzspan, hzdim⟩, c, hcinj, hcE⟩, s, hs⟩ := hZ x hx
  obtain ⟨n', z', ⟨hz'span, hz'dim⟩, c', hc'inj, hc'⟩ := hE.2 x
  have hxJ : x ∈ J.support := Scheme.IdealSheafData.support_antitone hle hx
  have hxH : x ∈ ((E.append J).component (toLex (Sum.inr PUnit.unit))).support := hxJ
  set g : X.presheaf.stalk x := z' (c' ⟨toLex (Sum.inr PUnit.unit), hxH⟩) with hg
  have hJg : J.stalkIdeal x = span {g} := hc' ⟨toLex (Sum.inr PUnit.unit), hxH⟩
  have hcE' : ∀ i : {i : E.ι // x ∈ (E.component i).support},
      (E.component i.1).stalkIdeal x = span {z' (c' ⟨toLex (Sum.inl i.1), i.2⟩)} :=
    fun i => hc' ⟨toLex (Sum.inl i.1), i.2⟩
  have hcEz : ∀ i : {i : E.ι // x ∈ (E.component i).support},
      (E.component i.1).stalkIdeal x = span {z (c i)} := fun i => hcE i
  have hZs : Z.stalkIdeal x = span (z '' ↑s) := hs
  have hgm : g ∈ maximalIdeal (X.presheaf.stalk x) := hz'span ▸ subset_span ⟨_, rfl⟩
  have hzm : ∀ t, z t ∈ maximalIdeal (X.presheaf.stalk x) := fun t => hzspan ▸ subset_span ⟨t, rfl⟩
  -- `g ∈ Z_x = (z_s)_{s ∈ S}`
  have hgZ : g ∈ span (Set.range fun t : ↥(↑s : Set (Fin n)) => z t) := by
    rw [← Set.image_eq_range, ← hZs]
    exact Scheme.IdealSheafData.stalkIdeal_mono hle x (hJg ▸ mem_span_singleton_self g)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hgZ
  -- the `E`-coordinates of the `z`-system lie in the span of those of the `z'`-system
  set S' : Finset (Fin n') := Finset.univ.image
    fun i : {i : E.ι // x ∈ (E.component i).support} => c' ⟨toLex (Sum.inl i.1), i.2⟩ with hS'
  have hspan_le : span (z '' Set.range c) ≤ span (z' '' ↑S') := by
    refine span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have h1 : z (c i) ∈ (E.component i.1).stalkIdeal x := by
      rw [hcEz i]; exact mem_span_singleton_self _
    rw [hcE' i] at h1
    have h2 : span {z' (c' ⟨toLex (Sum.inl i.1), i.2⟩)} ≤ span (z' '' ↑S') :=
      span_le.mpr (Set.singleton_subset_iff.mpr (subset_span
        ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)), rfl⟩))
    exact h2 h1
  -- a unit coefficient at a non-`E` index
  have hex : ∃ t : ↥(↑s : Set (Fin n)), IsUnit (a t) ∧ (t : Fin n) ∉ Set.range c := by
    by_contra hcon
    have hcon' : ∀ t : ↥(↑s : Set (Fin n)), IsUnit (a t) → (t : Fin n) ∈ Set.range c :=
      fun t hu => by_contra fun hn => hcon ⟨t, hu, hn⟩
    have hmem : g ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔ span (z '' Set.range c) := by
      rw [← ha]
      refine Ideal.sum_mem _ fun t _ => ?_
      by_cases hu : IsUnit (a t)
      · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (subset_span ⟨t, hcon' t hu, rfl⟩))
      · have ham : a t ∈ maximalIdeal (X.presheaf.stalk x) :=
          (IsLocalRing.mem_maximalIdeal _).mpr hu
        exact Ideal.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul ham (hzm t))
    have hmem' : g ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔ span (z' '' ↑S') :=
      sup_le_sup_left hspan_le _ hmem
    refine notMem_sq_sup_span_image hz'span.symm hz'dim (s := S')
      (j := c' ⟨toLex (Sum.inr PUnit.unit), hxH⟩) ?_ hmem'
    intro hin
    rw [hS', Finset.mem_image] at hin
    obtain ⟨i, -, hi⟩ := hin
    exact Sum.inl_ne_inr (toLex.injective (congrArg Subtype.val (hc'inj hi)))
  obtain ⟨t₀, hu, ht₀⟩ := hex
  -- the exchanged system `z̃ = update z t₀ g`
  set zt := Function.update z (t₀ : Fin n) g with hzt
  have hzt_ne : ∀ t, t ≠ (t₀ : Fin n) → zt t = z t := fun t ht => Function.update_of_ne ht _ _
  have hzt_t₀ : zt t₀ = g := Function.update_self _ _ _
  -- `z t₀` in terms of `g` and the other coordinates
  have hsplit : g = a t₀ * z t₀ + ∑ t ∈ Finset.univ.erase t₀, a t * z t := by
    rw [Finset.add_sum_erase Finset.univ (fun t => a t * z t) (Finset.mem_univ t₀)]; exact ha.symm
  have hz₀ : z t₀ = ↑hu.unit⁻¹ * (g - ∑ t ∈ Finset.univ.erase t₀, a t * z t) := by
    have h1 : a t₀ * z t₀ = g - ∑ t ∈ Finset.univ.erase t₀, a t * z t := by
      rw [hsplit]; ring
    calc z t₀ = ↑hu.unit⁻¹ * (↑hu.unit * z t₀) := (Units.inv_mul_cancel_left _ _).symm
      _ = ↑hu.unit⁻¹ * (g - ∑ t ∈ Finset.univ.erase t₀, a t * z t) := by
        rw [IsUnit.unit_spec, h1]
  have hmem_zt : ∀ t, zt t ∈ maximalIdeal (X.presheaf.stalk x) := by
    intro t
    by_cases ht : t = t₀
    · rw [ht, hzt_t₀]; exact hgm
    · rw [hzt_ne t ht]; exact hzm t
  have hz₀_mem : ∀ T : Set (Fin n), (t₀ : Fin n) ∈ T →
      (∀ t : ↥(↑s : Set (Fin n)), (t : Fin n) ∈ T) → z t₀ ∈ span (zt '' T) := by
    intro T ht₀T hsT
    rw [hz₀]
    refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ ?_ (Ideal.sum_mem _ fun t ht => ?_))
    · rw [← hzt_t₀]; exact subset_span ⟨t₀, ht₀T, rfl⟩
    · have hne : (t : Fin n) ≠ t₀ := fun h => (Finset.mem_erase.mp ht).1 (Subtype.ext h)
      rw [← hzt_ne t hne]
      exact Ideal.mul_mem_left _ _ (subset_span ⟨t, hsT t, rfl⟩)
  have hspan_zt : span (Set.range zt) = maximalIdeal (X.presheaf.stalk x) := by
    refine le_antisymm (span_le.mpr ?_) ?_
    · rintro _ ⟨t, rfl⟩; exact hmem_zt t
    · rw [← hzspan]
      refine span_le.mpr ?_
      rintro _ ⟨t, rfl⟩
      by_cases ht : t = t₀
      · rw [ht, ← Set.image_univ]
        exact hz₀_mem _ (Set.mem_univ _) fun _ => Set.mem_univ _
      · rw [← hzt_ne t ht]; exact subset_span ⟨t, rfl⟩
  have hZ_zt : Z.stalkIdeal x = span (zt '' ↑s) := by
    rw [hZs]
    refine le_antisymm (span_le.mpr ?_) (span_le.mpr ?_)
    · rintro _ ⟨t, hts, rfl⟩
      by_cases ht : t = t₀
      · rw [ht]; exact hz₀_mem _ t₀.2 fun t' => t'.2
      · rw [← hzt_ne t ht]; exact subset_span ⟨t, hts, rfl⟩
    · rintro _ ⟨t, hts, rfl⟩
      by_cases ht : t = t₀
      · rw [ht, hzt_t₀, Set.image_eq_range]; exact hgZ
      · rw [hzt_ne t ht]; exact subset_span ⟨t, hts, rfl⟩
  refine ⟨n, zt, ⟨⟨hspan_zt, hzdim⟩, appendIdx c (t₀ : Fin n), ?_, ?_⟩, s, hZ_zt⟩
  · rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ heq
    obtain ⟨a₁, rfl⟩ := toLex.surjective i₁
    obtain ⟨a₂, rfl⟩ := toLex.surjective i₂
    rcases a₁ with i₁ | u₁ <;> rcases a₂ with i₂ | u₂
    · have := hcinj (show c ⟨i₁, h₁⟩ = c ⟨i₂, h₂⟩ from heq)
      exact Subtype.ext (congrArg (fun j => toLex (Sum.inl j)) (congrArg Subtype.val this))
    · exact absurd ⟨⟨i₁, h₁⟩, heq⟩ ht₀
    · exact absurd ⟨⟨i₂, h₂⟩, heq.symm⟩ ht₀
    · cases u₁; cases u₂; rfl
  · rintro ⟨i, hi⟩
    obtain ⟨a₀, rfl⟩ := toLex.surjective i
    rcases a₀ with i₀ | u
    · change (E.component i₀).stalkIdeal x = span {zt (c ⟨i₀, hi⟩)}
      rw [hzt_ne _ fun h => ht₀ ⟨⟨i₀, hi⟩, h⟩]
      exact hcEz ⟨i₀, hi⟩
    · change J.stalkIdeal x = span {zt t₀}
      rw [hzt_t₀]; exact hJg

end PointLemma

/-! ### The families `E_i + H_i` along the sequence -/

/-- The reindexing between `(E + H)_1 = (E + H).totalTransform D` and
`E_1 + H_1 = (E.totalTransform D).append (strictTransform D J)`: the two appended slots are
swapped. -/
def appendTotalEquiv (E : DivisorFamily X) :
    (E.ι ⊕ₗ PUnit.{u + 1}) ⊕ₗ PUnit.{u + 1} ≃ (E.ι ⊕ₗ PUnit.{u + 1}) ⊕ₗ PUnit.{u + 1} :=
  (ofLex.trans ((ofLex.sumCongr (Equiv.refl PUnit.{u + 1})).trans
    ((Equiv.sumAssoc E.ι PUnit.{u + 1} PUnit.{u + 1}).trans
      (((Equiv.refl E.ι).sumCongr (Equiv.sumComm PUnit.{u + 1} PUnit.{u + 1})).trans
        ((Equiv.sumAssoc E.ι PUnit.{u + 1} PUnit.{u + 1}).symm.trans
          (toLex.sumCongr (Equiv.refl PUnit.{u + 1}))))))).trans toLex

/-- The reindexing `appendTotalEquiv` matches the components: strict transforms of `E` to strict
transforms of `E`, `H_1` to `H_1`, the exceptional divisor to itself. -/
theorem appendTotalEquiv_component (E : DivisorFamily X) (J D : X.IdealSheafData) (i) :
    ((E.totalTransform D).append (J.strictTransform D)).component (appendTotalEquiv E i) =
      ((E.append J).totalTransform D).component i := by
  obtain ⟨a, rfl⟩ := toLex.surjective i
  rcases a with b | u
  · obtain ⟨b', rfl⟩ := toLex.surjective b
    rcases b' with e | u'
    · rfl
    · rfl
  · rfl

section Stagewise

variable {k : Type u} [Field k] [PerfectField k]

/-- One step: if `E + H` has simple normal crossings and the center has simple normal crossings
with `E + H`, then `E_1 + H_1` has simple normal crossings, `H_1` the strict transform of `H`
([Kol07, Corollary 85, proof]; `AlgebraicGeometry.totalTransform_isSnc`). -/
theorem isSnc_totalTransform_append_of_hasSncWith (f : X ⟶ Spec (.of k)) [Smooth f]
    {E : DivisorFamily X} {J D : X.IdealSheafData} (hE : (E.append J).IsSnc)
    (hb : (E.append J).HasSncWith D) :
    ((E.totalTransform D).append (J.strictTransform D)).IsSnc :=
  isSnc_of_equiv (appendTotalEquiv E) (appendTotalEquiv_component E J D)
    (totalTransform_isSnc f (E.append J) D hE hb)

/-- `isSnc_totalTransformSeq_append` in the `⟨j, hj⟩` form of the indices: by induction along the
sequence, the head step by the point lemma `hasSncWith_append_of_le` and
`isSnc_totalTransform_append_of_hasSncWith`. -/
theorem isSnc_totalTransformSeq_append_mk (f : X ⟶ Spec (.of k)) [Smooth f]
    (S : BlowUpSequence X)
    (J : X.IdealSheafData) (E : DivisorFamily X) (hsm : S.IsSmooth f) (hE : (E.append J).IsSnc)
    (hsnc : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq J i.castSucc ≤ S.center i)
    (j : ℕ) (hj : j < S.length + 1) :
    ((S.totalTransformSeq E ⟨j, hj⟩).append (S.strictTransformSeq J ⟨j, hj⟩)).IsSnc := by
  induction S generalizing j with
  | nil X => exact hE
  | cons X D rest ih =>
    cases j with
    | zero => exact hE
    | succ j =>
      obtain ⟨hD, hsm'⟩ := (isSmooth_cons_iff f D rest).1 hsm
      have hb : (E.append J).HasSncWith D :=
        hasSncWith_append_of_le f hE (hsnc ⟨0, Nat.zero_lt_succ _⟩) (hZ ⟨0, Nat.zero_lt_succ _⟩)
      have hπ : Smooth (D.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth' f D
      exact ih (D.blowUpπ ≫ f) (J.strictTransform D) (E.totalTransform D) hsm'
        (isSnc_totalTransform_append_of_hasSncWith f hE hb)
        (fun ⟨i, hi⟩ => hsnc ⟨i + 1, Nat.succ_lt_succ hi⟩)
        (fun ⟨i, hi⟩ => hZ ⟨i + 1, Nat.succ_lt_succ hi⟩) j (Nat.lt_of_succ_lt_succ hj)

/-- Along a smooth blow-up sequence whose centers lie in the strict transforms `H_i` of `H = V(J)`
and have simple normal crossings with the induced families `E_i`, and with `E + H` having simple
normal crossings, every `E_i + H_i` has simple normal crossings [Kol07, Corollary 85, proof]. -/
theorem isSnc_totalTransformSeq_append (f : X ⟶ Spec (.of k)) [Smooth f]
    (S : BlowUpSequence X)
    (J : X.IdealSheafData) (E : DivisorFamily X) (hsm : S.IsSmooth f) (hE : (E.append J).IsSnc)
    (hsnc : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq J i.castSucc ≤ S.center i)
    (i : Fin (S.length + 1)) :
    ((S.totalTransformSeq E i).append (S.strictTransformSeq J i)).IsSnc := by
  obtain ⟨j, hj⟩ := i
  exact isSnc_totalTransformSeq_append_mk f S J E hsm hE hsnc hZ j hj

/-- Under the same hypotheses every center `Z_i` has simple normal crossings with `E_i + H_i`
(the point lemma `hasSncWith_append_of_le` at stage `i`, the stage being smooth over `k` by
`IsSmooth.smooth_stageMap'`). -/
theorem hasSncWith_totalTransformSeq_append (f : X ⟶ Spec (.of k)) [Smooth f]
    (S : BlowUpSequence X) (J : X.IdealSheafData) (E : DivisorFamily X) (hsm : S.IsSmooth f)
    (hE : (E.append J).IsSnc)
    (hsnc : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq J i.castSucc ≤ S.center i)
    (i : Fin S.length) :
    ((S.totalTransformSeq E i.castSucc).append (S.strictTransformSeq J i.castSucc)).HasSncWith
      (S.center i) := by
  have := IsSmooth.smooth_stageMap' hsm i.castSucc
  exact hasSncWith_append_of_le (S.stageMap i.castSucc ≫ f)
    (isSnc_totalTransformSeq_append f S J E hsm hE hsnc hZ i.castSucc) (hsnc i) (hZ i)

/-! ### Restriction of the induced divisors to `H` -/

/-- `totalTransformSeq_comap_pullback` for an arbitrary closed immersion `g : Y ⟶ X` with image
`H = V(g.ker)`, in the `⟨j, hj⟩` form: by induction along the sequence, the head step is the
one-step identity for the family, `totalTransform_comap_blowUpMap_of_hasSncWith`, and the tail's
embedding `blowUpMap g D` is again a closed immersion with kernel `strictTransform D g.ker`, so
that the hypotheses transport: `E_1 + H_1` has simple normal crossings by
`isSnc_totalTransform_append_of_hasSncWith`, the hypotheses on the centers by reindexing. -/
theorem totalTransformSeq_comap_pullbackStageHom_mk (f : X ⟶ Spec (.of k)) [Smooth f]
    (S : BlowUpSequence X) (g : Y ⟶ X) [IsClosedImmersion g] (E : DivisorFamily X)
    (hsm : S.IsSmooth f) (hE : (E.append g.ker).IsSnc)
    (hsnc : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq g.ker i.castSucc ≤ S.center i)
    (j : ℕ) (hj : j < S.length + 1) :
    (S.totalTransformSeq E ⟨j, hj⟩).comap (S.pullbackStageHom g ⟨j, hj⟩) =
      (S.pullback g).totalTransformSeq (E.comap g) (S.pullbackStageIdx g ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      obtain ⟨hD, hsm'⟩ := (isSmooth_cons_iff f D rest).1 hsm
      have hb : (E.append g.ker).HasSncWith D :=
        hasSncWith_append_of_le f hE (hsnc ⟨0, Nat.zero_lt_succ _⟩) (hZ ⟨0, Nat.zero_lt_succ _⟩)
      have hci : IsClosedImmersion (Scheme.Hom.blowUpMap g D) :=
        isClosedImmersion_blowUpMap_of_isClosedImmersion g D
      have hπ : Smooth (D.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth' f D
      have hE' : ((E.totalTransform D).append (Scheme.Hom.blowUpMap g D).ker).IsSnc := by
        rw [ker_blowUpMap_of_isClosedImmersion]
        exact isSnc_totalTransform_append_of_hasSncWith f hE hb
      have hZ' : ∀ i : Fin rest.length,
          rest.strictTransformSeq (Scheme.Hom.blowUpMap g D).ker i.castSucc ≤ rest.center i := by
        rintro ⟨i, hi⟩
        rw [ker_blowUpMap_of_isClosedImmersion]
        exact hZ ⟨i + 1, Nat.succ_lt_succ hi⟩
      have := ih (D.blowUpπ ≫ f) (Scheme.Hom.blowUpMap g D) (E.totalTransform D) hsm' hE'
        (fun ⟨i, hi⟩ => hsnc ⟨i + 1, Nat.succ_lt_succ hi⟩) hZ' j (Nat.lt_of_succ_lt_succ hj)
      rw [← totalTransform_comap_blowUpMap_of_hasSncWith f g hb (hZ ⟨0, Nat.zero_lt_succ _⟩)]
        at this
      exact this

/-- Let `H = V(J)` be a smooth hypersurface with `H + E` having simple normal crossings and `S` a
smooth blow-up sequence of the kind in [Kol07, Corollary 85]: its centers lie in the strict
transforms `H_i` and have simple normal crossings with the induced families `E_i`. Then at every
stage the induced family `E_i` restricted to `H_i` (along `pullbackStageHom`, a closed immersion
onto `H_i`) is the induced family of the restricted data on `H`: `E_i|_{H_i} = (E|_H)_i`
([Kol07, Corollary 85, proof]; the setting of [Kol07, Definition 78]). The case of `J.subschemeι`
of `totalTransformSeq_comap_pullbackStageHom_mk` (`ker_subschemeι`). -/
theorem totalTransformSeq_comap_pullback (f : X ⟶ Spec (.of k)) [Smooth f]
    (S : BlowUpSequence X) (J : X.IdealSheafData) (E : DivisorFamily X) (hsm : S.IsSmooth f)
    (_hH : Smooth (J.subschemeι ≫ f)) (hE : (E.append J).IsSnc)
    (hsnc : ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq J i.castSucc ≤ S.center i)
    (i : Fin (S.length + 1)) :
    (S.totalTransformSeq E i).comap (S.pullbackStageHom J.subschemeι i) =
      (S.pullback J.subschemeι).totalTransformSeq (E.comap J.subschemeι)
        (S.pullbackStageIdx J.subschemeι i) := by
  obtain ⟨j, hj⟩ := i
  have hker : J.subschemeι.ker = J := Scheme.IdealSheafData.ker_subschemeι J
  have hE' : (E.append J.subschemeι.ker).IsSnc := by rw [hker]; exact hE
  have hZ' : ∀ i : Fin S.length, S.strictTransformSeq J.subschemeι.ker i.castSucc ≤ S.center i := by
    rw [hker]; exact hZ
  exact totalTransformSeq_comap_pullbackStageHom_mk f S J.subschemeι E hsm hE' hsnc hZ' j hj

end Stagewise

end AlgebraicGeometry

/-! ### Push-forward of a nonzero ideal sheaf along a closed immersion -/

namespace AlgebraicGeometry

open AlgebraicGeometry TopologicalSpace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The push-forward along a closed immersion `ℓ : Y → X` of an ideal sheaf nonzero on every
component of `Y` is nonzero on every component of `X` (the condition of [Kol07, Notation 64 (2)]
for the intermediate triples `(Y_i, (Y ↪ Y_i)_* J, 1, ∅)` of the chain of hypersurfaces in
[Kol07, 108]). Off the image of `V(Z)` the stalk is the unit ideal (Mathlib's `support_map`); at
`ℓ y` with `y ∈ V(Z)` it is the preimage of the stalk `Z_y` under the surjective stalk map of `ℓ`
(`ker_stalkMap_of_isClosedImmersion` applied to `V(Z) → Y → X`, whose kernel ideal sheaf is
`Z.map ℓ`), nonzero since `Z_y` is. -/
theorem isNonzeroEverywhere_map_of_isClosedImmersion (ℓ : Y ⟶ X) [IsClosedImmersion ℓ]
    (Z : Y.IdealSheafData) (hZ : IsNonzeroEverywhere Z) : IsNonzeroEverywhere (Z.map ℓ) := by
  intro x
  by_cases hx : x ∈ (Z.map ℓ).support
  · -- `x = ℓ y` with `y ∈ V(Z)`: the stalk is the preimage of `Z_y` under the stalk map of `ℓ`
    have hcl : IsClosed (ℓ.base '' (Z.support : Set Y)) :=
      ℓ.isClosedEmbedding.isClosedMap _ Z.support.isClosed
    have hx' : x ∈ ℓ.base '' (Z.support : Set Y) := by
      have h2 : x ∈ (Closeds.closure (ℓ.base '' (Z.support : Set Y)) : Set X) := by
        rw [support_map] at hx
        exact hx
      rw [Closeds.coe_closure, hcl.closure_eq] at h2
      exact h2
    obtain ⟨y, hy, rfl⟩ := hx'
    obtain ⟨z, rfl⟩ : y ∈ Set.range Z.subschemeι := by rw [range_subschemeι]; exact hy
    have h3 : RingHom.ker ((Z.subschemeι ≫ ℓ).stalkMap z).hom =
        (Z.stalkIdeal (Z.subschemeι z)).comap (ℓ.stalkMap (Z.subschemeι z)).hom := by
      rw [← ker_stalkMap_subschemeι, RingHom.comap_ker, Scheme.Hom.stalkMap_comp]
      rfl
    have hstalk : (Z.map ℓ).stalkIdeal (ℓ (Z.subschemeι z)) =
        (Z.stalkIdeal (Z.subschemeι z)).comap (ℓ.stalkMap (Z.subschemeι z)).hom :=
      (h3.symm.trans (ker_stalkMap_of_isClosedImmersion (Z.subschemeι ≫ ℓ) z)).symm
    rw [hstalk]
    intro hbot
    apply hZ (Z.subschemeι z)
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨b, rfl⟩ := ℓ.stalkMap_surjective (Z.subschemeι z) a
    have hb : b ∈ (Z.stalkIdeal (Z.subschemeι z)).comap (ℓ.stalkMap (Z.subschemeι z)).hom := ha
    rw [hbot] at hb
    rw [Ideal.mem_bot.mp hb, map_zero]
    exact Ideal.zero_mem _
  · -- off the support the stalk is the unit ideal
    rw [stalkIdeal_eq_top_of_notMem_support _ hx]
    exact top_ne_bot

end AlgebraicGeometry
