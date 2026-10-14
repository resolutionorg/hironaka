/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquiv
public import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquiv
public import Hironaka.Scheme.Smooth.GraphFormal
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Hironaka.Algebra.Local.DerivativeCompletion
import Hironaka.Scheme.BlowUp.GlueIdealSheaf
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.GraphCompletion
import Hironaka.Scheme.Smooth.IdealSheafSpreadOut
import Hironaka.Scheme.Smooth.SubschemeStalk

/-!
# From agreement on a completed stalk to agreement on a neighbourhood

In the proof of Theorem 92 ([Kol07, 95]) Kollár passes from the completion to a neighbourhood:
the conditions (91.1)–(91.4) hold after completion at `(p, p)`, so "(91.1′–4′) also hold in an open
neighborhood `U(p) ∋ (p, p)` by (55)". Conditions (1′)–(3′) are equalities of ideal sheaves,
spread out by `exists_comap_eq_of_map_adicCompletion_eq`.
Condition (4′) is the equality of two morphisms `ψ, ψ'` on the closed subscheme `V(M)`,
`M = MC(ψ^*I)`; this file spreads it out from the completion at `q`. The argument (not in the
sources; Kollár's appeal to [Kol07, Definition 55] applied to the equalizer):

1. faithful flatness of the completion descends `ψ̂^*(x) − ψ̂'^*(x) ∈ M̂_q` to
   `ψ^*(s) − ψ'^*(s) ∈ M_q`, so the two composites `g, g' : V(M) ⇉ X` have the same stalk map at
   the point `z` over `q` (the stalk map of `V(M) → W` at `z` has kernel `M_q`);
2. two morphisms with the same stalk map at `z` agree after composing with
   `Spec 𝒪_{V(M),z} → V(M)` (`fromSpecStalk_comp_eq_of_stalkMap_eq`, Mathlib's
   `SpecMap_stalkMap_fromSpecStalk`), so `Spec 𝒪_{V(M),z}` lifts to their equalizer `E`;
3. the equalizer of two morphisms of schemes is an immersion (Mathlib), i.e. a closed subscheme of
   an open `coborder(E) ⊆ V(M)`; the lift makes `z` a point of `E` at which the stalk map of the
   immersion is bijective, so the kernel of the closed part `E → coborder(E)` has zero stalk at
   `z` and vanishes on an open neighbourhood (`V(M)` is locally Noetherian); over that open the
   closed immersion is an isomorphism (`isIso_iff_ker_eq_bot`), giving an open immersion `j` into
   `V(M)` through `z` with `j ≫ g = j ≫ g'` (`exists_openImmersion_comp_eq_of_lift`);
4. the open subset `range j` of the closed `V(M)` is the trace of an open `V ⊆ W`; the subscheme
   `V(M|_V) = V(M) ×_W V` factors through `j`, hence `ψ = ψ'` on it (`AgreeOn`).

If `q ∉ V(M)`, the complement of `V(M)` is the neighbourhood and `V(M|_V) = ∅`.

No hypothesis on the `k`-structures of `ψ, ψ'` is needed: the argument never chooses generators.
-/

public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace Topology AlgebraicGeometry

section Auxiliary

variable {X : Scheme.{u}}

/-- Every pair of morphisms agrees on the empty subscheme `V(⊤)`. -/
theorem agreeOn_top {U : Scheme.{u}} (ψ ψ' : U ⟶ X) : AgreeOn ψ ψ' ⊤ := by
  have : IsEmpty ((⊤ : U.IdealSheafData).subscheme) := by
    rw [← Set.range_eq_empty_iff, range_subschemeι, support_top, Closeds.coe_bot]
  exact (isInitialOfIsEmpty).hom_ext _ _

/-- Two morphisms `g, g' : T ⟶ X` with the same image point and the same stalk map at `t` agree
after composing with the canonical `Spec 𝒪_{T,t} ⟶ T` (Mathlib's `SpecMap_stalkMap_fromSpecStalk`,
with the stalks transported along the two image-point equalities). -/
theorem fromSpecStalk_comp_eq_of_stalkMap_eq {T : Scheme.{u}} (g g' : T ⟶ X) (t : T) {p : X}
    (h : g.base t = p) (h' : g'.base t = p)
    (hst : ∀ s : X.presheaf.stalk p,
      (g.stalkMap t).hom ((X.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom s) =
        (g'.stalkMap t).hom ((X.presheaf.stalkCongr (Inseparable.of_eq h'.symm)).hom s)) :
    T.fromSpecStalk t ≫ g = T.fromSpecStalk t ≫ g' := by
  subst h
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
  have e2 : X.fromSpecStalk (g'.base t) =
      Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq h'.symm)).hom ≫
        X.fromSpecStalk (g.base t) := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk _).symm
  have e3 : g.stalkMap t =
      (X.presheaf.stalkCongr (Inseparable.of_eq h'.symm)).hom ≫ g'.stalkMap t := by
    ext s
    have := hst s
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      CommRingCat.id_apply] at this
    rw [CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
    exact this
  rw [e2, ← Category.assoc, ← Spec.map_comp, ← e3]

/-- The core of the spreading-out argument, on an arbitrary locally Noetherian scheme `Z`: an
immersion `e : E ⟶ Z` equalizing `g, g' : Z ⟶ X`, together with a lift of `Spec 𝒪_{Z,z} ⟶ Z`
through `e`, yields an open immersion `j` into `Z` whose image contains `z` and on which `g = g'`.
Route: the closed part `E → coborder(E)` of the immersion has a kernel with zero stalk at `z` (the
lift makes the stalk map of `e` at the point over `z` injective), hence vanishing on an open
neighbourhood (Krull's intersection theorem, `exists_comap_eq_of_stalkIdeal_eq`), over which the
closed immersion is an isomorphism (`IsClosedImmersion.isIso_iff_ker_eq_bot`). -/
theorem exists_openImmersion_comp_eq_of_lift {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    {E : Scheme.{u}} (e : E ⟶ Z) [IsImmersion e] (g g' : Z ⟶ X) (hcond : e ≫ g = e ≫ g')
    (z : Z) (l : Spec (Z.presheaf.stalk z) ⟶ E) (hl : l ≫ e = Z.fromSpecStalk z) :
    ∃ (T : Scheme.{u}) (j : T ⟶ Z), IsOpenImmersion j ∧ z ∈ Set.range j ∧ j ≫ g = j ≫ g' := by
  classical
  -- the point of `E` over `z`
  set x₀ : E := l.base (closedPoint (Z.presheaf.stalk z)) with hx₀
  have hex₀ : e.base x₀ = z := by
    have h0 : (l ≫ e).base (closedPoint (Z.presheaf.stalk z)) =
        (Z.fromSpecStalk z).base (closedPoint (Z.presheaf.stalk z)) := by rw [hl]
    exact h0.trans Scheme.fromSpecStalk_closedPoint
  -- the stalk map of `Spec 𝒪_{Z,z} ⟶ Z` at the closed point is an isomorphism
  have hiso : IsIso ((Z.fromSpecStalk z).stalkMap (closedPoint (Z.presheaf.stalk z))) := by
    have h2 : IsIso ((Z.fromSpecStalk z).stalkMap (closedPoint (Z.presheaf.stalk z)) ≫
        (stalkClosedPointIso (Z.presheaf.stalk z)).hom) := by
      change IsIso (Scheme.stalkClosedPointTo (Z.fromSpecStalk z))
      rw [Scheme.stalkClosedPointTo_fromSpecStalk]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (stalkClosedPointIso (Z.presheaf.stalk z)).hom
  -- hence the stalk map of `e` at `x₀` is injective
  have hinj_e : Function.Injective (e.stalkMap x₀).hom := by
    have h1 : Function.Injective ((l ≫ e).stalkMap (closedPoint (Z.presheaf.stalk z))).hom := by
      rw [hl]
      exact (ConcreteCategory.bijective_of_isIso _).1
    have hc := Scheme.Hom.stalkMap_comp l e (closedPoint (Z.presheaf.stalk z))
    rw [hc] at h1
    exact Function.Injective.of_comp
      (f := ⇑(l.stalkMap (closedPoint (Z.presheaf.stalk z))).hom) h1
  -- the closed part of the immersion and its kernel
  have he₁ : e.liftCoborder ≫ e.coborderRange.ι = e := Scheme.Hom.liftCoborder_ι e
  have hpt₁ : e.base x₀ = (e.liftCoborder ≫ e.coborderRange.ι).base x₀ :=
    congrArg (fun φ : E ⟶ Z => φ.base x₀) he₁.symm
  have hinj_e₁ : Function.Injective (e.liftCoborder.stalkMap x₀).hom := by
    have h := Scheme.Hom.stalkMap_congr_hom e (e.liftCoborder ≫ e.coborderRange.ι) he₁.symm x₀
    rw [Scheme.Hom.stalkMap_comp] at h
    have h3 := hinj_e
    rw [h] at h3
    change Function.Injective (⇑(e.liftCoborder.stalkMap x₀).hom ∘
      ⇑((Z.presheaf.stalkCongr (Inseparable.of_eq hpt₁)).hom ≫
        e.coborderRange.ι.stalkMap (e.liftCoborder.base x₀)).hom) at h3
    have : IsIso (e.coborderRange.ι.stalkMap (e.liftCoborder.base x₀)) :=
      (AlgebraicGeometry.IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
    have hsurj : Function.Surjective
        (⇑(e.coborderRange.ι.stalkMap (e.liftCoborder.base x₀)).hom ∘
          ⇑((Z.presheaf.stalkCongr (Inseparable.of_eq hpt₁)).hom).hom) :=
      (ConcreteCategory.bijective_of_isIso _).2.comp (ConcreteCategory.bijective_of_isIso _).2
    exact h3.of_comp_right hsurj
  have hKz : e.liftCoborder.ker.stalkIdeal (e.liftCoborder.base x₀) = ⊥ := by
    have hti : e.liftCoborder.toImage ≫ e.liftCoborder.imageι = e.liftCoborder :=
      Scheme.Hom.toImage_imageι _
    have hpt₂ : e.liftCoborder.base x₀ = (e.liftCoborder.toImage ≫ e.liftCoborder.imageι).base x₀ :=
      congrArg (fun φ : E ⟶ e.coborderRange => φ.base x₀) hti.symm
    have h := Scheme.Hom.stalkMap_congr_hom _ _ hti.symm x₀
    rw [Scheme.Hom.stalkMap_comp] at h
    have h4 := hinj_e₁
    rw [h] at h4
    change Function.Injective (⇑(e.liftCoborder.toImage.stalkMap x₀).hom ∘
      ⇑((e.coborderRange.toScheme.presheaf.stalkCongr (Inseparable.of_eq hpt₂)).hom ≫
        e.liftCoborder.imageι.stalkMap (e.liftCoborder.toImage.base x₀)).hom) at h4
    have h5 : Function.Injective
        (⇑(e.liftCoborder.imageι.stalkMap (e.liftCoborder.toImage.base x₀)).hom ∘
          ⇑((e.coborderRange.toScheme.presheaf.stalkCongr (Inseparable.of_eq hpt₂)).hom).hom) :=
      h4.of_comp
    have h6 : Function.Injective
        (e.liftCoborder.imageι.stalkMap (e.liftCoborder.toImage.base x₀)).hom :=
      h5.of_comp_right (ConcreteCategory.bijective_of_isIso _).2
    rw [RingHom.injective_iff_ker_eq_bot, ker_stalkMap_subschemeι] at h6
    have hpt₃ : e.liftCoborder.imageι.base (e.liftCoborder.toImage.base x₀) =
        e.liftCoborder.base x₀ :=
      congrArg (fun φ : E ⟶ e.coborderRange => φ.base x₀) hti
    rw [hpt₃] at h6
    exact h6
  -- the kernel vanishes on an open neighbourhood
  have : IsLocallyNoetherian e.coborderRange :=
    LocallyOfFiniteType.isLocallyNoetherian e.coborderRange.ι
  obtain ⟨V₂, hzV₂, hV₂⟩ := exists_comap_eq_of_stalkIdeal_eq e.liftCoborder.ker ⊥
    (e.liftCoborder.base x₀) (by rw [hKz, stalkIdeal_bot])
  rw [comap_bot] at hV₂
  -- over `V₂` the closed immersion is an isomorphism, so `V₂ ⟶ coborder(E)` factors through `E`
  have hisoV : IsIso (pullback.fst V₂.ι e.liftCoborder) := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ker_fst_of_isClosedImmersion]
    exact hV₂
  have hV₂ι : V₂.ι = inv (pullback.fst V₂.ι e.liftCoborder) ≫
      pullback.snd V₂.ι e.liftCoborder ≫ e.liftCoborder := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  refine ⟨V₂.toScheme, V₂.ι ≫ e.coborderRange.ι, inferInstance, ⟨⟨_, hzV₂⟩, ?_⟩, ?_⟩
  · have h6 : (e.liftCoborder ≫ e.coborderRange.ι).base x₀ = z := by rw [he₁]; exact hex₀
    exact h6
  · rw [hV₂ι]
    simp only [Category.assoc, Scheme.Hom.liftCoborder_ι_assoc, hcond]

end Auxiliary

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The maximal-adic completion of a local ring ([Kol07, Definition 55]). -/
local notation "Ô(" R ")" => AdicCompletion (maximalIdeal R) R

/-- Kollár's "(91.1′–4′) also hold in an open neighborhood `U(p) ∋ (p, p)` by (55)" ([Kol07, 95]),
for the condition (4′): for an étale neighbourhood pair `Q` of `p` and an ideal sheaf `M` on `W`,
if `ψ̂^*(x) − ψ̂'^*(x) ∈ M̂_q` for every `x ∈ Ô_{X,p}`, then there is an open `V ∋ q` on which `ψ`
and `ψ'` agree on the closed subscheme `V(M|_V)` (`AgreeOn`). Faithful flatness descends the
hypothesis to the stalk; the two composites `V(M) ⇉ X` then agree on the stalk at the point over
`q`, so `q` lies in their equalizer with an isomorphic stalk there, and the equalizer contains an
open neighbourhood of `q` in `V(M)` because `W` is locally Noetherian
(`exists_openImmersion_comp_eq_of_lift`). -/
theorem exists_agreeOn_of_forall_completionMap_sub_mem [LocallyOfFiniteType f] {p : X}
    (Q : EtaleNbhdPair X p) (M : Q.W.IdealSheafData)
    (h : ∀ x : Ô(X.presheaf.stalk p),
      completionMap Q.stalkHom x - completionMap Q.stalkHom' x ∈ M.completionIdeal Q.q) :
    ∃ V : Q.W.Opens, Q.q ∈ V ∧ AgreeOn (V.ι ≫ Q.ψ) (V.ι ≫ Q.ψ') (M.comap V.ι) := by
  classical
  have hX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hW : IsLocallyNoetherian Q.W := LocallyOfFiniteType.isLocallyNoetherian Q.ψ
  -- (1) descent to the stalk: `ψ^*(s) − ψ'^*(s) ∈ M_q`
  have hst : ∀ s : X.presheaf.stalk p, Q.stalkHom s - Q.stalkHom' s ∈ M.stalkIdeal Q.q := by
    intro s
    have h1 := h (algebraMap _ _ s)
    rw [completionMap_algebraMap, completionMap_algebraMap, ← map_sub, completionIdeal_eq] at h1
    have h2 : (Ideal.span {Q.stalkHom s - Q.stalkHom' s}).map
        (algebraMap _ Ô(Q.W.presheaf.stalk Q.q)) ≤ (M.stalkIdeal Q.q).map (algebraMap _ _) := by
      rw [Ideal.map_span, Set.image_singleton]
      exact (Ideal.span_singleton_le_iff_mem _).mpr h1
    exact (Ideal.span_singleton_le_iff_mem _).mp (map_adicCompletion_le_iff.mp h2)
  by_cases hq : Q.q ∈ (M.support : Set Q.W)
  · -- `q ∈ V(M)`: the equalizer argument on `Z = V(M)`
    obtain ⟨z, hz⟩ : Q.q ∈ Set.range M.subschemeι := by rw [range_subschemeι]; exact hq
    have hZ : IsLocallyNoetherian M.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian M.subschemeι
    -- the two composites agree on the stalk at `z`, hence on `Spec 𝒪_{Z,z}`
    have hgz : (M.subschemeι ≫ Q.ψ).base z = p := by rw [Scheme.Hom.comp_apply, hz, Q.ψ_q]
    have hgz' : (M.subschemeι ≫ Q.ψ').base z = p := by rw [Scheme.Hom.comp_apply, hz, Q.ψ'_q]
    have hcomm : M.subscheme.fromSpecStalk z ≫ (M.subschemeι ≫ Q.ψ) =
        M.subscheme.fromSpecStalk z ≫ (M.subschemeι ≫ Q.ψ') := by
      refine fromSpecStalk_comp_eq_of_stalkMap_eq _ _ z hgz hgz' fun s => ?_
      -- transport `Q.stalkHom s` from `q` to `ι_Z z` and apply the stalk map of `ι_Z`
      have key : ∀ (ψ : Q.W ⟶ X) (hψ : ψ.base Q.q = p) (hψz : (M.subschemeι ≫ ψ).base z = p),
          ((M.subschemeι ≫ ψ).stalkMap z).hom
              ((X.presheaf.stalkCongr (Inseparable.of_eq hψz.symm)).hom s) =
            (M.subschemeι.stalkMap z).hom
              ((Q.W.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom
                ((ψ.stalkMap Q.q).hom
                  ((X.presheaf.stalkCongr (Inseparable.of_eq hψ.symm)).hom s))) := by
        intro ψ hψ hψz
        rw [Scheme.Hom.stalkMap_comp]
        change (M.subschemeι.stalkMap z).hom ((ψ.stalkMap (M.subschemeι.base z)).hom
          ((X.presheaf.stalkCongr (Inseparable.of_eq hψz.symm)).hom s)) = _
        congr 1
        have hnat := congrArg
          (fun φ => φ.hom ((X.presheaf.stalkCongr (Inseparable.of_eq hψ.symm)).hom s))
          (Scheme.Hom.stalkMap_congr_point ψ Q.q (M.subschemeι.base z) hz.symm)
        change (Q.W.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom
            ((ψ.stalkMap Q.q).hom ((X.presheaf.stalkCongr (Inseparable.of_eq hψ.symm)).hom s)) =
          (ψ.stalkMap (M.subschemeι.base z)).hom
            ((X.presheaf.stalkCongr (Inseparable.of_eq (congrArg ψ.base hz.symm))).hom
              ((X.presheaf.stalkCongr (Inseparable.of_eq hψ.symm)).hom s)) at hnat
        rw [hnat]
        congr 1
        have hcomp : X.presheaf.stalkCongr (Inseparable.of_eq hψ.symm) ≪≫
            X.presheaf.stalkCongr (Inseparable.of_eq (congrArg ψ.base hz.symm)) =
            X.presheaf.stalkCongr (Inseparable.of_eq hψz.symm) := by
          ext1
          simp only [Iso.trans_hom, TopCat.Presheaf.stalkCongr_hom]
          exact TopCat.Presheaf.stalkSpecializes_comp X.presheaf _ _
        exact (congrArg (fun φ : X.presheaf.stalk p ≅ _ => φ.hom s) hcomp).symm
      rw [key Q.ψ Q.ψ_q hgz, key Q.ψ' Q.ψ'_q hgz']
      -- the difference lies in `M_{ι_Z z}`, the kernel of the stalk map of `ι_Z`
      have hmem : (Q.W.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom
            ((Q.ψ.stalkMap Q.q).hom
              ((X.presheaf.stalkCongr (Inseparable.of_eq Q.ψ_q.symm)).hom s)) -
          (Q.W.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom
            ((Q.ψ'.stalkMap Q.q).hom
              ((X.presheaf.stalkCongr (Inseparable.of_eq Q.ψ'_q.symm)).hom s)) ∈
          M.stalkIdeal (M.subschemeι.base z) := by
        rw [← map_sub, ← stalkIdeal_map_stalkCongr M hz.symm]
        exact Ideal.mem_map_of_mem _ (hst s)
      rw [← ker_stalkMap_subschemeι, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
      exact hmem
    -- the open immersion through `z` on which the composites agree
    obtain ⟨T, j, hj, ⟨t, ht⟩, hjg⟩ := exists_openImmersion_comp_eq_of_lift
      (equalizer.ι (M.subschemeι ≫ Q.ψ) (M.subschemeι ≫ Q.ψ')) _ _ (equalizer.condition _ _) z
      (equalizer.lift _ hcomm) (equalizer.lift_ι _ _)
    -- its image is the trace on `V(M)` of an open `V ⊆ W`
    obtain ⟨U, hUo, hUpre⟩ := M.subschemeι.isEmbedding.isInducing.isOpen_iff.mp
      j.isOpenEmbedding.isOpen_range
    refine ⟨⟨U, hUo⟩, ?_, ?_⟩
    · rw [← hz]
      change M.subschemeι.base z ∈ U
      rw [← Set.mem_preimage, hUpre]
      exact ⟨t, ht⟩
    · -- the subscheme `V(M|_V)` maps into `range j`
      have hsq :=
        (isPullback_subschemeι_comap M (Scheme.Opens.ι (⟨U, hUo⟩ : Q.W.Opens))).w
      have hrange : Set.range (subschemeMap (M.comap (Scheme.Opens.ι (⟨U, hUo⟩ : Q.W.Opens))) M
          (Scheme.Opens.ι (⟨U, hUo⟩ : Q.W.Opens)) (le_map_comap M _)) ⊆ Set.range j := by
        rintro _ ⟨y, rfl⟩
        rw [← hUpre, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
        exact Scheme.Opens.ι_mem (U := ⟨U, hUo⟩) _
      have hfac := IsOpenImmersion.lift_fac j _ hrange
      change (M.comap (Scheme.Opens.ι (⟨U, hUo⟩ : Q.W.Opens))).subschemeι ≫
          Scheme.Opens.ι (⟨U, hUo⟩ : Q.W.Opens) ≫ Q.ψ =
        (M.comap (Scheme.Opens.ι (⟨U, hUo⟩ : Q.W.Opens))).subschemeι ≫
          Scheme.Opens.ι (⟨U, hUo⟩ : Q.W.Opens) ≫ Q.ψ'
      have h1 : (M.comap (Scheme.Opens.ι (⟨U, hUo⟩ : Q.W.Opens))).subschemeι ≫
          Scheme.Opens.ι (⟨U, hUo⟩ : Q.W.Opens) = IsOpenImmersion.lift j _ hrange ≫
            (j ≫ M.subschemeι) := by
        rw [← Category.assoc, hfac, ← hsq]
      rw [← Category.assoc, ← Category.assoc, h1]
      simp only [Category.assoc]
      rw [hjg]
  · -- `q ∉ V(M)`: the complement of `V(M)` is the neighbourhood, on which `V(M|_V) = ∅`
    refine ⟨⟨(M.support : Set Q.W)ᶜ, M.support.isClosed.isOpen_compl⟩, hq, ?_⟩
    have hcomap : M.comap (Scheme.Opens.ι
        (⟨(M.support : Set Q.W)ᶜ, M.support.isClosed.isOpen_compl⟩ : Q.W.Opens)) = ⊤ := by
      rw [← support_eq_bot_iff, support_comap]
      refine Closeds.ext ?_
      rw [Closeds.coe_preimage, Closeds.coe_bot, Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact Scheme.Opens.ι_mem x hx
    rw [hcomap]
    exact agreeOn_top _ _

end AlgebraicGeometry.Scheme.IdealSheafData
