/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquiv
public import Hironaka.Scheme.Smooth.Graph
public import Hironaka.Scheme.BlowUp.GlueIdealSheaf
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Smooth.EtaleCoverFinite
import Hironaka.Scheme.Smooth.GraphComponent
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The disjoint union of the étale neighbourhoods

Kollár ends the proof of Theorem 92 ([Kol07, 95]) by covering `X` with the images of finitely many
of the neighbourhoods `U(p)`: "We can take `U` to be their disjoint union." Given, for every
closed point `p` of the
cosupport `cosupp(I, m) = {x | m ≤ ord_x I}`, an étale neighbourhood pair `ψₚ, ψₚ' : Wₚ ⇉ X` over
`k` and an open `Vₚ ∋ qₚ` on which (1′)–(4′) hold
(`Hironaka/Resolution/Algebraic/MaximalContact/EtaleNbhdConditions.lean`), the disjoint union `U :=
∐ Vₚ` with `ψ := ∐ ψₚ|_{Vₚ}` and `ψ' := ∐ ψₚ'|_{Vₚ}` is an étale equivalence of `H` and `H'` with
respect to `(X, I, E)` (`EtaleEquiv`):

* the images cover the cosupport (`subset_iUnion_range_ι_comp_ψ`): étale maps are open and every
  point of the closed cosupport specializes to a closed point;
* the coproduct maps are étale and the pair is `EtaleImagePair.sigma`;
* (1′)–(3′) descend from the summands because an ideal sheaf on a coproduct is determined by its
  restrictions to the summands (`ext_of_openCover` with `sigmaOpenCover`), and `MC` commutes with
  the étale `ψ` and with the open immersions `Sigma.ι` ([Kol07, Lemma 74 (4)],
  `MC_comap_of_etale`);
* (4′) descends because the closed subscheme `V(MC(ψ^*I))` of the coproduct is covered by its
  traces on the summands (`AlgebraicGeometry.isPullback_subschemeι_comap`, `Scheme.Cover.hom_ext`).

Finiteness of the cover (Kollár's varieties are quasi-compact) plays no part here: the coproduct
is taken over all closed points of the cosupport, an index type in `Type u`. The finite, affine
form is `Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquivAffine.lean`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory CategoryTheory.Limits TopologicalSpace Scheme AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Kollár's "we can take `U` to be their disjoint union" ([Kol07, 95]), as a construction: a
family of étale pairs `ψᵢ, ψᵢ' : Wᵢ ⇉ X` over `k` whose images each cover the cosupport
`cosupp(I, m)` and which satisfy (1′)–(4′) summand by summand assembles to the étale equivalence
`∐ ψᵢ, ∐ ψᵢ' : ∐ Wᵢ ⇉ X` of `H` and `H'` with respect to `(X, I, E)` on the coproduct `∐ Wᵢ`
(`etaleEquivOfFamily_U`). The construction is needed, rather than the mere existence
`nonempty_etaleEquiv_of_family`, where the scheme of the equivalence matters (its affineness in
`Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquivAffine.lean`). -/
noncomputable def etaleEquivOfFamily [Smooth f] (I : X.IdealSheafData) (m : ℕ)
    (E : DivisorFamily X) (H H' : X.IdealSheafData) {ι : Type u} (W : ι → Scheme.{u})
    (ψ ψ' : ∀ i, W i ⟶ X) [∀ i, Etale (ψ i)] [∀ i, Etale (ψ' i)]
    (hcov : {x | (m : ℕ∞) ≤ I.ord x} ⊆ ⋃ i, Set.range (ψ i).base)
    (hcov' : {x | (m : ℕ∞) ≤ I.ord x} ⊆ ⋃ i, Set.range (ψ' i).base)
    (hf : ∀ i, ψ i ≫ f = ψ' i ≫ f)
    (h1 : ∀ i, H.comap (ψ i) = H'.comap (ψ' i)) (h2 : ∀ i, I.comap (ψ i) = I.comap (ψ' i))
    (h3 : ∀ i j, (E.component j).comap (ψ i) = (E.component j).comap (ψ' i))
    (h4 : ∀ i, AgreeOn (ψ i) (ψ' i) (MC (ψ i ≫ f) (I.comap (ψ i)) m)) :
    EtaleEquiv f I m E H H' := by
  classical
  have hdesc : Etale (Sigma.desc ψ) := IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  have hι : ∀ i, Sigma.ι W i ≫ Sigma.desc ψ = ψ i := fun i => Sigma.ι_comp_desc _ _
  have hι' : ∀ i, Sigma.ι W i ≫ Sigma.desc ψ' = ψ' i := fun i => Sigma.ι_comp_desc _ _
  refine EtaleEquiv.mk (EtaleImagePair.sigma W ψ ψ' hcov hcov') ?_ ?_ ?_ ?_ ?_
  · change Sigma.desc ψ ≫ f = Sigma.desc ψ' ≫ f
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, hι, ← Category.assoc, hι', hf]
  · change H.comap (Sigma.desc ψ) = H'.comap (Sigma.desc ψ')
    refine ext_of_openCover (sigmaOpenCover W) fun (i : ι) => ?_
    change (H.comap (Sigma.desc ψ)).comap (Sigma.ι W i) =
      (H'.comap (Sigma.desc ψ')).comap (Sigma.ι W i)
    rw [← comap_comp, ← comap_comp, hι, hι', h1]
  · change I.comap (Sigma.desc ψ) = I.comap (Sigma.desc ψ')
    refine ext_of_openCover (sigmaOpenCover W) fun (i : ι) => ?_
    change (I.comap (Sigma.desc ψ)).comap (Sigma.ι W i) =
      (I.comap (Sigma.desc ψ')).comap (Sigma.ι W i)
    rw [← comap_comp, ← comap_comp, hι, hι', h2]
  · intro j
    change (E.component j).comap (Sigma.desc ψ) = (E.component j).comap (Sigma.desc ψ')
    refine ext_of_openCover (sigmaOpenCover W) fun (i : ι) => ?_
    change ((E.component j).comap (Sigma.desc ψ)).comap (Sigma.ι W i) =
      ((E.component j).comap (Sigma.desc ψ')).comap (Sigma.ι W i)
    rw [← comap_comp, ← comap_comp, hι, hι', h3]
  · change AgreeOn (Sigma.desc ψ) (Sigma.desc ψ')
      (MC (Sigma.desc ψ ≫ f) (I.comap (Sigma.desc ψ)) m)
    obtain ⟨M, hM0⟩ : ∃ M : (∐ W).IdealSheafData,
        M = MC (Sigma.desc ψ ≫ f) (I.comap (Sigma.desc ψ)) m := ⟨_, rfl⟩
    rw [← hM0]
    -- the ideal restricted to a summand is `MC(ψᵢ^*I)`
    have hM : ∀ i, M.comap (Sigma.ι W i) = MC (ψ i ≫ f) (I.comap (ψ i)) m := fun i => by
      rw [hM0, MC_comap_of_etale f (Sigma.desc ψ) I m, ← comap_comp, hι,
        MC_comap_of_etale f (ψ i) I m]
    unfold AgreeOn
    refine Scheme.Cover.hom_ext ((sigmaOpenCover W).pullback₁ M.subschemeι) _ _ fun (i : ι) => ?_
    change pullback.fst M.subschemeι (Sigma.ι W i) ≫ M.subschemeι ≫ Sigma.desc ψ =
      pullback.fst M.subschemeι (Sigma.ι W i) ≫ M.subschemeι ≫ Sigma.desc ψ'
    have hP := (isPullback_subschemeι_comap M (Sigma.ι W i)).flip
    have hw := (isPullback_subschemeι_comap M (Sigma.ι W i)).w
    have hw' : ∀ {Y : Scheme.{u}} (φ : (∐ W) ⟶ Y),
        subschemeMap (M.comap (Sigma.ι W i)) M (Sigma.ι W i) (le_map_comap M _) ≫
            M.subschemeι ≫ φ =
          (M.comap (Sigma.ι W i)).subschemeι ≫ Sigma.ι W i ≫ φ := fun φ => by
      rw [← Category.assoc, ← hw, Category.assoc]
    have h4i := h4 i
    unfold AgreeOn at h4i
    rw [← hM i] at h4i
    rw [← hP.isoPullback_inv_fst]
    simp only [Category.assoc]
    rw [hw' (Sigma.desc ψ), hw' (Sigma.desc ψ'), hι, hι', h4i]

/-- The scheme of `etaleEquivOfFamily` is the coproduct `∐ Wᵢ` (definitional). -/
theorem etaleEquivOfFamily_U [Smooth f] (I : X.IdealSheafData) (m : ℕ)
    (E : DivisorFamily X) (H H' : X.IdealSheafData) {ι : Type u} (W : ι → Scheme.{u})
    (ψ ψ' : ∀ i, W i ⟶ X) [∀ i, Etale (ψ i)] [∀ i, Etale (ψ' i)]
    (hcov : {x | (m : ℕ∞) ≤ I.ord x} ⊆ ⋃ i, Set.range (ψ i).base)
    (hcov' : {x | (m : ℕ∞) ≤ I.ord x} ⊆ ⋃ i, Set.range (ψ' i).base)
    (hf : ∀ i, ψ i ≫ f = ψ' i ≫ f)
    (h1 : ∀ i, H.comap (ψ i) = H'.comap (ψ' i)) (h2 : ∀ i, I.comap (ψ i) = I.comap (ψ' i))
    (h3 : ∀ i j, (E.component j).comap (ψ i) = (E.component j).comap (ψ' i))
    (h4 : ∀ i, AgreeOn (ψ i) (ψ' i) (MC (ψ i ≫ f) (I.comap (ψ i)) m)) :
    (etaleEquivOfFamily f I m E H H' W ψ ψ' hcov hcov' hf h1 h2 h3 h4).U = ∐ W :=
  rfl

/-- A family of étale pairs `ψᵢ, ψᵢ' : Wᵢ ⇉ X` over `k` whose images each cover the cosupport
`cosupp(I, m)` and which satisfy (1′)–(4′) summand by summand assembles to an étale equivalence
`∐ ψᵢ, ∐ ψᵢ' : ∐ Wᵢ ⇉ X` of `H` and `H'` with respect to `(X, I, E)` (`etaleEquivOfFamily`). -/
theorem nonempty_etaleEquiv_of_family [Smooth f] (I : X.IdealSheafData) (m : ℕ)
    (E : DivisorFamily X) (H H' : X.IdealSheafData) {ι : Type u} (W : ι → Scheme.{u})
    (ψ ψ' : ∀ i, W i ⟶ X) [∀ i, Etale (ψ i)] [∀ i, Etale (ψ' i)]
    (hcov : {x | (m : ℕ∞) ≤ I.ord x} ⊆ ⋃ i, Set.range (ψ i).base)
    (hcov' : {x | (m : ℕ∞) ≤ I.ord x} ⊆ ⋃ i, Set.range (ψ' i).base)
    (hf : ∀ i, ψ i ≫ f = ψ' i ≫ f)
    (h1 : ∀ i, H.comap (ψ i) = H'.comap (ψ' i)) (h2 : ∀ i, I.comap (ψ i) = I.comap (ψ' i))
    (h3 : ∀ i j, (E.component j).comap (ψ i) = (E.component j).comap (ψ' i))
    (h4 : ∀ i, AgreeOn (ψ i) (ψ' i) (MC (ψ i ≫ f) (I.comap (ψ i)) m)) :
    Nonempty (EtaleEquiv f I m E H H') :=
  ⟨etaleEquivOfFamily f I m E H H' W ψ ψ' hcov hcov' hf h1 h2 h3 h4⟩

section Standing

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

include n in
/-- Kollár's "We can take `U` to be their disjoint union" ([Kol07, 95]), over all closed points:
given, for every closed point `p` of
`cosupp(I, m) = {x | m ≤ ord_x I}`, an étale neighbourhood pair `Qₚ` of `p` over `k` and an open
`Vₚ ∋ qₚ` on which (1′)–(4′) hold for the restricted maps, the disjoint union `U := ∐ Vₚ` with
`ψ := ∐ ψₚ|_{Vₚ}` and `ψ' := ∐ ψₚ'|_{Vₚ}` is an étale equivalence of `H` and `H'` with respect to
`(X, I, E)`: both images contain the cosupport (which is closed), the coproduct maps are étale,
and (1′)–(4′) descend from the summands (`nonempty_etaleEquiv_of_family`). The cover may be
infinite. -/
theorem nonempty_etaleEquiv_of_forall_isClosed (I : X.IdealSheafData) (m : ℕ)
    (E : DivisorFamily X) (H H' : X.IdealSheafData)
    (Q : ∀ p : {p : X // IsClosed ({p} : Set X) ∧ p ∈ {x | (m : ℕ∞) ≤ I.ord x}},
      EtaleNbhdPair X p.1)
    (V : ∀ p, (Q p).W.Opens) (hV : ∀ p, (Q p).q ∈ V p)
    (hf : ∀ p, (Q p).ψ ≫ f = (Q p).ψ' ≫ f)
    (h1 : ∀ p, H.comap ((V p).ι ≫ (Q p).ψ) = H'.comap ((V p).ι ≫ (Q p).ψ'))
    (h2 : ∀ p, I.comap ((V p).ι ≫ (Q p).ψ) = I.comap ((V p).ι ≫ (Q p).ψ'))
    (h3 : ∀ p i, (E.component i).comap ((V p).ι ≫ (Q p).ψ) =
      (E.component i).comap ((V p).ι ≫ (Q p).ψ'))
    (h4 : ∀ p, AgreeOn ((V p).ι ≫ (Q p).ψ) ((V p).ι ≫ (Q p).ψ')
      (MC (((V p).ι ≫ (Q p).ψ) ≫ f) (I.comap ((V p).ι ≫ (Q p).ψ)) m)) :
    Nonempty (EtaleEquiv f I m E H H') := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hS : IsClosed {x | (m : ℕ∞) ≤ I.ord x} := isClosed_setOf_le_ord f n I m
  exact nonempty_etaleEquiv_of_family f I m E H H' (fun p => (V p).toScheme)
    (fun p => (V p).ι ≫ (Q p).ψ) (fun p => (V p).ι ≫ (Q p).ψ')
    (subset_iUnion_range_ι_comp_ψ f hS Q V hV) (subset_iUnion_range_ι_comp_ψ' f hS Q V hV)
    (fun p => by rw [Category.assoc, Category.assoc, hf p]) h1 h2 h3 h4

end Standing

end AlgebraicGeometry.Scheme.IdealSheafData
