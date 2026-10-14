/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAdmissibleStratum
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealInf
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4NewCoords
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Tools
import Hironaka.Resolution.Algebraic.Wlo05.OffCentreTransport
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.TotalTransformOnCentre
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The sheaf forms of one blow-up along an admissible chain stratum

The statement CP4 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`;
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4`) in the form that CP6 consumes: with `I = Γ ⊓ K`
(or `I = (⨅ γ ∈ Γs, γ) ⊓ K` for pairwise disjoint protected components), the mark-`1` transform of
`I` along the blow-up of an admissible chain stratum is the meet of the strict transform(s) with the
mark-`1` transform of `K`, as ideal sheaves on the whole blow-up.

**The proof.** Ideal sheaves are compared stalk by stalk (`ext_stalkIdeal`). At `q` over `p ∉ Γ`
both sides are the mark-`1` transform of `K` (`I_p = K_p`, the locality of the marked transform,
and `Γ̃_q = 𝒪`). At `q` over `p ∈ Γ` off the exceptional divisor everything is the image under the
stalk isomorphism `π^*`, which preserves meets. At `q ∈ F` over `p ∈ Z ∩ Γ` the K-shape of `K_p`
and the intersection form `span_mul_chainIdeal_eq_span_inf` of
`Hironaka.Resolution.Algebraic.Wlo05.ChainIdealInf` give `I_p` its un-isolated form; the chart
computation of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4` transports both forms to `q`; if `q
∈ Γ̃`, the intersection form at `q` in the new parameters is the identity; if `q ∉ Γ̃` some
transported chain equation is a unit at `q` (the charts of the chain equations, and the points off
`Γ̃` of the charts of the members), and `chainIdeal_eq_chainKIdeal_of_isUnit` gives `Ĩ_q = K̃_q`
while `Γ̃_q = 𝒪`. For the finset form the meet of the members has, at every point, the stalk of the
one member through it or `𝒪` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Tools`), on `X` and on
the blow-up (strict transforms of disjoint members are disjoint). The chart is that of [Kol07,
Definition 60]. These statements are not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Stage`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Ideal Scheme.IdealSheafData
  Scheme BlowUpSequence IdealSheafData

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-! ### The pointwise identity -/

section Pointwise

variable {k : Type u} [Field k] [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f]
  (E : DivisorFamily X) (Γ K Z : X.IdealSheafData)

/-- Off `Γ` the mark-`1` transform of `Γ ⊓ K` is that of `K`. -/
theorem stalkIdeal_markedTransform_inf_of_notMem [IsLocallyNoetherian X] {q : blowUp Z}
    (hp : blowUpπ Z q ∉ Γ.support) :
    ((Γ ⊓ K).markedTransform Z 1).stalkIdeal q = (K.markedTransform Z 1).stalkIdeal q :=
  stalkIdeal_markedTransform_eq_of_stalkIdeal_eq Z (Γ ⊓ K) K 1
    (by rw [stalkIdeal_inf, stalkIdeal_eq_top_of_notMem_support _ hp, top_inf_eq])

/-- The image of a meet under the stalk isomorphism off the exceptional divisor. -/
theorem map_inf_stalkMapπEquiv {q : blowUp Z} (hq : q ∉ (Z.comap (blowUpπ Z)).support)
    (A B : Ideal (X.presheaf.stalk (blowUpπ Z q))) :
    (A ⊓ B).map ((blowUpπ Z).stalkMap q).hom =
      A.map ((blowUpπ Z).stalkMap q).hom ⊓ B.map ((blowUpπ Z).stalkMap q).hom := by
  have hiso := isIso_stalkMap_π_of_notMem_support Z hq
  have he : ((blowUpπ Z).stalkMap q).hom = (stalkMapπEquiv Z hq : _ →+* _) := rfl
  rw [he, Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv,
    Ideal.comap_inf]

include f in
/-- **The pointwise sheaf identity at a point over `Γ`**: for `p ∈ Γ`, with the K-shape of `K` at
`p` and admissibility at `p` when `p ∈ Z`, and the snc data of `Z` along `Z ∩ Γ` (for the
regularity of the stalks of the blow-up). -/
theorem stalkIdeal_markedTransform_inf_of_mem {q : blowUp Z}
    (hpΓ : blowUpπ Z q ∈ Γ.support)
    (hZ : ∀ p ∈ Z.support ⊓ Γ.support, AdmissibleChainStratumKAt E K Γ Z p) :
    ((Γ ⊓ K).markedTransform Z 1).stalkIdeal q =
      (Γ.strictTransform Z).stalkIdeal q ⊓ (K.markedTransform Z 1).stalkIdeal q := by
  classical
  by_cases hq : q ∈ (Z.comap (blowUpπ Z)).support
  · -- on the exceptional divisor: the chart
    have hpZ : blowUpπ Z q ∈ Z.support := (mem_support_comap_iff' Z _ q).mp hq
    have hreg : IsRegularLocalRing ((blowUp Z).presheaf.stalk q) :=
      isRegularLocalRing_stalk_blowUp_of_sncDataWith E Γ Z f hq hpΓ fun x hx hxΓ =>
        sncDataWith_of_admissibleK E Γ Z (hZ x (mem_inf_support hx hxΓ))
    have hregp : IsRegularLocalRing (X.presheaf.stalk (blowUpπ Z q)) :=
      isRegularLocalRing_stalk f _
    obtain ⟨n, z, c, r, σ, a, b, l, hl, s, hcoords, hb, hKp, hs, hZp, h₁, h₂⟩ :=
      hZ _ (mem_inf_support hpZ hpΓ)
    obtain ⟨hz, hcinj, hc, hσinj, hσc, ha, hΓ⟩ := id hcoords
    have hσs : ∀ i, σ i ∉ s := σ_notMem_of_subset_range hσc hs
    have hb' : ∀ k, b k ≠ 0 → k ∉ Set.range σ := notMem_range_of_ne_zero hσc hb
    have ha' : ∀ i k, a i k ≠ 0 → k ∉ Set.range σ := fun i => notMem_range_of_ne_zero hσc (ha i)
    have hb'' : ∀ k, k ∈ Set.range σ → b k = 0 := fun k hk => by
      by_contra h; exact hb' k h hk
    have ha'' : ∀ i k, k ∈ Set.range σ → a i k = 0 := fun i k hk => by
      by_contra h; exact ha' i k h hk
    -- the un-isolated form of `(Γ ⊓ K)_p` (the intersection form)
    have hIp : (Γ ⊓ K).stalkIdeal (blowUpπ Z q) =
        span {monomialOf z b} * chainIdeal (z ∘ σ) fun i => monomialOf z (a i) := by
      rw [stalkIdeal_inf, hΓ, hKp, span_mul_chainIdeal_eq_span_inf hz ha'' b hb'']
    have hZC : Z.stalkIdeal (blowUpπ Z q) = span (z '' ↑(stratumCoords σ s l)) :=
      hZp.trans (span_image_comp_sup_eq σ s z l)
    obtain ⟨D⟩ := nonempty_chartAt Z q f hz (stratumCoords σ s l) hZC
    have hδ : ∀ i, δAdm l i = if σ i ∈ stratumCoords σ s l then 1 else 0 :=
      fun i => (δAdm_eq σ s hσinj hσs l i).symm
    -- along an admissible stratum the last chain equation is not an equation of the centre
    have hδK : Function.update (δAdm l) (Fin.last r) 0 = δAdm l := by
      funext i
      by_cases hi : i = Fin.last r
      · subst hi
        rw [Function.update_self, δAdm, ite_eq_right (by simp only [Fin.val_last]; omega)]
      · rw [Function.update_of_ne hi]
    have hposI := one_le_epsOrderC_I σ s a b hb' l h₁
    have hmonoI := epsOrderC_I_mono σ s a b ha' l hl h₂
    have hposK := one_le_epsOrderC_K σ s a b hb' l hl h₁
    have hmonoK := epsOrderC_K_mono σ s a b ha' l hl h₂
    by_cases hqΓ : q ∈ (Γ.strictTransform Z).support
    · -- on `Γ̃`: both forms in the new parameters, then the intersection form at `q`
      have hσc₀ := D.σ_ne_c₀ Γ σ hΓ hqΓ
      have hmem := (D.w_σ_mem_and_stalkIdeal_strictTransform Γ σ hq hΓ hqΓ).1
      have hcc := D.chainCoords_totalTransform E Γ c σ a hq hcoords hqΓ
        (Dexp (epsOrderC (stratumCoords σ s l) a b (δAdm l)))
      obtain ⟨hz', -, -, hσinj', hσc', ha''', hΓ'⟩ := hcc
      rw [D.stalkIdeal_markedTransform_chainIdeal σ a hq hσc₀ hmem b (Γ ⊓ K) hIp (δAdm l) hδ hposI
        hmonoI _ (fun i => Dexp_castSucc _ i)]
      have hK' := D.stalkIdeal_markedTransform_chainKIdeal σ a hq hσc₀ hmem b K hKp (δAdm l) hδ
        hposK hmonoK _ (fun i => Dexp_castSucc _ i)
      rw [hδK] at hK'
      rw [hK', hΓ']
      exact span_mul_chainIdeal_eq_span_inf hz' (fun i k' hk' => by
          by_contra h
          obtain ⟨j', hj'⟩ := ha''' i k' h
          obtain ⟨i', rfl⟩ := hk'
          exact hσc' i' j' hj'.symm) _
        (fun k' hk' => by
          by_contra h
          obtain ⟨j', hj'⟩ := D.newExp_support E c hq hz hc _ _ hb k' h
          obtain ⟨i', rfl⟩ := hk'
          exact hσc' i' j' hj'.symm)
    · -- off `Γ̃`: a transported chain equation is a unit (`chainIdeal_eq_chainKIdeal_of_isUnit`)
      rw [stalkIdeal_eq_top_of_notMem_support _ hqΓ, top_inf_eq, markedTransform_one_eq,
        markedTransform_one_eq,
        D.stalkIdeal_controlledTransformAlong_chainIdeal σ a b (Γ ⊓ K) hIp (δAdm l) hδ hposI hmonoI
          _ (fun i => Dexp_castSucc _ i),
        D.stalkIdeal_controlledTransformAlong_chainKIdeal σ a b K hKp (δAdm l) hδ hposK hmonoK
          _ (fun i => Dexp_castSucc _ i), hδK]
      -- some `ŵ (σ i)` is a unit
      have hunit : ∃ i, IsUnit (D.wHat (σ i)) := by
        by_contra hno
        push Not at hno
        apply hqΓ
        have hσc₀ : ∀ i, σ i ≠ D.c₀ := fun i h => hno i (by
          rw [ChartAt.wHat, h, Function.update_self]; exact isUnit_one)
        have hmem : ∀ i, D.w (σ i) ∈ maximalIdeal ((blowUp Z).presheaf.stalk q) := fun i =>
          by_contra fun h => hno i (by rw [D.wHat_of_ne (hσc₀ i)]; exact D.isUnit_w_of_notMem h)
        rw [mem_support_iff_stalkIdeal_le_maximalIdeal (I := _) (x := q),
          strictTransform_eq_strictTransformAlong,
          D.stalkIdeal_strictTransformAlong_eq_span_range_of_mem hq σ hσc₀ Γ hΓ hmem, span_le]
        rintro _ ⟨i, rfl⟩
        exact hmem i
      obtain ⟨i₀, hu⟩ := hunit
      rw [chainIdeal_eq_chainKIdeal_of_isUnit _ _ hu]
  · -- off the exceptional divisor: the stalk isomorphism
    rw [stalkIdeal_markedTransform_one_of_notMem Z hq,
      stalkIdeal_markedTransform_one_of_notMem Z hq,
      stalkIdeal_strictTransform_eq_map_of_notMem Z hq, stalkIdeal_inf, map_inf_stalkMapπEquiv Z hq]

/-- Disjoint members have disjoint strict transforms (the strict transform lies over the member). -/
theorem disjoint_strictTransform_support_of_disjoint (Z a b : X.IdealSheafData)
    (h : Disjoint a.support b.support) :
    Disjoint (a.strictTransform Z).support (b.strictTransform Z).support :=
  disjoint_closeds_iff.mpr fun q hq hq' => notMem_of_disjoint_closeds h
    (π_mem_support_of_mem_support_strictTransformAlong Z a q hq)
    (π_mem_support_of_mem_support_strictTransformAlong Z b q hq')

end Pointwise

/-! ### The two sheaf identities -/

section Main

variable {k : Type u} [Field k] [CharZero k]

/-- **The single-blow-up sheaf form of CP4 for the pair `(I, K)`**: with `I = Γ ⊓ K` on `X`, `K` in
the K-shape along `Γ`, `Z` admissible at every point of `Z ∩ Γ`, and the order condition `K ≤ Z`
of the run (a GLOBAL condition needed off `Γ`; not the admissibility condition (★)), the mark-`1`
transform of `I` is the intersection of the strict transform of `Γ` with the mark-`1` transform of
`K`, as ideal sheaves on the whole blow-up. -/
theorem markedTransform_inf_of_admissible (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (E : DivisorFamily X) (I K Γ Z : X.IdealSheafData) (hE : E.IsSnc) (hΓ : E.HasSncWith Γ)
    (hsm : Smooth (Γ.subschemeι ≫ f)) (hI : I = Γ ⊓ K)
    (hK : ∀ p ∈ Γ.support, ChainRelativeKAt E K Γ p)
    (hZ : ∀ p ∈ Z.support ⊓ Γ.support, AdmissibleChainStratumKAt E K Γ Z p) (hKZ : K ≤ Z) :
    I.markedTransform Z 1 = Γ.strictTransform Z ⊓ K.markedTransform Z 1 := by
  have _hE := hE
  have _hΓ := hΓ
  have _hsm := hsm
  have _hKZ := hKZ
  have _hK := hK
  have : PerfectField k := PerfectField.ofCharZero
  have hLN : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hLN' : IsLocallyNoetherian (blowUp Z) := blowUp.isLocallyNoetherian Z
  subst hI
  refine ext_stalkIdeal fun q => ?_
  rw [stalkIdeal_inf]
  by_cases hp : blowUpπ Z q ∈ Γ.support
  · exact stalkIdeal_markedTransform_inf_of_mem f E Γ K Z hp hZ
  · rw [stalkIdeal_markedTransform_inf_of_notMem Γ K Z hp,
      stalkIdeal_strictTransform_eq_top_of_notMem Z Γ hp, top_inf_eq]

/-- **The finset form of the sheaf identity** (the blow-up step of CP6 for the SET of protected
components): with `I = (⨅ γ ∈ Γs, γ) ⊓ K`, pairwise disjoint protected components `Γs`, each
`K`-admissible along `Z`, and `K ≤ Z`, the mark-`1` transform of `I` is the meet of the strict
transforms with the mark-`1` transform of `K`. -/
theorem markedTransform_biInf_inf_of_admissible
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (E : DivisorFamily X)
    (I K Z : X.IdealSheafData) (Γs : Finset X.IdealSheafData) (hE : E.IsSnc)
    (hΓ : ∀ γ ∈ Γs, E.HasSncWith γ) (hsm : ∀ γ ∈ Γs, Smooth (γ.subschemeι ≫ f))
    (hdisj : (↑Γs : Set X.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support)
    (hI : I = (⨅ γ ∈ Γs, γ) ⊓ K) (hK : ∀ γ ∈ Γs, ∀ p ∈ γ.support, ChainRelativeKAt E K γ p)
    (hZ : ∀ γ ∈ Γs, ∀ p ∈ Z.support ⊓ γ.support, AdmissibleChainStratumKAt E K γ Z p)
    (hKZ : K ≤ Z) :
    I.markedTransform Z 1 = (⨅ γ ∈ Γs, γ.strictTransform Z) ⊓ K.markedTransform Z 1 := by
  have _hE := hE
  have _hΓ := hΓ
  have _hsm := hsm
  have _hKZ := hKZ
  have _hK := hK
  have : PerfectField k := PerfectField.ofCharZero
  have hLN : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hLN' : IsLocallyNoetherian (blowUp Z) := blowUp.isLocallyNoetherian Z
  have hdisj' : (↑Γs : Set X.IdealSheafData).Pairwise fun a b =>
      Disjoint (a.strictTransform Z).support (b.strictTransform Z).support :=
    fun a ha b hb hab => disjoint_strictTransform_support_of_disjoint Z a b (hdisj ha hb hab)
  subst hI
  refine ext_stalkIdeal fun q => ?_
  rw [stalkIdeal_inf]
  by_cases hp : ∃ γ ∈ Γs, blowUpπ Z q ∈ γ.support
  · obtain ⟨γ, hγ, hpγ⟩ := hp
    have hIp : ((⨅ γ ∈ Γs, γ) ⊓ K).stalkIdeal (blowUpπ Z q) =
        (γ ⊓ K).stalkIdeal (blowUpπ Z q) := by
      rw [stalkIdeal_inf, stalkIdeal_inf,
        stalkIdeal_biInf_eq_of_mem_of_pairwise_disjoint Γs (fun γ => γ) hdisj hγ hpγ]
    rw [stalkIdeal_markedTransform_eq_of_stalkIdeal_eq Z _ (γ ⊓ K) 1 hIp,
      stalkIdeal_markedTransform_inf_of_mem f E γ K Z hpγ (hZ γ hγ)]
    by_cases hqγ : q ∈ (γ.strictTransform Z).support
    · rw [stalkIdeal_biInf_eq_of_mem_of_pairwise_disjoint Γs (fun γ => γ.strictTransform Z)
        hdisj' hγ hqγ]
    · rw [stalkIdeal_eq_top_of_notMem_support _ hqγ,
        stalkIdeal_biInf_eq_top_of_forall_notMem Γs (fun γ => γ.strictTransform Z)
          fun γ' hγ' hq' => ?_]
      have hpγ' := π_mem_support_of_mem_support_strictTransformAlong Z γ' q hq'
      by_cases hγγ : γ' = γ
      · exact hqγ (hγγ ▸ hq')
      · exact notMem_of_disjoint_closeds (hdisj hγ' hγ hγγ) hpγ' hpγ
  · push Not at hp
    have hIp : ((⨅ γ ∈ Γs, γ) ⊓ K).stalkIdeal (blowUpπ Z q) = K.stalkIdeal (blowUpπ Z q) := by
      rw [stalkIdeal_inf, stalkIdeal_biInf_eq_top_of_forall_notMem Γs (fun γ => γ) hp, top_inf_eq]
    rw [stalkIdeal_markedTransform_eq_of_stalkIdeal_eq Z _ K 1 hIp,
      stalkIdeal_biInf_eq_top_of_forall_notMem Γs (fun γ => γ.strictTransform Z)
        fun γ hγ hq => hp γ hγ (π_mem_support_of_mem_support_strictTransformAlong Z γ q hq),
      top_inf_eq]

end Main

end Hironaka.Resolution
