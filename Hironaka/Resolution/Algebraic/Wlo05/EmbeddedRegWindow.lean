/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedSmoothWindow
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Reduced
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCoreTools
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Smooth.SubschemeStalk
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The smooth window at a regular point of `Y`, and clause (b) for `BED`

At a point `q` of `Y = V(I)` smooth over `k` the embedded desingularization sequence
`BED(X, I_Y, ∅)` (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) has no centre with a point over `ι
q`: clause (b) of [Wlo05, Theorem 1.0.2] ("all centers `Cᵢ` are disjoint from the set `Reg(Y)`"), in
the stronger form in which the point need not lie on the strict transform of `Y`
(`BED_center_disjoint_reg`).

* `isPrime_stalkIdeal_of_mem_smoothLocus`, `eq_of_specializes_of_mem_smoothLocus`: at a smooth
  point of `V(I)` the stalk `I_x` is prime (`𝒪_{V(I),q}` is a regular local ring,
  `mem_smoothLocus_iff_isRegularAt`, hence a domain), so exactly ONE irreducible component of `V(I)`
  passes through it (the minimal primes of `I_x` are the components' stalks).
* `isReduced_subscheme_vanishingIdeal`, `isReduced_subscheme_comap_of_isOpenImmersion`: the
  reduced components are reduced (radical stalks), and reducedness descends to an open subscheme.
* `exists_smoothWindow_of_mem_smoothLocus`: **the window** — an affine open `W ∋ ι q` inside the
  complement of `ι(Y ∖ Reg Y)` (closed: `ι` is a closed immersion) and of the other components
  (a finite union of closed sets) is a smooth window
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedSmoothWindow`) for `(X, I_Y, 1, ∅)` and the loop's
  member set: the boundary is empty, `I|_W = I_c|_W` (both radical with the same support), the
  component `c` is integral, `V(c) ∩ W = V(I) ∩ W ⊆ Reg(Y)` is smooth over `k`
  (`preimage_smoothLocus_eq` on the open piece of `V(I)`), and no other member meets `W`.
* `BED_center_disjoint_reg`: clause (b), by `centersMiss_BED_of_smoothWindow` on that window; the
  form used by `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Hironaka
  Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

/-! ### Reduced components -/

/-- The closed subscheme of a vanishing ideal is reduced: its stalks are the quotients of the
stalks of `X` by the stalks of `vanishingIdeal Z`, which are radical (`vanishingIdeal Z` is its own
radical, `vanishingIdeal_support`; `stalkIdeal_radical`). -/
theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have hs : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := Closeds.ext (by rw
      [Scheme.IdealSheafData.coe_support_vanishingIdeal])
  have hrad : (Scheme.IdealSheafData.vanishingIdeal Z).radical =
      Scheme.IdealSheafData.vanishingIdeal Z := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support, hs]
  have : ∀ z, IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme.presheaf.stalk z) :=
      fun z => by
    have h1 : IsReduced (X.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι z) ⧸
        (Scheme.IdealSheafData.vanishingIdeal Z).stalkIdeal ((Scheme.IdealSheafData.vanishingIdeal
            Z).subschemeι z)) := by
      rw [← Ideal.isRadical_iff_quotient_reduced, ← Ideal.radical_eq_iff, ← stalkIdeal_radical,
        hrad]
    exact isReduced_of_injective ((Scheme.IdealSheafData.vanishingIdeal Z).stalkQuotientEquiv
        z).symm
      ((Scheme.IdealSheafData.vanishingIdeal Z).stalkQuotientEquiv z).symm.injective
  exact isReduced_of_isReduced_stalk _

/-- Reducedness of `V(I)` descends to `V(h^* I)` along an open immersion `h`: `V(h^* I)` is
isomorphic to the fibre product `W ×_X V(I)` (Mathlib's `comapIso`), an open subscheme of
`V(I)`. -/
theorem isReduced_subscheme_comap_of_isOpenImmersion {X W : Scheme.{u}} (h : W ⟶ X)
    [IsOpenImmersion h] (I : X.IdealSheafData) [IsReduced I.subscheme] :
    IsReduced (I.comap h).subscheme := by
  have : IsReduced (Limits.pullback h I.subschemeι) :=
    isReduced_of_isOpenImmersion (pullback.snd h I.subschemeι)
  exact isReduced_of_isOpenImmersion (I.comapIso h).hom

variable {k : Type u} [Field k] [CharZero k]

/-! ### The unique component through a smooth point of `Y` -/

section SmoothPoint

variable (TX : Triple k)

/-- At a point `q` of `V(I)` smooth over `k` the stalk `I_{ι q}` is prime: `𝒪_{V(I),q}` is a
regular local ring (`mem_smoothLocus_iff_isRegularAt`), hence a domain, and it is the quotient of
`𝒪_{X, ι q}` by `I_{ι q}` (`stalkQuotientEquiv`). -/
theorem isPrime_stalkIdeal_of_mem_smoothLocus {q : TX.I.subscheme}
    (hq : q ∈ (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))).smoothLocus) :
    (TX.I.stalkIdeal (TX.I.subschemeι q)).IsPrime := by
  have hPF : PerfectField k := PerfectField.ofCharZero
  have hreg : IsRegularLocalRing (TX.I.subscheme.presheaf.stalk q) :=
    (Scheme.mem_smoothLocus_iff_isRegularAt (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))) q).mp hq
  have : IsDomain (TX.X.left.presheaf.stalk (TX.I.subschemeι q) ⧸
      TX.I.stalkIdeal (TX.I.subschemeι q)) :=
    Function.Injective.isDomain (TX.I.stalkQuotientEquiv q) (TX.I.stalkQuotientEquiv q).injective
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

/-- Two generic points of `V(I)` specializing to a point where `V(I)` is smooth over `k` coincide:
the stalks of their reduced components are minimal primes of the PRIME `I_x`
(`stalkIdeal_vanishingIdeal_mem_minimalPrimes`), hence both equal to `I_x`
(`eq_of_stalkIdeal_vanishingIdeal_closure_eq`). -/
theorem eq_of_specializes_of_mem_smoothLocus {q : TX.I.subscheme}
    (hq : q ∈ (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))).smoothLocus) {η η' : TX.X.left}
    (hη : η ∈ TX.I.support.genericPoints) (hη' : η' ∈ TX.I.support.genericPoints)
    (h1 : η ⤳ TX.I.subschemeι q) (h2 : η' ⤳ TX.I.subschemeι q) : η = η' := by
  have hprime := isPrime_stalkIdeal_of_mem_smoothLocus TX hq
  have hP := stalkIdeal_vanishingIdeal_mem_minimalPrimes TX.I hη h1
  have hP' := stalkIdeal_vanishingIdeal_mem_minimalPrimes TX.I hη' h2
  rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hP hP'
  exact eq_of_stalkIdeal_vanishingIdeal_closure_eq h1 h2 (hP.trans hP'.symm)

/-- **The smooth window at a regular point of `Y`** ([Wlo05, 4.6]) — for `q ∈ Reg(Y)` there is an
affine open `W ∋ ι q` of `X` which is a smooth window for `(X, I_Y, 1, ∅)` and the loop's member
set: `W` misses `ι(Y ∖ Reg Y)` (closed, `ι` a closed immersion) and every irreducible component of
`Y` other than the one through `ι q` (finitely many, closed); on it the boundary is empty,
`I_Y|_W = I_c|_W` (radical ideals with the same support), the component `c` is integral,
`V(c) ∩ W ⊆ Reg(Y)` is smooth over `k`, and no other member meets `W`. -/
theorem exists_smoothWindow_of_mem_smoothLocus (hE : IsEmpty TX.E.ι) [IsReduced TX.I.subscheme]
    {q : TX.I.subscheme} (hq : q ∈ (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))).smoothLocus) :
    ∃ W : TX.X.left.Opens, IsAffineOpen W ∧ TX.I.subschemeι q ∈ W ∧
      SmoothWindow ⟨TX, 1⟩ (componentIdeals TX) W.ι := by
  classical
  have hNS : NoetherianSpace TX.X.left := Hironaka.BD.noetherianSpace_triple TX
  have hyI : TX.I.subschemeι q ∈ TX.I.support := by
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨q, rfl⟩
  obtain ⟨η, hη, hηy⟩ := TX.I.support.exists_mem_genericPoints_specializes hyI
  -- the closed sets the window avoids: the image of the singular locus and the other components
  have hSingC : IsClosed (TX.I.subschemeι ''
      (((TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))).smoothLocus : Set TX.I.subscheme)ᶜ)) :=
    TX.I.subschemeι.isClosedEmbedding.isClosedMap _
      (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))).smoothLocus.isOpen.isClosed_compl
  have hOthersC : IsClosed (⋃ η' ∈ TX.I.support.genericPoints \ {η}, closure {η'}) :=
    Set.Finite.isClosed_biUnion (TX.I.support.genericPoints_finite.subset Set.sdiff_subset)
      fun _ _ => isClosed_closure
  have hU : IsOpen ((TX.I.subschemeι ''
      (((TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))).smoothLocus : Set TX.I.subscheme)ᶜ))ᶜ ∩
      (⋃ η' ∈ TX.I.support.genericPoints \ {η}, closure {η'})ᶜ) :=
    hSingC.isOpen_compl.inter hOthersC.isOpen_compl
  have hyU : TX.I.subschemeι q ∈ (TX.I.subschemeι ''
      (((TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))).smoothLocus : Set TX.I.subscheme)ᶜ))ᶜ ∩
      (⋃ η' ∈ TX.I.support.genericPoints \ {η}, closure {η'})ᶜ := by
    refine ⟨fun hmem => ?_, fun hmem => ?_⟩
    · obtain ⟨q', hq', hq'y⟩ := hmem
      have hqq : q' = q := TX.I.subschemeι.isClosedEmbedding.injective hq'y
      exact hq' (by rw [hqq]; exact hq)
    · rw [Set.mem_iUnion₂] at hmem
      obtain ⟨η', hη', hmem⟩ := hmem
      exact hη'.2 (eq_of_specializes_of_mem_smoothLocus TX hq hη'.1 hη
        (specializes_iff_mem_closure.mpr hmem) hηy)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ :=
    TX.X.left.isBasis_affineOpens.exists_subset_of_mem_open hyU hU
  have hIle : TX.I ≤ Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η}) :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
      (Closeds.closure_le.mpr (Set.singleton_subset_iff.mpr hη.1))
  have hmemW : ∀ w : (W : Scheme.{u}), (Scheme.Opens.ι W) w ∈ (W : Set TX.X.left) := fun w => by
    rw [← Scheme.Opens.range_ι]
    exact ⟨w, rfl⟩
  -- the supports of `I` and of the component agree over `W`
  have hsupp : (TX.I.comap (Scheme.Opens.ι W)).support =
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).comap
          (Scheme.Opens.ι W)).support := by
    refine Closeds.ext (Set.ext fun w => ?_)
    simp only [SetLike.mem_coe, mem_support_comap_iff_apply]
    constructor
    · intro hw
      obtain ⟨η', hη', hη'w⟩ := TX.I.support.exists_mem_genericPoints_specializes hw
      have heq : η' = η := by
        by_contra hne
        exact (hWU (hmemW w)).2
          (Set.mem_iUnion₂.mpr ⟨η', ⟨hη', hne⟩, specializes_iff_mem_closure.mp hη'w⟩)
      subst heq
      rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal, SetLike.mem_coe,
          Closeds.mem_closure]
      exact specializes_iff_mem_closure.mp hη'w
    · exact fun hw => Scheme.IdealSheafData.support_antitone hIle hw
  have hred : IsReduced (TX.I.comap (Scheme.Opens.ι W)).subscheme :=
    isReduced_subscheme_comap_of_isOpenImmersion (Scheme.Opens.ι W) TX.I
  have hIc : TX.I.comap (Scheme.Opens.ι W) =
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).comap (Scheme.Opens.ι W) := by
    refine le_antisymm (Scheme.IdealSheafData.comap_mono _ hIle) ?_
    calc (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).comap (Scheme.Opens.ι W)
        ≤ Scheme.IdealSheafData.vanishingIdeal
          ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).comap
              (Scheme.Opens.ι W)).support :=
          Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl
      _ = Scheme.IdealSheafData.vanishingIdeal (TX.I.comap (Scheme.Opens.ι W)).support :=
          by rw [hsupp]
      _ = (TX.I.comap (Scheme.Opens.ι W)).radical := Scheme.IdealSheafData.vanishingIdeal_support
      _ = TX.I.comap (Scheme.Opens.ι W) := radical_eq_self_of_isReduced_subscheme _
  refine ⟨W, hW, hyW, ⟨fun e => hE.elim e,
    Or.inr ⟨Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η}), ?_, hIc, ?_, ?_, ?_⟩⟩⟩
  · exact Finset.mem_image.mpr ⟨η, (Set.Finite.mem_toFinset _).mpr hη, rfl⟩
  · have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      {η})).subscheme :=
      irreducibleSpace_subscheme_componentFamily TX.I ⟨η, hη⟩
    have := isReduced_subscheme_vanishingIdeal (Closeds.closure {η})
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  · rw [← hIc]
    have hsnd : Smooth (pullback.snd (Scheme.Opens.ι W) TX.I.subschemeι ≫
        (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k)))) := by
      rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
      refine IsConcreteLE.le_iff.mpr fun p _ => ?_
      change pullback.snd (Scheme.Opens.ι W) TX.I.subschemeι p ∈
        (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))).smoothLocus
      by_contra hp
      have h1 : TX.I.subschemeι (pullback.snd (Scheme.Opens.ι W) TX.I.subschemeι p) =
          (Scheme.Opens.ι W) (pullback.fst (Scheme.Opens.ι W) TX.I.subschemeι p) := by
        rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      exact (hWU (hmemW (pullback.fst (Scheme.Opens.ι W) TX.I.subschemeι p))).1 ⟨_, hp, h1⟩
    have h : (TX.I.comap (Scheme.Opens.ι W)).subschemeι ≫ (Scheme.Opens.ι W) ≫
        (TX.X.left ↘ Spec (.of k)) =
        (TX.I.comapIso (Scheme.Opens.ι W)).hom ≫ pullback.snd (Scheme.Opens.ι W) TX.I.subschemeι ≫
          (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (.of k))) := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst TX.I (Scheme.Opens.ι W)]
      simp only [Category.assoc, pullback.condition_assoc]
    rw [h]
    infer_instance
  · intro c' hc' hne
    obtain ⟨η', hη', rfl⟩ := Finset.mem_image.mp hc'
    rw [Set.Finite.mem_toFinset] at hη'
    obtain ⟨w, hw⟩ := exists_mem_support_of_ne_top _ hne
    rw [mem_support_comap_iff_apply, ← SetLike.mem_coe,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, SetLike.mem_coe,
      Closeds.mem_closure] at hw
    by_contra hne'
    exact (hWU (hmemW w)).2 (Set.mem_iUnion₂.mpr
      ⟨η', ⟨hη', fun h => hne' (by rw [Set.mem_singleton_iff.mp h])⟩, hw⟩)

end SmoothPoint

/-! ### Clause (b) -/

/-- **Clause (b) of [Wlo05, Theorem 1.0.2]** — no point of a centre of `BED TX` maps to a point of
`Reg(Y)`. The hypothesis that `x` lies on the strict transform of `Y` is present because clause
(b) speaks of the points of the strict transform `Y_i` over `Reg(Y)`; the proof does not need it,
because the stronger statement holds — no point of a centre at all maps to a smooth point of `Y`,
Włodarczyk's literal (b) — by the smooth window at the regular point and
`centersMiss_BED_of_smoothWindow`. -/
theorem BED_center_disjoint_reg (TX : Triple k) (hE : IsEmpty TX.E.ι) [IsReduced TX.I.subscheme] :
    ∀ (i : Fin (BED TX).length) (x : (BED TX).stage i.castSucc),
      x ∈ ((BED TX).center i).support →
        x ∈ ((BED TX).strictTransformSeq TX.I i.castSucc).support →
          (BED TX).stageMap i.castSucc x ∉
            TX.I.subschemeι ''
              ((TX.I.subschemeι ≫ (TX.X.left ↘ Spec (CommRingCat.of k))).smoothLocus : Set _) := by
  intro i x hx _ hmem
  obtain ⟨q, hq, hqx⟩ := hmem
  obtain ⟨W, hW, hyW, hwin⟩ := exists_smoothWindow_of_mem_smoothLocus TX hE hq
  have : CompactSpace (W : Scheme.{u}) := isCompact_iff_compactSpace.mp hW.isCompact
  have hmiss := centersMiss_BED_of_smoothWindow TX W.ι hwin i x hx
  rw [Scheme.Opens.range_ι] at hmiss
  refine hmiss ?_
  rw [← hqx]
  exact hyW

end Hironaka.Resolution
