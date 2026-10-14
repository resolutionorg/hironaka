/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Deriv
public import Hironaka.Manifold.Submanifold
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.Chart.Adapted
import Hironaka.Manifold.Chart.Order
import Hironaka.Manifold.Germ.CoordDerivChart
import Hironaka.Manifold.Germ.CoordDerivCoords
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.CosupportDeriv
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Local existence of a smooth hypersurface of maximal contact

Kollár's local construction of maximal contact [Kol07, Theorem 80 (2); 51.2]: for `m = max-ord I`,
every point `x` has an open neighbourhood `U` and a section `h ∈ H⁰(U, MC(I))` whose zero divisor
`H := (h = 0) ⊂ U` is smooth, where `MC(I) = D^{m−1}(I)` is the `(m−1)`-st derivative ideal
[Kol07, 51]. Kollár's proof: at a point `x` with `ord_x I = m` the ideal `MC(I)` has order `1`
(by his Lemma 74 (3)), so some local section of `MC(I)` has order `1` at `x`, "and so its zero
divisor is smooth in a neighborhood of `x`". On analytic manifolds the last step — the Jacobian
criterion — is the
analytic implicit function theorem in the form `exists_adapted_chart_of_ord_eq_one'`
(`Hironaka/Manifold/Chart/Adapted.lean`). Włodarczyk's tangent directions are the same
sections: functions of multiplicity one in `D^{µ−1}(I)` [Wlo09, Lemma 5.3.4; Definition 5.3.5;
Lemma 5.3.6].

* `ord_iteratedDeriv_eq_one`: at a point of order exactly `m ≥ 1`, `ord_x D^{m−1}(I) = 1`. The
  stalk of `D^{m−1}(I)` is the iterated derivative ideal `D^{m−1}(I_x)` of the stalk in the regular
  coordinates of a chart (`stalkIdeal_iteratedDeriv_eq_Dpow`), whose order is
  `ord I_x − (m − 1) = 1` (`ord_Dpow_of_ord_eq`; [Kol07, Lemma 74 (3)]).
* `exists_mem_carrier_iteratedDeriv_ordElem_eq_one`: a local section of `MC(I)` of order `1` at
  `x`. The stalk `MC(I)_x` is spanned by the germs of finitely many local sections of `MC(I)` (local
  finite generation), and the order of a finitely generated ideal is attained by one of its
  generators (`exists_ord_span_eq_ordElem`); the generator set is nonempty since the zero ideal
  has order `⊤ ≠ 1`.
* `exists_smoothDivisor_of_ordElem_eq_one` (the analytic implicit function theorem applied): a
  section `g` of an ideal sheaf `J` with order `1` at `x` restricts, to the source `U` of an
  adapted chart `e` with `g = ψ(e(·))_{σ 0}` on `U`, to a section `h ∈ J(U)` whose zero set is a
  closed submanifold of codimension `1` of `U` and whose order at every zero `y ∈ U` is `1`: the
  germ of `h` at `y` is the coordinate germ `coord … (σ 0)` (two sections agreeing on `U` have the
  same germs), whose value at a zero is `0` and whose `σ 0`-th coordinate derivative is `1 ≠ 0`
  (`coordDerivStalk_coord_eq_ite`), which is the order-one criterion
  `ord_eq_one_iff_exists_coordDerivStalk_ne_zero'`.
* `exists_maximalContactHypersurface_nhd`, the theorem, for `m ≥ max-ord I` and every `x`. If `x`
  lies in the cosupport of `MC(I)` then `m ≥ 1` (for `m = 0`, `MC(I) = I` and `ord_x I ≤ 0` puts `x`
  off the cosupport) and `ord_x I = m` (`cosupport_iteratedDeriv`: `cosupp MC(I) = {ord I ≥ m}`),
  and the two lemmas above give the section. Otherwise `MC(I)` is the unit ideal sheaf on the open
  complement of its cosupport, where the constant section `1` lies in `MC(I)` and has empty zero
  set — Kollár's `H_x = ∅`, a smooth (empty) divisor; this covers the points with `ord_x I < m`,
  the zero-dimensional manifolds and the case `m = 0`.

This is the local input of the order-reduction algorithm on analytic manifolds
(`Hironaka/Resolution/Analytic/OrderReduction/LocalMaximalContact.lean`).
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Manifold Topology IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M]

/-- The analytic implicit function theorem applied to a section of order one (Kollár's local
section of `MC(I)` of order `1` at `x`, whose "zero divisor is smooth in a neighborhood of `x`",
[Kol07, Theorem 80, proof]): a section `g ∈ J(V)` of order `1` at `x` restricts to the source
`U` of an adapted chart to a section `h ∈ J(U)` whose zero set is a closed submanifold of
codimension `1` of `U` and which has order `1` at each of its zeros. -/
theorem exists_smoothDivisor_of_ordElem_eq_one (J : IdealSheaf (structureSheaf 𝕜 E M))
    {V : Opens M} {x : M} (hxV : x ∈ V) (g : (structureSheaf 𝕜 E M).presheaf.obj (op V))
    (hg : g ∈ J.carrier V)
    (hord : ordElem ((structureSheaf 𝕜 E M).presheaf.germ V x hxV g) = 1) :
    ∃ (U : Opens M) (_ : x ∈ U) (h : (structureSheaf 𝕜 E M).presheaf.obj (op U)),
      h ∈ J.carrier U ∧
        IsClosedSubmanifoldOn ψ (U : Set M) ((U : Set M) ∩ {y | extendSection 𝕜 E h y = 0}) 1 ∧
          ∀ y (hy : y ∈ U), extendSection 𝕜 E h y = 0 →
            ordElem ((structureSheaf 𝕜 E M).presheaf.germ U y hy h) = 1 := by
  obtain ⟨e, σ, he, hxe, hsub, -, hcoord, -, hclosed⟩ :=
    exists_adapted_chart_of_ord_eq_one' E ψ hxV g hord
  let U : Opens M := ⟨e.source, e.open_source⟩
  have hUV : U ≤ V := hsub
  have hxU : x ∈ U := hxe
  let h : (structureSheaf 𝕜 E M).presheaf.obj (op U) :=
    (structureSheaf 𝕜 E M).presheaf.map (homOfLE hUV).op g
  have hext : ∀ y ∈ U, extendSection 𝕜 E h y = extendSection 𝕜 E g y := by
    intro y hy
    rw [extendSection_of_mem 𝕜 E h hy, extendSection_of_mem 𝕜 E g (hUV hy)]
    rfl
  refine ⟨U, hxU, h, J.res_mem _ g hg, ?_, ?_⟩
  · have hset : (U : Set M) ∩ {y | extendSection 𝕜 E h y = 0} =
        e.source ∩ {y | extendSection 𝕜 E g y = 0} := by
      ext y
      refine and_congr_right fun hy => ⟨fun hy0 => ?_, fun hy0 => ?_⟩
      · change extendSection 𝕜 E g y = 0
        rw [← hext y hy]
        exact hy0
      · change extendSection 𝕜 E h y = 0
        rw [hext y hy]
        exact hy0
    rw [hset]
    exact hclosed
  · intro y hy hy0
    have hgerm : (structureSheaf 𝕜 E M).presheaf.germ U y hy h = coord E ψ e he hy (σ 0) := by
      rw [← germ_coordSection E ψ e he U (fun _ hz => hz) hy hy (σ 0)]
      change (structureSheaf 𝕜 E M).presheaf.germ U y hy
        ((structureSheaf 𝕜 E M).presheaf.map (homOfLE hUV).op g) = _
      rw [TopCat.Presheaf.germ_res_apply]
      refine TopCat.Presheaf.germ_ext (structureSheaf 𝕜 E M).presheaf U hy
        (homOfLE hUV : U ⟶ V) (homOfLE (le_refl U) : U ⟶ U) ?_
      refine Subtype.ext (funext fun z => ?_)
      change g (Set.inclusion hUV z) = ψ (e z) (σ 0)
      rw [← extendSection_of_mem 𝕜 E g (hUV z.2)]
      exact hcoord z z.2
    rw [hgerm, ord_eq_one_iff_exists_coordDerivStalk_ne_zero' E ψ e he hy]
    refine ⟨?_, σ 0, ?_⟩
    · rw [eval_coord, ← hcoord y hy, ← hext y hy]
      exact hy0
    · rw [coordDerivStalk_coord_eq_ite he hy, ite_eq_left rfl, map_one]
      exact one_ne_zero

variable [FiniteDimensional 𝕜 E] (I : IdealSheaf (structureSheaf 𝕜 E M))

/-- Kollár's "pick `x ∈ X` such that `ord_x I = m`. Then `ord_x MC(I) = 1` by (74.3)"
([Kol07, Theorem 80, proof]; [Kol07, Lemma 74 (3)] at the stalk, through the regular coordinates
of a chart): at a point of order exactly `m ≥ 1`, the derivative ideal `MC(I) = D^{m−1}(I)` has
order `1`. -/
theorem ord_iteratedDeriv_eq_one {m : ℕ} (hm : 1 ≤ m) {x : M} (hx : I.ord x = m) :
    (I.iteratedDeriv (m - 1)).ord x = 1 := by
  have hφ : chartAt E x ∈ maximalAtlas 𝓘(𝕜, E) ω M := IsManifold.chart_mem_maximalAtlas x
  have hdim : ((Module.finrank 𝕜 E : ℕ) : WithBot ℕ∞) =
      ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk x) := (ringKrullDim_stalk E x).symm
  obtain ⟨c, -, -, hk, hs⟩ := exists_regularCoords_stalk E (IdealSheaf.modelCoord (𝕜 := 𝕜) (E := E))
    (chartAt E x) hφ (mem_chart_source E x) hdim
  rw [IdealSheaf.ord, I.stalkIdeal_iteratedDeriv_eq_Dpow c hk hs,
    c.ord_Dpow_of_ord_eq hx (Nat.sub_le m 1), Nat.sub_sub_self hm, Nat.cast_one]

/-- Kollár's "there is a local section of `MC(I)` that has order 1 at `x`" ([Kol07, Theorem 80,
proof]; [Kol07, 51.2]): at a point of order exactly `m ≥ 1`, an open neighbourhood `U` of `x`
carries a section `h ∈ H⁰(U, MC(I))` of order `1` at `x` — one of the finitely many local
generators of the stalk `MC(I)_x`, whose order is attained by a generator. -/
theorem exists_mem_carrier_iteratedDeriv_ordElem_eq_one {m : ℕ} (hm : 1 ≤ m) {x : M}
    (hx : I.ord x = m) :
    ∃ (U : Opens M) (hxU : x ∈ U) (h : (structureSheaf 𝕜 E M).presheaf.obj (op U)),
      h ∈ (I.iteratedDeriv (m - 1)).carrier U ∧
        ordElem ((structureSheaf 𝕜 E M).presheaf.germ U x hxU h) = 1 := by
  have h1 := ord_iteratedDeriv_eq_one I hm hx
  obtain ⟨U, hxU, k, f, hf, hspan⟩ := (I.iteratedDeriv (m - 1)).exists_generators x
  have hne : (Set.range fun i => (structureSheaf 𝕜 E M).presheaf.germ U x hxU (f i)).Nonempty := by
    rw [Set.range_nonempty_iff_nonempty]
    by_contra hk
    have hbot : (I.iteratedDeriv (m - 1)).stalkIdeal x = ⊥ := by
      rw [hspan x hxU, Set.range_eq_empty_iff.mpr (not_nonempty_iff.mp hk), Ideal.span_empty]
    have := (I.iteratedDeriv (m - 1)).ord_eq_top_of_stalkIdeal_eq_bot hbot
    rw [h1] at this
    exact ENat.one_ne_top this
  obtain ⟨g, ⟨i, rfl⟩, hg⟩ := exists_ord_span_eq_ordElem (Set.finite_range _) hne
  refine ⟨U, hxU, f i, hf i, ?_⟩
  rw [← hg, ← hspan x hxU]
  exact h1

/-- **Local existence of a smooth hypersurface of maximal contact** ([Kol07, Theorem 80 (2)] and
its proof; [Kol07, 51.2]; Włodarczyk's tangent directions, [Wlo09, Lemma 5.3.4; Definition 5.3.5;
Lemma 5.3.6]): for `m ≥ max-ord I`, every `x ∈ M` has an open neighbourhood `U` and a section
`h ∈ H⁰(U, MC(I))` whose zero divisor `H := (h = 0) ⊂ U` is smooth — its zero set is a closed
submanifold of codimension `1` of `U` and `h` has order `1` at each of its zeros. At a point of the
cosupport of `MC(I)` the order of `I` is exactly `m ≥ 1` and a section of order `1` exists; off the
cosupport `MC(I)` is the unit ideal sheaf and the constant section `1`, with empty zero set, is
such a section. -/
theorem exists_maximalContactHypersurface_nhd {m : ℕ} (hI : ∀ y, I.ord y ≤ m) (x : M) :
    ∃ (U : Opens M) (_ : x ∈ U) (h : (structureSheaf 𝕜 E M).presheaf.obj (op U)),
      h ∈ (I.iteratedDeriv (m - 1)).carrier U ∧
        IsClosedSubmanifoldOn ψ (U : Set M) ((U : Set M) ∩ {y | extendSection 𝕜 E h y = 0}) 1 ∧
          ∀ y (hy : y ∈ U), extendSection 𝕜 E h y = 0 →
            ordElem ((structureSheaf 𝕜 E M).presheaf.germ U y hy h) = 1 := by
  by_cases hx : x ∈ (I.iteratedDeriv (m - 1)).support
  · have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · exfalso
        rw [Nat.zero_sub, IdealSheaf.iteratedDeriv_zero] at hx
        exact (IdealSheaf.ord_eq_zero_iff (J := I)).mp
          (nonpos_iff_eq_zero.mp (by simpa using hI x)) hx
      · exact hpos
    have hxm : I.ord x = m := by
      refine le_antisymm (hI x) ?_
      rw [IdealSheaf.support_iteratedDeriv I hm] at hx
      exact hx
    obtain ⟨V, hxV, g, hg, hord⟩ := exists_mem_carrier_iteratedDeriv_ordElem_eq_one I hm hxm
    exact exists_smoothDivisor_of_ordElem_eq_one ψ _ hxV g hg hord
  · refine ⟨⟨_, (I.iteratedDeriv (m - 1)).isOpen_compl_support⟩, hx, 1, ?_, ?_, ?_⟩
    · rw [IdealSheaf.mem_carrier_iff]
      intro y hy
      have htop : (I.iteratedDeriv (m - 1)).stalkIdeal y = ⊤ := not_not.mp hy
      rw [htop]
      exact Submodule.mem_top
    · have hempty : ((⟨_, (I.iteratedDeriv (m - 1)).isOpen_compl_support⟩ : Opens M) : Set M) ∩
          {y | extendSection 𝕜 E (1 : (structureSheaf 𝕜 E M).presheaf.obj
            (op ⟨_, (I.iteratedDeriv (m - 1)).isOpen_compl_support⟩)) y = 0} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun y ⟨hy, h0⟩ => ?_
        change extendSection 𝕜 E _ y = 0 at h0
        rw [extendSection_of_mem 𝕜 E _ hy] at h0
        exact one_ne_zero h0
      rw [hempty]
      exact ⟨by rw [Set.preimage_empty]; exact isClosed_empty,
        fun a ha => absurd ha.1 (Set.notMem_empty a)⟩
    · intro y hy h0
      exfalso
      rw [extendSection_of_mem 𝕜 E _ hy] at h0
      exact one_ne_zero h0

end Manifold

end
