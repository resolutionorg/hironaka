/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.LocalIsoEquiv
import Hironaka.Manifold.BlowUp.CoordGerm
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceCompletion
import Hironaka.Manifold.BlowUp.Transition
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.MaximalContact.AgreeOnSubspaceLemmas
import Hironaka.Resolution.Analytic.MaximalContact.BlowUpChartTransition
import Hironaka.Resolution.Analytic.MaximalContact.CoordCriterion
import Hironaka.Resolution.Analytic.MaximalContact.OneStepDescentLemmas
import Hironaka.Resolution.Analytic.MaximalContact.StalkEquiv
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# One-step descent of agreement through a blow-up

The inductive step of Kollár's proof of the uniqueness of blow-up sequences [Kol07, Theorem 97,
proof]; Włodarczyk's equivariance of test blow-ups under the glueing automorphism is the same
computation [Wlo09, Lemma 5.5.3, proof, (5)]. Let `f, g : U → M` agree on the closed analytic
subspace `V(J)`, let `Y ⊆ M` be a closed submanifold whose pulled-back ideal sheaves `f^*I_Y`,
`g^*I_Y` are both the ideal sheaf of one closed submanifold `Z ⊆ U` contained in `V(J)`, and let
`f', g' : Bl_Z U → Bl_Y M` be lifts of `f`, `g` over the blow-downs. Then `f'` and `g'` agree on
`V((π')^{-1}_*(J, 1))` (`agreeOnSubspace_blowUpLift`).

## The proof

Write `M_1 := (π')^{-1}_*(J, 1)`; its stalks are the colons `(π'^*J)_q : I_{F,q}`
(`isDivExceptional_birationalTransform`, with `1 ≤ ν_Z(J)` from `Z ⊆ V(J)`:
`stalkIdeal_le_vanishingStalk_of_subset_cosupport`). Fix `q` with `M_{1,q} ≠ 𝒪_q` (elsewhere there
is nothing to prove: `agreeOnSubspace_of_forall_sub_mem`). Then `u := π' q ∈ V(J)`, so `f u = g u`.

* **Off the exceptional divisor** (`u ∉ Z`): `I_{F,q}` is the unit ideal and `M_{1,q} = (π'^*J)_q`;
  the blow-down is a local isomorphism at `f' q`, whose fibre over `f u ∉ Y` is one point, so
  `f' q = g' q`; every germ at `f' q` is `π^* t` (`germMapInv`), and
  `f'^*π^*t − g'^*π^*t = π'^*(f^*t − g^*t) ∈ π'^*J` (functoriality, `germMap_germMap_germ`).
* **On the exceptional divisor** (`u ∈ Z`, `y := f u ∈ Y`): take an adapted chart `φ` of `Y` at `y`
  with coordinates `z_j`, a blow-up chart `Φ` of index `i` at `f' q` (`IsBlowUp.cover`), and a
  blow-up chart `Φ'` of `Bl_Z U` at `q` with scaling coordinate `e`, so that `I_{F,q} = (e)`
  (`stalkIdeal_exceptionalIdealSheaf_eq_span_coord`) and `x ∈ M_{1,q} ⟺ x e ∈ (π'^*J)_q`. Set
  `A_j := π'^* f^* z_j`, `B_j := π'^* g^* z_j`. For the centre indices, `A_{σk}, B_{σk} ∈ (e)`
  (`f^*I_Y = I_Z`, `IsBlowUp.stalkIdeal_pullback_eq_span_coord`): `A_{σk} = At_k e`,
  `B_{σk} = Bt_k e`, and `(At_k − Bt_k) e = π'^*(f^*z_{σk} − g^*z_{σk}) ∈ π'^*J`, so
  `At_k − Bt_k ∈ M_{1,q} ⊆ 𝔪_q`: `At_k(q) = Bt_k(q)`. The chart formulae `z_{σi} ∘ π = w_{σi}`,
  `z_{σk} ∘ π = w_{σi} w_{σk}`, `z_j ∘ π = w_j` (`germMap_coord_self`, `germMap_coord_of_ne`,
  `germMap_coord_off`) pulled back by `f'` give `A_{σi} = a_i`, `A_{σk} = a_i a_k` for the
  coordinates `a_j := f'^* w_j`. Since `e ∈ (A_{σk})_k` (the same identification of `π'^*I_Z`),
  `At_i` is a unit (else `e (1 − At_i t) = 0` with a unit factor, contradicting `coord_ne_zero`),
  hence so is `Bt_i`. Reading `g' q` in its own chart `Φ''` of index `i''`,
  `Bt_i e = Bt_{i''} e · g'^*w''_{σi}`, so `g'^*w''_{σi}(q) ≠ 0` and `g' q` lies in the chart `Φ`
  (`IsBlowUpChart.mem_source_of_mem_transitionDomain`). With `b_j := g'^* w_j` in the same chart,
  `At_i Bt_i (a_k − b_k) e = e [Bt_i(At_k − Bt_k) + Bt_k(Bt_i − At_i)]`, so `a_j − b_j ∈ M_{1,q}`
  for every coordinate; their values agree, so `Φ(f' q) = Φ(g' q)` and `f' q = g' q`; and the
  coordinate criterion `sub_mem_of_forall_coord_sub_mem` (Hadamard's lemma and Krull's
  intersection theorem) extends the agreement modulo `M_{1,q}` to every germ.

No smoothness or local-isomorphism hypothesis on `f`, `g` beyond the centre clause is used. The
`Hironaka` library proves the same step for schemes
(`Hironaka/Resolution/Algebraic/MaximalContact/AgreeOnBlowUpKernel.lean`).
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u v

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- **One-step descent of agreement through a blow-up** ([Kol07, Theorem 97, proof];
[Wlo09, Lemma 5.5.3, proof, (5)]): if `f, g : U → M` agree on `V(J)`, pull the ideal sheaf of the
closed submanifold `Y` back to the ideal sheaf of one closed submanifold `Z ⊆ V(J)`, and `f', g'`
are lifts of `f`, `g` to the blow-ups along `Z` and `Y`, then `f'` and `g'` agree on
`V((π')^{-1}_*(J, 1))`. -/
theorem agreeOnSubspace_blowUpLift {U : AnalyticManifold.{u} 𝕜 E} (f g : AnalyticMap U M)
    {Y : Set M} {Z : Set U} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c)
    (hZ : IsClosedSubmanifold ψ Z c)
    (hZf : hY.idealSheaf.pullback f f.contMDiff = hZ.idealSheaf)
    (hZg : hY.idealSheaf.pullback g g.contMDiff = hZ.idealSheaf)
    (J : AnalyticManifold.IdealSheaf U) (hJZ : Z ⊆ J.support)
    (hfg : AgreeOnSubspace f g J) (f' g' : AnalyticMap (Manifold.blowUp ψ hZ)
        (Manifold.blowUp ψ hY))
    (hf' : ∀ q, Manifold.blowUpπ ψ hY (f' q) = f (Manifold.blowUpπ ψ hZ q))
    (hg' : ∀ q, Manifold.blowUpπ ψ hY (g' q) = g (Manifold.blowUpπ ψ hZ q)) :
    AgreeOnSubspace f' g'
      (MarkedIdealSheaf.birationalTransform hZ (isBlowUp_blowUpπ ψ hZ) ⟨J, 1⟩).I := by
  classical
  set π := Manifold.blowUpπ ψ hY with hπdef
  set π' := Manifold.blowUpπ ψ hZ with hπ'def
  have hπ : IsBlowUp ψ Y c ⇑π := isBlowUp_blowUpπ ψ hY
  have hπ' : IsBlowUp ψ Z c ⇑π' := isBlowUp_blowUpπ ψ hZ
  -- the centre is the preimage of `Y` under either map
  have hZY : Z = ⇑f ⁻¹' Y :=
    calc Z = hZ.idealSheaf.support := hZ.cosupport_idealSheaf.symm
      _ = (hY.idealSheaf.pullback f f.contMDiff).support := by rw [hZf]
      _ = ⇑f ⁻¹' hY.idealSheaf.support :=
          IdealSheaf.support_pullback (φ := ⇑f) (hφ := f.contMDiff) hY.idealSheaf
      _ = ⇑f ⁻¹' Y := by rw [hY.cosupport_idealSheaf]
  -- the marked transform with mark `1` exists: `J ⊆ I_Z`
  have hm : ∀ a ∈ Z, ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hZ.idealSheaf J a := by
    intro a ha
    rw [IdealSheaf.le_ordAlongIdeal_iff, pow_one, hZ.stalkIdeal_idealSheaf_of_mem ha,
      hZ.ker_restrictStalk_eq_vanishingStalk ha]
    exact stalkIdeal_le_vanishingStalk_of_subset_cosupport J hJZ a
  have hdiv := isDivExceptional_birationalTransform hZ hπ' ⟨J, 1⟩ hm
  set J₁ := (MarkedIdealSheaf.birationalTransform hZ (isBlowUp_blowUpπ ψ hZ) ⟨J, 1⟩).I with hJ₁def
  refine agreeOnSubspace_of_forall_sub_mem f' g' J₁ fun q hq => ?_
  have hJ₁q := hdiv q
  simp only [pow_one] at hJ₁q
  have htot : (J.pullback ⇑π' hπ'.contMDiff).stalkIdeal q =
      Ideal.map (germMap (⇑π') π'.contMDiff q) (J.stalkIdeal (π' q)) :=
    stalkIdeal_comap_eq_map_germMap π' J q
  -- `π'^*J ⊆ M_1`
  have hle : (J.pullback ⇑π' hπ'.contMDiff).stalkIdeal q ≤ J₁.stalkIdeal q := by
    rw [hJ₁q]
    intro x hx
    exact Submodule.mem_colon.mpr fun s _ => Ideal.mul_mem_right s _ hx
  -- `u := π' q` lies in `V(J)`, so `f u = g u`
  have huJ : J.stalkIdeal (π' q) ≠ ⊤ := by
    intro htop
    apply hq
    rw [eq_top_iff]
    refine le_trans ?_ hle
    rw [htot, htop, Ideal.map_top]
  have hgu : g (π' q) = f (π' q) := (hfg.apply_eq_of_mem_support huJ).symm
  by_cases huZ : π' q ∈ Z
  · /- On the exceptional divisor. -/
    have hyY : f (π' q) ∈ Y := hZY.subset huZ
    have hgY : g (π' q) ∈ Y := by rw [hgu]; exact hyY
    obtain ⟨φ, σ, hyφ, hφ⟩ := hY.exists_adaptedChart (f (π' q)) hyY
    have hφm : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M := hφ.1
    have hgφ : g (π' q) ∈ φ.source := by rw [hgu]; exact hyφ
    have hp'φ : π (f' q) ∈ φ.source := by rw [hf' q]; exact hyφ
    have hp''φ : π (g' q) ∈ φ.source := by rw [hg' q]; exact hgφ
    obtain ⟨i, Φ, hΦ, hp'⟩ := hπ.cover φ σ hφ (f' q) hp'φ
    obtain ⟨i'', Φ'', hΦ'', hp''⟩ := hπ.cover φ σ hφ (g' q) hp''φ
    -- the scaling coordinate `e` of a blow-up chart of `Bl_Z U` at `q`
    obtain ⟨φ', σ', huφ', hφ'⟩ := hZ.exists_adaptedChart (π' q) huZ
    obtain ⟨i', Φ', hΦ', hqΦ'⟩ := hπ'.cover φ' σ' hφ' q huφ'
    set e := coord E ψ Φ' hΦ'.mem_maximalAtlas hqΦ' (σ' i') with he_def
    have hIF : (hZ.idealSheaf.pullback ⇑π' hπ'.contMDiff).stalkIdeal q = Ideal.span {e} :=
      stalkIdeal_exceptionalIdealSheaf_eq_span_coord hZ hπ' hφ' hΦ' hqΦ'
    have he0 : e ≠ 0 := coord_ne_zero hΦ'.mem_maximalAtlas hqΦ' (σ' i')
    rw [hIF] at hJ₁q
    have hmemJ₁ : ∀ x, x ∈ J₁.stalkIdeal q ↔
        x * e ∈ (J.pullback ⇑π' hπ'.contMDiff).stalkIdeal q := fun x => by
      rw [hJ₁q]
      exact Ideal.mem_colon_span_singleton_iff _ e x
    have hJ₁le : J₁.stalkIdeal q ≤ maximalIdeal _ := IsLocalRing.le_maximalIdeal hq
    -- the pulled-back coordinates of `φ`
    obtain ⟨A, hA⟩ : ∃ A : Fin n → (structureSheaf 𝕜 E (Manifold.blowUp ψ hZ)).presheaf.stalk q,
        ∀ j,
        A j = germMap (⇑π') π'.contMDiff q
          (germMap (⇑f) f.contMDiff (π' q) (coord E ψ φ hφm hyφ j)) := ⟨_, fun _ => rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Fin n → (structureSheaf 𝕜 E (Manifold.blowUp ψ hZ)).presheaf.stalk q,
        ∀ j,
        B j = germMap (⇑π') π'.contMDiff q
          (germMap (⇑g) g.contMDiff (π' q) (coord E ψ φ hφm hgφ j)) := ⟨_, fun _ => rfl⟩
    have hIY : hY.idealSheaf.stalkIdeal (f (π' q)) =
        Ideal.span (Set.range fun k => coord E ψ φ hφm hyφ (σ k)) :=
      hY.isIdealSheafOf_idealSheaf.2 φ σ hφ _ hyφ hyY
    have hIY' : hY.idealSheaf.stalkIdeal (g (π' q)) =
        Ideal.span (Set.range fun k => coord E ψ φ hφm hgφ (σ k)) :=
      hY.isIdealSheafOf_idealSheaf.2 φ σ hφ _ hgφ hgY
    -- `π'^*I_Z` is spanned by the `A_{σk}` and by the `B_{σk}`
    have hspanA : (hZ.idealSheaf.pullback ⇑π' hπ'.contMDiff).stalkIdeal q =
        Ideal.span (Set.range fun k => A (σ k)) := by
      have h1 : (fun k => A (σ k)) = ⇑(germMap (⇑π') π'.contMDiff q) ∘
          (⇑(germMap (⇑f) f.contMDiff (π' q)) ∘ fun k => coord E ψ φ hφm hyφ (σ k)) :=
        funext fun k => hA (σ k)
      rw [h1, Set.range_comp, Set.range_comp, ← Ideal.map_span, ← Ideal.map_span, ← hIY,
        ← stalkIdeal_comap_eq_map_germMap f hY.idealSheaf (π' q), hZf]
      exact stalkIdeal_comap_eq_map_germMap π' hZ.idealSheaf q
    have hspanB : (hZ.idealSheaf.pullback ⇑π' hπ'.contMDiff).stalkIdeal q =
        Ideal.span (Set.range fun k => B (σ k)) := by
      have h1 : (fun k => B (σ k)) = ⇑(germMap (⇑π') π'.contMDiff q) ∘
          (⇑(germMap (⇑g) g.contMDiff (π' q)) ∘ fun k => coord E ψ φ hφm hgφ (σ k)) :=
        funext fun k => hB (σ k)
      rw [h1, Set.range_comp, Set.range_comp, ← Ideal.map_span, ← Ideal.map_span, ← hIY',
        ← stalkIdeal_comap_eq_map_germMap g hY.idealSheaf (π' q), hZg]
      exact stalkIdeal_comap_eq_map_germMap π' hZ.idealSheaf q
    have hAmem : ∀ k, A (σ k) ∈ Ideal.span {e} := fun k => by
      rw [← hIF, hspanA]
      exact Ideal.subset_span ⟨k, rfl⟩
    have hBmem : ∀ k, B (σ k) ∈ Ideal.span {e} := fun k => by
      rw [← hIF, hspanB]
      exact Ideal.subset_span ⟨k, rfl⟩
    choose At hAt using fun k => Ideal.mem_span_singleton'.mp (hAmem k)
    choose Bt hBt using fun k => Ideal.mem_span_singleton'.mp (hBmem k)
    have heA : e ∈ Ideal.span (Set.range fun k => A (σ k)) := by
      rw [← hspanA, hIF]
      exact Ideal.mem_span_singleton_self e
    -- the defects `A_j − B_j` lie in `π'^*J`
    have hAB : ∀ j, A j - B j ∈ (J.pullback ⇑π' hπ'.contMDiff).stalkIdeal q := fun j => by
      rw [hA, hB, htot, ← map_sub]
      exact Ideal.mem_map_of_mem _
        (hfg (π' q) ⟨φ.source, φ.open_source⟩ hyφ hgφ (chartSection E ψ φ hφm j))
    have hAtBt : ∀ k, At k - Bt k ∈ J₁.stalkIdeal q := fun k => by
      rw [hmemJ₁, sub_mul, hAt k, hBt k]
      exact hAB (σ k)
    have hBtAt : ∀ k, Bt k - At k ∈ J₁.stalkIdeal q := fun k => by
      rw [← neg_sub]
      exact neg_mem_iff.mpr (hAtBt k)
    have hevalAtBt : ∀ k, Manifold.eval 𝕜 E _ q (At k) = Manifold.eval 𝕜 E _ q (Bt k) := fun k => by
      have := hJ₁le (hAtBt k)
      rwa [mem_maximalIdeal_iff_eval, map_sub, sub_eq_zero] at this
    -- the chart formulae, pulled back by `f'`
    obtain ⟨a, ha⟩ : ∃ a : Fin n → (structureSheaf 𝕜 E (Manifold.blowUp ψ hZ)).presheaf.stalk q,
        ∀ j,
        a j = germMap (⇑f') f'.contMDiff q (coord E ψ Φ hΦ.mem_maximalAtlas hp' j) :=
      ⟨_, fun _ => rfl⟩
    have hAf : ∀ j, A j = germMap (⇑f') f'.contMDiff q (germMap (⇑π) π.contMDiff (f' q)
        (coord E ψ φ hφm (hΦ.source_subset hp') j)) := fun j => by
      rw [hA]
      exact (germMap_germMap_germ f' π π' f hf' q (hΦ.source_subset hp') hyφ
        (chartSection E ψ φ hφm j)).symm
    have hai : A (σ i) = a (σ i) := by
      rw [hAf, hΦ.germMap_coord_self hπ.contMDiff hφm hp', ha]
    have hak : ∀ k, k ≠ i → A (σ k) = a (σ i) * a (σ k) := fun k hk => by
      rw [hAf, hΦ.germMap_coord_of_ne hπ.contMDiff hφm hp' hk, map_mul, ha, ha]
    have haj : ∀ j, (∀ k, σ k ≠ j) → A j = a j := fun j hj => by
      rw [hAf, hΦ.germMap_coord_off hπ.contMDiff hφm hp' hj, ha]
    -- `At_i` is a unit (reducedness of the centre)
    have hAti : IsUnit (At i) := by
      by_contra hnot
      have hmi : At i ∈ maximalIdeal _ :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnot)
      obtain ⟨r, hr⟩ := Ideal.mem_span_range_iff_exists_fun.mp heA
      set a' : Fin c → (structureSheaf 𝕜 E (Manifold.blowUp ψ hZ)).presheaf.stalk q :=
        fun k => if k = i then 1 else a (σ k) with ha'
      have hAa' : ∀ k, A (σ k) = A (σ i) * a' k := fun k => by
        by_cases hk : k = i
        · subst hk
          simp only [a', ite_true, mul_one]
        · simp only [a', ite_eq_right hk]
          rw [hak k hk, hai]
      have hee : e = e * (At i * ∑ k, r k * a' k) := by
        calc e = ∑ k, r k * A (σ k) := hr.symm
          _ = ∑ k, r k * (A (σ i) * a' k) := Finset.sum_congr rfl fun k _ => by rw [hAa' k]
          _ = A (σ i) * ∑ k, r k * a' k := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun k _ => by ring
          _ = e * (At i * ∑ k, r k * a' k) := by rw [← hAt i]; ring
      have hunit : IsUnit (1 - At i * ∑ k, r k * a' k) :=
        IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
          ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hmi))
      apply he0
      have h0 : e * (1 - At i * ∑ k, r k * a' k) = 0 := by
        rw [mul_sub, mul_one, ← hee, sub_self]
      exact hunit.mul_left_eq_zero.mp h0
    have hBti : IsUnit (Bt i) := by
      rw [← IsLocalRing.notMem_maximalIdeal, mem_maximalIdeal_iff_eval, ← hevalAtBt,
        ← mem_maximalIdeal_iff_eval, IsLocalRing.notMem_maximalIdeal]
      exact hAti
    -- the second lift, read in its own chart `Φ''`
    obtain ⟨b'', hb''⟩ : ∃ b'' : Fin n → (structureSheaf 𝕜 E (Manifold.blowUp ψ hZ)).presheaf.stalk
        q, ∀ j,
        b'' j = germMap (⇑g') g'.contMDiff q (coord E ψ Φ'' hΦ''.mem_maximalAtlas hp'' j) :=
      ⟨_, fun _ => rfl⟩
    have hBg'' : ∀ j, B j = germMap (⇑g') g'.contMDiff q (germMap (⇑π) π.contMDiff (g' q)
        (coord E ψ φ hφm (hΦ''.source_subset hp'') j)) := fun j => by
      rw [hB]
      exact (germMap_germMap_germ g' π π' g hg' q (hΦ''.source_subset hp'') hgφ
        (chartSection E ψ φ hφm j)).symm
    -- the common chart: `g' q` lies in the chart `Φ` of `f' q`
    have hp''Φ : g' q ∈ Φ.source := by
      by_cases hii : i'' = i
      · subst hii
        exact (hΦ''.mem_source_of_mem_transitionDomain hY hπ hΦ hp''
          (by rw [blowUpTransitionDomain_self]; exact Set.mem_univ _)).1
      · refine (hΦ''.mem_source_of_mem_transitionDomain hY hπ hΦ hp''
          ((mem_blowUpTransitionDomain σ _ hii).mpr ?_)).1
        rw [← eval_coord E ψ Φ'' hp'' hΦ''.mem_maximalAtlas (σ i),
          ← eval_map_of_isLocalHom (germMap (⇑g') g'.contMDiff q) (germMap_const g'.contMDiff q),
          ← hb'']
        intro h0
        have h1 : B (σ i) = B (σ i'') * b'' (σ i) := by
          rw [hBg'', hBg'', hΦ''.germMap_coord_of_ne hπ.contMDiff hφm hp'' (Ne.symm hii),
            map_mul, hΦ''.germMap_coord_self hπ.contMDiff hφm hp'', hb'']
        have h2 : (Bt i - Bt i'' * b'' (σ i)) * e = 0 := by
          rw [sub_mul, hBt i, h1, ← hBt i'']
          ring
        have hm : Bt i'' * b'' (σ i) ∈ maximalIdeal _ :=
          Ideal.mul_mem_left _ _ ((mem_maximalIdeal_iff_eval E _).mpr h0)
        have hunit : IsUnit (Bt i - Bt i'' * b'' (σ i)) := by
          rw [← IsLocalRing.notMem_maximalIdeal]
          intro hmem
          apply IsLocalRing.notMem_maximalIdeal.mpr hBti
          have := Ideal.add_mem _ hmem hm
          rwa [sub_add_cancel] at this
        exact he0 (hunit.mul_right_eq_zero.mp h2)
    -- the chart formulae, pulled back by `g'` in the chart `Φ`
    obtain ⟨b, hb⟩ : ∃ b : Fin n → (structureSheaf 𝕜 E (Manifold.blowUp ψ hZ)).presheaf.stalk q,
        ∀ j,
        b j = germMap (⇑g') g'.contMDiff q (coord E ψ Φ hΦ.mem_maximalAtlas hp''Φ j) :=
      ⟨_, fun _ => rfl⟩
    have hBg : ∀ j, B j = germMap (⇑g') g'.contMDiff q (germMap (⇑π) π.contMDiff (g' q)
        (coord E ψ φ hφm (hΦ.source_subset hp''Φ) j)) := fun j => by
      rw [hB]
      exact (germMap_germMap_germ g' π π' g hg' q (hΦ.source_subset hp''Φ) hgφ
        (chartSection E ψ φ hφm j)).symm
    have hbi : B (σ i) = b (σ i) := by
      rw [hBg, hΦ.germMap_coord_self hπ.contMDiff hφm hp''Φ, hb]
    have hbk : ∀ k, k ≠ i → B (σ k) = b (σ i) * b (σ k) := fun k hk => by
      rw [hBg, hΦ.germMap_coord_of_ne hπ.contMDiff hφm hp''Φ hk, map_mul, hb, hb]
    have hbj : ∀ j, (∀ k, σ k ≠ j) → B j = b j := fun j hj => by
      rw [hBg, hΦ.germMap_coord_off hπ.contMDiff hφm hp''Φ hj, hb]
    -- every coordinate defect lies in `M_{1,q}`
    have hab : ∀ j, a j - b j ∈ J₁.stalkIdeal q := by
      intro j
      rcases exists_eq_or_forall_ne σ j with ⟨k, rfl⟩ | hj
      · by_cases hk : k = i
        · subst hk
          rw [← hai, ← hbi]
          exact hle (hAB (σ k))
        · rw [hmemJ₁, ← Ideal.unit_mul_mem_iff_mem _ (hAti.mul hBti)]
          have e1 : At k * e = At i * e * a (σ k) := by rw [hAt k, hak k hk, ← hai, ← hAt i]
          have e2 : Bt k * e = Bt i * e * b (σ k) := by rw [hBt k, hbk k hk, ← hbi, ← hBt i]
          have h1 : At i * Bt i * ((a (σ k) - b (σ k)) * e) =
              Bt i * ((At k - Bt k) * e) + Bt k * ((Bt i - At i) * e) := by
            linear_combination (-Bt i) * e1 + At i * e2
          rw [h1]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ((hmemJ₁ _).mp (hAtBt k)))
            (Ideal.mul_mem_left _ _ ((hmemJ₁ _).mp (hBtAt i)))
      · rw [← haj j hj, ← hbj j hj]
        exact hle (hAB j)
    -- hence `f' q = g' q`
    have hpp' : f' q = g' q := by
      refine Φ.injOn hp' hp''Φ (ψ.injective (funext fun j => ?_))
      rw [← eval_coord E ψ Φ hp' hΦ.mem_maximalAtlas j,
        ← eval_coord E ψ Φ hp''Φ hΦ.mem_maximalAtlas j,
        ← eval_map_of_isLocalHom (germMap (⇑f') f'.contMDiff q) (germMap_const f'.contMDiff q),
        ← eval_map_of_isLocalHom (germMap (⇑g') g'.contMDiff q) (germMap_const g'.contMDiff q),
        ← ha, ← hb]
      have := hJ₁le (hab j)
      rwa [mem_maximalIdeal_iff_eval, map_sub, sub_eq_zero] at this
    refine ⟨hpp', fun s => ?_⟩
    -- and the coordinate criterion extends the agreement to every germ
    refine sub_mem_of_forall_coord_sub_mem E ψ Φ hp' hΦ.mem_maximalAtlas
      (germMap (⇑f') f'.contMDiff q) ((germMap (⇑g') g'.contMDiff q).comp (stalkCast hpp'))
      (germMap_const f'.contMDiff q)
      (fun c => by rw [RingHom.comp_apply, stalkCast_const, germMap_const]) (J₁.stalkIdeal q)
      (fun j => ?_) s
    rw [RingHom.comp_apply, stalkCast_coord ψ hpp' hΦ.mem_maximalAtlas hp' hp''Φ j, ← ha, ← hb]
    exact hab j
  · /- Off the exceptional divisor: the blow-down is a local isomorphism at `f' q`. -/
    have hIF : (hZ.idealSheaf.pullback ⇑π' hπ'.contMDiff).stalkIdeal q = ⊤ :=
      stalkIdeal_exceptionalIdealSheaf_of_notMem hZ hπ' huZ
    rw [hIF, Ideal.colon_coe_top] at hJ₁q
    have hyY : f (π' q) ∉ Y := fun h => huZ (hZY.symm.subset h)
    have hp'Y : f' q ∈ ⇑π ⁻¹' Yᶜ := by
      change π (f' q) ∉ Y
      rw [hf' q]
      exact hyY
    have hp''Y : g' q ∈ ⇑π ⁻¹' Yᶜ := by
      change π (g' q) ∉ Y
      rw [hg' q, hgu]
      exact hyY
    have hpp' : f' q = g' q :=
      hπ.bijOn_compl.injOn hp'Y hp''Y (by rw [hf' q, hg' q, hgu])
    refine ⟨hpp', fun s => ?_⟩
    have hb : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω π (f' q) :=
      hπ.isLocalDiffeomorphOn_compl ⟨f' q, hp'Y⟩
    obtain ⟨V, hV, t₀, ht₀⟩ := TopCat.Presheaf.exists_germ_eq _ (germMapInv π hb s)
    have hs : s = germMap (⇑π) π.contMDiff (f' q)
        ((structureSheaf 𝕜 E M).presheaf.germ V (π (f' q)) hV t₀) := by
      rw [ht₀]
      exact (RingHom.congr_fun (germMap_comp_germMapInv π hb) s).symm
    have hVf : f (π' q) ∈ V := by rw [← hf' q]; exact hV
    have hVg : g (π' q) ∈ V := by rw [hgu, ← hf' q]; exact hV
    have hV' : π (g' q) ∈ V := by rw [hg' q]; exact hVg
    rw [hs, stalkCast_germMap_germ π hpp' hV hV', germMap_germMap_germ f' π π' f hf' q hV hVf,
      germMap_germMap_germ g' π π' g hg' q hV' hVg, ← map_sub, hJ₁q, htot]
    exact Ideal.mem_map_of_mem _ (hfg (π' q) V hVf hVg t₀)

end Hironaka.Manifold

end
