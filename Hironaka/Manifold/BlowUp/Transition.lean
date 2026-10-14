/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Charts
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Transition laws of the blow-up charts

The function-level properties of the local model of the blowing-up with centre a coordinate
subspace [BM88, Definition 4.1], in block form. The
chart maps `π_i = blowUpChartMap σ i` and the transition maps `T_ik = blowUpTransition σ i k`
satisfy `π_k ∘ T_ik = π_i`, `T_ki ∘ T_ik = id` and the cocycle law `T_kl ∘ T_ik = T_il` on the
transition domains `{u_{σ k} ≠ 0}`, which are open; the transition maps are analytic there (they
are rational in the coordinates) and the chart maps are polynomial. The chart map `π_i` is
injective off the hyperplane `{u_{σ i} = 0}`, with the analytic inverse `blowUpChartInv σ i`,
`π_i u` lies on the centre exactly when `u_{σ i} = 0`, and `π_i` fixes the centre pointwise
(`BlowUpGlue.blowUpChartMap_of_mem_center`). For a compact set `C`, the set of points
`u` of chart `i` with `π_i u ∈ C` and all ratio coordinates of norm at most one is compact, and
every point of the chart is carried by a transition into such a box, the box of the chart of a
block coordinate of maximal norm; this is the estimate behind the properness of the blow-down map
of the glued blowing-up (`Hironaka.Manifold.BlowUp.GluedTopology`). The file ends with the two
charts and the transition of the blowing-up of the plane at the origin, computed explicitly.

The transition formula, the cocycle law and the compactness estimate are not stated in the
source; they are elementary verifications in coordinates.
-/

public section

open scoped ContDiff
open Filter

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n c : ℕ} (σ : Fin c ↪ Fin n) {i k l : Fin c} (u : Fin n → 𝕜)

/-! ### Case analysis on a coordinate index -/

/-- Every index `j` is a block index `σ l` or off the block. -/
theorem exists_eq_or_forall_ne (j : Fin n) : (∃ l, σ l = j) ∨ ∀ l, σ l ≠ j := by
  by_cases h : ∃ l, σ l = j
  · exact Or.inl h
  · exact Or.inr fun l hl => h ⟨l, hl⟩

namespace BlowUpGlue

/-- `π_i` fixes the centre pointwise. -/
theorem blowUpChartMap_of_mem_center {σ : Fin c ↪ Fin n} {i : Fin c} {x : Fin n → 𝕜}
    (hx : x ∈ blowUpCenter σ) : blowUpChartMap σ i x = x := by
  funext j
  rcases exists_eq_or_forall_ne σ j with ⟨l, rfl⟩ | hj
  · by_cases hl : l = i
    · subst hl
      exact blowUpChartMap_apply_scaling σ x
    · rw [blowUpChartMap_apply_ratio σ x hl, hx i, zero_mul, hx l]
  · exact blowUpChartMap_apply_off σ x hj

end BlowUpGlue

/-! ### Compatibility of the chart maps with the transitions: `π_k ∘ T_ik = π_i` -/

theorem blowUpChartMap_blowUpTransition (hu : u ∈ blowUpTransitionDomain σ i k) :
    blowUpChartMap σ k (blowUpTransition σ i k u) = blowUpChartMap σ i u := by
  by_cases hik : i = k
  · subst hik; rw [blowUpTransition_self]; rfl
  have huk : u (σ k) ≠ 0 := (mem_blowUpTransitionDomain σ u hik).mp hu
  funext j
  rcases exists_eq_or_forall_ne σ j with ⟨l, rfl⟩ | hj
  · by_cases hlk : l = k
    · subst hlk
      rw [blowUpChartMap_apply_scaling, blowUpTransition_apply_k σ u hik,
        blowUpChartMap_apply_ratio σ u (Ne.symm hik)]
    by_cases hli : l = i
    · subst hli
      rw [blowUpChartMap_apply_ratio σ _ hlk, blowUpTransition_apply_k σ u hik,
        blowUpTransition_apply_i σ u hik, blowUpChartMap_apply_scaling]
      field_simp
    · rw [blowUpChartMap_apply_ratio σ _ hlk, blowUpTransition_apply_k σ u hik,
        blowUpTransition_apply_block σ u hik hli hlk, blowUpChartMap_apply_ratio σ u hli]
      field_simp
  · rw [blowUpChartMap_apply_off σ _ hj, blowUpTransition_apply_off σ u hik hj,
      blowUpChartMap_apply_off σ u hj]

/-! ### Inverse and cocycle laws, openness and analyticity -/

theorem blowUpTransition_mem_domain (hu : u ∈ blowUpTransitionDomain σ i k) :
    blowUpTransition σ i k u ∈ blowUpTransitionDomain σ k i := by
  by_cases hik : i = k
  · subst hik; rw [blowUpTransitionDomain_self]; trivial
  have huk : u (σ k) ≠ 0 := (mem_blowUpTransitionDomain σ u hik).mp hu
  rw [mem_blowUpTransitionDomain σ _ (Ne.symm hik), blowUpTransition_apply_i σ u hik]
  exact inv_ne_zero huk

/-- The inverse law `T_ki ∘ T_ik = id` on the transition domain. -/
theorem blowUpTransition_blowUpTransition (hu : u ∈ blowUpTransitionDomain σ i k) :
    blowUpTransition σ k i (blowUpTransition σ i k u) = u := by
  by_cases hik : i = k
  · subst hik; rw [blowUpTransition_self]; rfl
  have huk : u (σ k) ≠ 0 := (mem_blowUpTransitionDomain σ u hik).mp hu
  have hki : k ≠ i := Ne.symm hik
  funext j
  rcases exists_eq_or_forall_ne σ j with ⟨l, rfl⟩ | hj
  · by_cases hli : l = i
    · subst hli
      rw [blowUpTransition_apply_k σ _ hki, blowUpTransition_apply_k σ u hik,
        blowUpTransition_apply_i σ u hik]
      field_simp
    by_cases hlk : l = k
    · subst hlk
      rw [blowUpTransition_apply_i σ _ hki, blowUpTransition_apply_i σ u hik, inv_inv]
    · rw [blowUpTransition_apply_block σ _ hki hlk hli,
        blowUpTransition_apply_block σ u hik hli hlk, blowUpTransition_apply_i σ u hik]
      field_simp
  · rw [blowUpTransition_apply_off σ _ hki hj, blowUpTransition_apply_off σ u hik hj]

/-- The cocycle law `T_kl ∘ T_ik = T_il` where both sides are defined. -/
theorem blowUpTransition_cocycle (hk : u ∈ blowUpTransitionDomain σ i k)
    (hl : u ∈ blowUpTransitionDomain σ i l) :
    blowUpTransition σ i k u ∈ blowUpTransitionDomain σ k l ∧
      blowUpTransition σ k l (blowUpTransition σ i k u) = blowUpTransition σ i l u := by
  by_cases hik : i = k
  · subst hik; rw [blowUpTransition_self]; exact ⟨hl, rfl⟩
  by_cases hil : i = l
  · subst hil
    rw [blowUpTransition_self]
    exact ⟨blowUpTransition_mem_domain σ u hk, blowUpTransition_blowUpTransition σ u hk⟩
  by_cases hkl : k = l
  · subst hkl
    refine ⟨by rw [blowUpTransitionDomain_self]; trivial, ?_⟩
    rw [blowUpTransition_self]; rfl
  have huk : u (σ k) ≠ 0 := (mem_blowUpTransitionDomain σ u hik).mp hk
  have hul : u (σ l) ≠ 0 := (mem_blowUpTransitionDomain σ u hil).mp hl
  have hli : l ≠ i := Ne.symm hil
  have hlk : l ≠ k := Ne.symm hkl
  have hmem : blowUpTransition σ i k u ∈ blowUpTransitionDomain σ k l := by
    rw [mem_blowUpTransitionDomain σ _ hkl, blowUpTransition_apply_block σ u hik hli hlk]
    exact div_ne_zero hul huk
  refine ⟨hmem, ?_⟩
  funext j
  rcases exists_eq_or_forall_ne σ j with ⟨m, rfl⟩ | hj
  · by_cases hml : m = l
    · subst hml
      rw [blowUpTransition_apply_k σ _ hkl, blowUpTransition_apply_k σ u hik,
        blowUpTransition_apply_block σ u hik hli hlk, blowUpTransition_apply_k σ u hil]
      field_simp
    by_cases hmk : m = k
    · subst hmk
      rw [blowUpTransition_apply_i σ _ hkl, blowUpTransition_apply_block σ u hik hli hlk,
        blowUpTransition_apply_block σ u hil (Ne.symm hik) hkl]
      field_simp
    by_cases hmi : m = i
    · subst hmi
      rw [blowUpTransition_apply_block σ _ hkl hmk hml, blowUpTransition_apply_i σ u hik,
        blowUpTransition_apply_block σ u hik hli hlk, blowUpTransition_apply_i σ u hil]
      field_simp
    · rw [blowUpTransition_apply_block σ _ hkl hmk hml,
        blowUpTransition_apply_block σ u hik hmi hmk, blowUpTransition_apply_block σ u hik hli hlk,
        blowUpTransition_apply_block σ u hil hmi hml]
      field_simp
  · rw [blowUpTransition_apply_off σ _ hkl hj, blowUpTransition_apply_off σ u hik hj,
      blowUpTransition_apply_off σ u hil hj]

/-- The transition domain is open. -/
theorem isOpen_blowUpTransitionDomain : IsOpen (blowUpTransitionDomain (𝕜 := 𝕜) σ i k) := by
  unfold blowUpTransitionDomain
  split_ifs
  · exact isOpen_univ
  · exact isOpen_compl_singleton.preimage (continuous_apply (σ k))

/-- A map into `Fin n → 𝕜` is analytic when its coordinates are. -/
theorem analyticAt_pi_of_forall {f : (Fin n → 𝕜) → (Fin n → 𝕜)} {x : Fin n → 𝕜}
    (h : ∀ j, AnalyticAt 𝕜 (fun v => f v j) x) : AnalyticAt 𝕜 f x :=
  (contDiffAt_pi.mpr fun j => (h j).contDiffAt).analyticAt

/-- Every point `u` of chart `i`, on the exceptional hyperplane or not, is carried by some
transition `T_ik` into the box `{‖u'_{σ l}‖ ≤ 1, l ≠ k}` of chart `k`: `k = i` when all ratio
coordinates have norm at most `1`, otherwise `k` is the index of a ratio coordinate of maximal
norm. Not in the sources; the boxes cover the exceptional divisor, which gives the properness of
the blow-down map. -/
theorem exists_blowUpTransition_mem_box :
    ∃ k, u ∈ blowUpTransitionDomain σ i k ∧ ∀ l, l ≠ k → ‖blowUpTransition σ i k u (σ l)‖ ≤ 1 := by
  classical
  by_cases hbig : ∃ l, l ≠ i ∧ 1 < ‖u (σ l)‖
  · obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun l => l ≠ i)
      (fun l => ‖u (σ l)‖) (by obtain ⟨l, hl, -⟩ := hbig; exact ⟨l, by simp [hl]⟩)
    have hki : k ≠ i := by simpa using hk
    have hk1 : 1 < ‖u (σ k)‖ := by
      obtain ⟨l, hl, hl1⟩ := hbig
      exact hl1.trans_le (hmax l (by simp [hl]))
    have hk0 : u (σ k) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hk1
      exact lt_irrefl _ (hk1.trans zero_lt_one)
    refine ⟨k, (mem_blowUpTransitionDomain σ u hki.symm).mpr hk0, fun l hlk => ?_⟩
    by_cases hli : l = i
    · subst hli
      rw [blowUpTransition_apply_i σ u hki.symm, norm_inv]
      exact inv_le_one_of_one_le₀ hk1.le
    · rw [blowUpTransition_apply_block σ u hki.symm hli hlk, norm_div]
      exact div_le_one_of_le₀ (hmax l (by simp [hli])) (norm_nonneg _)
  · push Not at hbig
    refine ⟨i, by rw [blowUpTransitionDomain_self]; exact Set.mem_univ u, fun l hli => ?_⟩
    rw [blowUpTransition_self]
    exact hbig l hli

/-- The coordinate projections are analytic. -/
theorem analyticAt_apply (j : Fin n) (x : Fin n → 𝕜) : AnalyticAt 𝕜 (fun v : Fin n → 𝕜 => v j) x :=
  (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) j).analyticAt x

/-- The transition map is analytic on its domain. -/
theorem analyticOnNhd_blowUpTransition :
    AnalyticOnNhd 𝕜 (blowUpTransition (𝕜 := 𝕜) σ i k) (blowUpTransitionDomain σ i k) := by
  classical
  intro v hv
  by_cases hik : i = k
  · subst hik; rw [blowUpTransition_self]; exact analyticAt_id
  have hvk : v (σ k) ≠ 0 := (mem_blowUpTransitionDomain σ v hik).mp hv
  refine analyticAt_pi_of_forall fun j => ?_
  simp only [blowUpTransition, hik, ite_false]
  split_ifs
  · exact (analyticAt_apply _ _).mul (analyticAt_apply _ _)
  · exact (analyticAt_apply _ _).inv hvk
  · exact (analyticAt_apply _ _).div (analyticAt_apply _ _) hvk
  · exact analyticAt_apply _ _

/-- The chart map `π_i` is analytic (it is polynomial in the coordinates). -/
theorem contDiff_blowUpChartMap : ContDiff 𝕜 ω (blowUpChartMap (𝕜 := 𝕜) σ i) := by
  classical
  refine contDiff_pi.mpr fun j => ?_
  simp only [blowUpChartMap]
  split_ifs
  · exact (contDiff_apply 𝕜 𝕜 (n := ω) (σ i)).mul (contDiff_apply 𝕜 𝕜 (n := ω) j)
  · exact contDiff_apply 𝕜 𝕜 (n := ω) j

/-! ### The exceptional set and the inverse chart map -/

theorem blowUpChartMap_mem_center_iff : blowUpChartMap σ i u ∈ blowUpCenter σ ↔ u (σ i) = 0 := by
  constructor
  · intro h
    have := h i
    rwa [blowUpChartMap_apply_scaling] at this
  · intro h k
    by_cases hk : k = i
    · subst hk; rwa [blowUpChartMap_apply_scaling]
    · rw [blowUpChartMap_apply_ratio σ u hk, h, zero_mul]

/-- `π_i ∘ π_i⁻¹ = id` off the hyperplane `{x_{σ i} = 0}`. -/
theorem blowUpChartMap_blowUpChartInv (x : Fin n → 𝕜) (hx : x (σ i) ≠ 0) :
    blowUpChartMap σ i (blowUpChartInv σ i x) = x := by
  funext j
  rcases exists_eq_or_forall_ne σ j with ⟨l, rfl⟩ | hj
  · by_cases hli : l = i
    · subst hli; rw [blowUpChartMap_apply_scaling, blowUpChartInv_apply_scaling]
    · rw [blowUpChartMap_apply_ratio σ _ hli, blowUpChartInv_apply_scaling,
        blowUpChartInv_apply_ratio σ x hli]
      field_simp
  · rw [blowUpChartMap_apply_off σ _ hj, blowUpChartInv_apply_off σ x hj]

/-- `π_i⁻¹ ∘ π_i = id` off the exceptional hyperplane `{u_{σ i} = 0}`. -/
theorem blowUpChartInv_blowUpChartMap (hu : u (σ i) ≠ 0) :
    blowUpChartInv σ i (blowUpChartMap σ i u) = u := by
  funext j
  rcases exists_eq_or_forall_ne σ j with ⟨l, rfl⟩ | hj
  · by_cases hli : l = i
    · subst hli; rw [blowUpChartInv_apply_scaling, blowUpChartMap_apply_scaling]
    · rw [blowUpChartInv_apply_ratio σ _ hli, blowUpChartMap_apply_scaling,
        blowUpChartMap_apply_ratio σ u hli]
      field_simp
  · rw [blowUpChartInv_apply_off σ _ hj, blowUpChartMap_apply_off σ u hj]

/-- The chart map `π_i` is injective off the exceptional hyperplane `{u_{σ i} = 0}`. -/
theorem blowUpChartMap_injOn : Set.InjOn (blowUpChartMap σ i) {u : Fin n → 𝕜 | u (σ i) ≠ 0} := by
  intro u hu v hv huv
  rw [← blowUpChartInv_blowUpChartMap σ u hu, ← blowUpChartInv_blowUpChartMap σ v hv, huv]

/-- The inverse `π_i⁻¹` is analytic off the hyperplane `{x_{σ i} = 0}`. -/
theorem analyticOnNhd_blowUpChartInv :
    AnalyticOnNhd 𝕜 (blowUpChartInv (𝕜 := 𝕜) σ i) {x : Fin n → 𝕜 | x (σ i) ≠ 0} := by
  classical
  intro x hx
  refine analyticAt_pi_of_forall fun j => ?_
  simp only [blowUpChartInv]
  split_ifs
  · exact (analyticAt_apply _ _).div (analyticAt_apply _ _) hx
  · exact analyticAt_apply _ _

/-! ### The compactness estimate -/

theorem isCompact_blowUpChartMap_preimage_inter_box {C : Set (Fin n → 𝕜)} (hC : IsCompact C) :
    IsCompact {u : Fin n → 𝕜 | blowUpChartMap σ i u ∈ C ∧ ∀ k, k ≠ i → ‖u (σ k)‖ ≤ 1} := by
  have hcont : Continuous (blowUpChartMap (𝕜 := 𝕜) σ i) := (contDiff_blowUpChartMap σ).continuous
  have : ProperSpace (Fin n → 𝕜) := FiniteDimensional.proper_rclike 𝕜 (Fin n → 𝕜)
  have hset : {u : Fin n → 𝕜 | blowUpChartMap σ i u ∈ C ∧ ∀ k, k ≠ i → ‖u (σ k)‖ ≤ 1} =
      blowUpChartMap σ i ⁻¹' C ∩ ⋂ k, ⋂ (_ : k ≠ i), {u : Fin n → 𝕜 | ‖u (σ k)‖ ≤ 1} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
  rw [hset]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine (hC.isClosed.preimage hcont).inter ?_
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_le ((continuous_apply (σ k)).norm) continuous_const
  · obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → 𝕜)) (r := max R 1)).subset
      fun u ⟨huC, hbox'⟩ => ?_
    have hbox : ∀ k, k ≠ i → ‖u (σ k)‖ ≤ 1 := fun k hk => Set.mem_iInter₂.mp hbox' k hk
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (le_max_of_le_right zero_le_one)).mpr fun j => ?_
    rcases exists_eq_or_forall_ne σ j with ⟨l, rfl⟩ | hj
    · by_cases hli : l = i
      · subst hli
        calc ‖u (σ l)‖ = ‖blowUpChartMap σ l u (σ l)‖ := by simp
          _ ≤ ‖blowUpChartMap σ l u‖ := norm_le_pi_norm _ _
          _ ≤ R := mem_closedBall_zero_iff.mp (hR huC)
          _ ≤ max R 1 := le_max_left _ _
      · exact (hbox l hli).trans (le_max_right _ _)
    · calc ‖u j‖ = ‖blowUpChartMap σ i u j‖ := by rw [blowUpChartMap_apply_off σ u hj]
        _ ≤ ‖blowUpChartMap σ i u‖ := norm_le_pi_norm _ _
        _ ≤ R := mem_closedBall_zero_iff.mp (hR huC)
        _ ≤ max R 1 := le_max_left _ _

/-- A point `x` off the centre is `π_i u` for some `i` and some `u` with `‖u_{σ k}‖ ≤ 1` for all
`k ≠ i`, namely for `i` the index of a block coordinate of `x` of maximal norm. -/
theorem exists_mem_box_of_ne_center (x : Fin n → 𝕜) (hx : x ∉ blowUpCenter σ) :
    ∃ (i : Fin c) (u : Fin n → 𝕜), blowUpChartMap σ i u = x ∧ ∀ k, k ≠ i → ‖u (σ k)‖ ≤ 1 := by
  classical
  have hne : (Finset.univ : Finset (Fin c)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
    exact hx fun k => (h.false k).elim
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun k => ‖x (σ k)‖) hne
  have hxi : x (σ i) ≠ 0 := by
    intro h0
    apply hx
    intro k
    have := hi k (Finset.mem_univ k)
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.mp this
  refine ⟨i, blowUpChartInv σ i x, blowUpChartMap_blowUpChartInv σ x hxi, fun k hk => ?_⟩
  rw [blowUpChartInv_apply_ratio σ x hk, norm_div, div_le_one (norm_pos_iff.mpr hxi)]
  exact hi k (Finset.mem_univ k)

/-! ### The blowing-up of the plane at the origin -/

theorem blowUpChartMap_fin_two_zero (a b : 𝕜) :
    blowUpChartMap (Function.Embedding.refl (Fin 2)) 0 ![a, b] = ![a, a * b] := by
  funext j
  fin_cases j <;> simp [blowUpChartMap]

/-- Chart `1` of the blowing-up of the plane at the origin: `(s, t) ↦ (ts, t)`. -/
theorem blowUpChartMap_fin_two_one (a b : 𝕜) :
    blowUpChartMap (Function.Embedding.refl (Fin 2)) 1 ![a, b] = ![b * a, b] := by
  funext j
  fin_cases j <;> simp [blowUpChartMap]

/-- The transition from chart `0` to chart `1` of the blowing-up of the plane at the origin:
`(u, v) ↦ (1/v, uv)` on `v ≠ 0`. -/
theorem blowUpTransition_fin_two (a b : 𝕜) :
    blowUpTransition (Function.Embedding.refl (Fin 2)) 0 1 ![a, b] = ![b⁻¹, a * b] := by
  funext j
  fin_cases j <;> simp [blowUpTransition]

end Manifold
