/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Identity
public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Resolution.Analytic.Restrict.StrictSubspaceSeqTransport
import Hironaka.Resolution.Analytic.Wlo09.IsoOverReg
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A closed subspace containing connected components of the ambient manifold

Włodarczyk's embedded desingularization [Wlo09, Theorem 2.0.2] places no condition on the closed
subspace `Y ⊆ M` beyond its being a subspace, while the embedded desingularization functor of this
library takes a triple whose ideal sheaf has nonzero stalks (`AnalyticTriple.isNonzeroEverywhere`).
By the identity theorem the set `Z` of points at which the ideal sheaf `𝓘_Y` vanishes is open and
closed (`IdealSheaf.isClopen_setOf_stalkIdeal_eq_bot`), a union of connected components of `M`
contained in `Y`. On it the desingularization is the identity, and the functor is applied to the
ideal sheaf which is `𝓘_Y` off `Z` and the unit ideal on `Z`:

* `IdealSheaf.unitOn Z`: the ideal sheaf which is the unit ideal on the clopen set `Z` and zero off
  it, and `IdealSheaf.unitOnZeroStalks I = I + unitOn {x | I_x = 0}`, the ideal sheaf `I` made the
  unit ideal on the components where it vanishes: reduced when `I` is, with nonzero stalks, and
  with the same singular locus `Sing(Y) = Y ∖ Reg(Y)` as `I` (a point where `I` vanishes is a
  simple point of `Y`, the local ring of `Y` there being the regular local ring `𝒪_{M,x}`).
* `FiniteSuccession.stalkIdeal_strictTransformSubspaceSeq_congr`: the strict transforms of two
  ideal sheaves agree at every point over the set where the ideal sheaves agree — the strict
  transform under a blow-up is the saturation of the total transform, a stalk-wise construction.
* `IdealSheaf.IsDesingularizedBy.of_eq_off_clopen`: the clauses of [Wlo09, Theorem 2.0.2] on a
  succession transfer from `I'` to `I` when `I = I'` off a clopen set `Z`, `I = 0` and `I' = 1`
  on `Z`, and the centres lie over `Sing(Y')`: over `Z` nothing is blown up, the exceptional
  divisor is empty, and the strict transform of `I` is the zero ideal, whose closed subspace is
  the ambient manifold itself, smooth and trivially transversal to the empty divisor.
-/

public section

noncomputable section

open Set Topology TopologicalSpace Opposite CategoryTheory Manifold
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace AnalyticManifold.IdealSheaf

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The unit ideal on a clopen set -/

open scoped Classical in
/-- The stalks of the ideal sheaf which is the unit ideal on the clopen set `Z` and zero off it
have local generators: the section `1` on `Z`, no section on its complement. -/
theorem hasLocalGenerators_unitOn (Z : Set M) (hZ : IsClopen Z) :
    Manifold.IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M)
      fun x => if x ∈ Z then (⊤ : Ideal (stalkRing M x)) else ⊥ := by
  intro a
  by_cases ha : a ∈ Z
  · refine ⟨⟨Z, hZ.isOpen⟩, ha, Unit, inferInstance, fun _ => 1, fun b hb => ?_⟩
    beta_reduce
    rw [ite_eq_left (show b ∈ Z from hb), eq_comm, Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨(), map_one _⟩
  · refine ⟨⟨Zᶜ, hZ.isClosed.isOpen_compl⟩, ha, Empty, inferInstance, fun i => i.elim,
      fun b hb => ?_⟩
    beta_reduce
    rw [ite_eq_right (show b ∉ Z from hb)]
    simp only [Set.range_eq_empty, Ideal.span_empty]

open scoped Classical in
/-- The ideal sheaf which is the unit ideal on the clopen set `Z` and zero off it. -/
def unitOn (Z : Set M) (hZ : IsClopen Z) : IdealSheaf M :=
  Manifold.IdealSheaf.ofStalks _ _ (hasLocalGenerators_unitOn Z hZ)

theorem stalkIdeal_unitOn_of_mem {Z : Set M} (hZ : IsClopen Z) {x : M} (hx : x ∈ Z) :
    (unitOn Z hZ).stalkIdeal x = ⊤ := by
  classical
  rw [unitOn, Manifold.IdealSheaf.stalkIdeal_ofStalks, ite_eq_left hx]

theorem stalkIdeal_unitOn_of_notMem {Z : Set M} (hZ : IsClopen Z) {x : M} (hx : x ∉ Z) :
    (unitOn Z hZ).stalkIdeal x = ⊥ := by
  classical
  rw [unitOn, Manifold.IdealSheaf.stalkIdeal_ofStalks, ite_eq_right hx]

/-! ### An ideal sheaf made the unit ideal on the components where it vanishes -/

variable (I : IdealSheaf M)

/-- The clopen set of points at which `I` vanishes (`isClopen_setOf_stalkIdeal_eq_bot`, the
identity theorem): the union of the connected components of `M` on which `I = 0`. -/
abbrev zeroLocus : Set M := {x | I.stalkIdeal x = ⊥}

theorem isClopen_zeroLocus : IsClopen I.zeroLocus := I.isClopen_setOf_stalkIdeal_eq_bot

/-- **The ideal sheaf `I` made the unit ideal on the components where it vanishes**:
`I + unitOn {x | I_x = 0}`, whose stalk is `I_x` where `I_x ≠ 0` and the unit ideal where
`I_x = 0`. -/
def unitOnZeroStalks : IdealSheaf M := I + unitOn I.zeroLocus I.isClopen_zeroLocus

theorem stalkIdeal_unitOnZeroStalks_of_eq_bot {x : M} (hx : I.stalkIdeal x = ⊥) :
    I.unitOnZeroStalks.stalkIdeal x = ⊤ := by
  rw [unitOnZeroStalks, Manifold.IdealSheaf.stalkIdeal_add,
    stalkIdeal_unitOn_of_mem _ (show x ∈ I.zeroLocus from hx), sup_top_eq]

theorem stalkIdeal_unitOnZeroStalks_of_ne_bot {x : M} (hx : I.stalkIdeal x ≠ ⊥) :
    I.unitOnZeroStalks.stalkIdeal x = I.stalkIdeal x := by
  rw [unitOnZeroStalks, Manifold.IdealSheaf.stalkIdeal_add,
    stalkIdeal_unitOn_of_notMem _ (show x ∉ I.zeroLocus from hx), sup_bot_eq]

/-- `I` made the unit ideal on its zero components is reduced when `I` is. -/
theorem isReduced_unitOnZeroStalks (hI : I.IsReduced) : I.unitOnZeroStalks.IsReduced := by
  intro x
  by_cases hx : I.stalkIdeal x = ⊥
  · rw [I.stalkIdeal_unitOnZeroStalks_of_eq_bot hx]
    exact le_top
  · rw [I.stalkIdeal_unitOnZeroStalks_of_ne_bot hx]
    exact hI x

/-- `I` made the unit ideal on its zero components has nonzero stalks. -/
theorem isNonzeroEverywhere_unitOnZeroStalks [FiniteDimensional 𝕜 E] :
    I.unitOnZeroStalks.IsNonzeroEverywhere := by
  intro x
  by_cases hx : I.stalkIdeal x = ⊥
  · rw [I.stalkIdeal_unitOnZeroStalks_of_eq_bot hx]
    intro h
    exact one_ne_zero (Ideal.mem_bot.mp (h ▸ Submodule.mem_top : (1 : stalkRing M x) ∈ ⊥))
  · rwa [I.stalkIdeal_unitOnZeroStalks_of_ne_bot hx]

/-- A point at which `I` vanishes is a simple point of the subspace of `I`: the local ring there
is `𝒪_{M,x}/0 ≅ 𝒪_{M,x}`, a regular local ring. -/
theorem zeroLocus_subset_regularLocus [FiniteDimensional 𝕜 E] :
    I.zeroLocus ⊆ I.regularLocus := by
  intro x hx
  change IsRegularLocalRing (stalkRing M x ⧸ I.stalkIdeal x)
  rw [show I.stalkIdeal x = ⊥ from hx]
  exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (stalkRing M x)).symm

/-- A point where an ideal sheaf is the unit ideal is not a simple point of its subspace (it is
not a point of the subspace: the local ring there is the zero ring, which is not local). -/
theorem notMem_regularLocus_of_stalkIdeal_eq_top {J : IdealSheaf M} {x : M}
    (hx : J.stalkIdeal x = ⊤) : x ∉ J.regularLocus := by
  intro h
  have hsub : Subsingleton (stalkRing M x ⧸ J.stalkIdeal x) :=
    Ideal.Quotient.subsingleton_iff.mpr hx
  have hreg : IsRegularLocalRing (stalkRing M x ⧸ J.stalkIdeal x) := h
  exact not_subsingleton _ hsub

/-- **`I` and `I` made the unit ideal on its zero components have the same singular locus**
`Sing(Y) = Y ∖ Reg(Y)`: off the zero components the stalks agree, and on them `I` is a simple
point while the unit ideal is not a point of its subspace. -/
theorem support_diff_regularLocus_unitOnZeroStalks [FiniteDimensional 𝕜 E] :
    I.unitOnZeroStalks.support \ I.unitOnZeroStalks.regularLocus =
      I.support \ I.regularLocus := by
  ext x
  by_cases hx : I.stalkIdeal x = ⊥
  · have h1 : x ∉ I.unitOnZeroStalks.support := fun h =>
      h (I.stalkIdeal_unitOnZeroStalks_of_eq_bot hx)
    have h2 : x ∈ I.regularLocus := I.zeroLocus_subset_regularLocus hx
    exact ⟨fun h => absurd h.1 h1, fun h => absurd h2 h.2⟩
  · have e := I.stalkIdeal_unitOnZeroStalks_of_ne_bot hx
    simp only [Set.mem_sdiff, IdealSheaf.support, IdealSheaf.regularLocus, Set.mem_ofPred_eq]
    rw [e]

/-- Making the unit ideal on the zero components commutes with the pull-back along a local
analytic isomorphism `g`: the germ maps are bijective, so a stalk of the pull-back vanishes
exactly when the stalk at the image point does. -/
theorem unitOnZeroStalks_pullback_of_isLocalDiffeomorph [FiniteDimensional 𝕜 E]
    {N : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) :
    unitOnZeroStalks (I.pullback g g.contMDiff) = I.unitOnZeroStalks.pullback g g.contMDiff := by
  refine Manifold.IdealSheaf.ext fun x => ?_
  have hbij := Manifold.germMap_bijective_of_isLocalDiffeomorphAt g g.contMDiff (hg x)
  by_cases hx : I.stalkIdeal (g x) = ⊥
  · have h0 : (I.pullback g g.contMDiff).stalkIdeal x = ⊥ := by
      rw [Manifold.IdealSheaf.stalkIdeal_pullback, hx, Ideal.map_bot]
    rw [stalkIdeal_unitOnZeroStalks_of_eq_bot _ h0, Manifold.IdealSheaf.stalkIdeal_pullback,
      I.stalkIdeal_unitOnZeroStalks_of_eq_bot hx, Ideal.map_top]
  · have h0 : (I.pullback g g.contMDiff).stalkIdeal x ≠ ⊥ := by
      rw [Manifold.IdealSheaf.stalkIdeal_pullback, Ne, Ideal.map_eq_bot_iff_of_injective hbij.1]
      exact hx
    rw [stalkIdeal_unitOnZeroStalks_of_ne_bot _ h0, Manifold.IdealSheaf.stalkIdeal_pullback,
      Manifold.IdealSheaf.stalkIdeal_pullback, I.stalkIdeal_unitOnZeroStalks_of_ne_bot hx]

end AnalyticManifold.IdealSheaf

/-! ### The strict transforms of two ideal sheaves agreeing over a set -/

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The strict transforms of two ideal sheaves which agree at every point off `Z` agree at every
point over the complement of `Z`: the strict transform under a blow-up is the saturation of the
total transform by the exceptional ideal, which depends only on the stalk of the ideal sheaf at
the image point (`strictTransformSubspace_eq_ofStalks`, `saturationStalk`). -/
theorem stalkIdeal_strictTransformSubspaceSeq_congr {I I' : IdealSheaf M} {Z : Set M}
    (heq : ∀ x ∉ Z, I.stalkIdeal x = I'.stalkIdeal x) (i : Fin (S.length + 1)) :
    ∀ z : S.stage i, S.stageMap i z ∉ Z →
      (S.strictTransformSubspaceSeq I i).stalkIdeal z =
        (S.strictTransformSubspaceSeq I' i).stalkIdeal z := by
  induction i using Fin.induction with
  | zero =>
    intro z hz
    obtain ⟨z', rfl⟩ : ∃ z' : (M : Type u), z' = z := ⟨z, rfl⟩
    exact heq z' hz
  | succ i ih =>
    intro z hz
    have h := ih (S.map i z) hz
    rw [strictTransformSubspaceSeq_succ, strictTransformSubspaceSeq_succ,
      Hironaka.Manifold.strictTransformSubspace_eq_ofStalks,
      Hironaka.Manifold.strictTransformSubspace_eq_ofStalks,
      Manifold.IdealSheaf.stalkIdeal_ofStalks, Manifold.IdealSheaf.stalkIdeal_ofStalks]
    unfold saturationStalk
    simp only [Manifold.IdealSheaf.stalkIdeal_pullback]
    rw [h]

/-- Over a set `Z` on which `I` vanishes and `I'` is the unit ideal, if the centres of `S` lie
over `Sing(Y')`, no exceptional divisor lies over `Z`, and the last strict transform of `I` has
zero stalk there (`stalkIdeal_strictTransformSubspaceSeq_eq_map_of_notMem_support`). -/
theorem stalkIdeal_strictTransformSubspaceSeq_last_eq_bot_of_mem {I I' : IdealSheaf M}
    {Z : Set M} (hbot : ∀ x ∈ Z, I.stalkIdeal x = ⊥) (htop : ∀ x ∈ Z, I'.stalkIdeal x = ⊤)
    (hc : S.CentersOver (I'.support \ I'.regularLocus)) (z : S.last) (hz : S.composite z ∈ Z) :
    (S.strictTransformSubspaceSeq I (Fin.last _)).stalkIdeal z = ⊥ := by
  have hoff : z ∉ (S.totalTransformSeq (Fin.last _)).support := fun hmem =>
    (S.support_totalTransformSeq_subset_preimage_of_centersOver hc (Fin.last _) hmem).1
      (htop _ hz)
  rw [S.stalkIdeal_strictTransformSubspaceSeq_eq_map_of_notMem_support I (Fin.last _) hoff,
    hbot _ (show S.stageMap (Fin.last _) z ∈ Z from hz), Ideal.map_bot]

/-- **The transversal chart clause transfers to an ideal sheaf vanishing on some connected
components**, with the same simple normal crossings family `G`: over the clopen `Z` the strict
transform of `I` has zero stalk, so any snc chart of `G` restricted over `Z` is adapted to it in
codimension `0`; off `Z` the strict transforms of `I` and `I'` agree
(`stalkIdeal_strictTransformSubspaceSeq_congr`), and the chart for `I'` restricted over the
complement of `Z` serves. -/
theorem exists_adaptedChart_strictTransformSubspaceSeq_of_eq_off_clopen {I I' : IdealSheaf M}
    {Z : Set M} (hZ : IsClopen Z) (hbot : ∀ x ∈ Z, I.stalkIdeal x = ⊥)
    (htop : ∀ x ∈ Z, I'.stalkIdeal x = ⊤) (heq : ∀ x ∉ Z, I.stalkIdeal x = I'.stalkIdeal x)
    (hc : S.CentersOver (I'.support \ I'.regularLocus)) {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
    {G : HypersurfaceFamily S.last} (hG : G.IsSnc ψ)
    (hpt : ∀ a ∈ (S.strictTransformSubspaceSeq I' (Fin.last _)).support,
      ∃ (c : ℕ) (φ : OpenPartialHomeomorph S.last E) (σ : Fin c ↪ Fin n)
        (cidx : {j // a ∈ G.hyp j} → Fin n),
        IsAdaptedChart ψ (S.strictTransformSubspaceSeq I' (Fin.last _)).support φ σ ∧
          G.IsSncChartAt ψ φ a cidx ∧ ∀ j, cidx j ∉ Set.range σ) :
    ∀ a ∈ (S.strictTransformSubspaceSeq I (Fin.last _)).support,
      ∃ (c : ℕ) (φ : OpenPartialHomeomorph S.last E) (σ : Fin c ↪ Fin n)
        (cidx : {j // a ∈ G.hyp j} → Fin n),
        IsAdaptedChart ψ (S.strictTransformSubspaceSeq I (Fin.last _)).support φ σ ∧
          G.IsSncChartAt ψ φ a cidx ∧ ∀ j, cidx j ∉ Set.range σ := by
  have hbotY := S.stalkIdeal_strictTransformSubspaceSeq_last_eq_bot_of_mem hbot htop hc
  have hcong : ∀ z : S.last, S.composite z ∉ Z →
      (S.strictTransformSubspaceSeq I (Fin.last _)).stalkIdeal z =
        (S.strictTransformSubspaceSeq I' (Fin.last _)).stalkIdeal z :=
    fun z hz => S.stalkIdeal_strictTransformSubspaceSeq_congr heq (Fin.last _) z hz
  have hWopen : IsOpen (S.composite ⁻¹' Z) := hZ.isOpen.preimage S.composite.contMDiff.continuous
  have hW'open : IsOpen (S.composite ⁻¹' Zᶜ) :=
    hZ.isClosed.isOpen_compl.preimage S.composite.contMDiff.continuous
  intro a ha
  by_cases haZ : S.composite a ∈ Z
  · -- over `Z`: codimension `0`, any snc chart of the exceptional family restricted over `Z`
    obtain ⟨φ, cidx, hφ⟩ := hG.2.2 a
    refine ⟨0, φ.restrOpen (S.composite ⁻¹' Z) hWopen, Function.Embedding.ofIsEmpty, cidx,
      ⟨?_, fun x hx => ⟨fun _ i => i.elim0, fun _ => ?_⟩⟩, hφ.restrOpen hWopen haZ,
      fun j ⟨i, _⟩ => i.elim0⟩
    · rw [OpenPartialHomeomorph.restrOpen_eq_restr]
      exact restr_mem_maximalAtlas _ hφ.mem_maximalAtlas hWopen
    · rw [OpenPartialHomeomorph.restrOpen_source] at hx
      change _ ≠ ⊤
      rw [hbotY x hx.2]
      exact bot_ne_top
  · -- off `Z`: the chart of the clause for `I'`, restricted over the complement of `Z`
    have ha' : a ∈ (S.strictTransformSubspaceSeq I' (Fin.last _)).support := by
      change _ ≠ ⊤
      rw [← hcong a haZ]
      exact ha
    obtain ⟨c, φ, σ, cidx, hadapt, hsnc, hdisj⟩ := hpt a ha'
    refine ⟨c, φ.restrOpen (S.composite ⁻¹' Zᶜ) hW'open, σ, cidx,
      ⟨(hadapt.restrOpen' _ hW'open).1, fun x hx => ?_⟩, hsnc.restrOpen hW'open haZ, hdisj⟩
    have hx' := (hadapt.restrOpen' _ hW'open).2 x hx
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    rw [← hx']
    change _ ≠ ⊤ ↔ _ ≠ ⊤
    rw [hcong x hx.2]

/-- **The monomial clause (6) transfers to an ideal sheaf vanishing on some connected
components**, with the same simple normal crossings family `G`: over `Z` both sides are zero, and
off `Z` the stalks of `I` and `I'` and of their strict transforms agree. -/
theorem exists_monomial_strictTransformSubspaceSeq_of_eq_off_clopen {I I' : IdealSheaf M}
    {Z : Set M} (hbot : ∀ x ∈ Z, I.stalkIdeal x = ⊥) (htop : ∀ x ∈ Z, I'.stalkIdeal x = ⊤)
    (heq : ∀ x ∉ Z, I.stalkIdeal x = I'.stalkIdeal x)
    (hc : S.CentersOver (I'.support \ I'.regularLocus)) {G : HypersurfaceFamily S.last}
    (hpt : ∀ x : S.last, ∃ (s : Finset G.ι) (α : G.ι → ℕ), (∀ j ∈ s, x ∈ G.hyp j) ∧
      (I'.pullback S.composite S.composite.contMDiff).stalkIdeal x =
        (S.strictTransformSubspaceSeq I' (Fin.last _)).stalkIdeal x *
          ∏ j ∈ s, Manifold.vanishingStalk (G.hyp j) x ^ α j) :
    ∀ x : S.last, ∃ (s : Finset G.ι) (α : G.ι → ℕ), (∀ j ∈ s, x ∈ G.hyp j) ∧
      (I.pullback S.composite S.composite.contMDiff).stalkIdeal x =
        (S.strictTransformSubspaceSeq I (Fin.last _)).stalkIdeal x *
          ∏ j ∈ s, Manifold.vanishingStalk (G.hyp j) x ^ α j := by
  have hbotY := S.stalkIdeal_strictTransformSubspaceSeq_last_eq_bot_of_mem hbot htop hc
  intro x
  by_cases hxZ : S.composite x ∈ Z
  · refine ⟨∅, fun _ => 0, fun j hj => absurd hj (Finset.notMem_empty _), ?_⟩
    rw [Manifold.IdealSheaf.stalkIdeal_pullback, hbot _ hxZ, Ideal.map_bot, hbotY x hxZ,
      Finset.prod_empty, Ideal.bot_mul]
  · obtain ⟨s, α, hs, hmon⟩ := hpt x
    refine ⟨s, α, hs, ?_⟩
    rw [Manifold.IdealSheaf.stalkIdeal_pullback, heq _ hxZ,
      ← Manifold.IdealSheaf.stalkIdeal_pullback, hmon,
      S.stalkIdeal_strictTransformSubspaceSeq_congr heq (Fin.last _) x hxZ]

end AnalyticManifold.FiniteSuccession

/-! ### The transfer of the desingularization clauses -/

namespace AnalyticManifold.IdealSheaf

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} {S : FiniteSuccession M}

/-- **The clauses of [Wlo09, Theorem 2.0.2] transfer to an ideal sheaf vanishing on some
connected components.** Let `Z` be clopen, `I = 0` and `I' = 1` on `Z`, `I = I'` off `Z`, and let
the centres of `S` lie over `Sing(Y')`. If `S` desingularizes `I'` it desingularizes `I`: the
singular loci agree; over `Z` no centre, hence no exceptional divisor, lies, so the strict
transform of `I` has zero stalk there
(`stalkIdeal_strictTransformSubspaceSeq_eq_map_of_notMem_support`), the ambient stalk is
regular, every chart is adapted to the whole space (codimension `0`) and is an snc chart of the
empty divisor, and `σ^*(I) = I_Ỹ · 1` with both sides zero; off `Z` the strict transforms of `I`
and `I'` agree (`stalkIdeal_strictTransformSubspaceSeq_congr`), and the charts of the clauses for
`I'`, restricted to the open set over the complement of `Z`, serve for `I`. -/
theorem IsDesingularizedBy.of_eq_off_clopen {I I' : IdealSheaf M} {Z : Set M} (hZ : IsClopen Z)
    (hbot : ∀ x ∈ Z, I.stalkIdeal x = ⊥) (htop : ∀ x ∈ Z, I'.stalkIdeal x = ⊤)
    (heq : ∀ x ∉ Z, I.stalkIdeal x = I'.stalkIdeal x) (h : I'.IsDesingularizedBy S)
    (hc : S.CentersOver (I'.support \ I'.regularLocus)) : I.IsDesingularizedBy S := by
  -- the singular loci agree
  have hsing : I.support \ I.regularLocus = I'.support \ I'.regularLocus := by
    ext x
    by_cases hx : x ∈ Z
    · have h1 : x ∈ I.regularLocus := I.zeroLocus_subset_regularLocus (hbot x hx)
      have h2 : x ∉ I'.support := fun h => h (htop x hx)
      exact ⟨fun h => absurd h1 h.2, fun h => absurd h.1 h2⟩
    · simp only [Set.mem_sdiff, IdealSheaf.support, IdealSheaf.regularLocus, Set.mem_ofPred_eq]
      rw [heq x hx]
  -- a point of a centre lies off `Z` and off `Reg(Y)`
  have hcent : ∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
      S.stageMap i.castSucc x ∉ Z ∧ S.stageMap i.castSucc x ∉ I.regularLocus := by
    intro i x hx
    obtain ⟨hsupp, hnreg⟩ := hc i hx
    have hnZ : S.stageMap i.castSucc x ∉ Z := fun hZ' => hsupp (htop _ hZ')
    refine ⟨hnZ, fun hreg => hnreg ?_⟩
    change IsRegularLocalRing (_ ⧸ I.stalkIdeal _) at hreg
    rwa [heq _ hnZ] at hreg
  -- over `Z` the strict transform of `I` is the zero ideal
  have hbotY := S.stalkIdeal_strictTransformSubspaceSeq_last_eq_bot_of_mem hbot htop hc
  -- off `Z` the strict transforms of `I` and `I'` agree
  have hcong : ∀ z : S.last, S.composite z ∉ Z →
      (S.strictTransformSubspaceSeq I (Fin.last _)).stalkIdeal z =
        (S.strictTransformSubspaceSeq I' (Fin.last _)).stalkIdeal z :=
    fun z hz => S.stalkIdeal_strictTransformSubspaceSeq_congr heq (Fin.last _) z hz
  refine ⟨h.isNonsingular_center, h.hasSncBoundaries, fun i x hx => (hcent i x hx).2, ?_,
    fun z hz => ?_, ?_, ?_⟩
  · -- the support of the last exceptional divisor
    rw [h.support_boundarySeq_last, hsing]
  · -- (3) the strict transform is smooth
    by_cases hzZ : S.composite z ∈ Z
    · rw [hbotY z hzZ]
      exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot _).symm
    · have hz' : z ∈ (S.strictTransformSubspaceSeq I' (Fin.last _)).support := by
        change _ ≠ ⊤
        rw [← hcong z hzZ]
        exact hz
      have := h.isNonsingular_strictTransform z hz'
      change IsRegularLocalRing (_ ⧸ _) at this ⊢
      rwa [hcong z hzZ]
  · -- (3) transversal simple normal crossings with the last exceptional divisor
    obtain ⟨n, ψ, G, hG, hGE, hpt⟩ := h.isSncBoundaryTransversalTo_strictTransform
    exact ⟨n, ψ, G, hG, hGE,
      S.exists_adaptedChart_strictTransformSubspaceSeq_of_eq_off_clopen hZ hbot htop heq hc hG hpt⟩
  · -- (6) `σ^*(I) = I_Ỹ · I_Ẽ`
    obtain ⟨n, ψ, G, hG, hGE, hpt⟩ := h.isMulBoundaryMonomial_pullback
    exact ⟨n, ψ, G, hG, hGE,
      S.exists_monomial_strictTransformSubspaceSeq_of_eq_off_clopen hbot htop heq hc hpt⟩

end AnalyticManifold.IdealSheaf

end

end
