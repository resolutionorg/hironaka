/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.PartialEuler
public import Hironaka.Manifold.BlowUp.Transform.Defs
public import Hironaka.Manifold.Germ.CoordDeriv
public import Hironaka.Manifold.Submanifold
import Hironaka.Algebra.Local.Order
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Germ.CoordDerivChart
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Submanifold.Components
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The order of an ideal sheaf along a closed submanifold

For the ideal sheaf `I_Y` of a closed submanifold `Y` and a locally finitely generated ideal
sheaf `I`, the order `ν_{Y,a}(I) = sup {p : I_a ⊆ I_{Y,a}^p}` along `Y` at `a`
(`IdealSheaf.ordAlongIdeal`) is the order of `I` along `Y` of [BM97, §3] and Hironaka's `ν(J_x)`
at the points of the centre [Hir64, Ch. 0, §5, p. 142]; Kollár defines the order along an
irreducible `Z` at its generic point [Kol07, Definition 47]. This file proves that the order is

* at most the order at `a` (`ordAlong_le_ord`, since `I_{Y,a} ⊆ 𝔪_a`);
* locally constant on `Y`, hence constant on preconnected subsets of `Y`
  (`ordAlong_eq_of_isPreconnected`): in an adapted chart at `b ∈ Y`, `I_b ⊆ I_{Y,b}^p` iff all
  iterated derivatives of the local generators along fewer than `p` centre coordinates vanish on
  `Y` near `b` (`stalkIdeal_le_pow_iff`, the Taylor criterion of
  `Hironaka.Algebra.Local.PartialEuler` read on the stalk through the coordinate derivations and the
  restriction of germs to `Y`), and a section vanishing on `Y` near one point of a connected chart
  ball of `Y` vanishes on `Y` near every point of the ball, by the identity theorem for analytic
  functions on the chart of `Y` (`eventually_zero_on_of_eventually_zero`); so the order is constant
  on the ball (`exists_open_ordAlong_eq`), locally constant on `Y` (`isLocallyConstant_ordAlong`),
  and `IsLocallyConstant.apply_eq_of_isPreconnected` finishes;
* the generic order along the component through `a` (`genericOrdAlong_eq_ordAlong`);
* for connected `Y`, `≥ p` at one point iff the order of `I` is `≥ p` at every point of `Y`
  (`le_ordAlong_iff_forall_le_ord`; the converse direction reads the derivatives of order `< p`
  vanishing at every point of `Y` near `a`, through the lowering of the power of the maximal
  ideal by a coordinate derivative (`iterD_mem_pow`), as the vanishing on `Y` of the coefficient
  functions).

The constancy of the order along a connected centre is what makes the exponent of Hironaka's weak
transform well defined; the order along a centre is the quantity the order-reduction arguments
of `Hironaka.Manifold.Sequence.OrderReduction` track.
-/

@[expose] public section
open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ}

/-- The index set of the centre coordinates of an adapted chart. -/
def centreIdx (σ : Fin c ↪ Fin n) : Finset (Fin n) := Finset.univ.map σ

/-- The centre indices as a set: the range of `σ`. -/
theorem coe_centreIdx (σ : Fin c ↪ Fin n) : (↑(centreIdx σ) : Set (Fin n)) = Set.range σ := by
  rw [centreIdx, Finset.coe_map, Finset.coe_univ, Set.image_univ]

/-- Membership in the centre indices. -/
theorem mem_centreIdx {σ : Fin c ↪ Fin n} {j : Fin n} : j ∈ centreIdx σ ↔ ∃ k, σ k = j := by
  rw [← Finset.mem_coe, coe_centreIdx]
  rfl

section Chart

variable {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}

/-- `∂_i x_j = δ_ij` on the coordinate germs, as an element of the
stalk. -/
theorem coordDerivStalk_coord_eq_ite (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {b : M}
    (hb : b ∈ φ.source) (i j : Fin n) :
    coordDerivStalk E ψ φ hφ hb i (coord E ψ φ hφ hb j) = if i = j then 1 else 0 := by
  rw [coordDerivStalk_coord]
  split_ifs <;> simp

/-- At a point of `Y` in an adapted chart, the stalk of `I_Y` is the coordinate ideal
`J_S` of the centre indices. -/
theorem IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_coordIdeal (hY : IsClosedSubmanifold ψ Y c)
    (hφ : IsAdaptedChart ψ Y φ σ) {b : M} (hb : b ∈ Y) (hbφ : b ∈ φ.source) :
    hY.idealSheaf.stalkIdeal b =
      coordIdeal (fun i => coord E ψ φ hφ.1 hbφ i) (centreIdx σ) := by
  rw [hY.stalkIdeal_idealSheaf_eq_span hb hφ hbφ]
  unfold coordIdeal
  rw [coe_centreIdx, ← Set.range_comp]
  rfl

variable (hφm : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (V : Opens M) (hV : (V : Set M) ⊆ φ.source)

variable (ψ) in
/-- Iterated coordinate derivatives of a section along a list of indices (`coordDeriv` on
sections). -/
noncomputable def iterDSec (l : List (Fin n)) (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    (structureSheaf 𝕜 E M).presheaf.obj (op V) :=
  l.foldr (fun i g => coordDeriv E ψ φ hφm V hV i g) f

/-- The germ of the iterated derivative is the iterated stalk derivative. -/
theorem germ_iterDSec {b : M} (hbV : b ∈ V) (l : List (Fin n))
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    (structureSheaf 𝕜 E M).presheaf.germ V b hbV (iterDSec ψ hφm V hV l f) =
      iterD (fun i => coordDerivStalk E ψ φ hφm (hV hbV) i) l
        ((structureSheaf 𝕜 E M).presheaf.germ V b hbV f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (structureSheaf 𝕜 E M).presheaf.germ V b hbV
        (coordDeriv E ψ φ hφm V hV i (iterDSec ψ hφm V hV l f)) =
      coordDerivStalk E ψ φ hφm (hV hbV) i (iterD _ l
        ((structureSheaf 𝕜 E M).presheaf.germ V b hbV f))
    rw [← ih, coordDerivStalk_germ]

omit hφm hV in
/-- The value of a germ is the value of the section. -/
theorem eval_germ' {b : M} (hbV : b ∈ V) (g : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    eval 𝕜 E M b ((structureSheaf 𝕜 E M).presheaf.germ V b hbV g) = extendSection 𝕜 E g b := by
  rw [eval_eq_value, stalkToGerm_structureSheaf_germ, Germ.value_ofFun]

omit hφm hV in
/-- A germ at `b ∈ Y` lies in the ideal of `Y` iff the section vanishes on `Y` near `b`. -/
theorem IsClosedSubmanifold.germ_mem_stalkIdeal_idealSheaf_iff (hY : IsClosedSubmanifold ψ Y c)
    {b : M} (hb : b ∈ Y) (hbV : b ∈ V) (g : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    (structureSheaf 𝕜 E M).presheaf.germ V b hbV g ∈ hY.idealSheaf.stalkIdeal b ↔
      ∀ᶠ y : Y in 𝓝 (⟨b, hb⟩ : Y), extendSection 𝕜 E g (y : M) = 0 := by
  rw [hY.stalkIdeal_idealSheaf_of_mem hb, RingHom.mem_ker]
  let _i := hY.chartedSpace
  rw [← (stalkToGerm_injective 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y ⟨b, hb⟩).eq_iff, map_zero,
    hY.stalkToGerm_restrictStalk, stalkToGerm_structureSheaf_germ, germRestrict_coe,
    ← Germ.coe_zero, Germ.coe_eq]
  rfl

/-- The Taylor criterion on the manifold: `I_b ⊆ I_{Y,b}^p` iff all iterated derivatives of the
local generators along fewer than `p` centre coordinates vanish on `Y` near `b`. -/
theorem stalkIdeal_le_pow_iff (hY : IsClosedSubmanifold ψ Y c) (hφ : IsAdaptedChart ψ Y φ σ)
    {b : M} (hb : b ∈ Y) (hbV : b ∈ V) (I : IdealSheaf (structureSheaf 𝕜 E M)) {k : ℕ}
    (f : Fin k → (structureSheaf 𝕜 E M).presheaf.obj (op V))
    (hgen : I.stalkIdeal b =
      Ideal.span (Set.range fun j => (structureSheaf 𝕜 E M).presheaf.germ V b hbV (f j)))
    (p : ℕ) :
    I.stalkIdeal b ≤ hY.idealSheaf.stalkIdeal b ^ p ↔
      ∀ j, ∀ l : List (Fin n), (∀ i ∈ l, i ∈ centreIdx σ) → l.length < p →
        ∀ᶠ y : Y in 𝓝 (⟨b, hb⟩ : Y),
          extendSection 𝕜 E (iterDSec ψ hφ.1 V hV l (f j)) (y : M) = 0 := by
  have hJ := hY.stalkIdeal_idealSheaf_eq_coordIdeal hφ hb (hV hbV)
  have hx : ∀ i ∈ centreIdx σ, ∀ j ∈ centreIdx σ,
      coordDerivStalk E ψ φ hφ.1 (hV hbV) i (coord E ψ φ hφ.1 (hV hbV) j) =
        if i = j then 1 else 0 :=
    fun i _ j _ => coordDerivStalk_coord_eq_ite hφ.1 (hV hbV) i j
  have key : ∀ j, (structureSheaf 𝕜 E M).presheaf.germ V b hbV (f j) ∈
      hY.idealSheaf.stalkIdeal b ^ p ↔
      ∀ l : List (Fin n), (∀ i ∈ l, i ∈ centreIdx σ) → l.length < p →
        ∀ᶠ y : Y in 𝓝 (⟨b, hb⟩ : Y),
          extendSection 𝕜 E (iterDSec ψ hφ.1 V hV l (f j)) (y : M) = 0 := by
    intro j
    rw [hJ, mem_coordIdeal_pow_iff _ _ _ hx p]
    refine forall_congr' fun l => forall_congr' fun _ => forall_congr' fun _ => ?_
    rw [← hJ, ← germ_iterDSec, hY.germ_mem_stalkIdeal_idealSheaf_iff V hb hbV]
  rw [hgen, Ideal.span_le]
  constructor
  · intro h j
    exact (key j).mp (h ⟨j, rfl⟩)
  · rintro h _ ⟨j, rfl⟩
    exact (key j).mpr (h j)

end Chart

/-- `x ≤ y` in `ℕ∞` when every natural lower bound of `x` bounds `y`. -/
theorem _root_.ENat.le_of_forall_natCast_le' {x y : ℕ∞} (h : ∀ p : ℕ, (p : ℕ∞) ≤ x → (p : ℕ∞) ≤ y) :
    x ≤ y := by
  induction y using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    induction x using ENat.recTopCoe with
    | top =>
      have := h (m + 1) le_top
      exact absurd (by exact_mod_cast this : m + 1 ≤ m) (by omega)
    | coe k => exact h k le_rfl

section Constancy

variable {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}

/-- The coordinate embedding `𝕜^{n-c} → 𝕜^n` of the adapted charts is analytic (linear). -/
theorem analyticAt_embedCompl (σ : Fin c ↪ Fin n) (w : Fin (n - c) → 𝕜) :
    AnalyticAt 𝕜 (embedCompl (𝕜 := 𝕜) σ) w := by
  rw [analyticAt_pi_iff]
  intro j
  by_cases h : j ∈ Set.range σ
  · simp only [embedCompl, dite_eq_left h]
    exact analyticAt_const
  · simp only [embedCompl, dite_eq_right h]
    exact (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin (n - c) => 𝕜)
      (complEquiv σ ⟨j, h⟩)).analyticAt w

/-- The identity theorem on a connected chart ball of `Y`: a section of `𝒪_M` vanishing on `Y` near
one point of a preconnected open `W ⊆ Y` inside an adapted chart vanishes on `Y` near every point of
`W`. -/
theorem eventually_zero_on_of_eventually_zero (hφ : IsAdaptedChart ψ Y φ σ) {b : M} (hb : b ∈ Y)
    (V : Opens M) (hV : (V : Set M) ⊆ φ.source)
    (g : (structureSheaf 𝕜 E M).presheaf.obj (op V)) {W : Set Y} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hWV : ∀ y ∈ W, (y : M) ∈ V) {y₀ : Y} (hy₀ : y₀ ∈ W)
    (h0 : ∀ᶠ y : Y in 𝓝 y₀, extendSection 𝕜 E g (y : M) = 0) :
    ∀ y ∈ W, ∀ᶠ y' : Y in 𝓝 y, extendSection 𝕜 E g (y' : M) = 0 := by
  set e := hφ.chartOn hb with he
  have hWsrc : W ⊆ e.source := fun y hy => hV (hWV y hy)
  have hsymm : ∀ w ∈ e.target, ((e.symm w : Y) : M) = φ.symm (ψ.symm (embedCompl σ w)) := by
    intro w hw
    rw [he, hφ.chartOn_symm_apply hb, hφ.coe_symmAux hb hw]
  set H : (Fin (n - c) → 𝕜) → 𝕜 := fun w => extendSection 𝕜 E g (φ.symm (ψ.symm (embedCompl σ w)))
    with hH
  have hHe : ∀ y ∈ W, H (e y) = extendSection 𝕜 E g (y : M) := by
    intro y hy
    have h1 : e.symm (e y) = y := e.left_inv (hWsrc hy)
    change extendSection 𝕜 E g (φ.symm (ψ.symm (embedCompl σ (e y)))) = _
    rw [← hsymm (e y) (e.map_source (hWsrc hy)), h1]
  have hU : IsOpen (e '' W) := e.isOpen_image_of_subset_source hWo hWsrc
  have hUc : IsPreconnected (e '' W) := hWc.image e (e.continuousOn.mono hWsrc)
  have hHan : AnalyticOnNhd 𝕜 H (e '' W) := by
    rintro _ ⟨y, hy, rfl⟩
    have hpt : ψ.symm (embedCompl σ (e y)) ∈ φ.target := e.map_source (hWsrc hy)
    have hyV : φ.symm (ψ.symm (embedCompl σ (e y))) ∈ (V : Set M) := by
      rw [← hsymm (e y) (e.map_source (hWsrc hy)), e.left_inv (hWsrc hy)]
      exact hWV y hy
    have hF : AnalyticAt 𝕜 (fun v : Fin n → 𝕜 => extendSection 𝕜 E g (φ.symm (ψ.symm v)))
        (embedCompl σ (e y)) := by
      set N : Set (Fin n → 𝕜) := ψ.symm ⁻¹' (φ.target ∩ φ.symm ⁻¹' (V : Set M)) with hN
      have hNo : IsOpen N := (φ.isOpen_inter_preimage_symm V.2).preimage ψ.symm.continuous
      have h2 : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) ω (fun v => φ.symm (ψ.symm v)) N :=
        (contMDiffOn_symm_of_mem_maximalAtlas hφ.1).comp
          ((ψ.symm : (Fin n → 𝕜) →L[𝕜] E).contMDiff.contMDiffOn) fun v hv => hv.1
      have h3 : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) ω
          (fun v => extendSection 𝕜 E g (φ.symm (ψ.symm v))) N :=
        (contMDiffOn_extendSection g).comp h2 fun v hv => hv.2
      exact ((contMDiffOn_iff_contDiffOn.mp h3).contDiffAt (hNo.mem_nhds ⟨hpt, hyV⟩)).analyticAt
    exact hF.comp (analyticAt_embedCompl σ (e y))
  have hz : H =ᶠ[𝓝 (e y₀)] 0 := by
    have hA : ∀ᶠ w : Fin (n - c) → 𝕜 in 𝓝 (e y₀), extendSection 𝕜 E g ((e.symm w : Y) : M) = 0 :=
      (e.tendsto_symm (hWsrc hy₀)).eventually h0
    have hB : ∀ᶠ w in 𝓝 (e y₀), w ∈ e.target :=
      e.open_target.mem_nhds (e.map_source (hWsrc hy₀))
    filter_upwards [hA, hB] with w hw1 hw2
    change extendSection 𝕜 E g (φ.symm (ψ.symm (embedCompl σ w))) = 0
    rw [← hsymm w hw2]
    exact hw1
  have hEq := hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ⟨y₀, hy₀, rfl⟩ hz
  intro y hy
  filter_upwards [hWo.mem_nhds hy] with y' hy'
  rw [← hHe y' hy']
  exact hEq ⟨y', hy', rfl⟩

/-- Restricting local generators of `I` to a smaller open set. -/
theorem exists_generators_restrict (I : IdealSheaf (structureSheaf 𝕜 E M)) {a : M}
    (φ : OpenPartialHomeomorph M E) (haφ : a ∈ φ.source) :
    ∃ (V : Opens M) (_ : (V : Set M) ⊆ φ.source) (_ : a ∈ V) (k : ℕ)
      (f : Fin k → (structureSheaf 𝕜 E M).presheaf.obj (op V)),
      ∀ y (hy : y ∈ V), I.stalkIdeal y =
        Ideal.span (Set.range fun j => (structureSheaf 𝕜 E M).presheaf.germ V y hy (f j)) := by
  obtain ⟨V₀, haV₀, k, f, -, hf⟩ := I.exists_generators a
  refine ⟨V₀ ⊓ ⟨φ.source, φ.open_source⟩, fun x hx => hx.2, ⟨haV₀, haφ⟩, k,
    fun j => (structureSheaf 𝕜 E M).presheaf.map (homOfLE (inf_le_left : V₀ ⊓ _ ≤ V₀)).op (f j),
    fun y hy => ?_⟩
  rw [hf y hy.1]
  exact congrArg Ideal.span (IdealSheaf.range_germ_map (homOfLE inf_le_left) hy f).symm

/-- The order along `Y` is locally constant on `Y`. -/
theorem exists_open_ordAlong_eq (hY : IsClosedSubmanifold ψ Y c)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {b : M} (hb : b ∈ Y) :
    ∃ W : Set Y, IsOpen W ∧ (⟨b, hb⟩ : Y) ∈ W ∧ ∀ y ∈ W,
      IdealSheaf.ordAlongIdeal hY.idealSheaf I (y : M) =
        IdealSheaf.ordAlongIdeal hY.idealSheaf I b := by
  obtain ⟨φ, σ, hbφ, hφ⟩ := hY.exists_adaptedChart b hb
  obtain ⟨V, hV, hbV, k, f, hgen⟩ := exists_generators_restrict I φ hbφ
  have hUopen : IsOpen {y : Y | (y : M) ∈ V} := continuous_subtype_val.isOpen_preimage _ V.2
  obtain ⟨W, hWn, hWo, hWc, hWU⟩ := hφ.exists_preconnected_mem_nhds hb hbφ
    (hUopen.mem_nhds (show (⟨b, hb⟩ : Y) ∈ {y : Y | (y : M) ∈ V} from hbV))
  have hbW : (⟨b, hb⟩ : Y) ∈ W := mem_of_mem_nhds hWn
  have hWV : ∀ y ∈ W, (y : M) ∈ V := fun y hy => hWU hy
  refine ⟨W, hWo, hbW, fun y hy => ?_⟩
  apply ENat.eq_of_forall_natCast_le_iff
  intro p
  rw [IdealSheaf.le_ordAlongIdeal_iff hY.idealSheaf I (y : M) p,
    IdealSheaf.le_ordAlongIdeal_iff hY.idealSheaf I b p,
    stalkIdeal_le_pow_iff V hV hY hφ y.2 (hWV y hy) I f (hgen y (hWV y hy)) p,
    stalkIdeal_le_pow_iff V hV hY hφ hb hbV I f (hgen b hbV) p]
  constructor
  · intro h j l hl hlen
    exact eventually_zero_on_of_eventually_zero hφ hb V hV (iterDSec ψ hφ.1 V hV l (f j)) hWo hWc
      hWV hy (h j l hl hlen) ⟨b, hb⟩ hbW
  · intro h j l hl hlen
    exact eventually_zero_on_of_eventually_zero hφ hb V hV (iterDSec ψ hφ.1 V hV l (f j)) hWo hWc
      hWV hbW (h j l hl hlen) y hy

/-- The order along `Y` is a locally constant function on `Y`. -/
theorem IsClosedSubmanifold.isLocallyConstant_ordAlong (hY : IsClosedSubmanifold ψ Y c)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) :
    IsLocallyConstant fun y : Y => IdealSheaf.ordAlongIdeal hY.idealSheaf I (y : M) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y
  obtain ⟨W, hWo, hyW, hW⟩ := exists_open_ordAlong_eq hY I y.2
  exact ⟨W, hWo, hyW, fun y' hy' => hW y' hy'⟩

/-- The order along `Y` is constant on preconnected subsets of
`Y` (the generic value of the order along the centre, [BM97, Remark 1.8]). -/
theorem ordAlong_eq_of_isPreconnected (hY : IsClosedSubmanifold ψ Y c)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {S : Set M} (hSY : S ⊆ Y) (hS : IsPreconnected S)
    {a b : M} (ha : a ∈ S) (hb : b ∈ S) :
    IdealSheaf.ordAlongIdeal hY.idealSheaf I a = IdealSheaf.ordAlongIdeal hY.idealSheaf I b := by
  have hS' : IsPreconnected ((Subtype.val : Y → M) ⁻¹' S) := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      Set.inter_eq_right.mpr hSY]
    exact hS
  exact (hY.isLocallyConstant_ordAlong I).apply_eq_of_isPreconnected hS'
    (x := ⟨a, hSY ha⟩) (y := ⟨b, hSY hb⟩) ha hb

/-- The generic order along the component through `a ∈ Y` is the order along `Y`
at `a`. -/
theorem genericOrdAlong_eq_ordAlong (hY : IsClosedSubmanifold ψ Y c)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {a : M} (ha : a ∈ Y) :
    IdealSheaf.genericOrdAlong hY.idealSheaf I a = IdealSheaf.ordAlongIdeal hY.idealSheaf I a := by
  rw [IdealSheaf.genericOrdAlong_def, hY.cosupport_idealSheaf]
  refine le_antisymm (biInf_le _ (mem_connectedComponentIn ha)) (le_iInf₂ fun y hy => ?_)
  exact (ordAlong_eq_of_isPreconnected hY I (connectedComponentIn_subset Y a)
    isPreconnected_connectedComponentIn (mem_connectedComponentIn ha) hy).le

/-- The order along `Y` at `a ∈ Y` is at most the order at `a`. -/
theorem ordAlong_le_ord (hY : IsClosedSubmanifold ψ Y c) (I : IdealSheaf (structureSheaf 𝕜 E M))
    {a : M} (ha : a ∈ Y) : IdealSheaf.ordAlongIdeal hY.idealSheaf I a ≤ I.ord a := by
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
  have hle : hY.idealSheaf.stalkIdeal a ≤ maximalIdeal _ := by
    rw [hY.stalkIdeal_idealSheaf_eq_span ha hφ haφ, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, mem_maximalIdeal_iff_eval, eval_coord]
    exact (hφ.2 a haφ).1 ha k
  unfold IdealSheaf.ordAlongIdeal IdealSheaf.ord
  refine iSup₂_le fun p hp => ?_
  exact le_ord_iff.mpr (hp.trans (Ideal.pow_right_mono hle p))

/-- If the order of `I` is at least `p` at the points of `Y` near `a`, then
`I_a ⊆ I_{Y,a}^p`. -/
theorem stalkIdeal_le_pow_of_eventually_le_ord (hY : IsClosedSubmanifold ψ Y c)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {a : M} (ha : a ∈ Y) {p : ℕ}
    (h : ∀ᶠ y : Y in 𝓝 (⟨a, ha⟩ : Y), (p : ℕ∞) ≤ I.ord (y : M)) :
    I.stalkIdeal a ≤ hY.idealSheaf.stalkIdeal a ^ p := by
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
  obtain ⟨V, hV, haV, k, f, hgen⟩ := exists_generators_restrict I φ haφ
  rw [stalkIdeal_le_pow_iff V hV hY hφ ha haV I f (hgen a haV) p]
  intro j l _ hlen
  have hUopen : IsOpen {y : Y | (y : M) ∈ V} := continuous_subtype_val.isOpen_preimage _ V.2
  filter_upwards [h, hUopen.mem_nhds (show (⟨a, ha⟩ : Y) ∈ {y : Y | (y : M) ∈ V} from haV)]
    with y hy hyV
  rw [← eval_germ' V hyV (iterDSec ψ hφ.1 V hV l (f j)), germ_iterDSec hφ.1 V hV hyV l (f j),
    ← mem_maximalIdeal_iff_eval]
  have h1 : (structureSheaf 𝕜 E M).presheaf.germ V y hyV (f j) ∈ maximalIdeal _ ^ p := by
    have h2 : I.stalkIdeal (y : M) ≤ maximalIdeal _ ^ p := by
      unfold IdealSheaf.ord at hy
      exact le_ord_iff.mp hy
    exact h2 (by rw [hgen y hyV]; exact Ideal.subset_span ⟨j, rfl⟩)
  have h3 := iterD_mem_pow (fun i => coordDerivStalk E ψ φ hφ.1 (hV hyV) i)
    (maximalIdeal _) l (p := p - l.length) (by rwa [Nat.sub_add_cancel hlen.le])
  exact Ideal.pow_le_self (by omega) h3

/-- For connected `Y`, `ν_{Y,a}(I) ≥ p` at one point iff
`ν_y(I) ≥ p` at every point of `Y`. -/
theorem le_ordAlong_iff_forall_le_ord (hY : IsClosedSubmanifold ψ Y c) (hconn : IsPreconnected Y)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {a : M} (ha : a ∈ Y) (p : ℕ) :
    (p : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a ↔ ∀ y ∈ Y, (p : ℕ∞) ≤ I.ord y := by
  constructor
  · intro hp y hy
    refine le_trans ?_ (ordAlong_le_ord hY I hy)
    rwa [ordAlong_eq_of_isPreconnected hY I subset_rfl hconn hy ha]
  · intro h
    rw [IdealSheaf.le_ordAlongIdeal_iff]
    exact stalkIdeal_le_pow_of_eventually_le_ord hY I ha (Eventually.of_forall fun y => h y y.2)

end Constancy

end Manifold
