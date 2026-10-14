/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.LocalModelRestrict
public import Hironaka.AnalyticSpace.Manifold.Restrict
import Hironaka.AnalyticSpace.Manifold.FullyFaithful
import Hironaka.AnalyticSpace.RegEval
import Hironaka.AnalyticSpace.RegPoints
import Hironaka.AnalyticSpace.RegularStalk
import Hironaka.AnalyticSpace.Restrict.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The dimension strata of a non-singular analytic space are analytic manifolds

On a non-singular analytic `K`-space `X`, every point `x` has an open neighbourhood `V` and a
`K`-isomorphism `(G', 𝒜_{G'}) ≅ X | V` with `G' ⊆ K^d` open and `d = dim 𝒪_{X,x}`, by Hironaka's
characterization of the simple points [Hir64, Ch. 0, §1, p. 121]
(`isRegular_stalk_iff_exists_manifold_nhd`), and every point of `V` then has dimension `d`. Hence

* the dimension is locally constant: the strata `X_d = {x | dim 𝒪_{X,x} = d}` are open
  (`isOpen_dimSet`) and partition `X` (`iUnion_dimSet_eq_univ`);
* the charts `x ↦ q ∈ G' ⊆ K^d` given by the inverses of these isomorphisms form an atlas of `X_d`
  (`stratumChart`, the `ChartedSpace` instance), whose chart changes are the underlying maps of the
  `K`-isomorphisms `(G'_x, 𝒜) | ⋯ ≅ X | (V_x ∩ V_y) ≅ (G'_y, 𝒜) | ⋯` and hence analytic
  (`contMDiff_baseFun`, `Hironaka.AnalyticSpace.Manifold.FullyFaithful`): `X_d` is an analytic
  manifold modelled on `K^d` (`stratumManifold : AnalyticManifold K (Fin d → K)`), Hausdorff and
  second countable as a subspace of `X`.

This is the manifold half of the statement that a smooth space is a manifold, locally
pure-dimensional [BM97, (3.8)(2)]; the `K`-isomorphism `Sp(X_d) ≅ X | X_d` completing it is
`Hironaka.AnalyticSpace.Manifold.StratumIso`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AnalyticSpace.KLocallyRingedSpace Manifold
open scoped Manifold ContDiff Topology

universe u

noncomputable section

namespace AnalyticSpace

variable {K : Type} [RCLike K] (X : AnalyticSpace.{u} K)

/-! ### The dimension strata -/

/-- The points of local dimension `d`: `X_d = {x | dim 𝒪_{X,x} = d}`. -/
def dimSet (d : ℕ) : Set X :=
  {x | ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x) = ((d : ℕ) : WithBot ℕ∞)}

theorem mem_reg_of_isNonsingular (hX : X.IsNonsingular) (x : X) : x ∈ regularLocus X := by
  rw [IsNonsingular] at hX
  rw [hX]
  trivial

/-- Every point of a chart neighbourhood `X | V ≅ (G', 𝒜_{G'})`, `G' ⊆ K^d`, has dimension `d`. -/
theorem mem_dimSet_of_chart {V : Opens X} {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V))
    (q : analyticSpaceOfOpen K d G') : (e.hom.1.base q).1 ∈ dimSet X d :=
  (isRegularLocalRing_stalk_of_kIso_analyticSpaceOfOpen (e.hom.1.base q).2 e.symm).2

theorem subset_dimSet_of_chart {V : Opens X} {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V)) :
    (V : Set X) ⊆ dimSet X d := by
  intro x hx
  obtain ⟨q, hq⟩ : ∃ q, e.hom.1.base q = ⟨x, hx⟩ :=
    ⟨(KIso.homeomorph e).symm ⟨x, hx⟩, (KIso.homeomorph e).apply_symm_apply _⟩
  have h := mem_dimSet_of_chart X e q
  rw [hq] at h
  exact h

/-- At a point of dimension `d` of a non-singular space there is a chart `(G', 𝒜_{G'}) ≅ X | V`,
`G' ⊆ K^d` [Hir64, Ch. 0, §1, p. 121]. -/
theorem exists_chart_of_mem_dimSet (hX : X.IsNonsingular) {d : ℕ} {x : X} (hx : x ∈ dimSet X d) :
    ∃ (V : Opens X) (_ : x ∈ V) (G' : Opens (Kn.{u} K d)),
      Nonempty (KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V)) := by
  obtain ⟨d', hd', V, hxV, G', ⟨e⟩⟩ :=
    (isRegular_stalk_iff_exists_manifold_nhd X x).mp (mem_reg_of_isNonsingular X hX x)
  have hdd : d' = d := by
    have h : ((d' : ℕ) : WithBot ℕ∞) = ((d : ℕ) : WithBot ℕ∞) := hd'.symm.trans hx
    exact_mod_cast h
  subst hdd
  exact ⟨V, hxV, G', ⟨e.symm⟩⟩

/-- **The dimension is locally constant on a non-singular space**: each stratum `X_d` is open. -/
theorem isOpen_dimSet (hX : X.IsNonsingular) (d : ℕ) : IsOpen (dimSet X d) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, hxV, G', ⟨e⟩⟩ := exists_chart_of_mem_dimSet X hX hx
  exact ⟨V, subset_dimSet_of_chart X e, V.isOpen, hxV⟩

/-- **The strata cover the space**: every stalk of a non-singular space has finite dimension. -/
theorem iUnion_dimSet_eq_univ (hX : X.IsNonsingular) : ⋃ d : ℕ, dimSet X d = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨d, hd, -⟩ :=
    (isRegular_stalk_iff_exists_manifold_nhd X x).mp (mem_reg_of_isNonsingular X hX x)
  exact Set.mem_iUnion.mpr ⟨d, hd⟩

variable (hX : X.IsNonsingular) (d : ℕ)

/-- The stratum `X_d` as an open of `X`. -/
def dimOpens : Opens X := ⟨dimSet X d, isOpen_dimSet X hX d⟩

/-! ### The charts -/

/-- The chart neighbourhood of a point of the stratum (a choice). -/
def chartV (x : dimOpens X hX d) : Opens X := (exists_chart_of_mem_dimSet X hX x.2).choose

theorem mem_chartV (x : dimOpens X hX d) : x.1 ∈ chartV X hX d x :=
  (exists_chart_of_mem_dimSet X hX x.2).choose_spec.choose

/-- The open `G' ⊆ K^d` of the chart. -/
def chartG (x : dimOpens X hX d) : Opens (Kn.{u} K d) :=
  (exists_chart_of_mem_dimSet X hX x.2).choose_spec.choose_spec.choose

/-- The `K`-isomorphism `(G', 𝒜_{G'}) ≅ X | V` of the chart. -/
def chartE (x : dimOpens X hX d) :
    KIso (analyticSpaceOfOpen K d (chartG X hX d x))
      (X.toKLocallyRingedSpace.restrictOpen (chartV X hX d x)) :=
  Classical.choice (exists_chart_of_mem_dimSet X hX x.2).choose_spec.choose_spec.choose_spec

theorem chartV_subset (x : dimOpens X hX d) : (chartV X hX d x : Set X) ⊆ dimSet X d :=
  subset_dimSet_of_chart X (chartE X hX d x)

/-- The homeomorphism `G' ≃ₜ V` underlying the chart isomorphism. -/
def chartHomeo (x : dimOpens X hX d) :
    analyticSpaceOfOpen K d (chartG X hX d x) ≃ₜ
      X.toKLocallyRingedSpace.restrictOpen (chartV X hX d x) :=
  KIso.homeomorph (chartE X hX d x)

theorem chartHomeo_apply (x : dimOpens X hX d) (q : analyticSpaceOfOpen K d (chartG X hX d x)) :
    chartHomeo X hX d x q = (chartE X hX d x).hom.1.base q :=
  rfl

variable {X hX d}

/-- The point of the stratum under a point of the chart's open `G'`. -/
def chartPt (x : dimOpens X hX d) (q : analyticSpaceOfOpen K d (chartG X hX d x)) :
    dimOpens X hX d :=
  ⟨((chartE X hX d x).hom.1.base q).1, mem_dimSet_of_chart X (chartE X hX d x) q⟩

theorem chartPt_val (x : dimOpens X hX d) (q : analyticSpaceOfOpen K d (chartG X hX d x)) :
    (chartPt x q).1 = ((chartE X hX d x).hom.1.base q).1 :=
  rfl

/-- The chart coordinates of a point of `V`, in `K^d`. -/
def stratumCoord (x : dimOpens X hX d) (w : dimOpens X hX d) (hw : w.1 ∈ chartV X hX d x) :
    Fin d → K :=
  ((chartHomeo X hX d x).symm ⟨w.1, hw⟩).1.down

theorem stratumCoord_chartPt (x : dimOpens X hX d) (q : analyticSpaceOfOpen K d (chartG X hX d x)) :
    stratumCoord x (chartPt x q) ((chartE X hX d x).hom.1.base q).2 = q.1.down := by
  unfold stratumCoord
  have h : ((chartHomeo X hX d x).symm ⟨(chartPt x q).1, ((chartE X hX d x).hom.1.base q).2⟩) =
      q := by
    rw [show (⟨(chartPt x q).1, ((chartE X hX d x).hom.1.base q).2⟩ :
      X.toKLocallyRingedSpace.restrictOpen (chartV X hX d x)) = chartHomeo X hX d x q from rfl]
    exact (chartHomeo X hX d x).symm_apply_apply q
  rw [h]

theorem continuous_stratumCoord (x : dimOpens X hX d) :
    Continuous fun w : {w : dimOpens X hX d // w.1 ∈ chartV X hX d x} =>
      stratumCoord x w.1 w.2 := by
  unfold stratumCoord
  exact Homeomorph.ulift.continuous.comp (continuous_subtype_val.comp
    ((chartHomeo X hX d x).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))

theorem continuous_chartPt (x : dimOpens X hX d) :
    Continuous fun z : {z : Fin d → K // (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x} =>
      chartPt x ⟨ULift.up z.1, z.2⟩ := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.comp ((chartE X hX d x).hom.1.base.hom.continuous.comp
    ((Homeomorph.ulift.symm.continuous.comp continuous_subtype_val).subtype_mk _))

open Classical in
/-- **The chart of the stratum at `x`**: on `V_x ∩ X_d`, the coordinates
`w ↦ e_x⁻¹(w) ∈ G'_x ⊆ K^d`. -/
def stratumChart (x : dimOpens X hX d) : OpenPartialHomeomorph (dimOpens X hX d) (Fin d → K) where
  toFun w := if hw : w.1 ∈ chartV X hX d x then stratumCoord x w hw else 0
  invFun z := if hz : (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x then chartPt x ⟨ULift.up z, hz⟩
    else x
  source := {w | w.1 ∈ chartV X hX d x}
  target := {z | (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x}
  map_source' w hw := by
    have hw' : w.1 ∈ chartV X hX d x := hw
    change (if hw : w.1 ∈ chartV X hX d x then stratumCoord x w hw else 0) ∈ {z | _}
    rw [dite_eq_left hw']
    exact ((chartHomeo X hX d x).symm ⟨w.1, hw'⟩).2
  map_target' z hz := by
    have hz' : (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x := hz
    change (if hz : (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x then chartPt x ⟨ULift.up z, hz⟩
      else x) ∈ {w | _}
    rw [dite_eq_left hz']
    exact ((chartE X hX d x).hom.1.base ⟨ULift.up z, hz'⟩).2
  left_inv' w hw := by
    have hw' : w.1 ∈ chartV X hX d x := hw
    rw [dite_eq_left hw']
    have hz : (ULift.up (stratumCoord x w hw') : Kn.{u} K d) ∈ chartG X hX d x :=
      ((chartHomeo X hX d x).symm ⟨w.1, hw'⟩).2
    rw [dite_eq_left hz]
    apply Subtype.ext
    change ((chartE X hX d x).hom.1.base ⟨_, hz⟩).1 = w.1
    have h : (⟨ULift.up (stratumCoord x w hw'), hz⟩ : analyticSpaceOfOpen K d (chartG X hX d x)) =
        (chartHomeo X hX d x).symm ⟨w.1, hw'⟩ := by
      apply Subtype.ext
      exact ULift.ext _ _ rfl
    rw [h]
    exact congrArg Subtype.val ((chartHomeo X hX d x).apply_symm_apply ⟨w.1, hw'⟩)
  right_inv' z hz := by
    have hz' : (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x := hz
    rw [dite_eq_left hz']
    have hw : (chartPt x ⟨ULift.up z, hz'⟩).1 ∈ chartV X hX d x :=
      ((chartE X hX d x).hom.1.base ⟨ULift.up z, hz'⟩).2
    rw [dite_eq_left hw]
    exact stratumCoord_chartPt x ⟨ULift.up z, hz'⟩
  open_source := (chartV X hX d x).2.preimage continuous_subtype_val
  open_target := (chartG X hX d x).2.preimage Homeomorph.ulift.symm.continuous
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_stratumCoord x).congr fun w => ?_
    have hw : w.1.1 ∈ chartV X hX d x := w.2
    change stratumCoord x w.1 hw =
      (if hw : w.1.1 ∈ chartV X hX d x then stratumCoord x w.1 hw else 0)
    rw [dite_eq_left hw]
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_chartPt x).congr fun z => ?_
    have hz : (ULift.up z.1 : Kn.{u} K d) ∈ chartG X hX d x := z.2
    change chartPt x ⟨ULift.up z.1, hz⟩ =
      (if hz : (ULift.up z.1 : Kn.{u} K d) ∈ chartG X hX d x then chartPt x ⟨ULift.up z.1, hz⟩
        else x)
    rw [dite_eq_left hz]

theorem stratumChart_source (x : dimOpens X hX d) :
    (stratumChart x).source = {w | w.1 ∈ chartV X hX d x} :=
  rfl

theorem stratumChart_target (x : dimOpens X hX d) :
    (stratumChart x).target = {z | (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x} :=
  rfl

open Classical in
theorem stratumChart_apply (x : dimOpens X hX d) {w : dimOpens X hX d}
    (hw : w.1 ∈ chartV X hX d x) :
    stratumChart x w = stratumCoord x w hw := by
  change (if hw : w.1 ∈ chartV X hX d x then stratumCoord x w hw else 0) = _
  rw [dite_eq_left hw]

open Classical in
theorem stratumChart_symm_apply (x : dimOpens X hX d) {z : Fin d → K}
    (hz : (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x) :
    (stratumChart x).symm z = chartPt x ⟨ULift.up z, hz⟩ := by
  change (if hz : (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x then chartPt x ⟨ULift.up z, hz⟩
    else x) = _
  rw [dite_eq_left hz]

theorem mem_stratumChart_source (x : dimOpens X hX d) : x ∈ (stratumChart x).source :=
  mem_chartV X hX d x

variable (X hX d)

/-- **The atlas of the stratum.** -/
instance instChartedSpaceDimOpens : ChartedSpace (Fin d → K) (dimOpens X hX d) where
  atlas := Set.range (stratumChart (X := X) (hX := hX) (d := d))
  chartAt := stratumChart
  mem_chart_source := mem_stratumChart_source
  chart_mem_atlas x := ⟨x, rfl⟩

theorem chartAt_eq (x : dimOpens X hX d) : chartAt (Fin d → K) x = stratumChart x :=
  rfl

/-! ### Chart changes are analytic -/

section Transition

variable {X hX d} (x y : dimOpens X hX d)

/-- The overlap `V_x ∩ V_y`, seen in `G'_x`. -/
def overlapOpens : Opens (analyticSpaceOfOpen K d (chartG X hX d x)) :=
  (Opens.map ((chartE X hX d x).hom ≫
    ofRestrict X.toKLocallyRingedSpace (chartV X hX d x)).1.base).obj (chartV X hX d y)

theorem mem_overlapOpens {q : analyticSpaceOfOpen K d (chartG X hX d x)} :
    q ∈ overlapOpens x y ↔ ((chartE X hX d x).hom.1.base q).1 ∈ chartV X hX d y :=
  Iff.rfl

/-- The open immersion `(G'_x, 𝒜) | (V_x ∩ V_y) ⟶ X`. -/
def overlapIncl : (analyticSpaceOfOpen K d (chartG X hX d x)).restrictOpen (overlapOpens x y) ⟶
    X.toKLocallyRingedSpace :=
  ofRestrict _ (overlapOpens x y) ≫ (chartE X hX d x).hom ≫
    ofRestrict X.toKLocallyRingedSpace (chartV X hX d x)

instance isOpenImmersion_overlapIncl : LocallyRingedSpace.IsOpenImmersion (overlapIncl x y).1 :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
    ((ofRestrict _ (overlapOpens x y)).1 ≫ (chartE X hX d x).hom.1 ≫
      (ofRestrict X.toKLocallyRingedSpace (chartV X hX d x)).1))

theorem overlapIncl_base_apply (p : (analyticSpaceOfOpen K d (chartG X hX d x)).restrictOpen
    (overlapOpens x y)) : (overlapIncl x y).1.base p = ((chartE X hX d x).hom.1.base p.1).1 :=
  rfl

theorem range_overlapIncl :
    Set.range (KLocallyRingedSpace.Hom.toFun (overlapIncl x y)) =
      (chartV X hX d x : Set X) ∩ chartV X hX d y := by
  ext w
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨((chartE X hX d x).hom.1.base p.1).2, p.2⟩
  · rintro ⟨hwx, hwy⟩
    obtain ⟨q, hq⟩ : ∃ q, (chartE X hX d x).hom.1.base q = ⟨w, hwx⟩ :=
      ⟨(chartHomeo X hX d x).symm ⟨w, hwx⟩, (chartHomeo X hX d x).apply_symm_apply _⟩
    refine ⟨⟨q, ?_⟩, ?_⟩
    · rw [mem_overlapOpens, hq]
      exact hwy
    · change ((chartE X hX d x).hom.1.base q).1 = w
      rw [hq]

/-- The transition `K`-isomorphism between the overlaps read in the two charts. -/
def transitionIso :
    (analyticSpaceOfOpen K d (chartG X hX d x)).restrictOpen (overlapOpens x y) ≅
      (analyticSpaceOfOpen K d (chartG X hX d y)).restrictOpen (overlapOpens y x) :=
  isoOfRangeEq (overlapIncl x y) (overlapIncl y x)
    (by rw [range_overlapIncl, range_overlapIncl, Set.inter_comm])

theorem transitionIso_hom_base (p : (analyticSpaceOfOpen K d (chartG X hX d x)).restrictOpen
    (overlapOpens x y)) :
    ((chartE X hX d y).hom.1.base ((transitionIso x y).hom.1.base p).1).1 =
      ((chartE X hX d x).hom.1.base p.1).1 := by
  have h := congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ p)
    (isoOfRangeEq_hom_comp (overlapIncl x y) (overlapIncl y x)
      (by rw [range_overlapIncl, range_overlapIncl, Set.inter_comm]))
  exact h

/-- The trace of the overlap on `K^d`: an open `G'' ≤ G'_x`. -/
def overlapTrace : Opens (Kn.{u} K d) :=
  (exists_opens_le_eq_trace K d (chartG X hX d x) (overlapOpens x y)).choose

theorem overlapTrace_le : overlapTrace x y ≤ chartG X hX d x :=
  (exists_opens_le_eq_trace K d (chartG X hX d x) (overlapOpens x y)).choose_spec.1

theorem mem_overlapOpens_iff (p : analyticSpaceOfOpen K d (chartG X hX d x)) :
    p ∈ overlapOpens x y ↔ p.1 ∈ overlapTrace x y :=
  (exists_opens_le_eq_trace K d (chartG X hX d x) (overlapOpens x y)).choose_spec.2 p

/-- The overlap flattened to `(G'', 𝒜_{G''})` (`traceIso`). -/
def overlapTraceIso :
    (analyticSpaceOfOpen K d (chartG X hX d x)).restrictOpen (overlapOpens x y) ≅
      analyticSpaceOfOpen K d (overlapTrace x y) :=
  traceIso K d (chartG X hX d x) (overlapTrace_le x y) (overlapOpens x y) (mem_overlapOpens_iff x y)

theorem overlapTraceIso_inv_base (p : analyticSpaceOfOpen K d (overlapTrace x y)) :
    ((overlapTraceIso x y).inv.1.base p).1.1 = p.1 :=
  traceIncl_base_apply K d (chartG X hX d x) (overlapTrace_le x y) (overlapOpens x y)
    (mem_overlapOpens_iff x y) p

theorem overlapTraceIso_hom_base (p : (analyticSpaceOfOpen K d (chartG X hX d x)).restrictOpen
    (overlapOpens x y)) : ((overlapTraceIso x y).hom.1.base p).1 = p.1.1 := by
  have h := overlapTraceIso_inv_base x y ((overlapTraceIso x y).hom.1.base p)
  have h2 : (overlapTraceIso x y).inv.1.base ((overlapTraceIso x y).hom.1.base p) = p :=
    KIso.inv_base_hom_base (overlapTraceIso x y) p
  rw [h2] at h
  exact h.symm

/-- The transition, as a `K`-isomorphism of the spaces of the open submanifolds `G''_x`, `G''_y` of
`K^d`. -/
def transitionManifoldIso :
    KIso (ofManifold K (Kn.{u} K d) (overlapTrace x y))
      (ofManifold K (Kn.{u} K d) (overlapTrace y x)) :=
  (ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K d) (M := Kn.{u} K d)
    (overlapTrace x y)).symm ≪≫
    (overlapTraceIso x y).symm ≪≫ transitionIso x y ≪≫ overlapTraceIso y x ≪≫
    ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K d) (M := Kn.{u} K d) (overlapTrace y x)

theorem ofManifold_restrictOpen_iso_hom_base {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] (U : Opens M)
    (p : (ofManifold K E M).restrictOpen U) :
    ((ofManifold_restrictOpen_iso (K := K) (E := E) U).hom.1.base p).1 = p.1 := by
  have h := congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ p)
    (ofManifold_restrictOpen_iso_hom_comp (K := K) (E := E) U)
  exact h

theorem ofManifold_restrictOpen_iso_inv_base {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] (U : Opens M) (q : U) :
    ((ofManifold_restrictOpen_iso (K := K) (E := E) U).inv.1.base q).1 = q.1 := by
  have h := ofManifold_restrictOpen_iso_hom_base (K := K) (E := E) U
    ((ofManifold_restrictOpen_iso (K := K) (E := E) U).inv.1.base q)
  have h2 : (ofManifold_restrictOpen_iso (K := K) (E := E) U).hom.1.base
      ((ofManifold_restrictOpen_iso (K := K) (E := E) U).inv.1.base q) = q :=
    KIso.hom_base_inv_base (ofManifold_restrictOpen_iso (K := K) (E := E) U) q
  rw [h2] at h
  exact h.symm

/-- The underlying map of the transition. -/
def transitionFun : overlapTrace x y → overlapTrace y x :=
  fun p => (transitionManifoldIso x y).hom.1.base p

theorem contMDiff_transitionFun :
    ContMDiff 𝓘(K, Kn.{u} K d) 𝓘(K, Kn.{u} K d) ω (transitionFun x y) :=
  contMDiff_baseFun ContinuousLinearEquiv.ulift (transitionManifoldIso x y).hom

/-- The transition preserves the point of `X`: `e_y (τ p) = e_x p` in `X`. -/
theorem chartE_transitionFun (p : overlapTrace x y) :
    ((chartE X hX d y).hom.1.base ⟨(transitionFun x y p).1, overlapTrace_le y x
        (transitionFun x y p).2⟩).1 =
      ((chartE X hX d x).hom.1.base ⟨p.1, overlapTrace_le x y p.2⟩).1 := by
  -- unwind the five pieces of `transitionManifoldIso`
  set p₁ := (ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K d) (M := Kn.{u} K d)
    (overlapTrace x y)).inv.1.base p with hp₁
  set p₂ := (overlapTraceIso x y).inv.1.base p₁ with hp₂
  set p₃ := (transitionIso x y).hom.1.base p₂ with hp₃
  set p₄ := (overlapTraceIso y x).hom.1.base p₃ with hp₄
  have hτ : transitionFun x y p = (ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K d)
      (M := Kn.{u} K d) (overlapTrace y x)).hom.1.base p₄ := rfl
  have e1 : p₁.1 = p.1 := ofManifold_restrictOpen_iso_inv_base _ p
  have e2 : p₂.1.1 = p₁.1 := overlapTraceIso_inv_base x y p₁
  have e3 := transitionIso_hom_base x y p₂
  have e4 : p₄.1 = p₃.1.1 := overlapTraceIso_hom_base y x p₃
  have e5 : (transitionFun x y p).1 = p₄.1 := by
    rw [hτ]
    exact ofManifold_restrictOpen_iso_hom_base _ p₄
  have hp₂' : (⟨p.1, overlapTrace_le x y p.2⟩ : analyticSpaceOfOpen K d (chartG X hX d x)) =
      p₂.1 := by
    apply Subtype.ext
    rw [e2, e1]
  have hp₃' : (⟨(transitionFun x y p).1, overlapTrace_le y x (transitionFun x y p).2⟩ :
      analyticSpaceOfOpen K d (chartG X hX d y)) = p₃.1 := by
    apply Subtype.ext
    rw [e5, e4]
  rw [hp₂', hp₃']
  exact e3

open Classical in
/-- The extension by an arbitrary value of the transition to `K^d`. -/
def transitionExt : Kn.{u} K d → Kn.{u} K d :=
  fun w => if hw : w ∈ overlapTrace x y then (transitionFun x y ⟨w, hw⟩).1 else 0

open Classical in
theorem transitionExt_of_mem {w : Kn.{u} K d} (hw : w ∈ overlapTrace x y) :
    transitionExt x y w = (transitionFun x y ⟨w, hw⟩).1 := by
  change (if hw : w ∈ overlapTrace x y then (transitionFun x y ⟨w, hw⟩).1 else 0) = _
  rw [dite_eq_left hw]

theorem contMDiffOn_transitionExt :
    ContMDiffOn 𝓘(K, Kn.{u} K d) 𝓘(K, Kn.{u} K d) ω (transitionExt x y) (overlapTrace x y) := by
  intro w hw
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hf : ContMDiffAt 𝓘(K, Kn.{u} K d) 𝓘(K, Kn.{u} K d) ω
      (transitionExt x y ∘ Subtype.val) (⟨w, hw⟩ : overlapTrace x y) := by
    have h : transitionExt x y ∘ (Subtype.val : overlapTrace x y → Kn.{u} K d) =
        Subtype.val ∘ transitionFun x y :=
      funext fun p => transitionExt_of_mem x y p.2
    rw [h]
    exact (contMDiff_subtype_val.comp (contMDiff_transitionFun x y)).contMDiffAt
  exact ((contDiffWithinAt_localInvariantProp (I := 𝓘(K, Kn.{u} K d)) (I' := 𝓘(K, Kn.{u} K d))
    ω).liftPropAt_iff_comp_subtype_val (U := overlapTrace x y) (transitionExt x y) ⟨w, hw⟩).mpr hf

theorem contDiffOn_transitionExt :
    ContDiffOn K ω (transitionExt x y) (overlapTrace x y) :=
  contMDiffOn_iff_contDiffOn.mp (contMDiffOn_transitionExt x y)

/-- The chart change of the stratum at a point of its domain is the transition. -/
theorem stratumChart_trans_apply {z : Fin d → K}
    (hz : z ∈ ((stratumChart x).symm ≫ₕ stratumChart y).source) :
    stratumChart y ((stratumChart x).symm z) =
      ((transitionExt x y (ULift.up z)).down) := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    stratumChart_target] at hz
  obtain ⟨hzx, hzy⟩ := hz
  have hzx' : (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x := hzx
  have hzy₀ : (stratumChart x).symm z ∈ (stratumChart y).source := hzy
  rw [stratumChart_symm_apply x hzx'] at hzy₀ ⊢
  have hzy' : ((chartE X hX d x).hom.1.base ⟨ULift.up z, hzx'⟩).1 ∈ chartV X hX d y := hzy₀
  have hmem : (⟨ULift.up z, hzx'⟩ : analyticSpaceOfOpen K d (chartG X hX d x)) ∈
      overlapOpens x y := hzy'
  have hT : (ULift.up z : Kn.{u} K d) ∈ overlapTrace x y :=
    (mem_overlapOpens_iff x y _).mp hmem
  rw [stratumChart_apply y hzy', transitionExt_of_mem x y hT]
  unfold stratumCoord
  have h1 := chartE_transitionFun x y ⟨ULift.up z, hT⟩
  have h2 : (⟨(chartPt x ⟨ULift.up z, hzx'⟩).1, hzy'⟩ :
      X.toKLocallyRingedSpace.restrictOpen (chartV X hX d y)) =
      chartHomeo X hX d y ⟨(transitionFun x y ⟨ULift.up z, hT⟩).1,
        overlapTrace_le y x (transitionFun x y ⟨ULift.up z, hT⟩).2⟩ := by
    apply Subtype.ext
    exact h1.symm
  rw [h2]
  exact congrArg (fun q : analyticSpaceOfOpen K d (chartG X hX d y) => q.1.down)
    ((chartHomeo X hX d y).symm_apply_apply ⟨(transitionFun x y ⟨ULift.up z, hT⟩).1,
      overlapTrace_le y x (transitionFun x y ⟨ULift.up z, hT⟩).2⟩)

theorem stratumChart_trans_source_subset :
    ((stratumChart x).symm ≫ₕ stratumChart y).source ⊆
      (fun z : Fin d → K => (ULift.up z : Kn.{u} K d)) ⁻¹' overlapTrace x y := by
  intro z hz
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    stratumChart_target] at hz
  obtain ⟨hzx, hzy⟩ := hz
  have hzx' : (ULift.up z : Kn.{u} K d) ∈ chartG X hX d x := hzx
  have hzy₀ : (stratumChart x).symm z ∈ (stratumChart y).source := hzy
  rw [stratumChart_symm_apply x hzx'] at hzy₀
  exact (mem_overlapOpens_iff x y ⟨ULift.up z, hzx'⟩).mp hzy₀

/-- **The chart changes of the stratum are analytic.** -/
theorem contDiffOn_stratumChart_trans :
    ContDiffOn K ω ((stratumChart x).symm ≫ₕ stratumChart y)
      ((stratumChart x).symm ≫ₕ stratumChart y).source := by
  have hg : ContDiffOn K ω (fun z : Fin d → K =>
      (transitionExt x y (ULift.up z)).down)
      ((fun z : Fin d → K => (ULift.up z : Kn.{u} K d)) ⁻¹' overlapTrace x y) := by
    have h1 : ContDiff K ω (fun w : Kn.{u} K d => w.down) :=
      (ContinuousLinearEquiv.ulift : Kn.{u} K d ≃L[K] (Fin d → K)).contDiff
    have h2 : ContDiff K ω (fun z : Fin d → K => (ULift.up z : Kn.{u} K d)) :=
      (ContinuousLinearEquiv.ulift.symm : (Fin d → K) ≃L[K] Kn.{u} K d).contDiff
    exact h1.comp_contDiffOn ((contDiffOn_transitionExt x y).comp h2.contDiffOn
      (Set.mapsTo_preimage _ _))
  refine (hg.mono (stratumChart_trans_source_subset x y)).congr fun z hz => ?_
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, stratumChart_trans_apply x y hz]

end Transition

/-- **The stratum `X_d` is an analytic manifold** modelled on `K^d`. -/
instance instIsManifoldDimOpens : IsManifold 𝓘(K, Fin d → K) ω (dimOpens X hX d) := by
  refine isManifold_of_contDiffOn 𝓘(K, Fin d → K) ω (dimOpens X hX d) fun e e' he he' => ?_
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  exact contDiffOn_stratumChart_trans x y

instance instT2SpaceDimOpens : T2Space (dimOpens X hX d) :=
  inferInstanceAs (T2Space (dimOpens X hX d : Set X))

instance instSecondCountableDimOpens : SecondCountableTopology (dimOpens X hX d) :=
  inferInstanceAs (SecondCountableTopology (dimOpens X hX d : Set X))

/-- **The stratum `X_d` as a bundled analytic manifold** over `K^d`. -/
def stratumManifold : AnalyticManifold.{u} K (Fin d → K) where
  carrier := dimOpens X hX d

end AnalyticSpace
