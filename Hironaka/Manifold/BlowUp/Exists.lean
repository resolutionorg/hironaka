/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Defs
import Hironaka.Manifold.BlowUp.GluedOffCenter
import Hironaka.Manifold.BlowUp.GluedTopology
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The blowing-up exists

For `Y ⊆ M` a closed analytic submanifold of codimension `c` there is a blowing-up `π : M' → M`
with centre `Y`: a Hausdorff second-countable analytic manifold `M'` (in the universe of `M`)
with a proper analytic map `π` satisfying conditions (1) and (2) of [BM88, Definition 4.1]
(`exists_isBlowUp`). There are three cases.

* `1 ≤ c ≤ n`: the glued space of `Hironaka.Manifold.BlowUp.Glued` with its blow-down, which
  is a blowing-up by `Hironaka.Manifold.BlowUp.GluedCharts`, `GluedBlowDown`, `GluedOffCenter`
  and `GluedTopology`.
* `c = 0`, a boundary case not considered in the source: `Y` is open and closed and
  `IsBlowUp ψ Y 0 π` forces `π⁻¹(Y) = ∅`; the blowing-up is the inclusion `M ∖ Y → M`.
* `c > n`: there is no block embedding `Fin c ↪ Fin n`, `Y` is empty, and the blowing-up is the
  identity of `M`.

The type `BlowUpSpace ψ hY`, its instances and the map `blowUpMap ψ hY` are a choice of these
data; every property of the chosen blowing-up is read off `isBlowUp_blowUpMap`. This chosen
blowing-up is the one from which the sequences of blowings-up of the analytic strand are built.
-/

@[expose] public section

open TopologicalSpace Topology
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

open BlowUpGlue

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-! ### The inclusion of an open subset as a local diffeomorphism -/

open scoped Classical in
/-- The inclusion of an open subset, as a partial diffeomorphism onto the subset. -/
def opensValDiffeo (U : Opens M) (x₀ : U) : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) U M ω where
  toFun := Subtype.val
  invFun a := if h : a ∈ U then ⟨a, h⟩ else x₀
  source := Set.univ
  target := (U : Set M)
  map_source' x _ := x.2
  map_target' _ _ := Set.mem_univ _
  left_inv' x _ := by rw [dite_eq_left x.2]
  right_inv' a ha := by rw [dite_eq_left (SetLike.mem_coe.mp ha)]
  open_source := isOpen_univ
  open_target := U.isOpen
  contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
  contMDiffOn_invFun := by
    intro a ha
    have h : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        (Subtype.val ∘ fun a : M => if h : a ∈ U then (⟨a, h⟩ : U) else x₀) (U : Set M) a := by
      refine contMDiffWithinAt_id.congr (fun y hy => ?_) ?_
      · simp only [Function.comp_apply, id_eq]
        rw [dite_eq_left (SetLike.mem_coe.mp hy)]
      · simp only [Function.comp_apply, id_eq]
        rw [dite_eq_left (SetLike.mem_coe.mp ha)]
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).mp h

variable [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {Y : Set M} {c : ℕ}

/-! ### The three cases -/

/-- The main case `1 ≤ c ≤ n`: the glued space with its blow-down is a blowing-up. The witness
`(σ₀, i₀)` is immaterial: it only serves to produce adapted charts at the points off `Y`
(`exists_isAdaptedChart_of_notMem`), so that the pieces cover `M`; the glued space, its blow-down
and the conclusion do not depend on it. -/
theorem exists_isBlowUp_of_embedding (hY : IsClosedSubmanifold ψ Y c) (σ₀ : Fin c ↪ Fin n)
    (i₀ : Fin c) :
    ∃ (M' : Type u) (_ : TopologicalSpace M') (_ : ChartedSpace E M')
      (_ : IsManifold 𝓘(𝕜, E) ω M') (_ : T2Space M') (_ : SecondCountableTopology M')
      (π : M' → M), IsBlowUp ψ Y c π := by
  have := t2Space_glued hY σ₀ i₀
  have := secondCountableTopology_glued hY σ₀ i₀
  refine ⟨Glued ψ Y c, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    gluedProj, ?_⟩
  exact
    { contMDiff := contMDiff_gluedProj
      isProperMap := isProperMap_gluedProj hY σ₀ i₀
      isLocalDiffeomorphOn_compl := isLocalDiffeomorphOn_gluedProj
      bijOn_compl := bijOn_gluedProj hY σ₀ i₀
      exists_chart := fun φ _ hφ i => by
        have : Nonempty M := ⟨φ.symm 0⟩
        have := nonempty_glued hY σ₀ i₀
        exact exists_isBlowUpChart hφ i
      cover := fun _ _ hφ p hp => exists_isBlowUpChart_mem_source hφ p hp }

/-- The case `c = 0`: `Y` is open and closed, and the inclusion `M ∖ Y → M` is a blowing-up. -/
theorem exists_isBlowUp_of_c_eq_zero (hY : IsClosedSubmanifold ψ Y 0) :
    ∃ (M' : Type u) (_ : TopologicalSpace M') (_ : ChartedSpace E M')
      (_ : IsManifold 𝓘(𝕜, E) ω M') (_ : T2Space M') (_ : SecondCountableTopology M')
      (π : M' → M), IsBlowUp ψ Y 0 π := by
  have hYopen : IsOpen Y := by
    rw [isOpen_iff_forall_mem_open]
    intro a ha
    obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
    exact ⟨φ.source, fun x hx => (hφ.2 x hx).mpr fun i => i.elim0, φ.open_source, haφ⟩
  have hYc : IsClosed Yᶜ := IsOpen.isClosed_compl hYopen
  let U : Opens M := ⟨Yᶜ, hY.isClosed.isOpen_compl⟩
  refine ⟨U, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Subtype.val, ?_⟩
  refine
    { contMDiff := contMDiff_subtype_val
      isProperMap :=
        Topology.IsClosedEmbedding.isProperMap (IsClosed.isClosedEmbedding_subtypeVal hYc)
      isLocalDiffeomorphOn_compl := fun x =>
        IsLocalDiffeomorphAt.of_eqOn (opensValDiffeo U x.1) (Set.mem_univ _) fun _ _ => rfl
      bijOn_compl :=
        ⟨fun x _ => x.2, fun _ _ _ _ h => Subtype.ext h, fun a ha => ⟨⟨a, ha⟩, ha, rfl⟩⟩
      exists_chart := fun _ _ _ i => i.elim0
      cover := fun _ _ hφ p hp => ?_ }
  exact (p.2 ((hφ.2 _ hp).mpr fun i => i.elim0)).elim

/-- The case `c > n`: no block embedding exists, `Y` is empty, and the identity is a
blowing-up. -/
theorem exists_isBlowUp_of_isEmpty (hemp : IsEmpty (Fin c ↪ Fin n)) :
    ∃ (M' : Type u) (_ : TopologicalSpace M') (_ : ChartedSpace E M')
      (_ : IsManifold 𝓘(𝕜, E) ω M') (_ : T2Space M') (_ : SecondCountableTopology M')
      (π : M' → M), IsBlowUp ψ Y c π := by
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, id, ?_⟩
  refine
    { contMDiff := contMDiff_id
      isProperMap := isProperMap_id
      isLocalDiffeomorphOn_compl := fun _ =>
        IsLocalDiffeomorphAt.of_eqOn (Diffeomorph.refl 𝓘(𝕜, E) M ω).toPartialDiffeomorphUniv
          (Set.mem_univ _) fun _ _ => rfl
      bijOn_compl := by rw [Set.preimage_id]; exact Set.bijOn_id _
      exists_chart := fun _ σ _ _ => (hemp.false σ).elim
      cover := fun _ σ _ _ _ => (hemp.false σ).elim }

/-- **The blowing-up exists** [BM88, Definition 4.1]: for `Y` a closed submanifold of codimension
`c` there is a Hausdorff second-countable analytic manifold `M'` in the universe of `M` with a
proper analytic map `π : M' → M` satisfying conditions (1) and (2) of the definition. -/
theorem exists_isBlowUp (hY : IsClosedSubmanifold ψ Y c) :
    ∃ (M' : Type u) (_ : TopologicalSpace M') (_ : ChartedSpace E M')
      (_ : IsManifold 𝓘(𝕜, E) ω M') (_ : T2Space M') (_ : SecondCountableTopology M')
      (π : M' → M), IsBlowUp ψ Y c π := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    exact exists_isBlowUp_of_c_eq_zero ψ hY
  · by_cases hcn : c ≤ n
    · exact exists_isBlowUp_of_embedding ψ hY (Fin.castLEEmb hcn) ⟨0, hc⟩
    · refine exists_isBlowUp_of_isEmpty ψ ⟨fun σ => hcn ?_⟩
      simpa using Fintype.card_le_of_embedding σ

/-! ### A chosen blowing-up -/

/-- **The blowing-up of `M` with centre `Y`** [BM88, Definition 4.1]: a choice of the data of
`exists_isBlowUp`. Its properties are read off `isBlowUp_blowUpMap`. -/
def BlowUpSpace (hY : IsClosedSubmanifold ψ Y c) : Type u := (exists_isBlowUp ψ hY).choose

variable (hY : IsClosedSubmanifold ψ Y c)

/-- The topology of the chosen blowing-up, from `exists_isBlowUp`. -/
instance : TopologicalSpace (BlowUpSpace ψ hY) := (exists_isBlowUp ψ hY).choose_spec.choose

/-- The charts of the chosen blowing-up, from `exists_isBlowUp`. -/
instance : ChartedSpace E (BlowUpSpace ψ hY) :=
  (exists_isBlowUp ψ hY).choose_spec.choose_spec.choose

/-- The remaining data of the chosen blowing-up. -/
theorem blowUpSpace_spec :
    ∃ (_ : IsManifold 𝓘(𝕜, E) ω (BlowUpSpace ψ hY)) (_ : T2Space (BlowUpSpace ψ hY))
      (_ : SecondCountableTopology (BlowUpSpace ψ hY)) (π : BlowUpSpace ψ hY → M),
      IsBlowUp ψ Y c π :=
  (exists_isBlowUp ψ hY).choose_spec.choose_spec.choose_spec

/-- The chosen blowing-up is an analytic manifold. -/
instance : IsManifold 𝓘(𝕜, E) ω (BlowUpSpace ψ hY) := (blowUpSpace_spec ψ hY).choose

/-- The chosen blowing-up is Hausdorff. -/
instance : T2Space (BlowUpSpace ψ hY) := (blowUpSpace_spec ψ hY).choose_spec.choose

/-- The chosen blowing-up is second countable. -/
instance : SecondCountableTopology (BlowUpSpace ψ hY) :=
  (blowUpSpace_spec ψ hY).choose_spec.choose_spec.choose

/-- The blow-down `π : M' → M` of the chosen blowing-up. -/
def blowUpMap : BlowUpSpace ψ hY → M :=
  (blowUpSpace_spec ψ hY).choose_spec.choose_spec.choose_spec.choose

/-- The chosen blowing-up is a blowing-up in the sense of [BM88, Definition 4.1]. -/
theorem isBlowUp_blowUpMap : IsBlowUp ψ Y c (blowUpMap ψ hY) :=
  (blowUpSpace_spec ψ hY).choose_spec.choose_spec.choose_spec.choose_spec

end

end Manifold
