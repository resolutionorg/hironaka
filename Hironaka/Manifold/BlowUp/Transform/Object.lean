/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Defs
public import Hironaka.Manifold.Submanifold.Restrict
import Hironaka.Manifold.BlowUp.Restrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The ideal sheaf of the centre and the total transform

The ideal sheaf `I_Y` of a closed submanifold `Y` (the specification `IsIdealSheafOf`: cosupport
`Y`, stalks on `Y` spanned by the adapted coordinates) exists and is unique, so the classically
chosen `IsClosedSubmanifold.idealSheaf` satisfies
the specification. The construction is `IdealSheaf.ofStalks` applied to the stalks given by the
kernel of the restriction of germs `𝒪_{M,a} → 𝒪_{Y,a}` at points of `Y` and by the unit ideal off
`Y`: these stalks have local generators; over an adapted chart, the coordinate sections `ψ_{σ i} ∘
φ` (their germs span the kernel at points of `Y`, and one of them is a unit at a point of the chart
off `Y`, since its value there is nonzero); off `Y`, the section `1` on the open complement.
Uniqueness is stalkwise (`IdealSheaf.ext`): both stalks are the span of the adapted coordinates on
`Y` and the unit ideal off `Y`. The stalks of the total transform are those of the pullback of an
ideal sheaf [Hir64, Ch. 0, §5, p. 142]. On an open subset `U ⊆ M` the trace `Y ∩ U` is a closed
submanifold of `U` (its adapted charts are the restrictions `subtypeRestr` of those of `Y`) whose
ideal sheaf is the pullback of `I_Y` along the inclusion (`IsClosedSubmanifold.preimage_val`,
`isIdealSheafOf_pullback_val`, `IsClosedSubmanifold.idealSheaf_preimage_val`).

These are the objects on which the transforms of `Hironaka.Manifold.BlowUp.Transform.Colon`
and the sequences of blowings-up (`FiniteSuccession`) operate.
-/

@[expose] public section

open TopologicalSpace Opposite CategoryTheory IsLocalRing
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

open TopologicalSpace

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ}

open scoped Classical in
/-- The stalks of the ideal sheaf of the closed submanifold `Y`: the kernel of the restriction of
germs `𝒪_{M,a} → 𝒪_{Y,a}` at a point of `Y`, the unit ideal off `Y`. -/
noncomputable def IsClosedSubmanifold.centerStalk (hY : IsClosedSubmanifold ψ Y c) (a : M) :
    Ideal ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  if h : a ∈ Y then RingHom.ker (hY.restrictStalk ⟨a, h⟩) else ⊤

/-- The stalk of the centre's ideal at a point of `Y`. -/
theorem IsClosedSubmanifold.centerStalk_of_mem (hY : IsClosedSubmanifold ψ Y c) {a : M}
    (ha : a ∈ Y) : hY.centerStalk a = RingHom.ker (hY.restrictStalk ⟨a, ha⟩) := dite_eq_left ha

/-- The stalk of the centre's ideal off `Y` is the unit ideal. -/
theorem IsClosedSubmanifold.centerStalk_of_notMem (hY : IsClosedSubmanifold ψ Y c) {a : M}
    (ha : a ∉ Y) : hY.centerStalk a = ⊤ := dite_eq_right ha

/-- At a point of `Y` in an adapted chart, the kernel of the restriction of germs is spanned by
the adapted coordinates (which vanish at that point). -/
theorem IsClosedSubmanifold.ker_restrictStalk_eq_span (hY : IsClosedSubmanifold ψ Y c) {a : M}
    (ha : a ∈ Y) {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ)
    (haφ : a ∈ φ.source) :
    RingHom.ker (hY.restrictStalk ⟨a, ha⟩) =
      Ideal.span (Set.range fun i => coord E ψ φ hφ.1 haφ (σ i)) := by
  rw [IsClosedSubmanifold.IsRestrictStalk.ker_eq_span' hY (hY.isRestrictStalk_restrictStalk ⟨a, ha⟩)
    hφ haφ]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  rw [eval_coord, (hφ.2 a haφ).1 ha i, map_zero, sub_zero]

/-- The stalks of the centre's ideal have local generators: the coordinate sections of an adapted
chart on `Y`, the section `1` on the complement of `Y`. -/
theorem IsClosedSubmanifold.hasLocalGenerators_centerStalk (hY : IsClosedSubmanifold ψ Y c) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M) hY.centerStalk := by
  intro a
  by_cases ha : a ∈ Y
  · obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
    refine ⟨⟨φ.source, φ.open_source⟩, haφ, Fin c, inferInstance,
      fun i => chartSection E ψ φ hφ.1 (σ i), fun b hb => ?_⟩
    by_cases hbY : b ∈ Y
    · rw [hY.centerStalk_of_mem hbY, hY.ker_restrictStalk_eq_span hbY hφ hb]
      rfl
    · rw [hY.centerStalk_of_notMem hbY, eq_comm, Ideal.span_eq_top_iff_exists_isUnit]
      obtain ⟨i, hi⟩ := not_forall.mp fun h => hbY ((hφ.2 b hb).2 h)
      refine ⟨_, ⟨i, rfl⟩, ?_⟩
      rw [← IsLocalRing.notMem_maximalIdeal]
      change coord E ψ φ hφ.1 hb (σ i) ∉ maximalIdeal _
      rw [mem_maximalIdeal_iff_eval, eval_coord]
      exact hi
  · refine ⟨⟨Yᶜ, hY.isClosed.isOpen_compl⟩, ha, Unit, inferInstance, fun _ => 1, fun b hb => ?_⟩
    rw [hY.centerStalk_of_notMem hb, eq_comm, Ideal.eq_top_iff_one]
    refine Ideal.subset_span ⟨(), ?_⟩
    simp

/-- The ideal sheaf of a closed submanifold exists (the specification `IsIdealSheafOf`). -/
theorem IsClosedSubmanifold.exists_isIdealSheafOf (hY : IsClosedSubmanifold ψ Y c) :
    ∃ J : IdealSheaf (structureSheaf 𝕜 E M), IsIdealSheafOf ψ Y c J := by
  refine ⟨IdealSheaf.ofStalks _ hY.centerStalk hY.hasLocalGenerators_centerStalk, ?_, ?_⟩
  · ext a
    rw [IdealSheaf.mem_support, IdealSheaf.stalkIdeal_ofStalks]
    constructor
    · intro h
      by_contra ha
      exact h (hY.centerStalk_of_notMem ha)
    · intro ha
      rw [hY.centerStalk_of_mem ha]
      let _i := hY.chartedSpace
      exact RingHom.ker_ne_top _
  · intro φ σ hφ a haφ ha
    rw [IdealSheaf.stalkIdeal_ofStalks, hY.centerStalk_of_mem ha,
      hY.ker_restrictStalk_eq_span ha hφ haφ]

/-- Off `Y`, the stalk of an ideal sheaf of `Y` is the unit ideal. -/
theorem IsIdealSheafOf.stalkIdeal_of_notMem {J : IdealSheaf (structureSheaf 𝕜 E M)}
    (hJ : IsIdealSheafOf ψ Y c J) {a : M} (ha : a ∉ Y) : J.stalkIdeal a = ⊤ := by
  by_contra h
  exact ha (hJ.1 ▸ (h : a ∈ J.support))

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- The total transform is generated by the `f ∘ π` for local generators `f` of `I`. -/
theorem totalTransform_stalkIdeal_eq_span (h : IsBlowUp ψ Y c π)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) {U : Opens M} {k : ℕ}
    {f : Fin k → (structureSheaf 𝕜 E M).presheaf.obj (op U)}
    (hgen : ∀ b (hb : b ∈ U), I.stalkIdeal b =
      Ideal.span (Set.range fun j => (structureSheaf 𝕜 E M).presheaf.germ U b hb (f j)))
    {a' : M'} (ha' : π a' ∈ U) :
    (I.pullback π h.contMDiff).stalkIdeal a' = Ideal.span (Set.range fun j =>
      germMap π h.contMDiff a' ((structureSheaf 𝕜 E M).presheaf.germ U (π a') ha' (f j))) := by
  rw [IdealSheaf.stalkIdeal_pullback, hgen (π a') ha', Ideal.map_span, ← Set.range_comp]
  rfl

/-- The chosen ideal sheaf `hY.idealSheaf` satisfies the specification `IsIdealSheafOf`. -/
theorem IsClosedSubmanifold.isIdealSheafOf_idealSheaf (hY : IsClosedSubmanifold ψ Y c) :
    IsIdealSheafOf ψ Y c hY.idealSheaf := by
  unfold IsClosedSubmanifold.idealSheaf
  rw [dite_eq_left hY.exists_isIdealSheafOf]
  exact Classical.choose_spec hY.exists_isIdealSheafOf

/-- The ideal sheaf of a closed submanifold is unique. -/
theorem IsIdealSheafOf.eq_idealSheaf (hY : IsClosedSubmanifold ψ Y c)
    {J : IdealSheaf (structureSheaf 𝕜 E M)} (hJ : IsIdealSheafOf ψ Y c J) : J = hY.idealSheaf := by
  have hJ' := hY.isIdealSheafOf_idealSheaf
  refine IdealSheaf.ext fun a => ?_
  by_cases ha : a ∈ Y
  · obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
    rw [hJ.2 φ σ hφ a haφ ha, hJ'.2 φ σ hφ a haφ ha]
  · rw [hJ.stalkIdeal_of_notMem ha, hJ'.stalkIdeal_of_notMem ha]

/-- The cosupport of the ideal sheaf of `Y` is `Y`. -/
theorem IsClosedSubmanifold.cosupport_idealSheaf (hY : IsClosedSubmanifold ψ Y c) :
    hY.idealSheaf.support = Y :=
  hY.isIdealSheafOf_idealSheaf.1

/-- At a point of `Y`, the stalk of the ideal sheaf of `Y` is the kernel of the restriction of
germs. -/
theorem IsClosedSubmanifold.stalkIdeal_idealSheaf_of_mem (hY : IsClosedSubmanifold ψ Y c) {a : M}
    (ha : a ∈ Y) : hY.idealSheaf.stalkIdeal a = RingHom.ker (hY.restrictStalk ⟨a, ha⟩) := by
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
  rw [hY.isIdealSheafOf_idealSheaf.2 φ σ hφ a haφ ha, hY.ker_restrictStalk_eq_span ha hφ haφ]

/-- Off `Y` the stalk of the ideal sheaf of `Y` is the unit ideal. -/
theorem IsClosedSubmanifold.stalkIdeal_idealSheaf_of_notMem (hY : IsClosedSubmanifold ψ Y c)
    {a : M} (ha : a ∉ Y) : hY.idealSheaf.stalkIdeal a = ⊤ :=
  hY.isIdealSheafOf_idealSheaf.stalkIdeal_of_notMem ha

/-- At a point of `Y`, the stalk of the ideal sheaf of `Y` is spanned by the adapted coordinates
of any adapted chart. -/
theorem IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_span (hY : IsClosedSubmanifold ψ Y c) {a : M}
    (ha : a ∈ Y) {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ)
    (haφ : a ∈ φ.source) :
    hY.idealSheaf.stalkIdeal a = Ideal.span (Set.range fun i => coord E ψ φ hφ.1 haφ (σ i)) :=
  hY.isIdealSheafOf_idealSheaf.2 φ σ hφ a haφ ha

/-! ### The centre on an open subset -/

section OpenSubset

open Filter Set

variable [IsManifold 𝓘(𝕜, E) ω M]

/-- The trace of a closed
submanifold on an open subset `U` is a closed submanifold of `U` of the same codimension — its
adapted charts are the restrictions of the adapted charts of `Y`. -/
theorem IsClosedSubmanifold.preimage_val (hY : IsClosedSubmanifold ψ Y c) (U : Opens M) :
    IsClosedSubmanifold ψ ((Subtype.val : U → M) ⁻¹' Y) c where
  isClosed := hY.isClosed.preimage continuous_subtype_val
  exists_adaptedChart := by
    intro a ha
    obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
    have hU : Nonempty U := ⟨a⟩
    refine ⟨φ.subtypeRestr hU, σ, ?_, subtypeRestr_mem_maximalAtlas_of_mem_maximalAtlas hU hφ.1,
      fun x hx => ?_⟩
    · rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact haφ
    · rw [OpenPartialHomeomorph.subtypeRestr_source] at hx
      exact hφ.2 x hx

/-- The pullback of the ideal sheaf of `Y` along the inclusion of an open
subset `U` is the ideal sheaf of the trace `Y ∩ U` — cosupport `Y ∩ U`, and in an adapted chart of
the trace, extended to `M`, the stalk spanned by the coordinate germs, which the stalk map of the
inclusion carries to the coordinate germs of the chart of `U`. -/
theorem isIdealSheafOf_pullback_val (hY : IsClosedSubmanifold ψ Y c) (U : Opens M) :
    IsIdealSheafOf ψ ((Subtype.val : U → M) ⁻¹' Y) c
      (hY.idealSheaf.pullback (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E)))) := by
  refine ⟨?_, ?_⟩
  · rw [IdealSheaf.support_pullback, hY.cosupport_idealSheaf]
  · intro φ' σ hφ' a ha haY
    have hU : Nonempty U := ⟨a⟩
    have hφ : IsAdaptedChart ψ Y (Opens.extendChart hU φ') σ := isAdaptedChart_extendChart hU hφ'
    have haφ : (a : M) ∈ (Opens.extendChart hU φ').source :=
      (Opens.mem_extendChart_source_iff hU φ').mpr ⟨a.2, ha⟩
    rw [IdealSheaf.stalkIdeal_pullback, hY.stalkIdeal_idealSheaf_eq_span haY hφ haφ, Ideal.map_span,
      ← Set.range_comp]
    refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
    apply stalkToGerm_injective 𝓘(𝕜, E) ω U a
    rw [Function.comp_apply, stalkToGerm_germMap, stalkToGerm_coord, stalkToGerm_coord,
      Germ.coe_compTendsto, Germ.coe_eq]
    filter_upwards [φ'.open_source.mem_nhds ha] with x hx
    rw [Function.comp_apply,
      extendSection_of_mem 𝕜 E _ ((Opens.mem_extendChart_source_iff hU φ').mpr ⟨x.2, hx⟩),
      extendSection_of_mem 𝕜 E _ hx]
    change ψ (Opens.extendChart hU φ' x) (σ i) = ψ (φ' x) (σ i)
    rw [Opens.extendChart_apply hU φ' x.2]

/-- The ideal sheaf of the trace is the pullback of the ideal sheaf of
the centre (uniqueness of the ideal sheaf of a closed submanifold). -/
theorem IsClosedSubmanifold.idealSheaf_preimage_val (hY : IsClosedSubmanifold ψ Y c) (U : Opens M)
    (hY' : IsClosedSubmanifold ψ ((Subtype.val : U → M) ⁻¹' Y) c) :
    hY'.idealSheaf =
      hY.idealSheaf.pullback (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E))) :=
  (IsIdealSheafOf.eq_idealSheaf hY' (isIdealSheafOf_pullback_val hY U)).symm

end OpenSubset

end Manifold
