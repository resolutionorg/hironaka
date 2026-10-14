/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Value
public import Hironaka.Resolution.Analytic.Functor.Family
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.RefinesAlong
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Comap
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.RealizePullback
import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialIndiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Compatibility, commutation with local isomorphisms and indifference to empty members

The value of the monomial procedure on a relatively compact open (`monomialStep3SeqOn`,
`BMO/Step3Monomial/Value.lean`) is the realised run of the input piece family, the traces on `U` of
the ambient components meeting `closure U`. Three further properties are required of it: it is
compatible under restriction to a smaller open (for `U ≤ V` the value on `U` is the value on `V`
pulled back and cleaned of its empty blow-ups, [Wlo09, Theorem 2.0.3 (4)]); it commutes with local
analytic isomorphisms up to empty blow-ups ([Kol07, 34.1], [Wlo09, Theorem 3.5.1 (1)–(2)]); and it
is unchanged when empty members of the boundary are deleted. Each is an instance of one theorem,
that the run of a piece family refining another along a local analytic isomorphism is the pull-back
of the run with its empty blow-ups erased (`RefinesAlong.realize_pullback_eraseEmpty`,
`BMO/Step3Monomial/RealizePullback.lean`), once the two input families are shown to refine one
another along the map in question. This file proves the three refinements and reads off the three
properties.

* One lemma for the three refinements (`refinesAlong_inputFamily_of_componentMap`): a map `φ` of
  ambient components, compatible with an order embedding of the members, that carries meeting
  components to meeting components, preserves the exponents, maps the trace of a component into the
  trace of its image, covers every point over a component and separates two components with the same
  image, induces a refinement of the input families; the parent map re-indexes through the
  enumerations and the label map factors the sorted enumerations of the members
  (`exists_labelMap_factor`).
* The three component maps: for `U ≤ V` the identity (a component meeting `closure U` meets
  `closure V`); along a local analytic isomorphism `g`, a connected component of `g⁻¹(Eʲ)` maps into
  one connected component of `Eʲ` (`parentIndex`), with the same exponent; for the deletion of empty
  members, the bijection of components `BMOmod.emptyExtIdx` of `Modified/NonmonomialIndiff.lean`.

The theorem is applied with the input family's own boundary family, so the boundary data need not
be transported: the run is a function of the pieces, their exponents and the order of the labels
alone.
-/

@[expose] public section

open Set Topology TopologicalSpace Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

/-! ### Sorted enumerations of nested finite sets factor (the label maps) -/

/-- Two order embeddings of `Fin a` and `Fin b` into a linear order, the range of the first inside
the range of the second: the first factors through the second by an order embedding
`Fin a ↪o Fin b`. -/
theorem exists_orderEmbedding_factor {ι : Type*} [LinearOrder ι] {a b : ℕ} (eU : Fin a ↪o ι)
    (eV : Fin b ↪o ι) (h : Set.range eU ⊆ Set.range eV) :
    ∃ σ : Fin a ↪o Fin b, ∀ ℓ, eV (σ ℓ) = eU ℓ := by
  classical
  have hex : ∀ ℓ : Fin a, ∃ ℓ' : Fin b, eV ℓ' = eU ℓ := fun ℓ => h ⟨ℓ, rfl⟩
  choose f hf using hex
  refine ⟨OrderEmbedding.ofStrictMono f fun ℓ₁ ℓ₂ hlt => ?_, hf⟩
  rw [← eV.lt_iff_lt, hf, hf]
  exact eU.strictMono hlt

/-- The factor of `exists_orderEmbedding_factor` as a map `ℕ → ℕ` on the labels below `a`: bounded
by `b` and strictly monotone there, and factoring the enumerations. -/
theorem exists_labelMap_factor {ι : Type*} [LinearOrder ι] {a b : ℕ} (eU : Fin a ↪o ι)
    (eV : Fin b ↪o ι) (h : Set.range eU ⊆ Set.range eV) :
    ∃ (σ : ℕ → ℕ) (hσ : ∀ ℓ, ℓ < a → σ ℓ < b), StrictMonoOn σ (Set.Iio a) ∧
      ∀ ℓ (hℓ : ℓ < a), eV ⟨σ ℓ, hσ ℓ hℓ⟩ = eU ⟨ℓ, hℓ⟩ := by
  classical
  obtain ⟨σ', hσ'⟩ := exists_orderEmbedding_factor eU eV h
  let σ : ℕ → ℕ := fun ℓ => if hℓ : ℓ < a then (σ' ⟨ℓ, hℓ⟩).1 else 0
  have hσ : ∀ ℓ, ℓ < a → σ ℓ < b := fun ℓ hℓ => by
    change (if hℓ : ℓ < a then (σ' ⟨ℓ, hℓ⟩).1 else 0) < b
    rw [dite_eq_left hℓ]
    exact (σ' ⟨ℓ, hℓ⟩).2
  refine ⟨σ, hσ, ?_, fun ℓ hℓ => ?_⟩
  · intro ℓ₁ h₁ ℓ₂ h₂ hlt
    simp only [Set.mem_Iio] at h₁ h₂
    change (if hℓ : ℓ₁ < a then (σ' ⟨ℓ₁, hℓ⟩).1 else 0) <
      if hℓ : ℓ₂ < a then (σ' ⟨ℓ₂, hℓ⟩).1 else 0
    rw [dite_eq_left h₁, dite_eq_left h₂]
    exact σ'.strictMono (Fin.mk_lt_mk.mpr hlt)
  · have h1 : (⟨σ ℓ, hσ ℓ hℓ⟩ : Fin b) = σ' ⟨ℓ, hℓ⟩ := Fin.ext (dite_eq_left hℓ)
    rw [h1, hσ']

/-! ### Components of a pulled-back family: the parent map -/

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] (g : N → M)
  (F : HypersurfaceFamily M)

/-- The map from a member of the pulled-back boundary family into the member. -/
def comapMemberMap (j : F.ι) : (F.comap g).hyp j → F.hyp j := fun x => ⟨g x.1, x.2⟩

variable {g}

theorem continuous_comapMemberMap (hg : Continuous g) (j : F.ι) :
    Continuous (comapMemberMap g F j) :=
  (hg.comp continuous_subtype_val).subtype_mk _

/-- The parent of a component of the pulled-back family: the same member, and the connected
component into which the image of the component maps (a connected set maps into one connected
component). -/
noncomputable def parentIndex (hg : Continuous g) (i' : ComponentIndex (F.comap g)) :
    ComponentIndex F :=
  ⟨i'.1, (ConnectedComponents.continuous_coe.comp
    (continuous_comapMemberMap F hg i'.1)).connectedComponentsLift i'.2⟩

theorem parentIndex_fst (hg : Continuous g) (i' : ComponentIndex (F.comap g)) :
    (parentIndex F hg i').1 = i'.1 := rfl

theorem mem_componentSet_parentIndex (hg : Continuous g) {i' : ComponentIndex (F.comap g)} {x : N}
    (hx : x ∈ componentSet (F.comap g) i') : g x ∈ componentSet F (parentIndex F hg i') := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨comapMemberMap g F i'.1 y, ?_, rfl⟩
  change ConnectedComponents.mk (comapMemberMap g F i'.1 y) =
    (ConnectedComponents.continuous_coe.comp
      (continuous_comapMemberMap F hg i'.1)).connectedComponentsLift i'.2
  have hy' : ConnectedComponents.mk y = i'.2 := hy
  rw [← hy']
  rfl

theorem componentSet_comap_subset_preimage (hg : Continuous g) (i' : ComponentIndex (F.comap g)) :
    componentSet (F.comap g) i' ⊆ g ⁻¹' componentSet F (parentIndex F hg i') :=
  fun _ hx => mem_componentSet_parentIndex F hg hx

/-- Every point over a component lies on a component of the pulled-back family whose parent is that
component. -/
theorem exists_parentIndex_eq (hg : Continuous g) {i : ComponentIndex F} {x : N}
    (hx : g x ∈ componentSet F i) :
    ∃ i' : ComponentIndex (F.comap g),
      x ∈ componentSet (F.comap g) i' ∧ parentIndex F hg i' = i := by
  obtain ⟨y, hy, hyx⟩ := hx
  have hxj : x ∈ (F.comap g).hyp i.1 := by
    change g x ∈ F.hyp i.1
    rw [← hyx]
    exact y.2
  refine ⟨⟨i.1, ConnectedComponents.mk ⟨x, hxj⟩⟩, ⟨⟨x, hxj⟩, rfl, rfl⟩, ?_⟩
  obtain ⟨j, C⟩ := i
  have hy' : ConnectedComponents.mk y = C := hy
  simp only at hyx hy'
  refine Sigma.ext rfl (heq_of_eq ?_)
  change (ConnectedComponents.continuous_coe.comp
      (continuous_comapMemberMap F hg j)).connectedComponentsLift
        (ConnectedComponents.mk (⟨x, hxj⟩ : (F.comap g).hyp j)) = C
  rw [Continuous.connectedComponentsLift_apply_coe, ← hy', Function.comp_apply]
  have e : comapMemberMap g F j ⟨x, hxj⟩ = y := Subtype.ext hyx.symm
  rw [e]

/-- Two distinct components of one member are disjoint. -/
theorem componentSet_disjoint_of_ne {j : F.ι} {C₁ C₂ : ConnectedComponents (F.hyp j)}
    (h : C₁ ≠ C₂) :
    Disjoint (componentSet F ⟨j, C₁⟩) (componentSet F ⟨j, C₂⟩) := by
  rw [Set.disjoint_left]
  rintro x ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, hy₂x⟩
  have h₁ : ConnectedComponents.mk y₁ = C₁ := hy₁
  have h₂ : ConnectedComponents.mk y₂ = C₂ := hy₂
  have e : y₂ = y₁ := Subtype.ext hy₂x
  subst e
  exact h (h₁.symm.trans h₂)

/-! ### The index of a meeting piece in the enumeration -/

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

section MeetingIndex

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (U : Opens M)
  (hU : IsCompact (closure (U : Set M)))

/-- The index of a meeting piece in the enumeration `meetingPiece`. -/
noncomputable def meetingIndex {i : ComponentIndex T.F} (hi : i ∈ meetingPieces T U hU) :
    Fin (meetingPieces T U hU).card :=
  (meetingPieces T U hU).equivFin ⟨i, hi⟩

theorem meetingPiece_meetingIndex {i : ComponentIndex T.F} (hi : i ∈ meetingPieces T U hU) :
    meetingPiece T U hU (meetingIndex T U hU hi) = i := by
  unfold meetingPiece meetingIndex
  rw [Equiv.symm_apply_apply]

end MeetingIndex

/-! ### The refinements between input families -/

namespace PieceFamily

open _root_.Manifold

/-- The common form of the three refinements: a map `φ` of ambient components, compatible with an
order embedding `eMem` of the members, carrying meeting components to meeting components,
preserving the exponents, mapping the trace of a component into the trace of its image, covering
every point over a component, and separating two components with the same image, induces a
refinement of the input families along `ρ` with some parent map `p` and label map `σ`. -/
theorem refinesAlong_inputFamily_of_componentMap {M₁ M₂ : AnalyticManifold.{u} 𝕜 E}
    (T₁ : AnalyticTriple ψ₀ M₁) (U₁ : Opens M₁) (hU₁ : IsCompact (closure (U₁ : Set M₁)))
    (T₂ : AnalyticTriple ψ₀ M₂) (U₂ : Opens M₂) (hU₂ : IsCompact (closure (U₂ : Set M₂)))
    (ρ : AnalyticMap (M₁.restrict U₁) (M₂.restrict U₂))
    (φ : ComponentIndex T₁.F → ComponentIndex T₂.F) (eMem : T₁.F.ι ↪o T₂.F.ι)
    (hφfst : ∀ i, (φ i).1 = eMem i.1)
    (hφmeet : ∀ i ∈ meetingPieces T₁ U₁ hU₁, φ i ∈ meetingPieces T₂ U₂ hU₂)
    (hφa : ∀ i ∈ meetingPieces T₁ U₁ hU₁,
      componentExponent T₂.F T₂.isSnc T₂.I (φ i) = componentExponent T₁.F T₁.isSnc T₁.I i)
    (hsub : ∀ i ∈ meetingPieces T₁ U₁ hU₁, ∀ x : M₁.restrict U₁,
      M₁.inclusion U₁ x ∈ componentSet T₁.F i → M₂.inclusion U₂ (ρ x) ∈ componentSet T₂.F (φ i))
    (hcover : ∀ i₂ ∈ meetingPieces T₂ U₂ hU₂, ∀ x : M₁.restrict U₁,
      M₂.inclusion U₂ (ρ x) ∈ componentSet T₂.F i₂ →
        ∃ i ∈ meetingPieces T₁ U₁ hU₁, φ i = i₂ ∧ M₁.inclusion U₁ x ∈ componentSet T₁.F i)
    (hdisj : ∀ i ∈ meetingPieces T₁ U₁ hU₁, ∀ i' ∈ meetingPieces T₁ U₁ hU₁, i ≠ i' → φ i = φ i' →
      ∀ x : M₁.restrict U₁, M₁.inclusion U₁ x ∈ componentSet T₁.F i →
        M₁.inclusion U₁ x ∉ componentSet T₁.F i') :
    ∃ p σ : ℕ → ℕ, (inputFamily T₁ U₁ hU₁).RefinesAlong ρ p σ (inputFamily T₂ U₂ hU₂) := by
  classical
  -- the parent map: re-index the image component through the enumerations
  let p : ℕ → ℕ := fun c => if hc : c < (meetingPieces T₁ U₁ hU₁).card then
    (meetingIndex T₂ U₂ hU₂ (hφmeet _ (meetingPiece_mem T₁ U₁ hU₁ ⟨c, hc⟩))).1 else 0
  have hp : ∀ c (hc : c < (meetingPieces T₁ U₁ hU₁).card),
      p c = (meetingIndex T₂ U₂ hU₂ (hφmeet _ (meetingPiece_mem T₁ U₁ hU₁ ⟨c, hc⟩))).1 :=
    fun c hc => dite_eq_left hc
  have hplt : ∀ c, c < (meetingPieces T₁ U₁ hU₁).card → p c < (meetingPieces T₂ U₂ hU₂).card :=
    fun c hc => by
      rw [hp c hc]
      exact Fin.is_lt _
  have hpφ : ∀ c (hc : c < (meetingPieces T₁ U₁ hU₁).card),
      meetingPiece T₂ U₂ hU₂ ⟨p c, hplt c hc⟩ = φ (meetingPiece T₁ U₁ hU₁ ⟨c, hc⟩) := by
    intro c hc
    have e : (⟨p c, hplt c hc⟩ : Fin (meetingPieces T₂ U₂ hU₂).card) =
        meetingIndex T₂ U₂ hU₂ (hφmeet _ (meetingPiece_mem T₁ U₁ hU₁ ⟨c, hc⟩)) :=
      Fin.ext (hp c hc)
    rw [e, meetingPiece_meetingIndex]
  have hpc : ∀ c (hc : c < (meetingPieces T₁ U₁ hU₁).card) c'
      (hc' : c' < (meetingPieces T₂ U₂ hU₂).card),
      p c = c' ↔ φ (meetingPiece T₁ U₁ hU₁ ⟨c, hc⟩) = meetingPiece T₂ U₂ hU₂ ⟨c', hc'⟩ := by
    intro c hc c' hc'
    constructor
    · intro hpc
      rw [← hpφ c hc]
      congr 1
      exact Fin.ext hpc
    · intro hφc
      have := meetingPiece_injective T₂ U₂ hU₂ ((hpφ c hc).trans hφc)
      exact congrArg Fin.val this
  -- the label map: the sorted meeting members of `T₁` embed into those of `T₂`
  have hrange : Set.range ((inputEmb T₁ U₁ hU₁).trans eMem) ⊆ Set.range (inputEmb T₂ U₂ hU₂) := by
    rintro _ ⟨ℓ, rfl⟩
    rw [range_inputEmb]
    have hm : inputEmb T₁ U₁ hU₁ ℓ ∈ meetingMembers T₁ U₁ hU₁ := by
      rw [← Finset.mem_coe, ← range_inputEmb]
      exact ⟨ℓ, rfl⟩
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hm
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨φ i, hφmeet i hi, ?_⟩)
    rw [hφfst, hij]
    rfl
  obtain ⟨σ, hσlt, hσmono, hσ⟩ :=
    exists_labelMap_factor ((inputEmb T₁ U₁ hU₁).trans eMem) (inputEmb T₂ U₂ hU₂) hrange
  refine ⟨p, σ, ?_⟩
  refine
    { p_lt := hplt
      σ_lt := hσlt
      σ_strictMonoOn := hσmono
      label_eq := fun c hc => ?_
      a_eq := fun c hc => ?_
      piece_subset := fun c hc => ?_
      preimage_eq := fun c' hc' => ?_
      disjoint := fun c c'' hc hc'' hne hpp => ?_ }
  · -- labels: both sides are the position of the same member among the sorted members of `T₂`
    have h₂ := inputEmb_label T₂ U₂ hU₂ ⟨p c, hplt c hc⟩
    have h₁ := inputEmb_label T₁ U₁ hU₁ ⟨c, hc⟩
    have hσc := hσ ((inputFamily T₁ U₁ hU₁).label c) ((inputFamily T₁ U₁ hU₁).label_lt c hc)
    have key : inputEmb T₂ U₂ hU₂ ⟨(inputFamily T₂ U₂ hU₂).label ↑(⟨p c, hplt c hc⟩ : Fin _),
        (inputFamily T₂ U₂ hU₂).label_lt _ (hplt c hc)⟩ =
        inputEmb T₂ U₂ hU₂ ⟨σ ((inputFamily T₁ U₁ hU₁).label c),
          hσlt _ ((inputFamily T₁ U₁ hU₁).label_lt c hc)⟩ := by
      rw [h₂, hσc, hpφ c hc, hφfst]
      exact congrArg eMem h₁.symm
    exact congrArg Fin.val ((inputEmb T₂ U₂ hU₂).injective key)
  · -- exponents
    rw [inputFamily_a_of_lt T₂ U₂ hU₂ (hplt c hc), inputFamily_a_of_lt T₁ U₁ hU₁ hc, hpφ c hc]
    exact hφa _ (meetingPiece_mem T₁ U₁ hU₁ ⟨c, hc⟩)
  · -- a trace maps into the trace of the image
    rw [inputFamily_piece_of_lt T₁ U₁ hU₁ hc, inputFamily_piece_of_lt T₂ U₂ hU₂ (hplt c hc),
      hpφ c hc]
    intro x hx
    exact hsub _ (meetingPiece_mem T₁ U₁ hU₁ ⟨c, hc⟩) x hx
  · -- the preimage of a trace is the union of the traces of the children
    rw [inputFamily_piece_of_lt T₂ U₂ hU₂ hc']
    ext x
    rw [Set.mem_iUnion₂]
    constructor
    · intro hx
      obtain ⟨i, hi, hφi, hxi⟩ := hcover _ (meetingPiece_mem T₂ U₂ hU₂ ⟨c', hc'⟩) x hx
      have hmi : meetingPiece T₁ U₁ hU₁ ⟨(meetingIndex T₁ U₁ hU₁ hi).1, Fin.is_lt _⟩ = i :=
        meetingPiece_meetingIndex T₁ U₁ hU₁ hi
      refine ⟨(meetingIndex T₁ U₁ hU₁ hi).1,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Fin.is_lt _), ?_⟩, ?_⟩
      · exact (hpc _ (Fin.is_lt _) c' hc').mpr (by rw [hmi, hφi])
      · rw [inputFamily_piece_of_lt T₁ U₁ hU₁ (Fin.is_lt _), hmi]
        exact hxi
    · rintro ⟨c, hcf, hx⟩
      obtain ⟨hcr, hpc'⟩ := Finset.mem_filter.mp hcf
      have hc : c < (meetingPieces T₁ U₁ hU₁).card := Finset.mem_range.mp hcr
      rw [inputFamily_piece_of_lt T₁ U₁ hU₁ hc] at hx
      have hφc := (hpc c hc c' hc').mp hpc'
      have := hsub _ (meetingPiece_mem T₁ U₁ hU₁ ⟨c, hc⟩) x hx
      rw [hφc] at this
      exact this
  · -- two children of one parent are disjoint
    rw [inputFamily_piece_of_lt T₁ U₁ hU₁ hc, inputFamily_piece_of_lt T₁ U₁ hU₁ hc'']
    have hne' : meetingPiece T₁ U₁ hU₁ ⟨c, hc⟩ ≠ meetingPiece T₁ U₁ hU₁ ⟨c'', hc''⟩ := fun h =>
      hne (congrArg Fin.val (meetingPiece_injective T₁ U₁ hU₁ h))
    have hφeq : φ (meetingPiece T₁ U₁ hU₁ ⟨c, hc⟩) = φ (meetingPiece T₁ U₁ hU₁ ⟨c'', hc''⟩) := by
      rw [← hpφ c hc, ← hpφ c'' hc'']
      congr 1
      exact Fin.ext hpp
    exact Set.disjoint_left.mpr fun x hx hx' =>
      hdisj _ (meetingPiece_mem T₁ U₁ hU₁ ⟨c, hc⟩) _ (meetingPiece_mem T₁ U₁ hU₁ ⟨c'', hc''⟩) hne'
        hφeq x hx hx'

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- For `U ≤ V` the input family of `U` refines the input family of `V` along the open inclusion:
one child per parent, its trace. -/
theorem refinesAlong_inputFamily_restrictLE (T : AnalyticTriple ψ₀ M) {U V : Opens M}
    (hU : IsCompact (closure (U : Set M))) (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    ∃ p σ : ℕ → ℕ,
      (inputFamily T U hU).RefinesAlong (M.restrictLE hUV) p σ (inputFamily T V hV) := by
  refine refinesAlong_inputFamily_of_componentMap T U hU T V hV (M.restrictLE hUV) id
    (OrderIso.refl T.F.ι).toOrderEmbedding (fun _ => rfl) ?_ (fun _ _ => rfl) ?_ ?_ ?_
  · intro i hi
    exact (mem_meetingPieces_iff T V hV).mpr (((mem_meetingPieces_iff T U hU).mp hi).mono
      (Set.inter_subset_inter_right _ (closure_mono fun x hx => hUV hx)))
  · intro i _ x hx
    exact hx
  · intro i₂ _ x hx
    exact ⟨i₂, mem_meetingPieces_of_mem T U hU hx (inclusion_mem U x), rfl, hx⟩
  · intro i _ i' _ hne heq
    exact absurd heq hne

/-- For `T'` the pull-back of `T` along a local analytic isomorphism `g` and `U' ⊆ N` relatively
compact, the input family of `(T', U')` refines the input family of `(T, g(U'))` along `g|_{U'}`:
the connected components of `g⁻¹(Eʲ)` over one component of `Eʲ` are the children of that component.
-/
theorem refinesAlong_inputFamily_restrictMap (T : AnalyticTriple ψ₀ M) (T' : AnalyticTriple ψ₀ N)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hT'T : T'.IsPullbackOf T g)
    (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))) :
    ∃ p σ : ℕ → ℕ, (inputFamily T' U' hU').RefinesAlong
      (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl) p σ
      (inputFamily T (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU')) := by
  obtain ⟨I', hI', F', hF'⟩ := T'
  have hI : I' = T.I.pullback g g.contMDiff := hT'T.1
  have hF : F' = T.F.comap g := hT'T.2
  subst hI hF
  have hgc : Continuous g := hg.contMDiff.continuous
  refine refinesAlong_inputFamily_of_componentMap ⟨T.I.pullback g g.contMDiff, hI', T.F.comap g,
      hF'⟩ U' hU' T
    (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU') _
    (parentIndex T.F hgc) (OrderIso.refl T.F.ι).toOrderEmbedding (fun _ => rfl) ?_ ?_ ?_ ?_ ?_
  · -- a component meeting `closure U'` has its parent meeting `closure (g U')`
    intro i hi
    obtain ⟨b, hb, hbU⟩ := (mem_meetingPieces_iff _ _ _).mp hi
    exact (mem_meetingPieces_iff _ _ _).mpr ⟨g b, mem_componentSet_parentIndex T.F hgc hb,
      image_closure_subset_closure_image hgc ⟨b, hbU, rfl⟩⟩
  · -- the exponent transports along `g`
    intro i hi
    obtain ⟨b, hb, -⟩ := (mem_meetingPieces_iff _ _ _).mp hi
    exact (componentExponent_comap g hg T.F T.isSnc T.I (parentIndex T.F hgc i) i hb
      (mem_componentSet_parentIndex T.F hgc hb) rfl).symm
  · intro i _ x hx
    exact mem_componentSet_parentIndex T.F hgc hx
  · intro i₂ _ x hx
    obtain ⟨i', hxi', hpar⟩ := exists_parentIndex_eq T.F hgc hx
    exact ⟨i', mem_meetingPieces_of_mem _ U' hU' hxi' (inclusion_mem U' x), hpar, hxi'⟩
  · -- two children of one parent are distinct components of one member, hence disjoint
    intro i hi i' hi' hne heq x hx hx'
    obtain ⟨j, C⟩ := i
    obtain ⟨j', C'⟩ := i'
    have hj : j = j' := congrArg Sigma.fst heq
    subst hj
    have hC : C ≠ C' := fun h => hne (by rw [h])
    exact Set.disjoint_left.mp (componentSet_disjoint_of_ne (T.F.comap g) hC) hx hx'

/-- The input families of `T` and of `T` with its empty boundary members deleted refine one another
along the identity: a bijection of the pieces, the labels through the order embedding `e`. -/
theorem refinesAlong_inputFamily_indiff (T : AnalyticTriple ψ₀ M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀)
    (e : F'.ι ↪o T.F.ι) (h1 : ∀ i, T.F.hyp (e i) = F'.hyp i)
    (h2 : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅) :
    ∃ p σ : ℕ → ℕ,
      (inputFamily (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M) U
        hU).RefinesAlong (ContMDiffMap.id : AnalyticMap (M.restrict U) (M.restrict U)) p σ
        (inputFamily T U hU) := by
  have he : HypersurfaceFamily.IsEmptyExtension e := ⟨h1, h2⟩
  refine refinesAlong_inputFamily_of_componentMap ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ U hU T U
    hU ContMDiffMap.id (BMOmod.emptyExtIdx he) e (fun _ => rfl) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    refine (mem_meetingPieces_iff _ _ _).mpr ?_
    rw [BMOmod.componentSet_emptyExtIdx]
    exact (mem_meetingPieces_iff _ _ _).mp hi
  · intro i _
    exact BMOmod.componentExponent_emptyExtIdx he hsnc' T.isSnc T.I i
  · intro i _ x hx
    rw [BMOmod.componentSet_emptyExtIdx]
    exact hx
  · intro i₂ _ x hx
    obtain ⟨i, rfl⟩ := BMOmod.emptyExtIdx_surjective he i₂
    rw [BMOmod.componentSet_emptyExtIdx] at hx
    exact ⟨i, mem_meetingPieces_of_mem _ U hU hx (inclusion_mem U x), rfl, hx⟩
  · intro i _ i' _ hne heq
    exact absurd (BMOmod.emptyExtIdx_injective he heq) hne

end PieceFamily

/-! ### The three properties of the value -/

section Clauses

variable {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- Compatibility under restriction: the value on `U` is the value on `V ⊇ U` pulled back to `U`
with its empty blow-ups erased ([Wlo09, Theorem 2.0.3 (4)]). -/
theorem monomialStep3SeqOn_compat (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (m : ℕ) (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (V : Opens M) (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    monomialStep3SeqOn T m hT U hU =
      ((monomialStep3SeqOn T m hT V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  obtain ⟨p, σ, h⟩ := PieceFamily.refinesAlong_inputFamily_restrictLE T hU hV hUV
  exact h.realize_pullback_eraseEmpty _ (inputFamily_realizes T V hV)
    (inputFamily_isValid T V hV hT) _ (inputFamily_realizes T U hU) (inputFamily_isValid T U hU hT)
    (isLocalDiffeomorph_restrictLE hUV)

/-- Commutation with local analytic isomorphisms ([Kol07, 34.1]): for `T'` the pull-back of `T`
along a local analytic isomorphism `g` and a relatively compact open `U'`, the value on `U'` is the
value on `g(U')` pulled back along `g|_{U'}` with its empty blow-ups erased. -/
theorem monomialStep3SeqOn_pullback
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
    (hT : AnalyticTriple.BMOClass m T)
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g) (hT'T : T'.IsPullbackOf T g)
    (hT' : AnalyticTriple.BMOClass m T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))) :
    monomialStep3SeqOn T' m hT' U' hU' =
      ((monomialStep3SeqOn T m hT (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU')).pullback
          (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
            Set.Subset.rfl)).eraseEmpty := by
  obtain ⟨p, σ, h⟩ := PieceFamily.refinesAlong_inputFamily_restrictMap T T' g hg hT'T U' hU'
  exact h.realize_pullback_eraseEmpty _ (inputFamily_realizes T _ _) (inputFamily_isValid T _ _ hT)
    _ (inputFamily_realizes T' U' hU') (inputFamily_isValid T' U' hU' hT')
    (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
      Set.Subset.rfl)

/-- Indifference to empty boundary members: deleting the empty members of the boundary does not
change the value. -/
theorem monomialStep3SeqOn_indiff (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (m : ℕ) (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (e : F'.ι ↪o T.F.ι) (h1 : ∀ i, T.F.hyp (e i) = F'.hyp i)
    (h2 : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hT' : AnalyticTriple.BMOClass m (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ :
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)) :
    monomialStep3SeqOn T m hT U hU =
      monomialStep3SeqOn ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ m hT' U hU := by
  obtain ⟨p, σ, h⟩ := PieceFamily.refinesAlong_inputFamily_indiff T U hU F' hsnc' e h1 h2
  have key : monomialStep3SeqOn ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ m hT' U hU =
      (monomialStep3SeqOn T m hT U hU).pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id _) :=
    h.realize_pullback_of_surjective _ (inputFamily_realizes T U hU)
      (inputFamily_isValid T U hU hT) _ (inputFamily_realizes _ U hU)
      (inputFamily_isValid _ U hU hT') (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id _)
          (fun x => ⟨x, rfl⟩)
  rw [AnalyticManifold.BlowUpSequence.pullback_id] at key
  exact key.symm

end Clauses

end Hironaka.Manifold.BMO
