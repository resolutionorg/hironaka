/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.LogDeriv
public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Algebra.Local.Chart
public import Hironaka.Manifold.BlowUp.Transform.Basic
public import Hironaka.Manifold.Germ.StalkNoetherian
public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivChart
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.KollarChart
import Hironaka.Manifold.BlowUp.Transform.KollarPerm
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.BlowUp.Transform.StrictFlag
import Hironaka.Manifold.BlowUp.Transform.StrictIdeal
import Hironaka.Manifold.Germ.CoordDerivChart
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.GermMapChainRule
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Scheme.BlowUpSequence.TransformLogDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Tools for the logarithmic derivative rule and Theorem 88 under a blowing-up

Bridges between the analytic stalks and the chart-level layer of the version for schemes, and one
transport:

* `stalkIdeal_logDerivIter`: the stalk of `D^r(−log S)(J)` is the intrinsic iterate
  `Ideal.logDerivativeIter 𝕜 (I_{S,a}) r J_a`.
* `logDerivativeIter_map_ringEquiv`: the iterate of `Ideal.logDerivative_map_ringEquiv` (the
  logarithmic derivative is transported by a ring isomorphism respecting the `𝕜`-structures, the
  preserving derivations conjugated along the isomorphism), hence the locality of `D(−log S)` at a
  point where the germ map is bijective (`stalkIdeal_logDeriv_pullback_of_bijective`), in
  particular off the centre of a blowing-up where the strict transform's ideal is the pull-back of
  `I_S` (`stalkIdeal_idealSheaf_strictTransform_of_notMem`, from `I_{S'} = π_*^{-1}(I_S, 1)`).
* `exists_kollarChartData_of_mem_strictTransform`: at a point `a'` of the strict transform `S'`
  over the centre, Kollár's good chart (the flag chart of
  `Hironaka.Manifold.BlowUp.Transform.StrictFlag`, a blow-up chart whose index is not the index
  of `S`, Kollár's permutation of the coordinates, regular coordinates and the chart-ring map `χ`)
  packaged with `I_{S,π a'} = (x_{h₀})`, `I_{S',a'} = (χ y_{h₀})`, `h₀ < r`, the rule (75.1)
  `χ ∂'_j = ∂_{u_{τ j}} χ`, the preservation of `(χ y_{h₀})` by `∂_{u_{τ j}}`, `j ≠ h₀`, the
  spanning of the `𝕜`-derivations by the `∂_{u_{τ j}}`, and the transform formula
  `π_*^{-1}(I, m)_{a'} = χ(transformIdeal I_a m)`.

Sources: [Kol07, 87, (87.3)], [Kol07, 75], [Kol07, Lemma 74, (4)]; the good chart is the one in
the proof of [Kol07, Theorem 88]. These tools are used in
`Hironaka.Manifold.BlowUp.Transform.LogDerivBlowUp`.
-/

public section

noncomputable section

open TopologicalSpace Opposite Set Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

/-! ### The iterated logarithmic derivative under a ring isomorphism -/

namespace Ideal

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  (e : A ≃+* B) (hk : ∀ a : k, e (algebraMap k A a) = algebraMap k B a)

include hk in
/-- The iterated form of `Ideal.logDerivative_map_ringEquiv`
(`Hironaka.Scheme.BlowUpSequence.TransformLogDerivative`). -/
theorem logDerivativeIter_map_ringEquiv (J : Ideal A) (r : ℕ) (I : Ideal A) :
    (logDerivativeIter k J r I).map e.toRingHom =
      logDerivativeIter k (J.map e.toRingHom) r (I.map e.toRingHom) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [logDerivativeIter_succ, logDerivativeIter_succ, logDerivative_map_ringEquiv e hk, ih]

end Ideal

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {S : Set M}

/-! ### The intrinsic iterate on stalks -/

/-- The stalk of `D^r(−log S)(J)` is the intrinsic iterate `D^r(−log I_{S,a})(J_a)`. -/
theorem IdealSheaf.stalkIdeal_logDerivIter (hS : IsClosedSubmanifold ψ S 1) (r : ℕ)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) (a : M) :
    (IdealSheaf.logDerivIter E ψ hS r J).stalkIdeal a =
      Ideal.logDerivativeIter 𝕜 (hS.idealSheaf.stalkIdeal a) r (J.stalkIdeal a) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [IdealSheaf.logDerivIter_succ, IdealSheaf.stalkIdeal_logDeriv, ih,
      Ideal.logDerivativeIter_succ]

/-! ### Locality of `D(−log S)` at a point where the germ map is bijective -/

variable {N : Type u} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(𝕜, E) ω N]
  {S' : Set N} (φ : N → M) (hφ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ)

/-- Locality of `D(−log S)` ([Kol07, Lemma 74, (4)] for the logarithmic derivative):
at a point `b` where the germ map of `φ` is bijective and the ideal of `S'` is the pull-back of the
ideal of `S`, the stalk of `D(−log S')(φ^* J)` is the stalk of `φ^*(D(−log S)(J))`. -/
theorem stalkIdeal_logDeriv_pullback_of_bijective (hS : IsClosedSubmanifold ψ S 1)
    (hS' : IsClosedSubmanifold ψ S' 1) (J : IdealSheaf (structureSheaf 𝕜 E M)) {b : N}
    (hb : Function.Bijective (germMap φ hφ b))
    (hI : hS'.idealSheaf.stalkIdeal b =
      Ideal.map (germMap φ hφ b) (hS.idealSheaf.stalkIdeal (φ b))) :
    (IdealSheaf.logDeriv E ψ hS' (J.pullback φ hφ)).stalkIdeal b =
      ((IdealSheaf.logDeriv E ψ hS J).pullback φ hφ).stalkIdeal b := by
  let e : (structureSheaf 𝕜 E M).presheaf.stalk (φ b) ≃+* (structureSheaf 𝕜 E N).presheaf.stalk b :=
    RingEquiv.ofBijective (germMap φ hφ b) hb
  have hk : ∀ a : 𝕜, e (algebraMap 𝕜 ((structureSheaf 𝕜 E M).presheaf.stalk (φ b)) a) =
      algebraMap 𝕜 ((structureSheaf 𝕜 E N).presheaf.stalk b) a :=
    fun a => germMap_algebraMap φ hφ b a
  have h := Ideal.logDerivative_map_ringEquiv (k := 𝕜) e hk (hS.idealSheaf.stalkIdeal (φ b))
    (J.stalkIdeal (φ b))
  have he : e.toRingHom = germMap φ hφ b := RingHom.ext fun _ => rfl
  rw [he] at h
  calc (IdealSheaf.logDeriv E ψ hS' (J.pullback φ hφ)).stalkIdeal b
      = Ideal.logDerivative 𝕜 (hS'.idealSheaf.stalkIdeal b) ((J.pullback φ hφ).stalkIdeal b) :=
        IdealSheaf.stalkIdeal_logDeriv E ψ hS' _ b
    _ = Ideal.logDerivative 𝕜 (Ideal.map (germMap φ hφ b) (hS.idealSheaf.stalkIdeal (φ b)))
          (Ideal.map (germMap φ hφ b) (J.stalkIdeal (φ b))) :=
        congrArg₂ (Ideal.logDerivative 𝕜) hI (IdealSheaf.stalkIdeal_pullback φ hφ J b)
    _ = Ideal.map (germMap φ hφ b)
          (Ideal.logDerivative 𝕜 (hS.idealSheaf.stalkIdeal (φ b)) (J.stalkIdeal (φ b))) := h.symm
    _ = Ideal.map (germMap φ hφ b) ((IdealSheaf.logDeriv E ψ hS J).stalkIdeal (φ b)) :=
        congrArg _ (IdealSheaf.stalkIdeal_logDeriv E ψ hS J (φ b)).symm
    _ = ((IdealSheaf.logDeriv E ψ hS J).pullback φ hφ).stalkIdeal b :=
        (IdealSheaf.stalkIdeal_pullback φ hφ _ b).symm

/-- The iterated form of `stalkIdeal_logDeriv_pullback_of_bijective`. -/
theorem stalkIdeal_logDerivIter_pullback_of_bijective (hS : IsClosedSubmanifold ψ S 1)
    (hS' : IsClosedSubmanifold ψ S' 1) (J : IdealSheaf (structureSheaf 𝕜 E M)) {b : N}
    (hb : Function.Bijective (germMap φ hφ b))
    (hI : hS'.idealSheaf.stalkIdeal b =
      Ideal.map (germMap φ hφ b) (hS.idealSheaf.stalkIdeal (φ b))) (r : ℕ) :
    (IdealSheaf.logDerivIter E ψ hS' r (J.pullback φ hφ)).stalkIdeal b =
      ((IdealSheaf.logDerivIter E ψ hS r J).pullback φ hφ).stalkIdeal b := by
  let e : (structureSheaf 𝕜 E M).presheaf.stalk (φ b) ≃+* (structureSheaf 𝕜 E N).presheaf.stalk b :=
    RingEquiv.ofBijective (germMap φ hφ b) hb
  have hk : ∀ a : 𝕜, e (algebraMap 𝕜 ((structureSheaf 𝕜 E M).presheaf.stalk (φ b)) a) =
      algebraMap 𝕜 ((structureSheaf 𝕜 E N).presheaf.stalk b) a :=
    fun a => germMap_algebraMap φ hφ b a
  have h := Ideal.logDerivativeIter_map_ringEquiv (k := 𝕜) e hk (hS.idealSheaf.stalkIdeal (φ b)) r
    (J.stalkIdeal (φ b))
  have he : e.toRingHom = germMap φ hφ b := RingHom.ext fun _ => rfl
  rw [he] at h
  calc (IdealSheaf.logDerivIter E ψ hS' r (J.pullback φ hφ)).stalkIdeal b
      = Ideal.logDerivativeIter 𝕜 (hS'.idealSheaf.stalkIdeal b) r
        ((J.pullback φ hφ).stalkIdeal b) :=
        IdealSheaf.stalkIdeal_logDerivIter hS' r _ b
    _ = Ideal.logDerivativeIter 𝕜 (Ideal.map (germMap φ hφ b) (hS.idealSheaf.stalkIdeal (φ b))) r
          (Ideal.map (germMap φ hφ b) (J.stalkIdeal (φ b))) :=
        congrArg₂ (fun X Y => Ideal.logDerivativeIter 𝕜 X r Y) hI
          (IdealSheaf.stalkIdeal_pullback φ hφ J b)
    _ = Ideal.map (germMap φ hφ b)
          (Ideal.logDerivativeIter 𝕜 (hS.idealSheaf.stalkIdeal (φ b)) r (J.stalkIdeal
            (φ b))) := h.symm
    _ = Ideal.map (germMap φ hφ b) ((IdealSheaf.logDerivIter E ψ hS r J).stalkIdeal (φ b)) :=
        congrArg _ (IdealSheaf.stalkIdeal_logDerivIter hS r J (φ b)).symm
    _ = ((IdealSheaf.logDerivIter E ψ hS r J).pullback φ hφ).stalkIdeal b :=
        (IdealSheaf.stalkIdeal_pullback φ hφ _ b).symm

/-- The iterated form of `stalkIdeal_deriv_pullback_of_bijective` at one point
(`iteratedDeriv_pullback_of_isLocalDiffeomorph`, pointwise). -/
theorem stalkIdeal_iteratedDeriv_pullback_of_bijective [FiniteDimensional 𝕜 E]
    (J : IdealSheaf (structureSheaf 𝕜 E M)) {b : N} (hb : Function.Bijective (germMap φ hφ b))
    (r : ℕ) :
    ((J.pullback φ hφ).iteratedDeriv r).stalkIdeal b =
      ((J.iteratedDeriv r).pullback φ hφ).stalkIdeal b := by
  induction r with
  | zero => rw [IdealSheaf.iteratedDeriv_zero, IdealSheaf.iteratedDeriv_zero]
  | succ r ih =>
    rw [IdealSheaf.iteratedDeriv_succ, IdealSheaf.stalkIdeal_deriv, ih,
      ← IdealSheaf.stalkIdeal_deriv, stalkIdeal_deriv_pullback_of_bijective φ hφ _ hb,
      IdealSheaf.iteratedDeriv_succ]

/-! ### The strict transform of the hypersurface `S ⊇ Y` under a blowing-up -/

section BlowUp

variable [FiniteDimensional 𝕜 E] {Y : Set M} {c : ℕ} {M' : Type u} [TopologicalSpace M']
  [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M']
  {π : M' → M} (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
  (hS : IsClosedSubmanifold ψ S 1) (hYS : Y ⊆ S)
  (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) 1)

omit [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E] in
include hYS in
/-- Definedness of the mark `1` on `I_S` along a centre `Y ⊆ S`:
`ord_Y I_S ≥ 1` at every point of `Y`. -/
theorem IsClosedSubmanifold.one_le_ordAlongIdeal_idealSheaf :
    ∀ a ∈ Y, ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf hS.idealSheaf a :=
  fun a ha => by
    rw [IdealSheaf.le_ordAlongIdeal_iff, pow_one]
    exact hY.stalkIdeal_idealSheaf_le_of_subset hS hYS ha

omit [FiniteDimensional 𝕜 E] in
include hY hYS in
/-- Off the centre the ideal sheaf of the strict transform `S'` is the pull-back of `I_S`
(`I_{S'} = π_*^{-1}(I_S, 1)` and `birationalTransform_stalkIdeal_of_notMem`). -/
theorem stalkIdeal_idealSheaf_strictTransform_of_notMem {a' : M'} (ha' : π a' ∉ Y) :
    hS'.idealSheaf.stalkIdeal a' =
      Ideal.map (germMap π h.contMDiff a') (hS.idealSheaf.stalkIdeal (π a')) := by
  rw [hS'.idealSheaf_congr (isClosedSubmanifold_strictTransform hY h hS hYS) rfl,
    idealSheaf_strictTransform_eq_markedTransform_one hY h hS hYS,
    birationalTransform_stalkIdeal_of_notMem hY h (hY.one_le_ordAlongIdeal_idealSheaf hS hYS) ha',
    IdealSheaf.stalkIdeal_pullback]

include hYS in
/-- Kollár's good chart at a point `a'` of the strict transform `S'` over the centre
(the proof of [Kol07, Theorem 88]: coordinates with `S = (x₁ = 0)`, and the chart where the
strict transform of `S` is `(y₁ = 0)`): regular coordinates `κ` of the stalk at `π a'` reindexed
by Kollár's permutation (`exists_kollarPerm`) with pivot `r`, the index `h₀ < r` of the
hypersurface coordinate
(`I_{S,π a'} = (κ.x h₀)`), the chart-ring map `χ` with `I_{S',a'} = (χ y_{h₀})`, the
coordinate derivations `δ j = ∂_{u_{τ j}}` of the stalk at `a'` with the (75.1) rule
`χ ∂'_j = δ j ∘ χ`, preserving `(χ y_{h₀})` for `j ≠ h₀` and spanning the
`𝕜`-derivations, and the transform formula `π_*^{-1}(I, m)_{a'} = χ(π_*^{-1}(I_a, m))`
for every marked ideal sheaf of order `≥ m` along `Y`. -/
theorem exists_kollarChartData_of_mem_strictTransform {a' : M'}
    (haS' : a' ∈ strictTransformSet π Y S) (haY : π a' ∈ Y) :
    ∃ (κ : IsLocalRing.RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) n)
      (r h₀ : Fin n)
      (χ : IsLocalRing.chartRing κ.x r →+* (structureSheaf 𝕜 E M').presheaf.stalk a')
      (δ : Fin n → Derivation 𝕜 ((structureSheaf 𝕜 E M').presheaf.stalk a')
        ((structureSheaf 𝕜 E M').presheaf.stalk a')),
      κ.IsLinearOver 𝕜 ∧ κ.SpansDerivations 𝕜 ∧ h₀ < r ∧
      IsLocalRing.chartCenter κ.x r = hY.idealSheaf.stalkIdeal (π a') ∧
      hS.idealSheaf.stalkIdeal (π a') = Ideal.span {κ.x h₀} ∧
      hS'.idealSheaf.stalkIdeal a' = Ideal.span {χ (IsLocalRing.chartYR κ.x r h₀)} ∧
      (∀ (j : Fin n) (g : IsLocalRing.chartRing κ.x r),
        χ (κ.chartDerivRing r j g) = δ j (χ g)) ∧
      (∀ j, j ≠ h₀ → (δ j).PreservesIdeal (Ideal.span {χ (IsLocalRing.chartYR κ.x r h₀)})) ∧
      (∀ (D : Derivation 𝕜 ((structureSheaf 𝕜 E M').presheaf.stalk a')
          ((structureSheaf 𝕜 E M').presheaf.stalk a'))
        (f : (structureSheaf 𝕜 E M').presheaf.stalk a'),
        ∃ a : Fin n → (structureSheaf 𝕜 E M').presheaf.stalk a', D f = ∑ j, a j * δ j f) ∧
      ∀ (I : IdealSheaf (structureSheaf 𝕜 E M)) {m : ℕ},
        (∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) →
        (MarkedIdealSheaf.birationalTransform hY h ⟨I, m⟩).I.stalkIdeal a' =
          Ideal.map χ (IsLocalRing.transformIdeal κ.x r (I.stalkIdeal (π a')) m) := by
  obtain ⟨φ, σ, τ', haφ, hφ, hSφ⟩ := exists_adaptedChart_flag hY hS hYS haY
  obtain ⟨i, Φ, hΦ, ha'⟩ := h.cover φ σ hφ a' haφ
  have hi : i ∉ Set.range τ' := fun hi =>
    Set.eq_empty_iff_forall_notMem.mp (strictTransform_inter_source_of_mem_range hφ hΦ hSφ hi) a'
      ⟨haS', ha'⟩
  have hΦS' : IsAdaptedChart ψ (strictTransformSet π Y S) Φ (τ'.trans σ) :=
    isAdaptedChart_strictTransform_of_not_mem_range hφ hΦ hSφ hi
  have hSφ' : IsAdaptedChart ψ S φ (τ'.trans σ) := ⟨hφ.1, hSφ⟩
  obtain ⟨r, τ, hτr, hlt⟩ := exists_kollarPerm σ i
  obtain ⟨κ, hτ, hpd, hk, hs⟩ :=
    exists_regularCoords_reindex (ψ := ψ) φ hφ.1 (hΦ.source_subset ha') τ
  obtain ⟨χ, hχ, hχy, -⟩ := exists_chartRing_hom h hφ hΦ ha' haY κ.x r τ hτr hτ hlt
  obtain ⟨h₀, hτh₀⟩ : ∃ h₀, τ h₀ = σ (τ' 0) := ⟨τ.symm _, τ.apply_symm_apply _⟩
  have hh₀ : h₀ < r := (hlt h₀).mpr ⟨τ' 0, fun e => hi ⟨0, e⟩, hτh₀⟩
  refine ⟨κ, r, h₀, χ, fun j => coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' (τ j), hk, hs, hh₀,
    chartCenter_eq_stalkIdeal_idealSheaf hY hφ haY (hΦ.source_subset ha') κ.x r τ hτr hτ hlt, ?_,
    ?_, fun j g => chartRingHom_chartDerivRing_eq_coordDerivStalk h hφ hΦ ha' haY κ r τ hτr hτ hpd
      hlt χ hχ hχy j g, ?_, ?_,
    fun I m hm => birationalTransform_stalkIdeal_eq_map_transformIdeal hY h hφ hΦ ha' haY κ.x r τ
      hτr hτ hlt χ hχ I hm⟩
  · rw [hS.stalkIdeal_idealSheaf_eq_span (hYS haY) hSφ' (hΦ.source_subset ha'), Set.range_unique,
      x_eq_coord_of_eq_σ hφ hΦ ha' haY κ.x τ hτ hτh₀]
    rfl
  · rw [hS'.stalkIdeal_idealSheaf_eq_span haS' hΦS' ha', Set.range_unique, hχy h₀ hh₀, hτh₀]
    rfl
  · intro j hj
    rw [Derivation.preservesIdeal_span_singleton_iff, hχy h₀ hh₀, coordDerivStalk_coord,
      ite_eq_right fun e => hj (τ.injective e), map_zero]
    exact zero_mem _
  · intro D f
    refine ⟨fun j => D (centredCoord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)), ?_⟩
    rw [derivation_eq_sum_coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' D f]
    exact (Equiv.sum_comp τ fun i => D (centredCoord E ψ Φ hΦ.mem_maximalAtlas ha' i) *
      coordDerivStalk E ψ Φ hΦ.mem_maximalAtlas ha' i f).symm

end BlowUp

end Manifold

end
