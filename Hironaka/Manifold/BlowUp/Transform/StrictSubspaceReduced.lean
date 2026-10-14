/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.RadicalSubspace
public import Hironaka.Manifold.BlowUp.Transform.Defs
public import Mathlib.Analysis.Complex.Basic
import Hironaka.AnalyticSpace.CoherentColon
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.StrictSubspace
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceBasic
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceClosure
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Over `ℂ`, reduction commutes with the strict transform

Bierstone–Milman remark that "it is easy to see that `(X')_red = (X_red)'`" [BM97, Remark 3.14];
this file proves it over `ℂ`. Write `K = π^*I` for the total transform, `F = I_F` for the
exceptional ideal (locally principal) and `sat J = ⋃_k (J : F^k)` for the saturation
(`saturationStalk`).

* The elementary half (any field): `sat(π^*√I) ⊆ √(sat π^*I)`, since `π^*√I ⊆ √(π^*I)`
  (`Ideal.map_radical_le`), and `g y^k ∈ √K` gives `g^n ∈ (K : y^{kn}) ⊆ sat K`
  (`iSup_colon_pow_le_radical_of_le_radical`, with the principal generator `y` of `F_{a'}`,
  `IsBlowUp.exists_span_singleton_stalkIdeal_exceptional`).
* The content (Rückert, `ℂ`): **`sat K` is radical whenever `K` is radical off `F`**
  (`mem_iSup_colon_pow_of_pow_mem`). Let `g^n ∈ sat K` at `a'`, so `g^n ∈ (K : F^j)_{a'}`; by
  coherence of the colon sheaf `(K : F^j)` (`hasLocalGenerators_colon_idealSheaf`) a
  representative `s` of `g` on an open `W ∋ a'` has `s^n ∈ (K : F^j)(W)`, so off `F` (where
  `F^j = 𝒪`) `s^n ∈ K` and, `K` being radical there, `s ∈ K`. On the open manifold `W` as an
  analytic space, the colon `C = (K|_W : ⟨s⟩)` of the pulled-back `K` by the principal ideal sheaf
  of `s` is coherent with `|C| ⊆ |F| ∩ W`; Rückert's Nullstellensatz puts every germ of `F` at
  `a'` into `√C_{a'}`, hence `F_{a'}^m ⊆ C_{a'}` for some `m` (the stalk is Noetherian), i.e.
  `F^m · g ⊆ K` at `a'`, so `g ∈ (K : F^m) ⊆ sat K`. The stalk isomorphism of the inclusion
  `W ⊆ M'` (`germMap_val_bijective`) transports between `M'` and `W`.
* Consequences: `isRadical_saturationStalk_of_isReduced` (`X` reduced implies `X'` reduced, the
  form used for the geometric strict transform), `saturationStalk_radical` (the stalkwise identity
  `√(sat π^*I) = sat(π^*√I)` with the finite type of `√I` as an explicit witness), and the form on
  `IdealSheaf.radicalSubspace`, `strictTransformSubspace_radicalSubspace_of_hasLocalGenerators`,
  given the four finite-type witnesses (Cartan's theorem for `I` and for `X'`, the finite type of
  the two saturations).

The coherence of colons is `Hironaka.AnalyticSpace.CoherentColon`; Rückert's Nullstellensatz for
stalks, `Hironaka.AnalyticSpace.Nullstellensatz`.
-/

public section

open TopologicalSpace Opposite CategoryTheory Set Filter Topology CompleteLattice
open scoped Manifold ContDiff

universe u

namespace Manifold

/-! ### Elementary algebra of saturations -/

section Algebra

variable {R : Type*} [CommRing R]

/-- `g y^k ∈ √K` gives `g ∈ √(sat_y K)`: the saturation of `K'` by `y` lies in the radical of the
saturation of `K` whenever `K' ⊆ √K`. -/
theorem iSup_colon_pow_le_radical_of_le_radical (K K' : Ideal R) (y : R)
    (hK' : K' ≤ K.radical) :
    (⨆ k : ℕ, Submodule.colon K' (SetLike.coe (Ideal.span {y} ^ k))) ≤
      (⨆ k : ℕ, Submodule.colon K (SetLike.coe (Ideal.span {y} ^ k))).radical := by
  refine iSup_le fun k g hg => ?_
  have h1 : g * y ^ k ∈ K' := by
    have := Submodule.mem_colon.mp hg (y ^ k)
      (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    rwa [smul_eq_mul] at this
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp (hK' h1)
  refine Ideal.mem_radical_iff.mpr ⟨m, Submodule.mem_iSup_of_mem (k * m) ?_⟩
  refine Submodule.mem_colon.mpr fun p hp => ?_
  rw [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hp
  obtain ⟨d, rfl⟩ := hp
  rw [smul_eq_mul, pow_mul, show g ^ m * (d * (y ^ k) ^ m) = d * (g * y ^ k) ^ m by ring]
  exact Ideal.mul_mem_left _ _ hm

/-- The saturation is monotone in the ideal. -/
theorem iSup_colon_pow_mono {K K' : Ideal R} (h : K ≤ K') (F : Ideal R) :
    (⨆ k : ℕ, Submodule.colon K (SetLike.coe (F ^ k))) ≤
      ⨆ k : ℕ, Submodule.colon K' (SetLike.coe (F ^ k)) :=
  iSup_mono fun _ => Submodule.colon_mono h le_rfl

end Algebra

section Principal

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- Every point: the stalk of the exceptional ideal sheaf is principal (a
coordinate germ of a blow-up chart on the divisor, the unit ideal off it). -/
theorem IsBlowUp.exists_span_singleton_stalkIdeal_exceptional (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (a' : M') :
    ∃ y, (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' = Ideal.span {y} := by
  by_cases ha' : π a' ∈ Y
  · obtain ⟨φ, σ, ha, hφ⟩ := hY.exists_adaptedChart (π a') ha'
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ a' ha
    exact ⟨_, h.stalkIdeal_pullback_eq_span_coord hY.isIdealSheafOf_idealSheaf hφ hΦ hpΦ⟩
  · refine ⟨1, ?_⟩
    rw [Ideal.span_singleton_one]
    have hF : a' ∉ (hY.idealSheaf.pullback π h.contMDiff).support := by
      rw [IsBlowUp.cosupport_exceptionalIdealSheaf hY h]
      exact ha'
    exact not_not.mp (mt (IdealSheaf.mem_support _).mpr hF)

end Principal

/-! ### The Rückert core over `ℂ` -/

section Core

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (ψ : E ≃L[ℂ] (Fin n → ℂ))
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℂ, E) ω M'] [T2Space M']
  [SecondCountableTopology M']

include ψ

/-- The stalkwise colon of two ideal sheaves on a complex manifold has local generators (at the
analytic space `Sp(M')`). -/
theorem hasLocalGenerators_colon_stalkIdeal (K F' : IdealSheaf (structureSheaf ℂ E M')) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf ℂ E M')
      fun x => Submodule.colon (K.stalkIdeal x) (SetLike.coe (F'.stalkIdeal x)) :=
  AnalyticSpace.hasLocalGenerators_colon_idealSheaf
    (AnalyticSpace.toSpace ψ
        ({ carrier := M' } : AnalyticManifold.{u} ℂ E)) K F'

omit ψ [IsManifold 𝓘(ℂ, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- A germ in a stalk of an ideal sheaf is the germ of a section of the ideal sheaf on a
neighbourhood: for `g^n ∈ K'_{a'}` and `s` a representative of `g`, `s^n` is a section of `K'` near
`a'`. -/
theorem exists_opens_pow_mem_carrier (K' : IdealSheaf (structureSheaf ℂ E M')) {a' : M'}
    {U : Opens M'} (ha'U : a' ∈ U) (s : (structureSheaf ℂ E M').presheaf.obj (op U)) {m : ℕ}
    (hs : (structureSheaf ℂ E M').presheaf.germ U a' ha'U s ^ m ∈ K'.stalkIdeal a') :
    ∃ (W : Opens M') (_ : a' ∈ W) (iU : W ⟶ U),
      (structureSheaf ℂ E M').presheaf.map iU.op s ^ m ∈ K'.carrier W := by
  obtain ⟨V, ha'V, k, hk, hkg⟩ := (IdealSheaf.mem_stalkIdeal_iff K').mp hs
  rw [← map_pow] at hkg
  obtain ⟨W, ha'W, iV, iU, hW⟩ :=
    TopCat.Presheaf.germ_eq (structureSheaf ℂ E M').presheaf a' ha'V ha'U k (s ^ m) hkg
  refine ⟨W, ha'W, iU, ?_⟩
  rw [← map_pow, ← hW]
  exact K'.res_mem iV k hk

omit ψ in
/-- The principal ideal sheaf generated by a section `t` over an open set `V` containing every
point: the stalk family `(t_x)` has local generators (`t` itself). -/
theorem hasLocalGenerators_span_germ {N : Type u} [TopologicalSpace N] [ChartedSpace E N]
    (V : Opens N) (hV : ∀ x, x ∈ V) (t : (structureSheaf ℂ E N).presheaf.obj (op V)) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf ℂ E N)
      fun x => Ideal.span {(structureSheaf ℂ E N).presheaf.germ V x (hV x) t} :=
  fun a => ⟨V, hV a, Unit, inferInstance, fun _ => t, fun b _ => by rw [Set.range_const]⟩

/-- **The Rückert core over `ℂ`**: if `K` is radical off `|F|`, its saturation by `F` is radical —
a germ whose `m`-th power lies in `⋃_k (K : F^k)` lies there itself. -/
theorem mem_iSup_colon_pow_of_pow_mem (K F : IdealSheaf (structureSheaf ℂ E M'))
    (hrad : ∀ x, x ∉ F.support → (K.stalkIdeal x).IsRadical) {a' : M'}
    {g : (structureSheaf ℂ E M').presheaf.stalk a'} {m : ℕ}
    (hg : g ^ m ∈ ⨆ k : ℕ, Submodule.colon (K.stalkIdeal a') (SetLike.coe (F.stalkIdeal a' ^ k))) :
    g ∈ ⨆ k : ℕ, Submodule.colon (K.stalkIdeal a') (SetLike.coe (F.stalkIdeal a' ^ k)) := by
  have : FiniteDimensional ℂ E := ψ.symm.toLinearEquiv.finiteDimensional
  -- `g^m ∈ (K : F^j)` for one `j`
  have hmono : Monotone fun k : ℕ =>
      Submodule.colon (K.stalkIdeal a') (SetLike.coe (F.stalkIdeal a' ^ k)) := fun j j' hjj' =>
    Submodule.colon_mono le_rfl (Ideal.pow_le_pow_right hjj')
  obtain ⟨j, hj⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hg
  -- the colon sheaf `(K : F^j)`; a representative `s` of `g` has `s^m` a section of it near `a'`
  obtain ⟨C, hC⟩ : ∃ C : IdealSheaf (structureSheaf ℂ E M'),
      C = IdealSheaf.ofStalks _ _ (hasLocalGenerators_colon_stalkIdeal ψ K (F ^ j)) := ⟨_, rfl⟩
  have hCst : ∀ x, C.stalkIdeal x =
      Submodule.colon (K.stalkIdeal x) (SetLike.coe (F.stalkIdeal x ^ j)) := by
    intro x
    rw [hC, IdealSheaf.stalkIdeal_ofStalks, IdealSheaf.stalkIdeal_pow]
  obtain ⟨U₀, ha'U₀, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq (structureSheaf ℂ E M').presheaf g
  have hgm : (structureSheaf ℂ E M').presheaf.germ U₀ a' ha'U₀ s₀ ^ m ∈ C.stalkIdeal a' := by
    rw [hs₀, hCst]
    exact hj
  obtain ⟨W, ha'W, iU, hW⟩ := exists_opens_pow_mem_carrier C ha'U₀ s₀ hgm
  obtain ⟨s, hs⟩ : ∃ s : (structureSheaf ℂ E M').presheaf.obj (op W),
      s = (structureSheaf ℂ E M').presheaf.map iU.op s₀ := ⟨_, rfl⟩
  have hsg : (structureSheaf ℂ E M').presheaf.germ W a' ha'W s = g := by
    rw [hs, TopCat.Presheaf.germ_res_apply, hs₀]
  rw [← hs] at hW
  -- off `F`, `s` is a section of `K` (there `F^j = 𝒪`, so `s^m ∈ K`, and `K` is radical)
  have hsK : ∀ x (hx : x ∈ W), x ∉ F.support →
      (structureSheaf ℂ E M').presheaf.germ W x hx s ∈ K.stalkIdeal x := by
    intro x hx hxF
    have h1 : (structureSheaf ℂ E M').presheaf.germ W x hx s ^ m ∈ C.stalkIdeal x := by
      rw [← map_pow]
      exact C.germ_mem_stalkIdeal hx hW
    rw [hCst] at h1
    have htop : F.stalkIdeal x = ⊤ := not_not.mp (mt (IdealSheaf.mem_support _).mpr hxF)
    rw [htop, Ideal.top_pow] at h1
    have h2 := Submodule.mem_colon.mp h1 1 Submodule.mem_top
    rw [smul_eq_mul, mul_one] at h2
    exact hrad x hxF (Ideal.mem_radical_iff.mpr ⟨m, h2⟩)
  -- the open manifold `W`: pull `K`, `F` back along the inclusion, take the principal sheaf of `s`
  have hιc : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (Subtype.val : W → M') := contMDiff_subtype_val
  have hVW : ∀ x : W, x ∈ preimageOpens (Subtype.val : W → M') hιc W := fun x => x.2
  obtain ⟨KW, hKW⟩ : ∃ KW : IdealSheaf (structureSheaf ℂ E W),
      KW = K.pullback (Subtype.val : W → M') hιc := ⟨_, rfl⟩
  obtain ⟨FW, hFW⟩ : ∃ FW : IdealSheaf (structureSheaf ℂ E W),
      FW = F.pullback (Subtype.val : W → M') hιc := ⟨_, rfl⟩
  obtain ⟨sW, hsW⟩ : ∃ sW : (structureSheaf ℂ E W).presheaf.obj
      (op (preimageOpens (Subtype.val : W → M') hιc W)),
      sW = comapSection (Subtype.val : W → M') hιc s := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : IdealSheaf (structureSheaf ℂ E W), P = IdealSheaf.ofStalks _ _
      (hasLocalGenerators_span_germ (preimageOpens (Subtype.val : W → M') hιc W) hVW sW) :=
    ⟨_, rfl⟩
  obtain ⟨CW, hCW⟩ : ∃ CW : IdealSheaf (structureSheaf ℂ E W),
      CW = IdealSheaf.ofStalks _ _ (hasLocalGenerators_colon_stalkIdeal ψ KW P) := ⟨_, rfl⟩
  have hPst : ∀ x : W, P.stalkIdeal x = Ideal.span
      {(structureSheaf ℂ E W).presheaf.germ (preimageOpens (Subtype.val : W → M') hιc W) x
        (hVW x) sW} := fun x => by
    rw [hP, IdealSheaf.stalkIdeal_ofStalks]
  have hCWst : ∀ x : W, CW.stalkIdeal x =
      Submodule.colon (KW.stalkIdeal x) (SetLike.coe (P.stalkIdeal x)) := fun x => by
    rw [hCW, IdealSheaf.stalkIdeal_ofStalks]
  have hgerm : ∀ x : W, germMap (Subtype.val : W → M') hιc x
      ((structureSheaf ℂ E M').presheaf.germ W x.1 x.2 s) =
        (structureSheaf ℂ E W).presheaf.germ (preimageOpens (Subtype.val : W → M') hιc W) x
          (hVW x) sW := by
    intro x
    rw [hsW]
    exact germMap_germ (Subtype.val : W → M') hιc x.2 s
  -- the colon `(K|_W : ⟨s⟩)` is supported on the exceptional divisor
  have hsub : ∀ y ∈ (⊤ : Opens W), y ∈ CW.support → y ∈ FW.support := by
    intro y _ hyC
    by_contra hyF
    apply hyC
    have hyF' : y.1 ∉ F.support := by
      intro hmem
      apply hyF
      rw [hFW, IdealSheaf.support_pullback]
      exact hmem
    have hPle : P.stalkIdeal y ≤ KW.stalkIdeal y := by
      rw [hPst, Ideal.span_le, Set.singleton_subset_iff, hKW, IdealSheaf.stalkIdeal_pullback,
        ← hgerm y]
      exact Ideal.mem_map_of_mem _ (hsK y.1 y.2 hyF')
    rw [hCWst, Ideal.eq_top_iff_one]
    exact Submodule.mem_colon.mpr fun p hp => by rw [one_smul]; exact hPle hp
  -- Rückert on `W`: the exceptional ideal lies in the radical of the colon
  have hle : FW.stalkIdeal ⟨a', ha'W⟩ ≤ (CW.stalkIdeal ⟨a', ha'W⟩).radical := fun f hf =>
    mem_radical_stalkIdeal_of_cosupport_subset ψ CW FW (o := ⊤) trivial hsub hf
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hle (IsNoetherian.noetherian _)
  -- transport back: every `p ∈ F_{a'}^k` has `p * g ∈ K_{a'}`
  refine Submodule.mem_iSup_of_mem k (Submodule.mem_colon.mpr fun p hp => ?_)
  rw [smul_eq_mul]
  have hbij : Function.Bijective (germMap (Subtype.val : W → M') hιc ⟨a', ha'W⟩) :=
    germMap_val_bijective (𝕜 := ℂ) (E := E) W ⟨a', ha'W⟩
  have hp' : germMap (Subtype.val : W → M') hιc ⟨a', ha'W⟩ p ∈ FW.stalkIdeal ⟨a', ha'W⟩ ^ k := by
    rw [hFW, IdealSheaf.stalkIdeal_pullback, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hp
  have h3 := hk hp'
  rw [hCWst] at h3
  have h4 := Submodule.mem_colon.mp h3 _
    (by rw [hPst]; exact Ideal.mem_span_singleton_self _)
  rw [smul_eq_mul, ← hgerm ⟨a', ha'W⟩, ← map_mul, hKW, IdealSheaf.stalkIdeal_pullback] at h4
  have hsg' : (structureSheaf ℂ E M').presheaf.germ W (⟨a', ha'W⟩ : W).1 ha'W s = g := hsg
  rw [hsg'] at h4
  rw [mul_comm, ← Ideal.comap_map_of_bijective _ hbij (I := K.stalkIdeal a')]
  exact Ideal.mem_comap.mpr h4

end Core

/-! ### Reduction commutes with the strict transform, over `ℂ` -/

section Reduced

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {ψ : E ≃L[ℂ] (Fin n → ℂ)}
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M} {c : ℕ} {M' : Type u}
  [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℂ, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M}
  (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (I : IdealSheaf (structureSheaf ℂ E M))

/-- Over `ℂ` [BM97, Remark 3.14], **the strict transform of
a reduced subspace is reduced** — for `I` with radical stalks the saturation stalks are radical. -/
theorem isRadical_saturationStalk_of_isReduced (hI : ∀ x, (I.stalkIdeal x).IsRadical) (a' : M') :
    (saturationStalk hY h I a').IsRadical := by
  refine Ideal.radical_eq_iff.mp (le_antisymm (fun g hg => ?_) Ideal.le_radical)
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hg
  exact mem_iSup_colon_pow_of_pow_mem ψ (I.pullback π h.contMDiff)
    (hY.idealSheaf.pullback π h.contMDiff) (fun x hx =>
        isRadical_stalkIdeal_totalTransform_of_notMem
      h I hI (by rwa [IsBlowUp.cosupport_exceptionalIdealSheaf hY h] at hx)) hm

/-- Over `ℂ` ([BM97, Remark 3.14]), stalkwise with the finite type of
`√I` as an explicit witness: **`√(sat π^*I) = sat(π^*√I)`**. -/
theorem saturationStalk_radical
    (hI : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf ℂ E M)
      fun x => (I.stalkIdeal x).radical) (a' : M') :
    (saturationStalk hY h I a').radical =
      saturationStalk hY h (IdealSheaf.ofStalks (structureSheaf ℂ E M) _ hI) a' := by
  obtain ⟨y, hy⟩ := h.exists_span_singleton_stalkIdeal_exceptional hY a'
  have hJ : ∀ x, ((IdealSheaf.ofStalks (structureSheaf ℂ E M) _ hI).stalkIdeal x).IsRadical :=
    fun x => by
      rw [IdealSheaf.stalkIdeal_ofStalks]
      exact Ideal.radical_isRadical _
  have hrad := isRadical_saturationStalk_of_isReduced hY h _ hJ a'
  refine le_antisymm (hrad.radical_le_iff.mpr ?_) ?_
  · unfold saturationStalk
    refine iSup_colon_pow_mono ?_ _
    rw [IdealSheaf.stalkIdeal_pullback π h.contMDiff, IdealSheaf.stalkIdeal_pullback π h.contMDiff,
      IdealSheaf.stalkIdeal_ofStalks]
    exact Ideal.map_mono Ideal.le_radical
  · unfold saturationStalk
    rw [hy]
    refine iSup_colon_pow_le_radical_of_le_radical _ _ y ?_
    rw [IdealSheaf.stalkIdeal_pullback π h.contMDiff, IdealSheaf.stalkIdeal_pullback π h.contMDiff,
      IdealSheaf.stalkIdeal_ofStalks]
    exact Ideal.map_radical_le (f := germMap π h.contMDiff a')

/-- Over `ℂ`, on `strictTransformSubspace` (unconditional — in the
degenerate branch the stalks are `⊤`): the strict transform of a reduced subspace has radical
stalks. -/
theorem isRadical_stalkIdeal_strictTransformSubspace_of_isReduced
    (hI : ∀ x, (I.stalkIdeal x).IsRadical) (a' : M') :
    ((strictTransformSubspace hY h I).stalkIdeal a').IsRadical := by
  by_cases hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf ℂ E M') (saturationStalk hY h I)
  · rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex]
    exact isRadical_saturationStalk_of_isReduced hY h I hI a'
  · rw [strictTransformSubspace_of_not_hasLocalGenerators hY h I hex, IdealSheaf.stalkIdeal_top]
    exact Ideal.radical_eq_iff.mp (Ideal.radical_top _)

/-- Over `ℂ` ([BM97, Remark 3.14], "`(X')_red = (X_red)'`"), given the four
witnesses (Cartan's theorem for `I` and for `X'`, the Noether lemma for the two saturations): the
form on `IdealSheaf.radicalSubspace`. -/
theorem strictTransformSubspace_radicalSubspace_of_hasLocalGenerators
    (hI : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf ℂ E M)
      fun x => (I.stalkIdeal x).radical)
    (hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf ℂ E M') (saturationStalk hY h I))
    (hex' : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf ℂ E M')
      (saturationStalk hY h (IdealSheaf.radicalSubspace I)))
    (hR : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf ℂ E M')
      fun x => ((strictTransformSubspace hY h I).stalkIdeal x).radical) :
    strictTransformSubspace hY h (IdealSheaf.radicalSubspace I) =
      IdealSheaf.radicalSubspace (strictTransformSubspace hY h I) := by
  refine IdealSheaf.ext fun a' => ?_
  rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _ hex',
    IdealSheaf.stalkIdeal_radicalSubspace_of_hasLocalGenerators _ hR,
    stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex,
    saturationStalk_radical hY h I hI a', IdealSheaf.radicalSubspace, dite_eq_left hI]

end Reduced

end Manifold
