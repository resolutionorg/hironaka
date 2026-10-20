/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Transform
public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
public import Hironaka.Scheme.IdealSheaf.Order.Along
import Hironaka.Algebra.Local.BlowUpLiftLog
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.Transform
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.TransformDerivative
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicLocalization
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicSheaf
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The logarithmic version of Theorem 76 for one smooth blow-up

Kollár's logarithmic version of Theorem 76, equation (87.3) of [Kol07, 87]: for a smooth blow-up
`π : B_Z X → X` with center `Z ⊆ S` and `ord_Z I ≥ m + 1`,
`π_*^{-1}(D(−log S)(I), m) ⊆ D(−log S₁)(π_*^{-1}(I, m + 1))`, `S₁` the strict transform of `S`
(`markedTransform_logDerivative_le`); and for `ord_Z I ≥ m`, `j ≤ m`,
`π_*^{-1}(D^j(−log S)(I), m − j) ⊆ D^j(−log S₁)(π_*^{-1}(I, m))`
(`markedTransform_logDerivativeIter_le`, by induction on `j` as for Theorem 76). Kollár says it
"is proved the same way using (75.4)"; the proof here is that of
`Hironaka/Scheme/BlowUpSequence/TransformDerivative.lean`, stalkwise on `B_Z X`, in the logarithmic
vocabulary of `Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicSheaf.lean`.

* **Off the center** (`stalkIdeal_markedTransform_logDerivative_le_of_notMem`): the marked
  transforms are the total transforms `π^* K_z` along the isomorphism `π^♯ : 𝒪_{X,z} ≅ 𝒪_{B,q}`
  (`stalkMapπEquiv`), the stalk of `S₁` is `π^*(S_z)` (the saturation by the unit exceptional
  stalk), and `D(−log ·)` is transported along a ring isomorphism respecting the `k`-structures
  (`Ideal.logDerivative_map_ringEquiv`: conjugation of a derivation preserves the transported
  ideal).
* **Over the center** (`stalkIdeal_markedTransform_logDerivative_le_of_mem`): the chart description
  `e : 𝒪_{B,q} ≅ R'_𝔮` of the stalk, with `R' = 𝒪_{X,z}[yᵢ/y_ρ]` the chart ring at `P = Z_z`; the
  stalk of `π_*^{-1}(K, c)` is the colon `(π^* K_z : (π^♯ y_ρ)^c)`
  (`stalkIdeal_markedTransform_of_chart`), so `t · (π^♯ y_ρ)^m ∈ D(−log S_z)(I_z) 𝒪_{B,q}`, which
  is `(π^♯ y_ρ)^m · π_*^{-1}(D(−log S_z)(I_z), m) 𝒪_{B,q}`, and `t` lies in the localization of
  the chart transform (`π^♯ y_ρ` a nonzerodivisor). The chart-level inclusion
  `transformIdeal_logDerivative_le` puts that transform inside
  `D(−log (S_z R')^{sat})(π_*^{-1}(I_z, m + 1))`, `Ideal.map_logDerivative_le` carries `D(−log ·)`
  through the localization `R' → 𝒪_{B,q}`, and the localized saturation
  `⋃ᵢ (S_z R' : y_ρⁱ) 𝒪_{B,q}` is the stalk `(S₁)_q = ⋃ᵢ (π^* S_z : (π^♯ y_ρ)ⁱ)`
  (`stalkIdeal_saturate_of_isInvertible`, and the colon by a finitely generated ideal commutes with
  localization, `map_colon_of_fg`). Finally `π_*^{-1}(I_z, m + 1) 𝒪_{B,q} ⊆ T_q` as for Theorem 76.

Conventions. The statements assume no smoothness of `S` or of `S₁`: the stalk formula
`stalkIdeal_logDerivative` holds for every closed subscheme, and the saturation is compared with
the stalk of the strict transform directly. Nor do they assume Kollár's hypothesis `Z ⊆ S`: the
chart lemma holds for every ideal
`J`, and the strict transform of `S` is defined for every `S`; the theorems here are stated for an
arbitrary closed subscheme `S`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
  Scheme.IdealSheafData Scheme.BlowUpSequence AlgebraicGeometry.Scheme.IdealSheafData

/-! ### Logarithmic derivative ideals and ring isomorphisms -/

namespace Ideal

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  (e : A ≃+* B) (hk : ∀ a : k, e (algebraMap k A a) = algebraMap k B a)

include hk in
/-- The logarithmic derivative ideal is transported by a ring isomorphism respecting the
`k`-structures: `D(−log J)(I) B = D(−log (J B))(I B)` — derivations are conjugated along `e`, and
conjugation preserves the transported ideal. -/
theorem logDerivative_map_ringEquiv (J I : Ideal A) :
    (logDerivative k J I).map e.toRingHom =
      logDerivative k (J.map e.toRingHom) (I.map e.toRingHom) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    refine logDerivative_le_iff.mpr ⟨fun f hf => Ideal.mem_comap.mpr
      (le_logDerivative _ _ (Ideal.mem_map_of_mem _ hf)), fun δ hδ f hf => ?_⟩
    rw [Ideal.mem_comap]
    have hcomm : ∀ a, Derivation.congrRingEquiv e hk δ (e.toRingHom a) = e.toRingHom (δ a) := by
      intro a
      change e (δ (e.symm (e a))) = e (δ a)
      rw [RingEquiv.symm_apply_apply]
    rw [← hcomm f]
    exact derivation_apply_mem_logDerivative (hδ.map_of_forall e.toRingHom _ hcomm)
      (Ideal.mem_map_of_mem _ hf)
  · refine logDerivative_le_iff.mpr ⟨Ideal.map_mono (le_logDerivative J I), fun δ' hδ' b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hb
    have hk' : ∀ c : k, e.symm (algebraMap k B c) = algebraMap k A c :=
      fun c => Derivation.symm_algebraMap_of_forall e hk c
    have hcomm : ∀ a, δ' (e.toRingHom a) =
        e.toRingHom (Derivation.congrRingEquiv e.symm hk' δ' a) := by
      intro a
      change δ' (e a) = e (e.symm (δ' (e.symm.symm a)))
      rw [RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
    have hpres : (Derivation.congrRingEquiv e.symm hk' δ').PreservesIdeal J := by
      intro x hx
      rw [Ideal.mem_iff_map_mem_map e J, ← hcomm x]
      exact hδ' _ (Ideal.mem_map_of_mem _ hx)
    rw [hcomm a]
    exact Ideal.mem_map_of_mem _ (derivation_apply_mem_logDerivative hpres ha)

end Ideal

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

section StalkCases

variable (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] (Z S I : X.IdealSheafData)

include n in
/-- Off the center: at `q` with `π q ∉ Z`, the marked transforms are the total transforms along
the isomorphism `π^♯`, the stalk of `S₁` is `π^*(S_z)`, and `D(−log ·)` is transported along the
isomorphism. -/
theorem stalkIdeal_markedTransform_logDerivative_le_of_notMem {m : ℕ} (q : Z.blowUp)
    (hq : Z.blowUpπ q ∉ Z.support) :
    ((S.logDerivative f I).markedTransform Z m).stalkIdeal q ≤
      letI := (Z.blowUpπ ≫ f).stalkAlgebra q
      Ideal.logDerivative k ((S.strictTransform Z).stalkIdeal q)
        ((I.markedTransform Z (m + 1)).stalkIdeal q) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hft : LocallyOfFiniteType f := inferInstance
  have hq' : q ∉ (Z.comap Z.blowUpπ).support := by
    rwa [support_comap]
  let _ := f.stalkAlgebra (Z.blowUpπ q)
  let _ := (Z.blowUpπ ≫ f).stalkAlgebra q
  have hS1 : (S.strictTransform Z).stalkIdeal q =
      (S.stalkIdeal (Z.blowUpπ q)).map (Z.blowUpπ.stalkMap q).hom := by
    have hK : Z.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π Z
    have hE : Z.exceptionalDivisor.stalkIdeal q = ⊤ := stalkIdeal_eq_top_of_notMem_support _ hq'
    unfold strictTransform strictTransformAlong
    rw [stalkIdeal_saturate_of_isInvertible _ hK, stalkIdeal_comap]
    simp only [hE, Ideal.top_pow, Ideal.colon_coe_top, iSup_const]
  rw [stalkIdeal_markedTransform_of_notMem Z _ m hq', stalkIdeal_markedTransform_of_notMem Z I
    (m + 1) hq', stalkIdeal_logDerivative f S I, hS1]
  have hk : ∀ a : k, stalkMapπEquiv Z hq' (algebraMap k _ a) = algebraMap k _ a :=
    fun a => stalkMap_algebraMap_stalkAlgebra f Z q a
  have hhom : (stalkMapπEquiv Z hq').toRingHom = (Z.blowUpπ.stalkMap q).hom :=
    RingHom.ext fun _ => rfl
  have h := Ideal.logDerivative_map_ringEquiv (stalkMapπEquiv Z hq') hk
    (S.stalkIdeal (Z.blowUpπ q)) (I.stalkIdeal (Z.blowUpπ q))
  rw [hhom] at h
  exact le_of_eq h

include n in
/-- Over the center, through the chart description of the stalk at `q`: the chart-level inclusion
`transformIdeal_logDerivative_le`, localized at the prime `𝔮` of the fibre and transported along
`e`, with the localized saturation identified with the stalk of the strict transform. -/
theorem stalkIdeal_markedTransform_logDerivative_le_of_mem [CharZero k]
    [Smooth (Z.subschemeι ≫ f)] {m : ℕ}
    (hm : I.LeOrdAlong Z.support ((m + 1 : ℕ) : ℕ∞)) (q : Z.blowUp)
    (hq : Z.blowUpπ q ∈ Z.support) :
    ((S.logDerivative f I).markedTransform Z m).stalkIdeal q ≤
      letI := (Z.blowUpπ ≫ f).stalkAlgebra q
      Ideal.logDerivative k ((S.strictTransform Z).stalkIdeal q)
        ((I.markedTransform Z (m + 1)).stalkIdeal q) := by
  classical
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hft : LocallyOfFiniteType f := inferInstance
  have hreg := isRegularLocalRing_stalk f (Z.blowUpπ q)
  obtain ⟨n', y, ρ, hn', hy, hZ', 𝔮, hprime, -, e, he⟩ :=
    exists_stalk_equiv_localization_chart_of_smooth f Z q hq
  let _ := f.stalkAlgebra (Z.blowUpπ q)
  let _ := (Z.blowUpπ ≫ f).stalkAlgebra q
  -- `I_z ⊆ P^{m+1}` and `D(−log S_z)(I_z) ⊆ P^m`
  have hIz : I.stalkIdeal (Z.blowUpπ q) ≤ chartCenter y ρ ^ (m + 1) := by
    have := stalkIdeal_le_pow_of_leOrdAlong f n Z I hm hq
      (stalkIdeal_ne_bot_of_mem_support_of_smooth f Z q hq)
    rwa [hZ'] at this
  have hD : Ideal.logDerivative k (S.stalkIdeal (Z.blowUpπ q)) (I.stalkIdeal
      (Z.blowUpπ q)) ≤
      chartCenter y ρ ^ m :=
    (Ideal.logDerivative_le_derivative _ _).trans (Ideal.derivative_le_pow hIz)
  -- `ψ' : R' → 𝒪_{B,q}`, the localization map read back through `e⁻¹`; `ψ' ∘ φ = π^♯`. Everything
  -- below is stated on the stalk `𝒪_{B,q}`, never on `Localization.AtPrime 𝔮` (as for Theorem 76).
  let algS : Algebra (chartRing y ρ) (Z.blowUp.presheaf.stalk q) :=
    (e.symm.toRingHom.comp (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮))).toAlgebra
  have hψφ : (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)).comp
      (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ)) =
      (Z.blowUpπ.stalkMap q).hom :=
    RingHom.ext fun c => (congrArg e.symm (he c)).symm.trans (e.symm_apply_apply _)
  have hψy : algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)
      (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)) =
      Z.blowUpπ.stalkMap q (y ρ) := RingHom.congr_fun hψφ (y ρ)
  have hloc : IsLocalization 𝔮.primeCompl (Z.blowUp.presheaf.stalk q) :=
    (IsLocalization.isLocalization_iff_of_ringEquiv (S := Localization.AtPrime 𝔮) 𝔮.primeCompl
      e.symm).mp inferInstance
  have htower : IsScalarTower k (chartRing y ρ) (Z.blowUp.presheaf.stalk q) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((stalkMap_algebraMap_stalkAlgebra f Z q a).symm.trans
        (RingHom.congr_fun hψφ (algebraMap k _ a)).symm).trans
        (congrArg (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q))
          (IsScalarTower.algebraMap_apply k (X.presheaf.stalk (Z.blowUpπ q))
            (chartRing y ρ) a).symm)
  -- the domain `𝒪_{B,q} ≅ R'_𝔮` and the nonzerodivisor `π^♯ y_ρ`
  have hdom : IsDomain (chartRing y ρ) := isDomain_chartRing y ρ hy hn'
  have hdom' : IsDomain (Localization.AtPrime 𝔮) :=
    IsLocalization.isDomain_localization 𝔮.primeCompl_le_nonZeroDivisors
  have hdomS : IsDomain (Z.blowUp.presheaf.stalk q) :=
    MulEquiv.isDomain (Localization.AtPrime 𝔮) e.toMulEquiv
  have hne : algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
      (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)) ≠ 0 := by
    intro h0
    have hinj' : Function.Injective (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)) :=
      IsLocalization.injective (M := 𝔮.primeCompl) (S := Localization.AtPrime 𝔮)
        𝔮.primeCompl_le_nonZeroDivisors
    have h1 := hinj' (h0.trans (map_zero _).symm)
    exact x_ne_zero_of_span_eq y hy hn' ρ
      (algebraMap_chartRing_injective y ρ hy hn' (h1.trans (map_zero _).symm))
  have ha : Z.blowUpπ.stalkMap q (y ρ) ≠ 0 := fun h0 =>
    hne ((he (y ρ)).symm.trans ((congrArg e h0).trans (map_zero e)))
  -- the stalk of `S₁`: the localized saturation `⋃ᵢ (S_z R' : y_ρⁱ) 𝒪_{B,q}`
  have hS1 : (S.strictTransform Z).stalkIdeal q =
      (⨆ i : ℕ, ((S.stalkIdeal (Z.blowUpπ q)).map
        (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ))).colon
          ((Ideal.span
            {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)} ^ i :
            Ideal (chartRing y ρ)) : Set (chartRing y ρ))).map
        (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) := by
    have hK : Z.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π Z
    have hF : Z.exceptionalDivisor.stalkIdeal q =
        Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} :=
      stalkIdeal_comap_eq_span_of_chart q y ρ hZ' 𝔮 e he
    have step1 : (S.strictTransform Z).stalkIdeal q =
        ⨆ i : ℕ, ((S.stalkIdeal (Z.blowUpπ q)).map
            (Z.blowUpπ.stalkMap q).hom).colon
          ((Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} ^ i :
            Ideal (Z.blowUp.presheaf.stalk q)) :
                Set (Z.blowUp.presheaf.stalk q)) := by
      unfold strictTransform strictTransformAlong
      rw [stalkIdeal_saturate_of_isInvertible _ hK, stalkIdeal_comap, hF]
    rw [step1, Ideal.map_iSup]
    refine iSup_congr fun i => ?_
    have hfg : (Ideal.span
      {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)} ^ i
        : Ideal (chartRing y ρ)).FG := by
      rw [Ideal.span_singleton_pow]
      exact Submodule.fg_span_singleton _
    rw [map_colon_of_fg 𝔮.primeCompl _ _ hfg]
    congr 1
    · exact ((Ideal.map_map _ _).trans
        (congrArg (fun g => Ideal.map g (S.stalkIdeal (Z.blowUpπ q))) hψφ)).symm
    · congr 1
      rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, hψy]
  -- the stalks of the two transforms and of `D(−log S)(I)`
  rw [stalkIdeal_markedTransform_of_chart Z _ m q y ρ hZ' 𝔮 e he,
    stalkIdeal_markedTransform_of_chart Z I (m + 1) q y ρ hZ' 𝔮 e he,
    stalkIdeal_logDerivative f S I]
  intro t ht
  -- `t · (π^♯ y_ρ)^m ∈ D(−log S_z)(I_z) 𝒪_{B,q}`
  -- `  = (π^♯ y_ρ)^m · π_*^{-1}(D(−log S_z)(I_z), m) 𝒪_{B,q}`
  have h1 : t * Z.blowUpπ.stalkMap q (y ρ) ^ m ∈
      (Ideal.logDerivative k (S.stalkIdeal (Z.blowUpπ q)) (I.stalkIdeal
          (Z.blowUpπ q))).map
        (Z.blowUpπ.stalkMap q).hom := by
    have := Submodule.mem_colon.mp ht (Z.blowUpπ.stalkMap q (y ρ) ^ m)
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m)
    rwa [smul_eq_mul] at this
  set L := Ideal.logDerivative k (S.stalkIdeal (Z.blowUpπ q)) (I.stalkIdeal
      (Z.blowUpπ q))
    with hL
  have hideal : L.map (Z.blowUpπ.stalkMap q).hom =
      Ideal.span {Z.blowUpπ.stalkMap q (y ρ) ^ m} *
        (transformIdeal y ρ L m).map
          (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
    calc L.map (Z.blowUpπ.stalkMap q).hom
        = L.map ((algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)).comp
              (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ))) :=
          (congrArg (fun g => Ideal.map g L) hψφ).symm
      _ = (L.map (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ))).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
          (Ideal.map_map _ _).symm
      _ = (Ideal.span
        {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)} ^ m *
            transformIdeal y ρ L m).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
          congrArg (Ideal.map _) (span_pow_mul_transformIdeal y ρ hD).symm
      _ = (Ideal.span
        {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ m} *
            transformIdeal y ρ L m).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) := by
          rw [Ideal.span_singleton_pow]
      _ = (Ideal.span
            {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ m}).map
            (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) *
            (transformIdeal y ρ L m).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
                  Ideal.map_mul _ _ _
      _ = Ideal.span (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q) ''
            {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ m}) *
            (transformIdeal y ρ L m).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
          congrArg (· * _) (Ideal.map_span _ _)
      _ = Ideal.span
        {algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)
              (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ m)} *
            (transformIdeal y ρ L m).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
          congrArg (fun S : Set (Z.blowUp.presheaf.stalk q) => Ideal.span S * _)
            (Set.image_singleton
                (f := algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)))
      _ = _ := congrArg (fun z : Z.blowUp.presheaf.stalk q => Ideal.span {z} * _)
            ((map_pow _ _ m).trans (congrArg (· ^ m) hψy))
  have hmem := (congrArg (fun J : Ideal (Z.blowUp.presheaf.stalk q) =>
    t * Z.blowUpπ.stalkMap q (y ρ) ^ m ∈ J) hideal).mp h1
  obtain ⟨w, hw, hwt⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have hew : t = w := by
    have _ : IsLeftCancelMulZero (Z.blowUp.presheaf.stalk q) :=
      hdomS.toIsCancelMulZero.toIsLeftCancelMulZero
    exact (mul_left_cancel₀ (pow_ne_zero m ha) (hwt.trans (mul_comm _ _))).symm
  refine (congrArg (fun z : Z.blowUp.presheaf.stalk q => z ∈ _) hew).mpr ?_
  rw [hS1]
  -- the chart-level inclusion, localized: `π_*^{-1}(D(−log S_z)(I_z), m) 𝒪_{B,q} ⊆
  -- D(−log (S_z R')^{sat})(π_*^{-1}(I_z, m+1)) 𝒪_{B,q} ⊆ D(−log (S_z R')^{sat} 𝒪_{B,q})(J 𝒪_{B,q})`
  have h3 : (transformIdeal y ρ L m).map
      (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) ≤
      Ideal.logDerivative k
        ((⨆ i : ℕ, ((S.stalkIdeal (Z.blowUpπ q)).map
          (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ))).colon
            ((Ideal.span
              {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)} ^ i :
              Ideal (chartRing y ρ)) : Set (chartRing y ρ))).map
          (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)))
        ((transformIdeal y ρ (I.stalkIdeal (Z.blowUpπ q)) (m + 1)).map
          (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q))) :=
    (Ideal.map_mono (Derivation.transformIdeal_logDerivative_le (k := k) y ρ _ hIz)).trans
      (Ideal.map_logDerivative_le (k := k) 𝔮.primeCompl _ _)
  refine Ideal.logDerivative_mono ?_ (h3 hw)
  -- `J 𝒪_{B,q} ⊆ T_q`: for `g ∈ J`, `ψ' g · (π^♯ y_ρ)^{m+1} = ψ'(g · φ(y_ρ)^{m+1}) ∈ π^*(I_z)`
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, Submodule.mem_colon]
  intro p hp
  rw [Ideal.span_singleton_pow] at hp
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  have hre : algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q) g •
      (c * Z.blowUpπ.stalkMap q (y ρ) ^ (m + 1)) =
      c * (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q) g *
        Z.blowUpπ.stalkMap q (y ρ) ^ (m + 1)) :=
    (smul_eq_mul _ _).trans (mul_left_comm _ _ _)
  rw [hre]
  refine Ideal.mul_mem_left _ c ?_
  have hideal2 : (I.stalkIdeal (Z.blowUpπ q)).map (Z.blowUpπ.stalkMap
      q).hom =
      ((I.stalkIdeal (Z.blowUpπ q)).map
        (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ))).map
          (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
    (congrArg (fun g => Ideal.map g (I.stalkIdeal (Z.blowUpπ q))) hψφ).symm.trans
      (Ideal.map_map _ _).symm
  have helt' : algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q) g *
      Z.blowUpπ.stalkMap q (y ρ) ^ (m + 1) =
      algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)
        (g * algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^
            (m + 1)) :=
    (congrArg (_ * ·) ((congrArg (· ^ (m + 1)) hψy.symm).trans (map_pow _ _ (m + 1)).symm)).trans
      (map_mul _ _ _).symm
  refine (congrArg (fun J : Ideal (Z.blowUp.presheaf.stalk q) =>
    algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q) g *
      Z.blowUpπ.stalkMap q (y ρ) ^ (m + 1) ∈ J) hideal2).mpr ?_
  refine (congrArg (fun z : Z.blowUp.presheaf.stalk q => z ∈ _) helt').mpr ?_
  refine Ideal.mem_map_of_mem _ ?_
  rw [← span_pow_mul_transformIdeal y ρ hIz, Ideal.span_singleton_pow,
    mul_comm g (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^
        (m + 1))]
  exact Ideal.mem_span_singleton_mul.mpr ⟨g, hg, rfl⟩

end StalkCases

section Main

variable [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)] (S I : X.IdealSheafData)

include f n

/-- Equation (87.3) of [Kol07, 87] for `j = 1` and one blow-up: for a smooth blow-up with
`ord_Z I ≥ m + 1` along every component of the center, and any closed `S` (Kollár's `Z ⊆ S` is
not assumed), `π_*^{-1}(D(−log S)(I), m) ⊆ D(−log S₁)(π_*^{-1}(I, m + 1))`, `S₁` the strict
transform of `S`. -/
theorem markedTransform_logDerivative_le {m : ℕ}
    (hm : I.LeOrdAlong Z.support ((m + 1 : ℕ) : ℕ∞)) :
    (S.logDerivative f I).markedTransform Z m ≤
      (S.strictTransform Z).logDerivative (Z.blowUpπ ≫ f) (I.markedTransform Z (m + 1)) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hπ : Smooth (Z.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth f n Z
  have hft : LocallyOfFiniteType (Z.blowUpπ ≫ f) := inferInstance
  refine Scheme.IdealSheafData.le_of_stalkIdeal_le fun q => ?_
  rw [stalkIdeal_logDerivative (Z.blowUpπ ≫ f)]
  by_cases hq : Z.blowUpπ q ∈ Z.support
  · exact stalkIdeal_markedTransform_logDerivative_le_of_mem f n Z S I hm q hq
  · exact stalkIdeal_markedTransform_logDerivative_le_of_notMem f n Z S I q hq

/-! ### One blow-up, all `j` -/

/-- Equation (87.3) of [Kol07, 87] for one blow-up, by induction on `j` as in Theorem 76: for a
smooth blow-up with `ord_Z I ≥ m`, any closed `S`, and `j ≤ m`,
`π_*^{-1}(D^j(−log S)(I), m − j) ⊆ D^j(−log S₁)(π_*^{-1}(I, m))`. -/
theorem markedTransform_logDerivativeIter_le {m : ℕ}
    (hm : I.LeOrdAlong Z.support (m : ℕ∞)) {j : ℕ} (hj : j ≤ m) :
    (S.logDerivativeIter f j I).markedTransform Z (m - j) ≤
      (S.strictTransform Z).logDerivativeIter (Z.blowUpπ ≫ f) j
          (I.markedTransform Z m) := by
  induction j with
  | zero =>
    rw [logDerivativeIter_zero, logDerivativeIter_zero, Nat.sub_zero]
  | succ j ih =>
    have hj' : j ≤ m := Nat.le_of_succ_le hj
    have hmj : m - j = m - (j + 1) + 1 := by omega
    have h1 : (S.logDerivativeIter f j I).LeOrdAlong Z.support ((m - (j + 1) + 1 : ℕ) : ℕ∞) := by
      have := leOrdAlong_derivativeIter f n Z I hm hj'
      rw [hmj] at this
      exact fun η hη =>
          (this η hη).trans
              (Scheme.IdealSheafData.ord_anti (logDerivativeIter_le_derivativeIter f S I j) η)
    calc (S.logDerivativeIter f (j + 1) I).markedTransform Z (m - (j + 1))
        = (S.logDerivative f (S.logDerivativeIter f j I)).markedTransform Z (m - (j + 1)) := by
          rw [logDerivativeIter_succ]
      _ ≤ (S.strictTransform Z).logDerivative (Z.blowUpπ ≫ f)
            ((S.logDerivativeIter f j I).markedTransform Z (m - (j + 1) + 1)) :=
          markedTransform_logDerivative_le f n Z S (S.logDerivativeIter f j I) h1
      _ = (S.strictTransform Z).logDerivative (Z.blowUpπ ≫ f)
            ((S.logDerivativeIter f j I).markedTransform Z (m - j)) := by
          rw [← hmj]
      _ ≤ (S.strictTransform Z).logDerivative (Z.blowUpπ ≫ f)
            ((S.strictTransform Z).logDerivativeIter (Z.blowUpπ ≫ f) j
                (I.markedTransform Z m)) :=
          logDerivative_mono _ _ (ih hj')
      _ = (S.strictTransform Z).logDerivativeIter (Z.blowUpπ ≫ f) (j + 1)
            (I.markedTransform Z m) :=
          (logDerivativeIter_succ _ _ _ _).symm

end Main

end AlgebraicGeometry
