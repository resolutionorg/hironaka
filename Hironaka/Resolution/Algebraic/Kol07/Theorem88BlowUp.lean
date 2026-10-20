/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TransformDeriv
public import Hironaka.Scheme.BlowUp.Transform
public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.ColonPow
import Hironaka.Algebra.Local.ChartCoords
import Hironaka.Algebra.Local.ChartLogDerivations
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.Transform
import Hironaka.Algebra.Local.TransformDerivNormalForm
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Resolution.Algebraic.Kol07.Theorem88Chart
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.Theorem88Basic
import Hironaka.Scheme.BlowUpSequence.TransformDerivative
import Hironaka.Scheme.BlowUpSequence.TransformLogDerivative
import Hironaka.Scheme.IdealSheaf.Derivative.DualSpans
import Hironaka.Scheme.IdealSheaf.Derivative.FlagCoords
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicLocalization
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicSheaf
import Hironaka.Scheme.IdealSheaf.Derivative.Properties
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.DifferentialBasis
import Hironaka.Scheme.Smooth.LocalBlowUpChart
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 88 for one blow-up

[Kol07, Theorem 88] for a single smooth blow-up `π : B_Z X → X` with center `Z ⊆ S`, `S` a smooth
hypersurface, `ord_Z I ≥ m`, `s ≤ m`:
`D^s π_*^{-1}(I, m) = ∑_{j ≤ s} D^{s−j}(−log S₁) π_*^{-1}(D^j I, m − j)` (88.1). Kollár proves
this case in a local chart; the induction along a sequence is in
`Hironaka/Resolution/Algebraic/Kol07/Theorem88Sequence.lean`.

* `⊇` is the coordinate-free inclusion of `Hironaka/Scheme/BlowUpSequence/Theorem88Basic.lean` for
  one blow-up (Theorem 76 and `D(−log S₁) ⊆ D`).
* `⊆` is checked at the closed points `q` of `B_Z X` (`le_of_forall_stalkIdeal_le_of_isClosed`;
  `B_Z X` is Jacobson, being locally of finite type over `k`). Off the center the two sides are the
  transported `D^s I_z` (`stalkIdeal_derivativeIter_markedTransform_of_notMem`, the `j = s`
  summand). Over the center, at `z = π(q)`: `κ(z)` is algebraic
  (`isAlgebraic_residueField_π_of_isClosed`), so `dim 𝒪_{X,z} = n` and the flag coordinates
  `x_0, …, x_{n−1}` (`exists_flagCoords`: a regular system of parameters whose first member is the
  equation of `S` and whose first `r` members generate `Z`) have `n` members; the chart description
  of the stalk with these coordinates (`exists_stalk_equiv_localization_chart_of_chartCenter`) puts
  `q` in the chart of some `x_j`, `j ≤ r`. If `j = 0` (the chart of the equation of `S`) the strict
  transform misses `q` (`Hironaka/Resolution/Algebraic/Kol07/Theorem88Chart.lean`) and (88.1) at `q`
  is its `j = 0` summand. Otherwise, with the coordinates reindexed so that the pivot is the last
  center coordinate and `x_0` stays first: the stalks of the marked transforms are the images of the
  chart transforms `transformIdeal` (`stalkIdeal_markedTransform_eq_map_transformIdeal`); the
  derivative ideals of the stalk are computed by the chart derivations, which generate
  `Der_k(𝒪_{B,q})` at the closed point `q` (`derivativeIter_map_le_map_iterate_chartD`, from
  `forall_derivation_eq_sum_of_isClosed`); `iterate_chartD_transformIdeal_le` gives the
  chart-level inclusion, Kollár's formula (88.2); the chart logarithmic derivations are logarithmic
  along the strict transform's chart ideal `(x_r y_0)^{sat}` (`chartDlogpow_le_logDerivativeIter`),
  whose image is `(S₁)_q` (`stalkIdeal_strictTransform_eq_map_span_colon`), and `D(−log)` is
  transported through the localization and the isomorphism `e` (`map_logDerivativeIter_le`);
  finally the coordinate derivatives `c.Dpow j I_z` lie in the full `D^j I_z`
  (`Dpow_le_derivativeIter`, `k`-linear coordinates).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData IsLocalRing

namespace Derivation

/-- Leibniz on the generators of an image ideal: `δ (J B) ⊆ J B + span (δ (φ J))`. -/
theorem mem_map_sup_span_image {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k B]
    (δ : Derivation k B B) (φ : A →+* B) (J : Ideal A) {z : B} (hz : z ∈ J.map φ) :
    δ z ∈ J.map φ ⊔ Ideal.span (δ '' (φ '' (J : Set A))) :=
  δ.mem_span_sup_span_image (φ '' (J : Set A)) hz

end Derivation

namespace Ideal

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  (e : A ≃+* B) (hk : ∀ a : k, e (algebraMap k A a) = algebraMap k B a)

include hk in
/-- The iterated derivative ideal is transported by a ring isomorphism respecting the
`k`-structures (`derivative_map_ringEquiv`, iterated). -/
theorem derivativeIter_map_ringEquiv (s : ℕ) (J : Ideal A) :
    (derivativeIter k s J).map e.toRingHom = derivativeIter k s (J.map e.toRingHom) := by
  induction s with
  | zero => rfl
  | succ s ih => rw [derivativeIter_succ, derivativeIter_succ, derivative_map_ringEquiv e hk, ih]

/-- Cancelling a power of a nonzerodivisor, `((aᶜ) T : (a)ᶜ) = T` in a domain: a corollary of
`Ideal.colon_span_pow_mul_self` (`Hironaka/Algebra/ColonPow.lean`; the colon by the ideal `(a)ᶜ`
is the colon by `{aᶜ}`). -/
theorem colon_span_singleton_pow_mul_eq {A : Type*} [CommRing A] [IsDomain A] {a : A} (ha : a ≠ 0)
    (c : ℕ) (T : Ideal A) :
    (Ideal.span {a ^ c} * T).colon ((Ideal.span {a} ^ c : Ideal A) : Set A) = T := by
  rw [Ideal.span_singleton_pow, Ideal.colon_span]
  exact colon_span_pow_mul_self T ha c

/-- `D(−log)` through a localization followed by a ring isomorphism respecting the
`k`-structures, iterated: `(D^t(−log J) K) C ⊆ D^t(−log J C)(K C)`. -/
theorem map_logDerivativeIter_le {C : Type*} [CommRing C] [Algebra k C] [Algebra A B]
    [IsScalarTower k A B] (M : Submonoid A) [IsLocalization M B] (e : B ≃+* C)
    (hk : ∀ a : k, e (algebraMap k B a) = algebraMap k C a) (J : Ideal A) (t : ℕ) (K : Ideal A) :
    (logDerivativeIter k J t K).map (e.toRingHom.comp (algebraMap A B)) ≤
      logDerivativeIter k (J.map (e.toRingHom.comp (algebraMap A B))) t
        (K.map (e.toRingHom.comp (algebraMap A B))) := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [logDerivativeIter_succ, logDerivativeIter_succ]
    calc (logDerivative k J (logDerivativeIter k J t K)).map (e.toRingHom.comp (algebraMap A B))
        = ((logDerivative k J (logDerivativeIter k J t K)).map (algebraMap A B)).map e.toRingHom :=
          (Ideal.map_map _ _).symm
      _ ≤ (logDerivative k (J.map (algebraMap A B))
            ((logDerivativeIter k J t K).map (algebraMap A B))).map e.toRingHom :=
          Ideal.map_mono (map_logDerivative_le M J _)
      _ = logDerivative k ((J.map (algebraMap A B)).map e.toRingHom)
            (((logDerivativeIter k J t K).map (algebraMap A B)).map e.toRingHom) :=
          logDerivative_map_ringEquiv e hk _ _
      _ = logDerivative k (J.map (e.toRingHom.comp (algebraMap A B)))
            ((logDerivativeIter k J t K).map (e.toRingHom.comp (algebraMap A B))) := by
          rw [Ideal.map_map, Ideal.map_map]
      _ ≤ _ := logDerivative_mono ih

end Ideal

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]

include f n in
/-- The residue field of `z = π(q)` is algebraic over `k` when `q` is a closed point of `B_Z X`:
`κ(z) ↪ κ(q)` over `k`, and `κ(q)` is algebraic (`trdeg_residueField_stalk_eq_zero_of_isClosed`). -/
theorem isAlgebraic_residueField_π_of_isClosed (q : Z.blowUp)
    (hq : IsClosed ({q} : Set Z.blowUp)) :
    letI := f.stalkAlgebra (Z.blowUpπ q)
    Algebra.IsAlgebraic k (ResidueField (X.presheaf.stalk (Z.blowUpπ q))) := by
  let _ := f.stalkAlgebra (Z.blowUpπ q)
  let _ := (Z.blowUpπ ≫ f).stalkAlgebra q
  have hπ : SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) :=
    smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n Z
  have hq' : Algebra.IsAlgebraic k (ResidueField (Z.blowUp.presheaf.stalk q)) :=
    trdeg_eq_zero_iff.mp
      (trdeg_residueField_stalk_eq_zero_of_isClosed (Z.blowUpπ ≫ f) n hq)
  let φ : ResidueField (X.presheaf.stalk (Z.blowUpπ q)) →ₐ[k]
      ResidueField (Z.blowUp.presheaf.stalk q) :=
    { toRingHom := ResidueField.map (Z.blowUpπ.stalkMap q).hom
      commutes' := fun a => by
        change ResidueField.map _ (residue _ (algebraMap k _ a)) = residue _ (algebraMap k _ a)
        rw [ResidueField.map_residue, stalkMap_algebraMap_stalkAlgebra f Z q a] }
  exact Algebra.IsAlgebraic.of_injective φ (ResidueField.map _).injective

include f n in
/-- At `z = π(q)`, `q` closed, `dim 𝒪_{X,z} = n`. -/
theorem ringKrullDim_stalk_π_eq_of_isClosed (q : Z.blowUp)
    (hq : IsClosed ({q} : Set Z.blowUp)) :
    ringKrullDim (X.presheaf.stalk (Z.blowUpπ q)) = n := by
  let _ := f.stalkAlgebra (Z.blowUpπ q)
  have halg := isAlgebraic_residueField_π_of_isClosed f n Z q hq
  have h := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension f n
    (Z.blowUpπ q)
  rw [trdeg_eq_zero_iff.mpr halg] at h
  simpa using h

section ChartAtClosedPoint

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [Algebra k R] [Algebra ℚ R]

/-- At a closed point `q` of `B_Z X` identified with a localization of the chart ring
`R' = R[c.x_i / c.x_ρ]` of `k`-linear coordinates `c` (the chart isomorphism `e`, respecting the
`k`-structures), the derivative ideal of the stalk is computed by the chart derivations:
`D^s(T 𝒪_{B,q}) ⊆ (D'^s T) 𝒪_{B,q}`. The chart derivations, localized and transported along `e`,
are dual to the transported chart coordinates, so they generate `Der_k(𝒪_{B,q})`
(`forall_derivation_eq_sum_of_isClosed`), and Leibniz on the generators finishes. -/
theorem derivativeIter_map_le_map_iterate_chartD (q : Z.blowUp)
    (hq : IsClosed ({q} : Set Z.blowUp)) (c : RegularCoords R n)
        (hk : c.IsLinearOver k)
    (ρ : Fin n) (𝔮 : Ideal (chartRing c.x ρ)) [𝔮.IsPrime]
    (e : Z.blowUp.presheaf.stalk q ≃+* Localization.AtPrime 𝔮)
    (hk' : letI := (Z.blowUpπ ≫ f).stalkAlgebra q
      ∀ a : k, e.symm (algebraMap k (Localization.AtPrime 𝔮) a) =
        algebraMap k (Z.blowUp.presheaf.stalk q) a)
    (T : Ideal (chartRing c.x ρ)) (s : ℕ) :
    letI := (Z.blowUpπ ≫ f).stalkAlgebra q
    Ideal.derivativeIter k s
        (T.map (e.symm.toRingHom.comp
          (algebraMap (chartRing c.x ρ) (Localization.AtPrime 𝔮)))) ≤
      ((c.chartD ρ)^[s] T).map (e.symm.toRingHom.comp
        (algebraMap (chartRing c.x ρ) (Localization.AtPrime 𝔮))) := by
  let _ := (Z.blowUpπ ≫ f).stalkAlgebra q
  have hπ : SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) :=
    smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n Z
  set ψ' := e.symm.toRingHom.comp (algebraMap (chartRing c.x ρ) (Localization.AtPrime 𝔮))
    with hψ'
  -- the chart derivations, localized and transported to `𝒪_{B,q}`
  let der : Fin n → Derivation k (Z.blowUp.presheaf.stalk q)
      (Z.blowUp.presheaf.stalk q) :=
    fun i => Derivation.congrRingEquiv e.symm hk'
      ((c.chartDerivRingOver ρ hk i).localization 𝔮.primeCompl)
  have hder_ψ : ∀ (i : Fin n) (t : chartRing c.x ρ),
      der i (ψ' t) = ψ' (c.chartDerivRing ρ i t) := by
    intro i t
    change e.symm (((c.chartDerivRingOver ρ hk i).localization 𝔮.primeCompl)
      (e.symm.symm (e.symm (algebraMap _ _ t)))) = e.symm (algebraMap _ _ (c.chartDerivRing ρ i t))
    rw [RingEquiv.symm_symm, e.apply_symm_apply, Derivation.localization_algebraMap]
    rfl
  -- they are dual to the transported chart coordinates, hence span `Der_k(𝒪_{B,q})`
  have hdual : ∀ i j, der i (ψ' (chartYR c.x ρ j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hder_ψ, c.chartDerivRing_chartYR ρ]
    split_ifs <;> simp
  have hspan := forall_derivation_eq_sum_of_isClosed (Z.blowUpπ ≫ f) n hq
    (fun j => ψ' (chartYR c.x ρ j)) der hdual
  -- Leibniz on the generators, by induction on `s`
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    rw [Ideal.derivativeIter_succ, Function.iterate_succ_apply']
    refine (Ideal.derivative_mono ih).trans ?_
    refine Ideal.derivative_le_iff.mpr ⟨Ideal.map_mono (c.le_chartD ρ _), fun δ z hz => ?_⟩
    rw [hspan δ z]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
    have hmem := (der i).mem_map_sup_span_image ψ' _ hz
    have hle : ((c.chartD ρ)^[s] T).map ψ' ⊔
        Ideal.span (der i '' (ψ' '' ((c.chartD ρ)^[s] T : Set _))) ≤
          (c.chartD ρ ((c.chartD ρ)^[s] T)).map ψ' := by
      refine sup_le (Ideal.map_mono (c.le_chartD ρ _)) (Ideal.span_le.mpr ?_)
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      rw [hder_ψ]
      exact Ideal.mem_map_of_mem _ (c.chartDerivRing_mem_chartD ρ ht i)
    exact hle hmem

end ChartAtClosedPoint

section ChartData

variable (K : X.IdealSheafData) (c : ℕ) (q : Z.blowUp) {n' : ℕ}
  (y : Fin n' → X.presheaf.stalk (Z.blowUpπ q)) (ρ : Fin n')
  (hn' : (n' : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.blowUpπ q)))
  (hy : maximalIdeal (X.presheaf.stalk (Z.blowUpπ q)) = Ideal.span (Set.range y))
  (hZ' : Z.stalkIdeal (Z.blowUpπ q) = chartCenter y ρ) (𝔮 : Ideal (chartRing y ρ))
      [𝔮.IsPrime]
  (e : Z.blowUp.presheaf.stalk q ≃+* Localization.AtPrime 𝔮)
  (he : ∀ a, e (Z.blowUpπ.stalkMap q a) =
    algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
      (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) a))

omit [CharZero k] [Smooth (Z.subschemeι ≫ f)] in
include f n hn' hy hZ' he in
/-- Over the center, in the chart data at `q`: the stalk of `π_*^{-1}(K, c)` is the image under
`ψ' = e⁻¹ ∘ (R' → R'_𝔮)` of the chart transform `transformIdeal` (for `K_z ⊆ P^c`): the colon
formula `stalkIdeal_markedTransform_of_chart` and `x_r^c · π_*^{-1}(K_z, c) = K_z R'`, the power of
the nonzerodivisor `π^♯ y_ρ` cancelled. -/
theorem stalkIdeal_markedTransform_eq_map_transformIdeal
    (hK : K.stalkIdeal (Z.blowUpπ q) ≤ chartCenter y ρ ^ c) :
    (K.markedTransform Z c).stalkIdeal q =
      (transformIdeal y ρ (K.stalkIdeal (Z.blowUpπ q)) c).map
        (e.symm.toRingHom.comp (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮))) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg := isRegularLocalRing_stalk f (Z.blowUpπ q)
  set ψ' := e.symm.toRingHom.comp (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)) with hψ'
  have hψφ : ψ'.comp (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ)) =
      (Z.blowUpπ.stalkMap q).hom :=
    RingHom.ext fun a => (congrArg e.symm (he a)).symm.trans (e.symm_apply_apply _)
  have hψy : ψ' (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)) =
      Z.blowUpπ.stalkMap q (y ρ) := RingHom.congr_fun hψφ (y ρ)
  have hdom : IsDomain (chartRing y ρ) := isDomain_chartRing y ρ hy hn'
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
  have hideal : (K.stalkIdeal (Z.blowUpπ q)).map (Z.blowUpπ.stalkMap q).hom
      =
      Ideal.span {Z.blowUpπ.stalkMap q (y ρ) ^ c} *
        (transformIdeal y ρ (K.stalkIdeal (Z.blowUpπ q)) c).map ψ' :=
    calc (K.stalkIdeal (Z.blowUpπ q)).map (Z.blowUpπ.stalkMap q).hom
        = (K.stalkIdeal (Z.blowUpπ q)).map
            (ψ'.comp (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ))) :=
          (congrArg (fun g => Ideal.map g (K.stalkIdeal (Z.blowUpπ q))) hψφ).symm
      _ = ((K.stalkIdeal (Z.blowUpπ q)).map
            (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ))).map ψ' :=
          (Ideal.map_map _ _).symm
      _ = (Ideal.span
        {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)} ^ c *
            transformIdeal y ρ (K.stalkIdeal (Z.blowUpπ q)) c).map ψ' :=
          congrArg (Ideal.map _) (span_pow_mul_transformIdeal y ρ hK).symm
      _ = (Ideal.span
        {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ c} *
            transformIdeal y ρ (K.stalkIdeal (Z.blowUpπ q)) c).map ψ' := by
          rw [Ideal.span_singleton_pow]
      _ = (Ideal.span
            {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ c}).map ψ' *
            (transformIdeal y ρ (K.stalkIdeal (Z.blowUpπ q)) c).map ψ' :=
                Ideal.map_mul _ _ _
      _ = Ideal.span (ψ' ''
            {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ c}) *
            (transformIdeal y ρ (K.stalkIdeal (Z.blowUpπ q)) c).map ψ' :=
          congrArg (· * _) (Ideal.map_span _ _)
      _ = Ideal.span
        {ψ' (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ c)}
            * (transformIdeal y ρ (K.stalkIdeal (Z.blowUpπ q)) c).map ψ' :=
          congrArg (fun S : Set (Z.blowUp.presheaf.stalk q) => Ideal.span S * _)
            (Set.image_singleton (f := ψ'))
      _ = _ := congrArg (fun z : Z.blowUp.presheaf.stalk q => Ideal.span {z} * _)
            ((map_pow _ _ c).trans (congrArg (· ^ c) hψy))
  rw [stalkIdeal_markedTransform_of_chart Z K c q y ρ hZ' 𝔮 e he, hideal,
    Ideal.colon_span_singleton_pow_mul_eq ha]

include hZ' he in
/-- The stalk of the strict transform in the chart data: for `S_z = (g)`, `(S₁)_q` is the image
under `ψ'` of the `y_ρ`-saturation `⋃ᵢ ((φ g) : y_ρⁱ)` of the total transform `(φ g) R'`. -/
theorem stalkIdeal_strictTransform_eq_map_span_colon (S : X.IdealSheafData) {g}
    (hSz : S.stalkIdeal (Z.blowUpπ q) = Ideal.span {g}) :
    (S.strictTransform Z).stalkIdeal q =
      (⨆ i : ℕ, (Ideal.span
        {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) g}).colon
        ((Ideal.span
          {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)} ^ i :
          Ideal (chartRing y ρ)) : Set (chartRing y ρ))).map
        (e.symm.toRingHom.comp (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮))) := by
  classical
  set ψ' := e.symm.toRingHom.comp (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)) with hψ'
  have hψφ : ψ'.comp (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ)) =
      (Z.blowUpπ.stalkMap q).hom :=
    RingHom.ext fun a => (congrArg e.symm (he a)).symm.trans (e.symm_apply_apply _)
  have hψy : ψ' (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)) =
      Z.blowUpπ.stalkMap q (y ρ) := RingHom.congr_fun hψφ (y ρ)
  let algS : Algebra (chartRing y ρ) (Z.blowUp.presheaf.stalk q) := ψ'.toAlgebra
  have hloc : IsLocalization 𝔮.primeCompl (Z.blowUp.presheaf.stalk q) :=
    (IsLocalization.isLocalization_iff_of_ringEquiv (S := Localization.AtPrime 𝔮) 𝔮.primeCompl
      e.symm).mp inferInstance
  have hK : Z.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π Z
  have hF : Z.exceptionalDivisor.stalkIdeal q =
      Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} :=
    stalkIdeal_comap_eq_span_of_chart q y ρ hZ' 𝔮 e he
  have step1 : (S.strictTransform Z).stalkIdeal q =
      ⨆ i : ℕ, (Ideal.span {Z.blowUpπ.stalkMap q g}).colon
        ((Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} ^ i :
          Ideal (Z.blowUp.presheaf.stalk q)) : Set
              (Z.blowUp.presheaf.stalk q)) := by
    unfold strictTransform strictTransformAlong
    rw [stalkIdeal_saturate_of_isInvertible _ hK, stalkIdeal_comap, hF, hSz, Ideal.map_span,
      Set.image_singleton]
  change _ = (⨆ i : ℕ,
      (Ideal.span {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) g}).colon
        ((Ideal.span
          {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)} ^ i :
          Ideal (chartRing y ρ)) : Set (chartRing y ρ))).map
      (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q))
  rw [step1, Ideal.map_iSup]
  refine iSup_congr fun i => ?_
  have hfg : (Ideal.span
    {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)} ^ i
      : Ideal (chartRing y ρ)).FG := by
    rw [Ideal.span_singleton_pow]
    exact Submodule.fg_span_singleton _
  rw [map_colon_of_fg 𝔮.primeCompl _ _ hfg]
  congr 1
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {Z.blowUpπ.stalkMap q g} = Ideal.span {ψ' (algebraMap _ _ g)}
    rw [← RingHom.comp_apply, hψφ]
  · congr 1
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    change Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} ^ i = Ideal.span {ψ' _} ^ i
    rw [hψy]

end ChartData

/-! ### Off the center -/

omit [CharZero k] [Smooth (Z.subschemeι ≫ f)] in
include f n in
/-- Off the center the marked transforms are total transforms along the isomorphism `π^♯`, and
`D^s π_*^{-1}(I, m) = π_*^{-1}(D^s I, m − s)` there: (88.1)'s left side is its `j = s` summand. -/
theorem stalkIdeal_derivativeIter_markedTransform_of_notMem (I : X.IdealSheafData) (m s : ℕ)
    (q : Z.blowUp) (hq : Z.blowUpπ q ∉ Z.support) :
    letI := (Z.blowUpπ ≫ f).stalkAlgebra q
    Ideal.derivativeIter k s ((I.markedTransform Z m).stalkIdeal q) =
      ((I.derivativeIter f s).markedTransform Z (m - s)).stalkIdeal q := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hft : LocallyOfFiniteType f := inferInstance
  have hq' : q ∉ (Z.comap Z.blowUpπ).support := by rwa [support_comap]
  let _ := f.stalkAlgebra (Z.blowUpπ q)
  let _ := (Z.blowUpπ ≫ f).stalkAlgebra q
  rw [stalkIdeal_markedTransform_of_notMem Z I m hq',
    stalkIdeal_markedTransform_of_notMem Z _ (m - s) hq', stalkIdeal_derivativeIter f s I]
  have hk : ∀ a : k, stalkMapπEquiv Z hq' (algebraMap k _ a) = algebraMap k _ a :=
    fun a => stalkMap_algebraMap_stalkAlgebra f Z q a
  have hhom : (stalkMapπEquiv Z hq').toRingHom = (Z.blowUpπ.stalkMap q).hom :=
    RingHom.ext fun _ => rfl
  have h := Ideal.derivativeIter_map_ringEquiv (stalkMapπEquiv Z hq') hk s
    (I.stalkIdeal (Z.blowUpπ q))
  rw [hhom] at h
  exact h.symm

/-! ### Theorem 88 for one blow-up -/

section Main

variable (S I : X.IdealSheafData)

include f n in
/-- [Kol07, Theorem 88] for one blow-up: for a smooth blow-up with center `Z ⊆ S`, `S` a smooth
hypersurface, `ord_Z I ≥ m` and `s ≤ m`,
`D^s π_*^{-1}(I, m) = ∑_{j ≤ s} D^{s−j}(−log S₁) π_*^{-1}(D^j I, m − j)`. -/
theorem derivativeIter_markedTransform_eq_iSup (hS : IsSmoothDivisor S) {m : ℕ}
    (hZS : S ≤ Z) (hm : I.LeOrdAlong Z.support (m : ℕ∞)) {s : ℕ} (hs : s ≤ m) :
    (I.markedTransform Z m).derivativeIter (Z.blowUpπ ≫ f) s =
      ⨆ j ≤ s, (S.strictTransform Z).logDerivativeIter (Z.blowUpπ ≫ f) (s - j)
        ((I.derivativeIter f j).markedTransform Z (m - j)) := by
  classical
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hπ : SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) :=
    smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n Z
  have hπs : Smooth (Z.blowUpπ ≫ f) := SmoothOfRelativeDimension.smooth n _
  have hft : LocallyOfFiniteType (Z.blowUpπ ≫ f) := inferInstance
  refine le_antisymm ?_ ?_
  · -- `⊆`: at the closed points of `B_Z X`
    have hJ : JacobsonSpace Z.blowUp := LocallyOfFiniteType.jacobsonSpace
        (Z.blowUpπ ≫ f)
    refine le_of_forall_stalkIdeal_le_of_isClosed fun q hq => ?_
    let _ := (Z.blowUpπ ≫ f).stalkAlgebra q
    rw [stalkIdeal_derivativeIter (Z.blowUpπ ≫ f) s _ q]
    simp only [stalkIdeal_iSup', stalkIdeal_logDerivativeIter (Z.blowUpπ ≫ f)]
    by_cases hq0 : Z.blowUpπ q ∈ Z.support
    · -- over the center: flag coordinates at `z = π(q)`, with `n` members
      let _ := f.stalkAlgebra (Z.blowUpπ q)
      let _ := f.stalkAlgebraRat (Z.blowUpπ q)
      have hreg := isRegularLocalRing_stalk f (Z.blowUpπ q)
      obtain ⟨n', c, h0, r, hk, hSz, hZz⟩ :=
        exists_flagCoords f n Z S hS hZS hq0
      have hn' : n' = n := by
        have h1 := c.card
        rw [ringKrullDim_stalk_π_eq_of_isClosed f n Z q hq] at h1
        exact_mod_cast h1
      subst n'
      -- the chart description with the flag coordinates: `q` lies in the chart of `c.x j`, `j ≤ r`
      obtain ⟨j, hjr, hZ'', 𝔮₀, hprime₀, -, e₀, he₀⟩ :=
        exists_stalk_equiv_localization_chart_of_chartCenter Z q c.x r hZz
      set c' := c.reindex (Equiv.swap j r) with hc'
      have hc'x : c'.x = c.x ∘ Equiv.swap j r := rfl
      -- the chart data, retyped along `c'.x = c.x ∘ swap j r` (definitional)
      let 𝔮 : Ideal (chartRing c'.x r) := 𝔮₀
      have hprime : 𝔮.IsPrime := hprime₀
      let e : Z.blowUp.presheaf.stalk q ≃+* Localization.AtPrime 𝔮 := e₀
      have he : ∀ a, e (Z.blowUpπ.stalkMap q a) =
          algebraMap (chartRing c'.x r) (Localization.AtPrime 𝔮)
            (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing c'.x r) a) := he₀
      have hZ' : Z.stalkIdeal (Z.blowUpπ q) = chartCenter c'.x r := hZ''
      have hy : maximalIdeal (X.presheaf.stalk (Z.blowUpπ q)) = Ideal.span
          (Set.range c'.x) :=
        c'.span_x
      have hn'' : (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.blowUpπ q)) :=
          c'.card
      have hyr : c'.x r = c.x j := by
        rw [hc'x, Function.comp_apply, Equiv.swap_apply_right]
      by_cases hj0 : j = ⟨0, h0⟩
      · -- the bad chart: the pivot is the equation of `S`, and `S₁` misses `q`
        have hSz' : S.stalkIdeal (Z.blowUpπ q) = Ideal.span {c'.x r} := by
          rw [hyr, hj0]
          exact hSz
        have hS1 := stalkIdeal_strictTransform_eq_top_of_pivot Z S q c'.x r hZ' hSz' 𝔮 e he
        refine le_iSup₂_of_le 0 (Nat.zero_le s) ?_
        rw [hS1, Ideal.logDerivativeIter_top, Nat.sub_zero, derivativeIter_zero, Nat.sub_zero]
      · -- a good chart: `x_0` (the equation of `S`) stays at index `0 < r`
        have hr0 : (⟨0, h0⟩ : Fin n) < r := by
          rw [Fin.lt_def]
          rcases Nat.eq_zero_or_pos r.val with hr | hr
          · exact absurd (Fin.ext (Nat.le_zero.mp (hr ▸ Fin.le_iff_val_le_val.mp hjr))) hj0
          · exact hr
        have hy0 : c'.x ⟨0, h0⟩ = c.x ⟨0, h0⟩ := by
          rw [hc'x, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hj0) hr0.ne]
        have hSz0 : S.stalkIdeal (Z.blowUpπ q) = Ideal.span {c'.x ⟨0, h0⟩} := by
          rw [hy0]
          exact hSz
        have hk' : c'.IsLinearOver k := c.reindex_isLinearOver hk _
        -- the marks: `I_z ⊆ P^m` and `(D^j I)_z ⊆ P^{m−j}`
        have hZne : Z.stalkIdeal (Z.blowUpπ q) ≠ ⊥ :=
          stalkIdeal_ne_bot_of_mem_support_of_smooth f Z q hq0
        have hIz : I.stalkIdeal (Z.blowUpπ q) ≤ chartCenter c'.x r ^ m := by
          have := stalkIdeal_le_pow_of_leOrdAlong f n Z I hm hq0 hZne
          rwa [hZ'] at this
        have hDIz : ∀ j' ≤ s, (I.derivativeIter f j').stalkIdeal (Z.blowUpπ q) ≤
            chartCenter c'.x r ^ (m - j') := fun j' hj' => by
          have := stalkIdeal_le_pow_of_leOrdAlong f n Z _
            (leOrdAlong_derivativeIter f n Z I hm (hj'.trans hs)) hq0 hZne
          rwa [hZ'] at this
        -- the `k`-structures agree along `e`
        set ψ' := e.symm.toRingHom.comp (algebraMap (chartRing c'.x r) (Localization.AtPrime 𝔮))
          with hψ'
        have hkk' : ∀ a : k, e.symm (algebraMap k (Localization.AtPrime 𝔮) a) =
            algebraMap k (Z.blowUp.presheaf.stalk q) a := fun a =>
          have h1 : algebraMap k (Localization.AtPrime 𝔮) a =
              e (algebraMap k (Z.blowUp.presheaf.stalk q) a) :=
            ((IsScalarTower.algebraMap_apply k (chartRing c'.x r) (Localization.AtPrime 𝔮) a).trans
              (congrArg (algebraMap (chartRing c'.x r) (Localization.AtPrime 𝔮))
                (IsScalarTower.algebraMap_apply k (X.presheaf.stalk (Z.blowUpπ q))
                  (chartRing c'.x r) a))).trans
              ((he (algebraMap k _ a)).symm.trans
                (congrArg e (stalkMap_algebraMap_stalkAlgebra f Z q a)))
          (congrArg e.symm h1).trans (e.symm_apply_apply _)
        -- the stalks of the transforms, and of the strict transform
        have hJ : (I.markedTransform Z m).stalkIdeal q =
            (transformIdeal c'.x r (I.stalkIdeal (Z.blowUpπ q)) m).map ψ' :=
          stalkIdeal_markedTransform_eq_map_transformIdeal f n Z I m q c'.x r hn'' hy hZ' 𝔮 e he
            hIz
        have hM : ∀ j' ≤ s, ((I.derivativeIter f j').markedTransform Z (m - j')).stalkIdeal q =
            (transformIdeal c'.x r (Ideal.derivativeIter k j' (I.stalkIdeal
                (Z.blowUpπ q)))
              (m - j')).map ψ' := fun j' hj' =>
          (stalkIdeal_markedTransform_eq_map_transformIdeal f n Z _ (m - j') q c'.x r hn'' hy
            hZ' 𝔮 e he (hDIz j' hj')).trans
            (congrArg (fun J => (transformIdeal c'.x r J (m - j')).map ψ')
              (stalkIdeal_derivativeIter f j' I (Z.blowUpπ q)))
        have hS1 : (S.strictTransform Z).stalkIdeal q =
            (c'.chartSat r (algebraMap _ (chartRing c'.x r) (c'.x ⟨0, h0⟩))).map ψ' :=
          stalkIdeal_strictTransform_eq_map_span_colon Z q c'.x r hZ' 𝔮 e he S hSz0
        rw [hJ]
        calc Ideal.derivativeIter k s
              ((transformIdeal c'.x r (I.stalkIdeal (Z.blowUpπ q)) m).map ψ')
            ≤ ((c'.chartD r)^[s] (transformIdeal c'.x r (I.stalkIdeal
                (Z.blowUpπ q)) m)).map ψ' :=
              derivativeIter_map_le_map_iterate_chartD f n Z q hq c' hk' r 𝔮 e hkk' _ s
          _ ≤ (⨆ j' ≤ s, c'.chartDlogpow r ⟨0, h0⟩ (s - j')
                (transformIdeal c'.x r (c'.Dpow j' (I.stalkIdeal (Z.blowUpπ q)))
                    (m - j'))).map
                ψ' :=
              Ideal.map_mono (c'.iterate_chartD_transformIdeal_le r hr0 hIz hs)
          _ = ⨆ j' ≤ s, (c'.chartDlogpow r ⟨0, h0⟩ (s - j')
                (transformIdeal c'.x r (c'.Dpow j' (I.stalkIdeal (Z.blowUpπ q)))
                    (m - j'))).map
                ψ' := by
              simp only [Ideal.map_iSup]
          _ ≤ ⨆ j' ≤ s, Ideal.logDerivativeIter k ((S.strictTransform Z).stalkIdeal q) (s - j')
                (((I.derivativeIter f j').markedTransform Z (m - j')).stalkIdeal q) := by
              refine iSup₂_mono fun j' hj' => ?_
              rw [hM j' hj', hS1]
              refine (Ideal.map_mono (c'.chartDlogpow_le_logDerivativeIter r hk' hr0 _ _)).trans ?_
              refine (Ideal.map_logDerivativeIter_le 𝔮.primeCompl e.symm hkk' _ _ _).trans ?_
              exact Ideal.logDerivativeIter_mono _ _ (Ideal.map_mono (transformIdeal_mono c'.x r
                (Ideal.Dpow_le_derivativeIter c' hk' j' _)))
    · -- off the center: the `j = s` summand
      rw [stalkIdeal_derivativeIter_markedTransform_of_notMem f n Z I m s q hq0]
      refine le_iSup₂_of_le s le_rfl ?_
      rw [Nat.sub_self, Ideal.logDerivativeIter_zero]
  · -- `⊇`: every summand (Theorem 76 and `D(−log S₁) ⊆ D`)
    refine iSup₂_le fun j hj => ?_
    have h1 := logDerivativeIter_le_derivativeIter (Z.blowUpπ ≫ f) (S.strictTransform Z)
      ((I.derivativeIter f j).markedTransform Z (m - j)) (s - j)
    have h2 := derivativeIter_mono (Z.blowUpπ ≫ f) (s - j)
      (markedTransform_derivativeIter_le f n Z I hm (hj.trans hs))
    refine h1.trans (h2.trans ?_)
    rw [derivativeIter_derivativeIter, Nat.sub_add_cancel hj]

end Main

end Hironaka.Sequence
