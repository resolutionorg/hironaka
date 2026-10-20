/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Scheme.BlowUp.Transform
public import Hironaka.Scheme.IdealSheaf.Order.Along
import Hironaka.Algebra.Derivative.Localization
import Hironaka.Algebra.Local.BlowUpLiftTransform
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.Transform
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Derivative.Cosupport
import Hironaka.Scheme.IdealSheaf.Derivative.Properties
import Hironaka.Scheme.IdealSheaf.Derivative.Pullback
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 76 for a single smooth blow-up: the birational transform of derivatives

[Kol07, Theorem 76] for one blow-up `π : B_Z X → X` of a smooth `k`-scheme along a smooth center
`Z`, in characteristic zero: for a marked ideal `(I, m)` with `ord_Z I ≥ m` and `j ≤ m`,
`π_*^{-1}(D^j(I), m − j) ⊆ D^j(π_*^{-1}(I, m))`, with `D` the derivative ideal sheaf of
[Kol07, Definition 73] and `π_*^{-1}(·, ·)` the marked transform of [Kol07, Definition 60]. Kollár
derives it from the chart formulas of [Kol07, 75]; the proof here follows the derivation-theoretic
argument of [Wlo05, Lemma 2.6.3]. The statement along a sequence is in
`Hironaka/Scheme/BlowUpSequence/DerivativeSequence.lean`.

**Order bookkeeping.** `ord_Z I ≥ m` gives `ord_Z D^j(I) ≥ m − j` at every generic point of `Z`
([Kol07, Lemma 74 (3)], `le_ord_iff_le_ord_derivativeIter`), hence, for a smooth center,
`F^{m−j} ∣ π^* D^j(I)` (`pow_dvd_comap_of_leOrdAlong`): the marked transform
`π_*^{-1}(D^j(I), m − j)` is defined in Kollár's sense.

**The case `j = 1`.** The inclusion `π_*^{-1}(D(I), m) ⊆ D(π_*^{-1}(I, m+1))` is checked on stalks
(`Scheme.IdealSheafData.le_of_stalkIdeal_le`). Off the exceptional divisor `π` is an isomorphism
(`isIso_stalkMap_π_of_notMem_support`), the stalks of both transforms are `π^*` of the stalks of
`D(I)` and `I` (`F_q = 𝒪`, the colon by the unit ideal is trivial), the stalk of `D(I)` is
`D_k(I_z)` (`stalkIdeal_derivative`), and `D_k` commutes with a `k`-algebra isomorphism
(`Ideal.derivative_map_ringEquiv`). Over a point `z ∈ Z` the stalk `𝒪_{B,q}` is the localization
`R'_𝔮` of the chart ring `R' = 𝒪_{X,z}[yᵢ/y_ρ]` at a prime of the fibre, compatibly with `π^♯`
(`exists_stalk_equiv_localization_chart_of_smooth`), the exceptional stalk is `(π^♯ y_ρ)`
(`stalkIdeal_comap_eq_span_of_chart`) and `I_z ⊆ P^{m+1}` for `P = Z_z = (y₀, …, y_ρ)`
(`stalkIdeal_le_pow_of_leOrdAlong`). The stalk of a marked transform is the colon
`(K_z 𝒪_{B,q} : (π^♯ y_ρ)^c)`, and through the isomorphism `e` with `R'_𝔮` it is the localization
of the chart transform `transformIdeal`:
`e(t) · y_ρ^m ∈ D_k(I_z) R'_𝔮 = y_ρ^m · π_*^{-1}(D_k(I_z), m) R'_𝔮` and `y_ρ` is a nonzerodivisor,
so `e(t)` lies in the localization of `π_*^{-1}(D_k(I_z), m) ⊆ D_k(π_*^{-1}(I_z, m+1))` (the
ring-level inclusion `transformIdeal_derivative_le`, the argument of [Wlo05, Lemma 2.6.3]), which
lies in `D_k` of the localization (`derivative_map_le`), i.e. in `D_k(e(T_q))` for the stalk `T_q`
of `π_*^{-1}(I, m+1)`; transporting back along `e` gives `t ∈ D_k(T_q)`. The `k`-algebra
structures are those of `f` and `π ≫ f` on the stalks (`stalkAlgebra`), and `e` respects them
(`stalkMap_comp_algebraMap_stalkAlgebra`).

**All `j`.** Induction on `j`: the case `j = 1` for `(D^j(I), m − j)`, defined by the order
bookkeeping, then monotonicity of `D` and `D(D^j(I)) = D^{j+1}(I)`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
  Scheme.IdealSheafData Scheme.BlowUpSequence AlgebraicGeometry.Scheme.IdealSheafData

/-! ### Derivative ideals and ring isomorphisms -/

namespace Derivation

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  (e : A ≃+* B) (hk : ∀ a : k, e (algebraMap k A a) = algebraMap k B a)

include hk in
theorem symm_algebraMap_of_forall (a : k) : e.symm (algebraMap k B a) = algebraMap k A a := by
  rw [← hk, RingEquiv.symm_apply_apply]

/-- Conjugation of a `k`-derivation by a ring isomorphism respecting the `k`-structures. -/
noncomputable def congrRingEquiv (D : Derivation k A A) : Derivation k B B where
  toFun b := e (D (e.symm b))
  map_add' b c := by simp only [map_add]
  map_smul' c b := by
    have h1 : e.symm (c • b) = c • e.symm b := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, symm_algebraMap_of_forall e hk]
    change e (D (e.symm (c • b))) = c • e (D (e.symm b))
    rw [h1, D.map_smul, Algebra.smul_def, Algebra.smul_def, map_mul, hk]
  map_one_eq_zero' := by simp
  leibniz' b c := by
    change e (D (e.symm (b * c))) = b * e (D (e.symm c)) + c * e (D (e.symm b))
    rw [map_mul, D.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
      e.apply_symm_apply, e.apply_symm_apply]

theorem congrRingEquiv_apply (D : Derivation k A A) (b : B) :
    congrRingEquiv e hk D b = e (D (e.symm b)) := rfl

end Derivation

namespace Ideal

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  (e : A ≃+* B) (hk : ∀ a : k, e (algebraMap k A a) = algebraMap k B a)

include hk in
/-- The derivative ideal is transported by a ring isomorphism respecting the `k`-structures:
`D(J) B = D(J B)` — derivations are conjugated along `e`. -/
theorem derivative_map_ringEquiv (J : Ideal A) :
    (derivative k J).map e.toRingHom = derivative k (J.map e.toRingHom) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    refine derivative_le_iff.mpr ⟨fun f hf => Ideal.mem_comap.mpr
      (le_derivative _ (Ideal.mem_map_of_mem _ hf)), fun δ f hf => ?_⟩
    rw [Ideal.mem_comap]
    have : e.toRingHom (δ f) = Derivation.congrRingEquiv e hk δ (e.toRingHom f) := by
      change e (δ f) = e (δ (e.symm (e f)))
      rw [RingEquiv.symm_apply_apply]
    rw [this]
    exact derivation_apply_mem_derivative _ (Ideal.mem_map_of_mem _ hf)
  · refine derivative_le_iff.mpr ⟨Ideal.map_mono (le_derivative J), fun δ' b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hb
    have : δ' (e.toRingHom a) = e.toRingHom (Derivation.congrRingEquiv e.symm
        (fun c => by rw [Derivation.symm_algebraMap_of_forall e hk]) δ' a) := by
      change δ' (e a) = e (e.symm (δ' (e.symm.symm a)))
      rw [RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
    rw [this]
    exact Ideal.mem_map_of_mem _ (derivation_apply_mem_derivative _ ha)

/-- Membership through a ring isomorphism. -/
theorem mem_iff_map_mem_map (J : Ideal A) (x : A) :
    x ∈ J ↔ e.toRingHom x ∈ J.map e.toRingHom := by
  conv_lhs => rw [← Ideal.comap_map_of_bijective e.toRingHom e.bijective (I := J)]
  exact Iff.rfl

end Ideal

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-! ### Order bookkeeping -/

section Order

variable [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (Z I : X.IdealSheafData)

include f n

/-- [Kol07, Lemma 74 (3)]: if `ord_Z I ≥ m` along every component and `j ≤ m`, then
`ord_Z D^j(I) ≥ m − j`. -/
theorem leOrdAlong_derivativeIter {m : ℕ} (hm : I.LeOrdAlong Z.support (m : ℕ∞)) {j : ℕ}
    (hj : j ≤ m) : (I.derivativeIter f j).LeOrdAlong Z.support ((m - j : ℕ) : ℕ∞) := by
  intro η hη
  rcases lt_or_eq_of_le hj with hlt | rfl
  · exact (le_ord_iff_le_ord_derivativeIter f n I η hlt).mp (hm η hη)
  · rw [Nat.sub_self, Nat.cast_zero]
    exact zero_le

end Order

section BlowUp

variable [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)] (I : X.IdealSheafData)

include f n

/-- For a smooth center with `ord_Z I ≥ m` and `j ≤ m`, `F^{m−j}` divides `π^* D^j(I)`: the marked
transform `π_*^{-1}(D^j(I), m − j)` of [Kol07, Definition 73 (73.3)] is defined in the sense of
[Kol07, Definition 60]. -/
theorem exceptionalDivisor_pow_dvd_comap_derivativeIter {m : ℕ}
    (hm : I.LeOrdAlong Z.support (m : ℕ∞)) {j : ℕ} (hj : j ≤ m) :
    Z.exceptionalDivisor ^ (m - j) ∣ (I.derivativeIter f j).comap Z.blowUpπ :=
  pow_dvd_comap_of_leOrdAlong f n Z _ (leOrdAlong_derivativeIter f n Z I hm hj)

end BlowUp

/-! ### The stalks of a marked transform -/

section Stalks

variable (Z K : X.IdealSheafData) (c : ℕ)

/-- Off the exceptional divisor the stalk of `π_*^{-1}(K, c)` is `π^*(K_{π q})` (the exceptional
stalk is the unit ideal). -/
theorem stalkIdeal_markedTransform_of_notMem {q : Z.blowUp}
    (hq : q ∉ (Z.comap Z.blowUpπ).support) :
    (K.markedTransform Z c).stalkIdeal q =
      (K.stalkIdeal (Z.blowUpπ q)).map (Z.blowUpπ.stalkMap q).hom := by
  change ((K.comap Z.blowUpπ).colon (Z.comap Z.blowUpπ ^ c)).stalkIdeal q
      = _
  rw [stalkIdeal_colon_of_isInvertible _ (isInvertible_pow (blowUp.isInvertible_comap_π Z) c),
    stalkIdeal_pow, stalkIdeal_comap, stalkIdeal_eq_top_of_notMem_support _ hq, Ideal.top_pow,
    Ideal.colon_coe_top]

/-- Over the center, in the chart data at `q` (`exists_stalk_equiv_localization_chart_of_smooth`),
the stalk of `π_*^{-1}(K, c)` is the colon `(π^*(K_z) : (π^♯ y_ρ)^c)`. -/
theorem stalkIdeal_markedTransform_of_chart (q : Z.blowUp) {n' : ℕ}
    (y : Fin n' → X.presheaf.stalk (Z.blowUpπ q)) (ρ : Fin n')
    (hZ' : Z.stalkIdeal (Z.blowUpπ q) = chartCenter y ρ) (𝔮 : Ideal (chartRing y ρ))
    [𝔮.IsPrime] (e : Z.blowUp.presheaf.stalk q ≃+* Localization.AtPrime 𝔮)
    (he : ∀ a, e (Z.blowUpπ.stalkMap q a) =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) a)) :
    (K.markedTransform Z c).stalkIdeal q =
      ((K.stalkIdeal (Z.blowUpπ q)).map (Z.blowUpπ.stalkMap q).hom).colon
        ((Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} ^ c : Ideal _) : Set _) := by
  have hF : (Z.comap Z.blowUpπ).stalkIdeal q =
      Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} :=
    stalkIdeal_comap_eq_span_of_chart q y ρ hZ' 𝔮 e he
  change ((K.comap Z.blowUpπ).colon (Z.comap Z.blowUpπ ^ c)).stalkIdeal q
      = _
  rw [stalkIdeal_colon_of_isInvertible _ (isInvertible_pow (blowUp.isInvertible_comap_π Z) c),
    stalkIdeal_pow, stalkIdeal_comap, hF]

end Stalks

/-! ### One blow-up, `j = 1`: the two kinds of points of `B_Z X` -/

section StalkCases

variable (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
  (I : X.IdealSheafData)

/-- The `k`-algebra structure of `𝒪_{B,q}` through `π ≫ f` is `π^♯` of the structure of `𝒪_{X,πq}`
through `f` (`stalkMap_comp_algebraMap_stalkAlgebra`), pointwise. -/
theorem stalkMap_algebraMap_stalkAlgebra (q : Z.blowUp) (a : k) :
    letI := f.stalkAlgebra (Z.blowUpπ q)
    letI := (Z.blowUpπ ≫ f).stalkAlgebra q
    Z.blowUpπ.stalkMap q (algebraMap k (X.presheaf.stalk (Z.blowUpπ q)) a) =
      algebraMap k (Z.blowUp.presheaf.stalk q) a :=
  RingHom.congr_fun (Scheme.Hom.stalkMap_comp_algebraMap_stalkAlgebra f Z.blowUpπ q) a

include f n

/-- Off the exceptional divisor: `π` is an isomorphism there, so the stalks of both transforms are
`π^*` of the stalks on `X`, and `D_k` is transported by the ring isomorphism `π^♯`. -/
theorem stalkIdeal_markedTransform_derivative_le_of_notMem {m : ℕ} (q : Z.blowUp)
    (hq : Z.blowUpπ q ∉ Z.support) :
    ((I.derivative f).markedTransform Z m).stalkIdeal q ≤
      letI := (Z.blowUpπ ≫ f).stalkAlgebra q
      Ideal.derivative k ((I.markedTransform Z (m + 1)).stalkIdeal q) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hft : LocallyOfFiniteType f := inferInstance
  have hq' : q ∉ (Z.comap Z.blowUpπ).support := by
    rwa [support_comap]
  let _ := f.stalkAlgebra (Z.blowUpπ q)
  let _ := (Z.blowUpπ ≫ f).stalkAlgebra q
  rw [stalkIdeal_markedTransform_of_notMem Z _ m hq', stalkIdeal_markedTransform_of_notMem Z I
    (m + 1) hq', stalkIdeal_derivative f I]
  have hk : ∀ a : k, stalkMapπEquiv Z hq' (algebraMap k _ a) = algebraMap k _ a :=
    fun a => stalkMap_algebraMap_stalkAlgebra f Z q a
  have hhom : (stalkMapπEquiv Z hq').toRingHom = (Z.blowUpπ.stalkMap q).hom :=
    RingHom.ext fun _ => rfl
  have h := Ideal.derivative_map_ringEquiv (stalkMapπEquiv Z hq') hk
    (I.stalkIdeal (Z.blowUpπ q))
  rw [hhom] at h
  exact le_of_eq h

/-- Over the center, through the chart description of the stalk at `q`: the ring-level inclusion
`transformIdeal_derivative_le`, localized at the prime `𝔮` of the fibre and transported along
`e`. -/
theorem stalkIdeal_markedTransform_derivative_le_of_mem [CharZero k] [Smooth (Z.subschemeι ≫ f)]
    {m : ℕ} (hm : I.LeOrdAlong Z.support ((m + 1 : ℕ) : ℕ∞)) (q : Z.blowUp)
    (hq : Z.blowUpπ q ∈ Z.support) :
    ((I.derivative f).markedTransform Z m).stalkIdeal q ≤
      letI := (Z.blowUpπ ≫ f).stalkAlgebra q
      Ideal.derivative k ((I.markedTransform Z (m + 1)).stalkIdeal q) := by
  classical
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hft : LocallyOfFiniteType f := inferInstance
  have hreg := isRegularLocalRing_stalk f (Z.blowUpπ q)
  obtain ⟨n', y, ρ, hn', hy, hZ', 𝔮, hprime, -, e, he⟩ :=
    exists_stalk_equiv_localization_chart_of_smooth f Z q hq
  let _ := f.stalkAlgebra (Z.blowUpπ q)
  let _ := (Z.blowUpπ ≫ f).stalkAlgebra q
  -- `I_z ⊆ P^{m+1}` and `D_k(I_z) ⊆ P^m`
  have hIz : I.stalkIdeal (Z.blowUpπ q) ≤ chartCenter y ρ ^ (m + 1) := by
    have := stalkIdeal_le_pow_of_leOrdAlong f n Z I hm hq
      (stalkIdeal_ne_bot_of_mem_support_of_smooth f Z q hq)
    rwa [hZ'] at this
  have hD : Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q)) ≤ chartCenter y ρ ^ m :=
    Ideal.derivative_le_pow hIz
  -- `ψ' : R' → 𝒪_{B,q}`, the localization map read back through `e⁻¹`; `ψ' ∘ φ = π^♯`. Everything
  -- below is stated on the stalk `𝒪_{B,q}` (an abstract ring), never on `Localization.AtPrime 𝔮`:
  -- the ring instances of the concrete localization make every defeq check time out.
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
  -- the stalks of the two transforms and of `D(I)`
  rw [stalkIdeal_markedTransform_of_chart Z _ m q y ρ hZ' 𝔮 e he,
    stalkIdeal_markedTransform_of_chart Z I (m + 1) q y ρ hZ' 𝔮 e he, stalkIdeal_derivative f I]
  intro t ht
  -- `t · (π^♯ y_ρ)^m ∈ D_k(I_z) 𝒪_{B,q} = (π^♯ y_ρ)^m · π_*^{-1}(D_k(I_z), m) 𝒪_{B,q}`
  have h1 : t * Z.blowUpπ.stalkMap q (y ρ) ^ m ∈
      (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))).map
          (Z.blowUpπ.stalkMap q).hom := by
    have := Submodule.mem_colon.mp ht (Z.blowUpπ.stalkMap q (y ρ) ^ m)
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m)
    rwa [smul_eq_mul] at this
  have hideal : (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))).map
      (Z.blowUpπ.stalkMap q).hom =
      Ideal.span {Z.blowUpπ.stalkMap q (y ρ) ^ m} *
        (transformIdeal y ρ (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))) m).map
          (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
    calc (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))).map
           (Z.blowUpπ.stalkMap q).hom
        = (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))).map
            ((algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)).comp
              (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ))) :=
          (congrArg (fun g => Ideal.map g (Ideal.derivative k (I.stalkIdeal
              (Z.blowUpπ q))))
            hψφ).symm
      _ = ((Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))).map
            (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ))).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
          (Ideal.map_map _ _).symm
      _ = (Ideal.span
        {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)} ^ m *
            transformIdeal y ρ (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))) m).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
          congrArg (Ideal.map _) (span_pow_mul_transformIdeal y ρ hD).symm
      _ = (Ideal.span
        {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ m} *
            transformIdeal y ρ (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))) m).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) := by
          rw [Ideal.span_singleton_pow]
      _ = (Ideal.span
            {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ m}).map
            (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) *
            (transformIdeal y ρ (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))) m).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
                  Ideal.map_mul _ _ _
      _ = Ideal.span (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q) ''
            {algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ m}) *
            (transformIdeal y ρ (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))) m).map
              (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) :=
          congrArg (· * _) (Ideal.map_span _ _)
      _ = Ideal.span
        {algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)
              (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ) ^ m)} *
            (transformIdeal y ρ (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))) m).map
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
  -- the ring-level inclusion, localized:
  -- `π_*^{-1}(D_k(I_z), m) 𝒪_{B,q} ⊆ D_k(π_*^{-1}(I_z, m+1)) 𝒪_{B,q} ⊆ D_k(J 𝒪_{B,q})`
  have h3 : (transformIdeal y ρ (Ideal.derivative k (I.stalkIdeal (Z.blowUpπ q))) m).map
      (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q)) ≤
      Ideal.derivative k ((transformIdeal y ρ (I.stalkIdeal (Z.blowUpπ q)) (m + 1)).map
        (algebraMap (chartRing y ρ) (Z.blowUp.presheaf.stalk q))) :=
    (Ideal.map_mono (Derivation.transformIdeal_derivative_le (k := k) y ρ hIz)).trans
      (Ideal.derivative_map_le (k := k) 𝔮.primeCompl _)
  refine Ideal.derivative_mono ?_ (h3 hw)
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
  (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)] (I : X.IdealSheafData)

include f n

/-- [Kol07, Theorem 76] for `j = 1` and one blow-up: for a smooth blow-up with `ord_Z I ≥ m + 1`
along every component of the center, `π_*^{-1}(D(I), m) ⊆ D(π_*^{-1}(I, m + 1))`. -/
theorem markedTransform_derivative_le {m : ℕ}
    (hm : I.LeOrdAlong Z.support ((m + 1 : ℕ) : ℕ∞)) :
    (I.derivative f).markedTransform Z m ≤
      (I.markedTransform Z (m + 1)).derivative (Z.blowUpπ ≫ f) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hπ : Smooth (Z.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth f n Z
  have hft : LocallyOfFiniteType (Z.blowUpπ ≫ f) := inferInstance
  refine Scheme.IdealSheafData.le_of_stalkIdeal_le fun q => ?_
  rw [stalkIdeal_derivative (Z.blowUpπ ≫ f)]
  by_cases hq : Z.blowUpπ q ∈ Z.support
  · exact stalkIdeal_markedTransform_derivative_le_of_mem f n Z I hm q hq
  · exact stalkIdeal_markedTransform_derivative_le_of_notMem f n Z I q hq

/-! ### One blow-up, all `j` -/

/-- [Kol07, Theorem 76] for one blow-up, by induction on `j` (compare [Wlo05, Lemma 2.6.3]): for
a smooth blow-up with `ord_Z I ≥ m` and `j ≤ m`, `π_*^{-1}(D^j(I), m − j) ⊆ D^j(π_*^{-1}(I, m))`. -/
theorem markedTransform_derivativeIter_le {m : ℕ} (hm : I.LeOrdAlong Z.support (m : ℕ∞))
    {j : ℕ} (hj : j ≤ m) :
    (I.derivativeIter f j).markedTransform Z (m - j) ≤
      (I.markedTransform Z m).derivativeIter (Z.blowUpπ ≫ f) j := by
  induction j with
  | zero =>
    rw [derivativeIter_zero, derivativeIter_zero, Nat.sub_zero]
  | succ j ih =>
    have hj' : j ≤ m := Nat.le_of_succ_le hj
    have hmj : m - j = m - (j + 1) + 1 := by omega
    have h1 : (I.derivativeIter f j).LeOrdAlong Z.support ((m - (j + 1) + 1 : ℕ) : ℕ∞) := by
      have := leOrdAlong_derivativeIter f n Z I hm hj'
      rwa [hmj] at this
    calc (I.derivativeIter f (j + 1)).markedTransform Z (m - (j + 1))
        = ((I.derivativeIter f j).derivative f).markedTransform Z (m - (j + 1)) := by
          rw [derivativeIter_succ]
      _ ≤ ((I.derivativeIter f j).markedTransform Z (m - (j + 1) + 1)).derivative
            (Z.blowUpπ ≫ f) :=
          markedTransform_derivative_le f n Z (I.derivativeIter f j) h1
      _ = ((I.derivativeIter f j).markedTransform Z (m - j)).derivative
          (Z.blowUpπ ≫ f) := by
          rw [← hmj]
      _ ≤ ((I.markedTransform Z m).derivativeIter (Z.blowUpπ ≫ f) j).derivative
            (Z.blowUpπ ≫ f) :=
          derivative_mono _ (ih hj')
      _ = (I.markedTransform Z m).derivativeIter (Z.blowUpπ ≫ f) (j + 1) :=
          (derivativeIter_succ _ _ _).symm

end Main

end AlgebraicGeometry
