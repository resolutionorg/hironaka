/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Scheme.BlowUp.Transform.Defs
public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.ColonPow
import Hironaka.Algebra.Local.ChartGenericFibre
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Algebra.Local.TransformOrder
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.CosuppTransport
import Hironaka.Resolution.Algebraic.MaximalContact.Transform
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedComponentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The exceptional divisor at its generic points

Four lemmas on one blow-up, used in the proof of the statement CP3 of the embedded
desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`;
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Weak`):
for the blow-up `π : B_Z X → X` of a smooth `X` along a smooth centre `Z` of any shape with
exceptional divisor `F = π⁻¹Z`, at a generic point `ε` of `F`:

* `π ε` is a generic point of `Z`
  (`blowUpπ_mem_genericPoints_of_mem_genericPoints_exceptionalDivisor`);
* `ord_ε (π^* J) = ord_{π ε} J` (`ord_comap_blowUpπ_of_mem_genericPoints_exceptionalDivisor`;
  [Kol07, Definition 47]: the order along `Z` is the multiplicity of the pullback along the
  exceptional divisor);
* the weak transform of an ideal of constant order `d` along `Z` has order `0` at `ε`
  (`ord_weakTransform_eq_zero_of_mem_genericPoints_exceptionalDivisor`; the weak transform of
  [Kol07, 58], formula (58.1));
* the weak transform of an ideal vanishing generically on `D` has order `0` at the generic points
  of the strict transform of `D` (`ord_weakTransform_eq_zero_of_mem_genericPoints_strictTransform`).

**The local computation** (`exists_chart_of_mem_genericPoints_exceptionalDivisor`). `F` is a
smooth divisor of the smooth `B_Z X`, so `F_ε = 𝔪_ε` at a generic point `ε` of `F`. In the chart at
`z = π ε` (`exists_stalk_equiv_localization_chart_of_smooth`): `𝒪_{B,ε} ≅ R'_𝔮` with
`R' = 𝒪_{X,z}[y_i/y_ρ]`, `Z_z = P = (y_0, …, y_ρ)` a partial centre of the regular system of
parameters `y`, `𝔮` a prime of `R'` over `𝔪_z`. The ideal `F_ε = Z_z 𝒪_{B,ε}` corresponds to
`P R'_𝔮 = (y_ρ) R'_𝔮` (`map_chartCenter`), and `(y_ρ)` is a prime of `R'` since
`R'/(y_ρ) ≅ (𝒪_{X,z}/P)[Y]` (`exists_quotient_span_algebraMap_x_ringEquiv_chartCenter`). As
`F_ε = 𝔪_ε`, `(y_ρ) R'_𝔮` is the maximal ideal, whence `𝔮 = (y_ρ)` and
`𝔪_z ≤ 𝔮 ∩ 𝒪_{X,z} = P = Z_z`: the centre is the whole maximal ideal at `z`, `ρ` is the last
parameter (`𝔪_z` needs `dim` generators), and `z` is a generic point of `Z`
(`mem_genericPoints_of_stalkIdeal_eq_maximalIdeal`). Then the order identity is the computation of
the order along the exceptional divisor in the chart of the last coordinate
(`ordAlong_span_algebraMap_x_map`) transported through the isomorphism, and the vanishing of the
weak transform is the order computation in the regular local ring `𝒪_{B,ε}` with `𝔪_ε = (a)`:
`π^* J` has order `d` and lies in `(a)^d`, so its colon by `(a)^d` is the unit ideal
(`colon_span_singleton_pow_eq_top_of_ord_le`). The chart is that of [Kol07, Definition 60] and
[Hau14, Definition 6.2] (the strict transform); the order along a centre is [Kol07, Lemma 61].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
  Scheme.IdealSheafData Scheme BlowUpSequence Hironaka.Sequence Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-! ### The generic-point criterion `Z_z = 𝔪_z` -/

/-- A point `z` of `V(Z)` with `Z_z = 𝔪_z` is a generic point of `V(Z)` (the converse of
`stalkIdeal_eq_maximalIdeal_of_mem_genericPoints`, on any scheme): a generization `ξ ∈ V(Z)` of `z`
is, on an affine `U ∋ z`, a prime `q ⊆ p` of `Γ(U)` containing `Z(U)`; both `q` and `p` become
`𝔪_z = Z_z` in `𝒪_{X,z} = Γ(U)_p`, so `q = p` and `ξ = z`. -/
theorem mem_genericPoints_of_stalkIdeal_eq_maximalIdeal (Z : X.IdealSheafData) (z : X)
    (hz : Z.stalkIdeal z = maximalIdeal (X.presheaf.stalk z)) : z ∈ Z.support.genericPoints := by
  classical
  have hzZ : z ∈ Z.support := (mem_support_iff_stalkIdeal_le_maximalIdeal Z z).mpr hz.le
  refine ⟨hzZ, fun ξ hξZ hξ => ?_⟩
  obtain ⟨U, hzU⟩ := exists_affineOpens_mem z
  have hU : IsAffineOpen U.1 := U.2
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hzU⟩ : U.1)
  have hloc_z := hU.isLocalization_stalk ⟨z, hzU⟩
  have hξU : ξ ∈ (U.1 : Set X) := hξ.mem_open U.1.2 hzU
  set p := hU.primeIdealOf ⟨z, hzU⟩ with hpdef
  set q := hU.primeIdealOf ⟨ξ, hξU⟩ with hqdef
  have hqp : q ≤ p := by
    rw [PrimeSpectrum.le_iff_specializes]
    have h1 : hU.fromSpec q ⤳ hU.fromSpec p := by
      rw [hqdef, hpdef, hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]
      exact hξ
    exact hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h1
  have hZq : Z.ideal U ≤ q.asIdeal :=
    (mem_zeroLocus_iff_le_primeIdealOf U hξU _).mp ((mem_support_iff_of_mem hξU).mp hξZ)
  have hqmap : q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk z)) =
      p.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk z)) := by
    refine le_antisymm (Ideal.map_mono hqp) ?_
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal (X.presheaf.stalk z), ← hz,
      stalkIdeal_eq_map_germ Z U hzU]
    exact Ideal.map_mono hZq
  have hdisj : Disjoint (p.asIdeal.primeCompl : Set Γ(X, U)) (q.asIdeal : Set Γ(X, U)) :=
    Set.disjoint_left.mpr fun a ha haq => ha (hqp haq)
  have hdisj' : Disjoint (p.asIdeal.primeCompl : Set Γ(X, U)) (p.asIdeal : Set Γ(X, U)) :=
    Set.disjoint_left.mpr fun a ha hap => ha hap
  have hq : q.asIdeal = p.asIdeal := by
    rw [← IsLocalization.under_map_of_isPrime_disjoint p.asIdeal.primeCompl (X.presheaf.stalk z)
      q.isPrime hdisj, hqmap, IsLocalization.under_map_of_isPrime_disjoint p.asIdeal.primeCompl
      (X.presheaf.stalk z) p.isPrime hdisj']
  have hqp' : q = p := PrimeSpectrum.ext hq
  calc ξ = hU.fromSpec q := (hU.fromSpec_primeIdealOf ⟨ξ, hξU⟩).symm
    _ = hU.fromSpec p := congrArg (fun t => hU.fromSpec t) hqp'
    _ = z := hU.fromSpec_primeIdealOf ⟨z, hzU⟩

/-! ### The chart identification, algebraically -/

section Algebra

variable {R : Type*} [CommRing R] {R' : Type*} [CommRing R'] {B : Type*} [CommRing B]

/-- Transport of an extended ideal through a commutative square `e ∘ φ = α ∘ ψ`:
`e(φ(I) B) ⊆ α(ψ(I) R')`. -/
theorem map_map_le_map_map_of_comp_eq {A : Type*} [CommRing A] (φ : R →+* B) (ψ : R →+* R')
    (α : R' →+* A) (e : B →+* A) (h : ∀ c, e (φ c) = α (ψ c)) (I : Ideal R) :
    (I.map φ).map e ≤ (I.map ψ).map α := by
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  intro c hc
  rw [Ideal.mem_comap, Ideal.mem_comap, h c]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hc)

/-- A prime `𝔮` of `R'` whose localization is identified with a local ring `B` in such a way that
the maximal ideal of `B` lands in `P R'_𝔮` for a prime `P ⊆ 𝔮` is `P`: for `a ∈ 𝔮`, `a/1` is in the
maximal ideal of `R'_𝔮 ≅ B`, hence in `P R'_𝔮`, whose trace on `R'` is `P` (`P` prime, `P ⊆ 𝔮`). -/
theorem le_of_map_maximalIdeal_le [IsLocalRing B] {𝔮 P : Ideal R'} [𝔮.IsPrime] (hP : P.IsPrime)
    (hPq : P ≤ 𝔮) (e : B ≃+* Localization.AtPrime 𝔮)
    (hle : (maximalIdeal B).map (e : B →+* Localization.AtPrime 𝔮) ≤
      P.map (algebraMap R' (Localization.AtPrime 𝔮))) :
    𝔮 ≤ P := by
  intro a ha
  have hmem : algebraMap R' (Localization.AtPrime 𝔮) a ∈
      P.map (algebraMap R' (Localization.AtPrime 𝔮)) := by
    obtain ⟨b, hb⟩ := e.surjective (algebraMap R' (Localization.AtPrime 𝔮) a)
    have hbm : b ∈ maximalIdeal B := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' : IsUnit (algebraMap R' (Localization.AtPrime 𝔮) a) := by
        rw [← hb]
        exact hu.map e
      exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔮) 𝔮 a).mp hu' ha
    rw [← hb]
    exact hle (Ideal.mem_map_of_mem _ hbm)
  have hunder := IsLocalization.under_map_of_isPrime_disjoint 𝔮.primeCompl
    (Localization.AtPrime 𝔮) hP (Set.disjoint_left.mpr fun x hx hxP => hx (hPq hxP))
  rw [← hunder]
  exact Ideal.mem_comap.mpr hmem

end Algebra

section Chart

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {n' : ℕ} (y : Fin n' → R)
  (hy : maximalIdeal R = Ideal.span (Set.range y)) (hn' : (n' : WithBot ℕ∞) = ringKrullDim R)
  (ρ : Fin n')

include hy hn'

/-- The prime of the chart identified: for a regular system of parameters `y` of `R`, the chart
ring `R' = R[y_i/y_ρ]` of the partial centre `P = (y_0, …, y_ρ)`, a prime `𝔮` of `R'` over `𝔪`, and
a local ring `B ≅ R'_𝔮` compatibly with `φ : R → B` — if `P B` is the maximal ideal of `B`, then
`𝔮 = (y_ρ)`: `P B` corresponds to `P R'_𝔮 = (y_ρ) R'_𝔮` (`map_chartCenter`), and `(y_ρ)` is a prime
of `R'` below `𝔮` (`isPrime_span_algebraMap_x_of_chartCenter`), so `le_of_map_maximalIdeal_le`
applies. -/
theorem prime_eq_span_of_map_chartCenter_eq_maximalIdeal (𝔮 : Ideal (chartRing y ρ)) [𝔮.IsPrime]
    (hle : maximalIdeal R ≤ 𝔮.comap (algebraMap R (chartRing y ρ))) {B : Type*} [CommRing B]
    [IsLocalRing B] (φ : R →+* B) (e : B ≃+* Localization.AtPrime 𝔮)
    (he : ∀ c, e (φ c) = algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
      (algebraMap R (chartRing y ρ) c))
    (hF : (chartCenter y ρ).map φ = maximalIdeal B) :
    𝔮 = Ideal.span {algebraMap R (chartRing y ρ) (y ρ)} := by
  have hP := isPrime_span_algebraMap_x_of_chartCenter y hy hn' ρ
  have hPq : Ideal.span {algebraMap R (chartRing y ρ) (y ρ)} ≤ 𝔮 := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hle (hy ▸ Ideal.subset_span ⟨ρ, rfl⟩)
  refine le_antisymm (le_of_map_maximalIdeal_le hP hPq e ?_) hPq
  rw [← hF, ← map_chartCenter y ρ]
  exact map_map_le_map_map_of_comp_eq φ _ _ _ he _

omit hy in
/-- If the partial centre `(y_0, …, y_ρ)` of a regular system of parameters `y` is the whole
maximal ideal, `ρ` is the last parameter: `𝔪` needs `dim R = n'` generators (`spanFinrank`), and
`(y_0, …, y_ρ)` has `ρ + 1`. -/
theorem val_add_one_eq_of_chartCenter_eq_maximalIdeal (h : chartCenter y ρ = maximalIdeal R) :
    ρ.val + 1 = n' := by
  classical
  have h1 : (maximalIdeal R).spanFinrank = n' := spanFinrank_maximalIdeal_eq_of_natCast_eq hn'
  have h2 : (maximalIdeal R).spanFinrank ≤ ρ.val + 1 := by
    rw [← h, chartCenter]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    have hset : {i : Fin n' | i ≤ ρ} = ↑(Finset.Iic ρ) := by
      ext i
      simp
    rw [hset, Set.ncard_coe_finset, Fin.card_Iic]
  have h3 : ρ.val < n' := ρ.2
  omega

end Chart

/-! ### The chart at a generic point of the exceptional divisor -/

section Smooth

variable (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ f))

include f n hZ

/-- At a generic point `ε` of the exceptional divisor `F = π⁻¹Z` of the blow-up of the smooth `X`
along the smooth centre `Z`: `F_ε = 𝔪_ε` — `F` is a smooth divisor of `B_Z X`
(`isSmoothDivisor_exceptionalDivisor_of_smooth`), and the stalk of a smooth divisor at a generic
point of its support is the maximal ideal. -/
theorem stalkIdeal_exceptionalDivisor_eq_maximalIdeal_of_mem_genericPoints {ε : Z.blowUp}
    (hε : ε ∈ Z.exceptionalDivisor.support.genericPoints) :
    Z.exceptionalDivisor.stalkIdeal ε = maximalIdeal (Z.blowUp.presheaf.stalk ε)
        := by
  have := hZ
  exact (stalkIdeal_vanishingIdeal_closure_eq_of_isSmoothDivisor
    (isSmoothDivisor_exceptionalDivisor_of_smooth f n Z) hε specializes_rfl).symm.trans
    (stalkIdeal_vanishingIdeal_closure_self ε)

/-- The local computation at a generic point `ε` of the exceptional divisor, `z = π ε` (the chart
`exists_stalk_equiv_localization_chart_of_smooth` at `z`, with its prime `𝔮` identified):
`Z_z = 𝔪_z`; adapted parameters `y` at `z` with `Z_z = (y_0, …, y_ρ)`; `𝒪_{B,ε} ≅ R'_𝔮` for
`R' = 𝒪_{X,z}[y_i/y_ρ]`, compatibly with `π^♯`; `ρ` is the last parameter; and `𝔮 = (y_ρ)`. The
identification: `F_ε = 𝔪_ε` is `(y_0, …, y_ρ) 𝒪_{B,ε}` (`stalkIdeal_comap`), so
`prime_eq_span_of_map_chartCenter_eq_maximalIdeal` gives `𝔮 = (y_ρ)`; then
`𝔪_z ≤ 𝔮 ∩ 𝒪_{X,z} = (y_0, …, y_ρ) = Z_z` (`comap_span_algebraMap_x_eq_chartCenter`), and `𝔪_z`
needs `dim 𝒪_{X,z}` generators (`val_add_one_eq_of_chartCenter_eq_maximalIdeal`). -/
theorem exists_chart_of_mem_genericPoints_exceptionalDivisor {ε : Z.blowUp}
    (hε : ε ∈ Z.exceptionalDivisor.support.genericPoints) :
    Z.stalkIdeal (Z.blowUpπ ε) = maximalIdeal (X.presheaf.stalk
        (Z.blowUpπ ε)) ∧
    ∃ (n' : ℕ) (y : Fin n' → X.presheaf.stalk (Z.blowUpπ ε)) (ρ : Fin n'),
      (n' : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (Z.blowUpπ ε)) ∧
      maximalIdeal (X.presheaf.stalk (Z.blowUpπ ε)) = Ideal.span (Set.range y) ∧
      Z.stalkIdeal (Z.blowUpπ ε) = chartCenter y ρ ∧
      ∃ (𝔮 : Ideal (chartRing y ρ)) (_ : 𝔮.IsPrime),
        maximalIdeal (X.presheaf.stalk (Z.blowUpπ ε)) ≤
            𝔮.comap (algebraMap (X.presheaf.stalk (Z.blowUpπ ε)) (chartRing y ρ)) ∧
          (∃ e : Z.blowUp.presheaf.stalk ε ≃+* Localization.AtPrime 𝔮,
            ∀ c : X.presheaf.stalk (Z.blowUpπ ε),
              e (Z.blowUpπ.stalkMap ε c) =
                algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
                  (algebraMap (X.presheaf.stalk (Z.blowUpπ ε)) (chartRing y ρ) c)) ∧
          ρ.val + 1 = n' ∧
          𝔮 = Ideal.span
            {algebraMap (X.presheaf.stalk (Z.blowUpπ ε)) (chartRing y ρ) (y ρ)} := by
  have := hZ
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hz : Z.blowUpπ ε ∈ Z.support := (mem_support_comap_iff_apply Z
      Z.blowUpπ ε).mp hε.1
  have hFε := stalkIdeal_exceptionalDivisor_eq_maximalIdeal_of_mem_genericPoints f n Z hZ hε
  have hreg : IsRegularLocalRing (X.presheaf.stalk (Z.blowUpπ ε)) :=
    isRegularLocalRing_stalk f _
  obtain ⟨n', y, ρ, hn', hy, hZy, 𝔮, h𝔮, hle, e, he⟩ :=
    exists_stalk_equiv_localization_chart_of_smooth f Z ε hz
  -- `F_ε = Z_z 𝒪_{B,ε} = (y_0, …, y_ρ) 𝒪_{B,ε}` is the maximal ideal, so `𝔮 = (y_ρ)`
  have hF : (chartCenter y ρ).map (Z.blowUpπ.stalkMap ε).hom =
      maximalIdeal (Z.blowUp.presheaf.stalk ε) := by
    rw [← hZy, ← stalkIdeal_comap Z Z.blowUpπ ε]
    exact hFε
  have hqeq :
      𝔮 = Ideal.span
        {algebraMap (X.presheaf.stalk (Z.blowUpπ ε)) (chartRing y ρ) (y ρ)} :=
    prime_eq_span_of_map_chartCenter_eq_maximalIdeal y hy hn' ρ 𝔮 hle _ e (fun c => he c) hF
  -- `𝔪_z ≤ 𝔮 ∩ 𝒪_{X,z} = (y_0, …, y_ρ) = Z_z`
  have hZz : Z.stalkIdeal (Z.blowUpπ ε) = maximalIdeal (X.presheaf.stalk
      (Z.blowUpπ ε)) := by
    refine le_antisymm ((mem_support_iff_stalkIdeal_le_maximalIdeal Z _).mp hz) ?_
    rw [hZy, ← comap_span_algebraMap_x_eq_chartCenter y hy hn' ρ, ← hqeq]
    exact hle
  have hr : ρ.val + 1 = n' :=
    val_add_one_eq_of_chartCenter_eq_maximalIdeal y hn' ρ (hZy.symm.trans hZz)
  exact ⟨hZz, n', y, ρ, hn', hy, hZy, 𝔮, h𝔮, hle, ⟨e, he⟩, hr, hqeq⟩

/-- The image under `π` of a generic point of the exceptional divisor is a generic point of the
centre — `Z_{π ε} = 𝔪_{π ε}` by the local computation
(`exists_chart_of_mem_genericPoints_exceptionalDivisor`), and a point of `V(Z)` where the stalk of
`Z` is the maximal ideal is a generic point (`mem_genericPoints_of_stalkIdeal_eq_maximalIdeal`). -/
theorem blowUpπ_mem_genericPoints_of_mem_genericPoints_exceptionalDivisor {ε : Z.blowUp}
    (hε : ε ∈ Z.exceptionalDivisor.support.genericPoints) :
    Z.blowUpπ ε ∈ Z.support.genericPoints :=
  mem_genericPoints_of_stalkIdeal_eq_maximalIdeal Z _
    (exists_chart_of_mem_genericPoints_exceptionalDivisor f n Z hZ hε).1

/-- The order along the exceptional divisor ([Kol07, Definition 47]: the order of `I` along `Z`
equals the multiplicity of `π^* I` along the exceptional divisor; here for a smooth centre of any
shape): at a generic point `ε` of the exceptional divisor, `ord_ε (π^* J) = ord_{π ε} J` — in the
chart at `z = π ε`, the centre is `𝔪_z` and `ε` is the prime `(y_ρ)` of the last coordinate
(`exists_chart_of_mem_genericPoints_exceptionalDivisor`), so this is
`ordAlong_span_algebraMap_x_map` transported through `𝒪_{B,ε} ≅ R'_{(y_ρ)}`. -/
theorem ord_comap_blowUpπ_of_mem_genericPoints_exceptionalDivisor (J : X.IdealSheafData)
    {ε : Z.blowUp} (hε : ε ∈ Z.exceptionalDivisor.support.genericPoints) :
    (J.comap Z.blowUpπ).ord ε = J.ord (Z.blowUpπ ε) := by
  obtain ⟨-, n', y, ρ, hn', hy, -, 𝔮, h𝔮, -, ⟨e, he⟩, hr, hqeq⟩ :=
    exists_chart_of_mem_genericPoints_exceptionalDivisor f n Z hZ hε
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg : IsRegularLocalRing (X.presheaf.stalk (Z.blowUpπ ε)) :=
    isRegularLocalRing_stalk f _
  have hcomp : (e : Z.blowUp.presheaf.stalk ε →+* Localization.AtPrime 𝔮).comp
        (Z.blowUpπ.stalkMap ε).hom =
      (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)).comp
        (algebraMap (X.presheaf.stalk (Z.blowUpπ ε)) (chartRing y ρ)) :=
    RingHom.ext fun c => he c
  subst hqeq
  rw [ord_eq_ord_stalkIdeal, ord_eq_ord_stalkIdeal, stalkIdeal_comap,
    ← ord_map_ringEquiv e, Ideal.map_map, hcomp, ← Ideal.map_map,
    ← ordAlong_span_algebraMap_x_map y hy hn' ρ hr (J.stalkIdeal (Z.blowUpπ ε))]
  rfl

/-- The weak transform ([Kol07, 58], formula (58.1), read against [Kol07, Definition 60]; for a
smooth centre of any shape): if `J` has order exactly `d` at every generic point of the centre, its
weak transform has order `0` at every generic point `ε` of the exceptional divisor — the weak
transform is the marked transform `(π^* J : F^d)` (`weakTransform_eq_markedTransform_of_smooth`);
at `ε`, `F_ε = 𝔪_ε = (a)` and `π^* J` has order `d` by the two previous lemmas, so
`(π^* J)_ε ⊆ (a)^d` and the colon `((π^* J)_ε : a^d)` is the unit ideal
(`colon_span_singleton_pow_eq_top_of_ord_le`, the order being multiplicative on the regular local
ring `𝒪_{B,ε}` containing `ℚ`). -/
theorem ord_weakTransform_eq_zero_of_mem_genericPoints_exceptionalDivisor {J : X.IdealSheafData}
    {d : ℕ} (hJ : J.OrdAlongEq Z.support (d : ℕ∞)) {ε : Z.blowUp}
    (hε : ε ∈ Z.exceptionalDivisor.support.genericPoints) :
    (J.weakTransform Z).ord ε = 0 := by
  have := hZ
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : Smooth (Z.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth f n Z
  have hreg : IsRegularLocalRing (Z.blowUp.presheaf.stalk ε) :=
    isRegularLocalRing_stalk (Z.blowUpπ ≫ f) ε
  let _ := (Z.blowUpπ ≫ f).stalkAlgebraRat ε
  have hz : Z.blowUpπ ε ∈ Z.support.genericPoints :=
    blowUpπ_mem_genericPoints_of_mem_genericPoints_exceptionalDivisor f n Z hZ hε
  have hord : IsLocalRing.ord ((J.comap Z.blowUpπ).stalkIdeal ε) = d := by
    rw [← ord_eq_ord_stalkIdeal,
      ord_comap_blowUpπ_of_mem_genericPoints_exceptionalDivisor f n Z hZ J hε]
    exact hJ _ hz
  have hFε := stalkIdeal_exceptionalDivisor_eq_maximalIdeal_of_mem_genericPoints f n Z hZ hε
  obtain ⟨a, ha, -, hFa⟩ := (isSmoothDivisor_exceptionalDivisor_of_smooth f n Z).2 ε hε.1
  have hst : (J.markedTransform Z d).stalkIdeal ε =
      ((J.comap Z.blowUpπ).stalkIdeal ε).colon
        ((Z.exceptionalDivisor.stalkIdeal ε ^ d : Ideal _) : Set _) := by
    have hinv : (Z.exceptionalDivisor ^ d).IsInvertible :=
      isInvertible_pow (blowUp.isInvertible_comap_π Z) d
    rw [markedTransform, controlledTransformAlong,
      stalkIdeal_colon_of_isInvertible _ hinv, stalkIdeal_pow]
  rw [weakTransform_eq_markedTransform_of_smooth f n Z J hJ, ord_eq_ord_stalkIdeal, hst, hFa,
    colon_span_singleton_pow_eq_top_of_ord_le
      (ordElem_mul_of_algebraRat _) ha ?_ hord.le, IsLocalRing.ord_top]
  rw [← hFa, hFε]
  exact IsLocalRing.le_ord_iff.mp hord.ge

end Smooth

/-! ### (W3): the strict transform of a divisor on which the ideal vanishes generically -/

/-- If `J` has order `0` at every generic point of `V(D)`, its weak transform has order `0` at
every generic point `ε` of the strict transform of `D` — no smoothness or order hypothesis is
needed. The support of the strict transform is the union of the strict transforms of the closures
of the generic points `ξ` of `V(D)` (`coe_support_strictTransform_biUnion`); `ε` lies in one of
them, `ξ ∉ V(Z)` (else that strict transform is empty), the generic point `ξ'` of the strict
transform of `closure {ξ}` maps to `ξ`
(`exists_isGenericPoint_strictTransformSeq_and_isIso_of_le_firstCenterIndex` for the one-step
sequence) and specializes to `ε`, so `ξ' = ε`, `π ε = ξ ∉ V(Z)`, `ε ∉ F`, and `π` is a local
isomorphism at `ε` (`ord_weakTransform_of_notMem`). -/
theorem ord_weakTransform_eq_zero_of_mem_genericPoints_strictTransform [IsNoetherian X]
    (Z : X.IdealSheafData) {J : X.IdealSheafData} (D : X.IdealSheafData)
    (hJD : ∀ ξ ∈ D.support.genericPoints, J.ord ξ = 0) {ε : Z.blowUp}
    (hε : ε ∈ (D.strictTransform Z).support.genericPoints) :
    (J.weakTransform Z).ord ε = 0 := by
  classical
  have hfin := TopologicalSpace.Closeds.genericPoints_finite D.support
  have hD : (D.support : Set X) =
      ⋃ ξ ∈ D.support.genericPoints, ((vanishingIdeal (Closeds.closure {ξ})).support : Set X) := by
    rw [coe_closeds_eq_iUnion_closure_genericPoints D.support]
    refine Set.iUnion₂_congr fun ξ _ => ?_
    rw [support_vanishingIdeal_eq, Closeds.coe_closure]
  have hbi := coe_support_strictTransform_biUnion Z _ hfin
    (fun ξ => vanishingIdeal (Closeds.closure {ξ})) D hD
  have hεmem : ε ∈ ((D.strictTransform Z).support : Set Z.blowUp) := hε.1
  rw [hbi] at hεmem
  obtain ⟨ξ, hξ, hεξ⟩ := Set.mem_iUnion₂.mp hεmem
  -- `ξ ∉ Z`: otherwise the strict transform of its closure is empty
  have hξZ : ξ ∉ Z.support := by
    intro hξZ
    have hsub : (Closeds.closure {ξ} : Set X) ⊆ Z.support :=
      Z.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξZ)
    have h0 : (((vanishingIdeal (Closeds.closure {ξ})).strictTransform Z).support :
        Set Z.blowUp) = ∅ := by
      rw [coe_support_strictTransform, support_vanishingIdeal_eq]
      have hdiff : (Z.blowUpπ ⁻¹' (Closeds.closure {ξ} : Set X)) \
          (Z.blowUpπ ⁻¹' (Z.support : Set X)) = ∅ := by
        rw [Set.sdiff_eq_empty]
        exact Set.preimage_mono hsub
      rw [hdiff, closure_empty]
    rw [h0] at hεξ
    exact hεξ
  -- the generic lift along the one-step sequence
  set S₁ : BlowUpSequence X := cons X Z (nil Z.blowUp) with hS₁
  have hint := isIntegral_subscheme_vanishingIdeal_closure ξ
  have hgen := isGenericPoint_support_vanishingIdeal_closure ξ
  have hnot : ∀ m < 1, ¬ CenterContains S₁ (vanishingIdeal (Closeds.closure {ξ})) m := by
    intro m hm hcont
    obtain ⟨hlt, hle⟩ := hcont
    have hm0 : m = 0 := by omega
    subst hm0
    have hle' : Z ≤ vanishingIdeal (Closeds.closure {ξ}) := hle
    apply hξZ
    refine support_antitone hle' ?_
    rw [support_vanishingIdeal_eq]
    exact subset_closure (Set.mem_singleton ξ)
  have hfirst : 1 ≤ firstCenterIndex S₁ (vanishingIdeal (Closeds.closure {ξ})) :=
    le_firstCenterIndex_of_forall_lt_not S₁ _ le_rfl hnot
  obtain ⟨ξ', hξ'gen, hξ'map, -, -, -⟩ :=
    exists_isGenericPoint_strictTransformSeq_and_isIso_of_le_firstCenterIndex S₁
      (vanishingIdeal (Closeds.closure {ξ})) hgen ⟨1, Nat.one_lt_two⟩ hfirst
  change IsGenericPoint ξ' (((vanishingIdeal (Closeds.closure {ξ})).strictTransform Z).support :
    Set Z.blowUp) at hξ'gen
  change (𝟙 Z.blowUp ≫ Z.blowUpπ) ξ' = ξ at hξ'map
  rw [Category.id_comp] at hξ'map
  have hsp : ξ' ⤳ ε := hξ'gen.specializes hεξ
  have hξ'big : ξ' ∈ (D.strictTransform Z).support := by
    change ξ' ∈ ((D.strictTransform Z).support : Set Z.blowUp)
    rw [hbi]
    exact Set.mem_iUnion₂.mpr ⟨ξ, hξ, hξ'gen.mem⟩
  have heq : ξ' = ε := hε.2 hξ'big hsp
  have hεmap : Z.blowUpπ ε = ξ := by
    rw [← heq]
    exact hξ'map
  have hεE : ε ∉ Z.exceptionalDivisor.support := by
    intro h
    rw [exceptionalDivisor, mem_support_comap_iff_apply, hεmap] at h
    exact hξZ h
  rw [ord_weakTransform_of_notMem Z J hεE, hεmap]
  exact hJD ξ hξ

end Hironaka.Resolution
