/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.RegDensityLemmas
public import Hironaka.Analytic.Rueckert.ZeroSet
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Hironaka.Algebra.Local.Regular
import Hironaka.Analytic.ConvSeries.Mul
import Hironaka.Analytic.ConvSeries.Rescale
import Hironaka.Analytic.Germ.CoordDiv
import Hironaka.Analytic.Rueckert.GraphIdeal
import Hironaka.Analytic.Rueckert.Hypersurface
import Hironaka.Analytic.Rueckert.UFD
import Hironaka.AnalyticSpace.RegularStalk
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Density of the simple points of a reduced complex space

The simple points of a reduced complex analytic space are dense [Fre17, II 5.13]: Hironaka's
remark that "if `X` is a reduced complex-analytic space, then the open subspace `V` is dense in
`X`" [Hir64, Introduction]. This file proves it (`dense_reg_of_isReduced_of_hyps`) from two
statements of the local parametrization theory of a prime germ, taken as explicit hypotheses
`h17a`, `h17c` and proved in `Hironaka/Analytic/Rueckert/ParametrizationPrimitive.lean`
(`exists_primitive_normalization`) and `ParametrizationGraph.lean` (`exists_graph_of_isPrime`); the
unconditional statement is `Manifold.dense_reg_of_isReduced_complex` of
`Hironaka/Manifold/FiniteSuccession/Restrict/LiftRegDense.lean`.

**The argument (Freitag's, with one change).** Let `x` be a point of a reduced complex space `X`,
not simple; `X|U ≅ (localModel V(f))|W` near `x`, `z` the image of `x`, and `I = (f)_z ⊆ 𝒪_n` the
ideal of the model at `z` read through the Taylor isomorphism. Because every stalk of `X` is
reduced, `(f)_{z'}` is radical at every point `z'` of `W` — Freitag spreads radicality from `z` by
Cartan's coherence theorem, which is therefore not needed. `I ≠ ⊤, ⊥` (`z` is a point, and
`𝒪_n/⊥ = 𝒪_n` is regular). Take a minimal prime `P` of `I` (finitely many) and a separating
series `h₀` in every other minimal prime but not in `P` (prime avoidance). The local
parametrization theorem gives a Noether normalization with a primitive fibre coordinate (`h17a`:
`Q`, `A`, `B_i`, in the coordinates of `σ = substEquiv L`, i.e. for `P' = comap σ P`) and the
graph structure of `V(P')` near every point `x'` off `A · Res(Q, Q')` (`h17c`). Rückert's
Nullstellensatz gives points `x'` of `V(P')` arbitrarily near `0` off
`g := (A · Res)(X ∘ e) · σ⁻¹ h₀` (`frequently_mem_zeroSet_and_ne_zero`). At such `x'`: (i)
`V(I') = V(P')` near `x'` (`I' = comap σ I`): every `F ∈ P'` has `F · σ⁻¹h₀ ∈ I'`
(`mul_mem_of_mem_minimalPrimes_of_forall_mem`), and `σ⁻¹h₀` does not vanish near `x'`; (ii)
`V(I')` is the translated point set of the model
(`eventually_forall_evalSeries_modelGens_eq_zero_iff`, `eventually_mem_zeroSet_image_symm_iff`),
so `z'` with `z'.1.1 = z.1.1 + L⁻¹ x'` is a point of the model, in `W` and in any prescribed
neighbourhood of `z` (`eventually_exists_localModel_pt`, `exists_mem_nhds_of_mem_opens_localModel`,
`exists_mem_nhds_of_mem_nhds_localModel_restrict`); (iii) the ideal `comap σ (f)_{z'}` has, near
`0`, the zero set of the graph ideal `J = (X_j − T_j(X ∘ e))_j` of the translated graph
(`eventually_graph_eq_zero_iff`), `J` is prime because `𝒪_n/J` is regular
(`isRegularLocalRing_quotient_graphIdeal`; a regular local ring is a domain), both are radical, so
Rückert identifies them (`eq_of_isRadical_of_zeroSet_eventuallyEq`) and `𝒪_n/(f)_{z'}` is regular
(`isRegularLocalRing_quotient_comap_iff`); (iv) the point of `X` under `z'` is simple
(`mem_reg_iff_isRegularLocalRing_quotient`) and lies in the prescribed neighbourhood of `x`
(`exists_regular_pt_of_hyps`, `dense_reg_of_isReduced_of_hyps`). The parametrization is that of
[GR84, Ch. 3–4]. Used by `Hironaka/Manifold/FiniteSuccession/Restrict/LiftRegDense.lean`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open Analytic Filter Topology
open MvPowerSeries Polynomial

universe u

noncomputable section

namespace Analytic

variable {n : ℕ}

/-- Translation of an eventual property at `0`: for `x'` near `0`, it holds at `x' + y'` for `y'`
near `0`. -/
theorem eventually_eventually_add_of_eventually {P : (Fin n → ℂ) → Prop}
    (h : ∀ᶠ w in 𝓝 (0 : Fin n → ℂ), P w) :
    ∀ᶠ x' in 𝓝 (0 : Fin n → ℂ), ∀ᶠ y' in 𝓝 (0 : Fin n → ℂ), P (x' + y') := by
  filter_upwards [h.eventually_nhds] with x' hx'
  have hc : Continuous fun y' : Fin n → ℂ => x' + y' := continuous_const.add continuous_id
  exact (hc.tendsto' 0 x' (add_zero _)).eventually hx'

end Analytic

namespace AnalyticSpace

open KLocallyRingedSpace

variable {n : ℕ} (G : Opens (Kn.{u} ℂ n)) {k : ℕ} (f : Fin k → AnalyticFun ℂ n G)

/-- The finite generating system of `(f)_z` in `Conv ℂ n`. -/
def modelGensFinset (z : localModel ℂ n G f) : Finset (Analytic.Conv ℂ n) := by
  classical exact Finset.univ.image (modelGens G f z)

/-- `modelGensFinset` generates `(f)_z`. -/
theorem span_modelGensFinset (z : localModel ℂ n G f) :
    Ideal.span ((modelGensFinset G f z : Finset (Analytic.Conv ℂ n)) : Set (Analytic.Conv ℂ n)) =
      modelIdealAt G f z := by
  classical
  unfold modelGensFinset
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, span_range_modelGens]

/-- The zero set of `modelGensFinset`. -/
theorem mem_zeroSet_modelGensFinset_iff (z : localModel ℂ n G f) (y' : Fin n → ℂ) :
    y' ∈ zeroSet (modelGensFinset G f z) ↔
      ∀ j, evalSeries (modelGens G f z j : MvPowerSeries (Fin n) ℂ) y' = 0 := by
  classical
  unfold modelGensFinset
  simp only [mem_zeroSet_iff, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h j
    exact h _ ⟨j, rfl⟩
  · rintro h _ ⟨j, rfl⟩
    exact h j

/-- The core of [Fre17, II 5.13] on a local model over `ℂ`, in the form the component clauses use:
at a point `z` of a model whose ideals are radical on an open `W ∋ z`, every nonzero minimal prime
`P` of `(f)_z` comes with a normalizing linear change of coordinates `L`, a generating system `S`
of `P' = comap σ P` and a series `g ∉ P'` such that every point `x'` of `V(P')` near `0` off `g`
is, in the original coordinates, a simple model point of `W` — given the local parametrization
theorem (the two statements `h17a`, `h17c` as hypotheses). -/
theorem eventually_regular_pt_of_minimalPrime
    (h17a : ∀ {n : ℕ} (P : Ideal (Analytic.Conv ℂ n)) [P.IsPrime], P ≠ ⊥ →
      ∃ (d : ℕ) (e : Fin d ↪ Fin n) (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)),
        Function.Injective (normMap ℂ P e L) ∧
        RingHom.Finite (A := Analytic.Conv ℂ d) (B := Analytic.Conv ℂ n ⧸ P)
          (normMap ℂ P e L : Analytic.Conv ℂ d →+* Analytic.Conv ℂ n ⧸ P) ∧
        ∃ (i₀ : Fin n) (_ : i₀ ∉ Set.range e) (Q : Polynomial (Analytic.Conv ℂ d))
            (A : Analytic.Conv ℂ d),
          Q.Monic ∧ Irreducible Q ∧ A ≠ 0 ∧
          (Q.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P ∧
          ∀ i, i ∉ Set.range e → ∃ B : Polynomial (Analytic.Conv ℂ d),
            convEmbed ℂ e A * convX ℂ i - (B.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈
              Ideal.comap (substEquiv L) P)
    (h17c : ∀ {n : ℕ} (P : Ideal (Analytic.Conv ℂ n)) [P.IsPrime] {d : ℕ} (e : Fin d ↪ Fin n)
      (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)), Function.Injective (normMap ℂ P e L) →
      RingHom.Finite (A := Analytic.Conv ℂ d) (B := Analytic.Conv ℂ n ⧸ P)
        (normMap ℂ P e L : Analytic.Conv ℂ d →+* Analytic.Conv ℂ n ⧸ P) →
      ∀ (i₀ : Fin n), i₀ ∉ Set.range e → ∀ (Q : Polynomial (Analytic.Conv ℂ d)),
          Q.Monic → Irreducible Q →
      (Q.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P →
      ∀ (A : Analytic.Conv ℂ d), A ≠ 0 → ∀ (B : Fin n → Polynomial (Analytic.Conv ℂ d)),
      (∀ i, i ∉ Set.range e → convEmbed ℂ e A * convX ℂ i -
        ((B i).map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P) →
      ∀ {S : Finset (Analytic.Conv ℂ n)},
      Ideal.span (S : Set (Analytic.Conv ℂ n)) = Ideal.comap (substEquiv L) P →
      ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), x ∈ zeroSet S →
        evalSeries ((A * resultant Q (derivative Q) : Analytic.Conv ℂ d) : MvPowerSeries (Fin d) ℂ)
            (x ∘ e)
          ≠ 0 →
        ∃ φ : (Fin d → ℂ) → (Fin n → ℂ), AnalyticAt ℂ φ (x ∘ e) ∧ φ (x ∘ e) = x ∧
          (∀ u, φ u ∘ e = u) ∧ ∀ᶠ y in 𝓝 x, (y ∈ zeroSet S ↔ y = φ (y ∘ e)))
    {W : Opens (localModel ℂ n G f)} {z : localModel ℂ n G f} (hzW : z ∈ W)
    (hrad : ∀ z' ∈ W, (modelIdealAt G f z').IsRadical)
    {P : Ideal (Analytic.Conv ℂ n)} (hP : P ∈ (modelIdealAt G f z).minimalPrimes) (hPbot : P ≠ ⊥) :
    ∃ (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) (S : Finset (Analytic.Conv ℂ n)) (g : Analytic.Conv ℂ n),
      Ideal.span (S : Set (Analytic.Conv ℂ n)) = Ideal.comap (substEquiv L) P ∧
      g ∉ Ideal.comap (substEquiv L) P ∧
      ∀ᶠ x' in 𝓝 (0 : Fin n → ℂ), x' ∈ zeroSet S →
        evalSeries (g : MvPowerSeries (Fin n) ℂ) x' ≠ 0 →
        ∃ z' : localModel ℂ n G f, z'.1.1 = ULift.up (z.1.1.down + L.symm x') ∧ z' ∈ W ∧
          IsRegularLocalRing (Analytic.Conv ℂ n ⧸ modelIdealAt G f z') := by
  classical
  set I := modelIdealAt G f z with hI
  have hIrad : I.IsRadical := hrad z hzW
  have hPprime : P.IsPrime := hP.1.1
  have hIP : I ≤ P := hP.1.2
  obtain ⟨h₀, hh₀Q, hh₀P⟩ := exists_mem_forall_minimalPrimes_ne_of_mem_minimalPrimes hP
  obtain ⟨d, e, L, hinj, hfin, i₀, hi₀, Q, A, hQ, hQirr, hA, hQP, hB⟩ := h17a P hPbot
  choose! B hB using hB
  set σ := substEquiv L with hσ
  set P' := Ideal.comap σ P with hP'
  have hP'prime : P'.IsPrime := Ideal.comap_isPrime σ P
  obtain ⟨S, hS⟩ := exists_finset_span_eq P'
  have hgraph := h17c P e L hinj hfin i₀ hi₀ Q hQ hQirr hQP A hA B hB hS
  -- the separating series in the coordinates of σ
  set h₀' := σ.symm h₀ with hh₀'
  have hh₀'P' : h₀' ∉ P' := by
    rw [hP', Ideal.mem_comap, hh₀', AlgEquiv.apply_symm_apply]
    exact hh₀P
  set c := A * resultant Q (derivative Q) with hc_def
  have hc : c ≠ 0 :=
    mul_ne_zero hA (resultant_derivative_ne_zero_of_squarefree hQ hQirr.squarefree)
  have hcP' : convEmbed ℂ e c ∉ P' := by
    intro hmem
    apply hc
    apply hinj
    rw [map_zero, normMap_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [hP', Ideal.mem_comap] at hmem
    exact hmem
  set g := convEmbed ℂ e c * h₀' with hg_def
  have hg : g ∉ P' := fun h => (hP'prime.mul_mem_iff_mem_or_mem.mp h).elim hcP' hh₀'P'
  have hfreq := frequently_mem_zeroSet_and_ne_zero hS hg
  -- the ideal `I` in the coordinates of σ and its zero set
  set SI := (modelGensFinset G f z).image σ.symm with hSI_def
  have hSI : Ideal.span (SI : Set (Analytic.Conv ℂ n)) = Ideal.comap σ I := by
    rw [hSI_def, span_image_symm, span_modelGensFinset]
  have hI'P' : Ideal.span (SI : Set (Analytic.Conv ℂ n)) ≤ Ideal.span (S : Set
      (Analytic.Conv ℂ n)) := by
    rw [hSI, hS]
    exact Ideal.comap_mono hIP
  -- (ii): off `h₀'`, the zero set of `I'` is the zero set of `P'`
  have hii : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), y ∈ zeroSet SI →
      evalSeries (h₀' : MvPowerSeries (Fin n) ℂ) y ≠ 0 → y ∈ zeroSet S := by
    have hF : ∀ F ∈ S, F * h₀' ∈ Ideal.span (SI : Set (Analytic.Conv ℂ n)) := by
      intro F hF
      rw [hSI, Ideal.mem_comap, map_mul, hh₀', AlgEquiv.apply_symm_apply]
      have hFP : σ F ∈ P := by
        have : F ∈ P' := hS ▸ Ideal.subset_span hF
        rwa [hP', Ideal.mem_comap] at this
      exact mul_mem_of_mem_minimalPrimes_of_forall_mem hIrad hP hh₀Q hFP
    have h1 : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ∀ F ∈ S,
        (y ∈ zeroSet SI → evalSeries ((F * h₀' : Analytic.Conv ℂ n) : MvPowerSeries
            (Fin n) ℂ) y = 0) ∧
        evalSeries ((F * h₀' : Analytic.Conv ℂ n) : MvPowerSeries (Fin n) ℂ) y =
          evalSeries (F : MvPowerSeries (Fin n) ℂ) y *
            evalSeries (h₀' : MvPowerSeries (Fin n) ℂ) y := by
      rw [eventually_all_finset]
      intro F hFS
      exact (VanishesOn.of_mem_span (hF F hFS)).and (evalSeries_conv_mul_eventually F h₀')
    filter_upwards [h1] with y hy hySI hyh
    intro F hFS
    obtain ⟨hv, hm⟩ := hy F hFS
    have := hv hySI
    rw [hm] at this
    exact (mul_eq_zero.mp this).resolve_right hyh
  -- (iii): the zero set of `I'` near `0` is the translated model
  have hSIiff := eventually_mem_zeroSet_image_symm_iff L (modelGensFinset G f z)
  have hiii : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), (y ∈ zeroSet SI ↔
      ∀ j, extendSection ℂ (Kn.{u} ℂ n) (f j) (ULift.up (z.1.1.down + L.symm y)) = 0) := by
    have h2 := (tendsto_clequiv_zero L.symm).eventually
      (eventually_forall_evalSeries_modelGens_eq_zero_iff G f z)
    filter_upwards [hSIiff, h2] with y hy1 hy2
    rw [hSI_def, hy1, mem_zeroSet_modelGensFinset_iff]
    exact hy2
  -- (iv) continuity of `h₀'` off its zero set
  obtain ⟨ρh, hρh⟩ := h₀'.2
  have hiv : ∀ᶠ x' in 𝓝 (0 : Fin n → ℂ), evalSeries (h₀' : MvPowerSeries (Fin n) ℂ) x' ≠ 0 →
      ∀ᶠ y in 𝓝 x', evalSeries (h₀' : MvPowerSeries (Fin n) ℂ) y ≠ 0 := by
    have hpoly : ∀ᶠ x' in 𝓝 (0 : Fin n → ℂ), x' ∈ polydisc ℂ ρh :=
      (isOpen_polydisc ρh).mem_nhds fun k => by simpa using ρh.pos k
    filter_upwards [hpoly] with x' hx' hne
    exact ((analyticOnNhd_evalSeries hρh x' hx').continuousAt).eventually_ne hne
  -- (v) the model point over `L.symm x'` and the two neighbourhoods
  have hmodel := (tendsto_clequiv_zero L.symm).eventually (eventually_exists_localModel_pt G f z)
  obtain ⟨OW, hOW, hOWsub⟩ := exists_mem_nhds_of_mem_opens_localModel G f hzW
  have hpt : Tendsto (fun x' : Fin n → ℂ => (ULift.up (z.1.1.down + L.symm x') : Kn.{u} ℂ n))
      (𝓝 0) (𝓝 z.1.1) := by
    have hc : Continuous fun x' : Fin n → ℂ =>
        (ULift.up (z.1.1.down + L.symm x') : Kn.{u} ℂ n) :=
      (ContinuousLinearEquiv.ulift : Kn.{u} ℂ n ≃L[ℂ] (Fin n → ℂ)).symm.continuous.comp
        (continuous_const.add L.symm.continuous)
    exact hc.tendsto' 0 z.1.1 (ULift.ext (by simp))
  have hOW' := hpt.eventually hOW
  have hSle := eventually_mem_zeroSet_of_span_le hI'P'
  have hmulg := evalSeries_conv_mul_eventually (convEmbed ℂ e c) h₀'
  -- the translated eventualities
  have hii' := eventually_eventually_add_of_eventually hii
  have hiii' := eventually_eventually_add_of_eventually hiii
  have hSle' := eventually_eventually_add_of_eventually hSle
  have hSIiff' := eventually_eventually_add_of_eventually hSIiff
  refine ⟨L, S, g, hS, hg, ?_⟩
  have hall := hiv.and (hmodel.and (hOW'.and (hSle.and (hmulg.and (hSIiff.and (hiii.and
    (hii'.and (hiii'.and (hSle'.and hSIiff')))))))))
  filter_upwards [hgraph, hall] with x' hgr ⟨hiv', hmod, hOWx, hSlex, hmulgx, hSIx, hiiix, hii'x,
    hiii'x, hSle'x, hSIiff'x⟩ hxS hgx
  -- the two factors of `g` at `x'`
  rw [hmulgx] at hgx
  have hcx : evalSeries (c : MvPowerSeries (Fin d) ℂ) (x' ∘ e) ≠ 0 := by
    intro h0
    apply hgx
    rw [evalSeries_convEmbed, h0, zero_mul]
  have hhx : evalSeries (h₀' : MvPowerSeries (Fin n) ℂ) x' ≠ 0 := fun h0 =>
    hgx (by rw [h0, mul_zero])
  obtain ⟨φ, hφan, hφx, hφe, hφgraph⟩ := hgr hxS hcx
  -- the model point `z'` over `L.symm x'`
  have hxSI : x' ∈ zeroSet SI := hSlex hxS
  have hxmg : L.symm x' ∈ zeroSet (modelGensFinset G f z) := by
    rw [hSI_def] at hxSI
    exact hSIx.mp hxSI
  obtain ⟨z', hz'⟩ := hmod ((mem_zeroSet_modelGensFinset_iff G f z _).mp hxmg)
  have hz'W : z' ∈ W := hOWsub z' (by rw [hz']; exact hOWx)
  refine ⟨z', hz', hz'W, ?_⟩
  -- regularity at `z'`: the Taylor series of the graph
  have hIprad : (modelIdealAt G f z').IsRadical := hrad z' hz'W
  have hφj : ∀ j : Fin n, AnalyticAt ℂ (fun u => φ u j - x' j) (x' ∘ e) := fun j =>
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).analyticAt _).comp
      hφan).sub analyticAt_const
  choose T hT using fun j => exists_conv_eventuallyEq_shift (hφj j)
  have hT0 : ∀ j, j ∉ Set.range e → constantCoeff (T j : MvPowerSeries (Fin d) ℂ) = 0 := by
    intro j _
    have := (hT j).self_of_nhds
    rw [add_zero, hφx, sub_self, evalSeries_zero_eq] at this
    exact this.symm
  have hJreg := isRegularLocalRing_quotient_graphIdeal e T hT0
  have hJprime : (Ideal.span (Set.range fun j : {j : Fin n // j ∉ Set.range e} =>
      convX ℂ j - convEmbed ℂ e (T j))).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp
      (@IsLocalRing.isDomain_of_isRegularLocalRing _ _ hJreg)
  obtain ⟨SJ, hSJ_def⟩ : ∃ SJ : Finset (Analytic.Conv ℂ n), SJ = Finset.univ.image
      fun j : {j : Fin n // j ∉ Set.range e} => convX ℂ j - convEmbed ℂ e (T j) := ⟨_, rfl⟩
  have hSJ : Ideal.span (SJ : Set (Analytic.Conv ℂ n)) = Ideal.span (Set.range
      fun j : {j : Fin n // j ∉ Set.range e} => convX ℂ j - convEmbed ℂ e (T j)) := by
    rw [hSJ_def, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hJzero : ∀ᶠ y' in 𝓝 (0 : Fin n → ℂ), (y' ∈ zeroSet SJ ↔ x' + y' = φ ((x' + y') ∘ e)) := by
    filter_upwards [eventually_graph_eq_zero_iff e φ x' hφe T (fun j _ => hT j)] with y' hy'
    rw [← hy', hSJ_def]
    simp only [mem_zeroSet_iff, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro h j hj
      exact h _ ⟨⟨j, hj⟩, rfl⟩
    · rintro h _ ⟨⟨j, hj⟩, rfl⟩
      exact h j hj
  -- the ideal at `z'` in the coordinates of σ has the same zero set
  obtain ⟨SIp, hSIp_def⟩ : ∃ SIp : Finset (Analytic.Conv ℂ n),
      SIp = (modelGensFinset G f z').image (substEquiv L).symm := ⟨_, rfl⟩
  have hSIp : Ideal.span (SIp : Set (Analytic.Conv ℂ n)) =
      Ideal.comap (substEquiv L) (modelIdealAt G f z') := by
    rw [hSIp_def, span_image_symm, span_modelGensFinset]
  have hp_down : z'.1.1.down = z.1.1.down + L.symm x' := by rw [hz']
  have hIpzero : ∀ᶠ y' in 𝓝 (0 : Fin n → ℂ),
      (y' ∈ zeroSet SIp ↔ x' + y' = φ ((x' + y') ∘ e)) := by
    have h1 := eventually_mem_zeroSet_image_symm_iff L (modelGensFinset G f z')
    have h2 := (tendsto_clequiv_zero L.symm).eventually
      (eventually_forall_evalSeries_modelGens_eq_zero_iff G f z')
    have h3 : Tendsto (fun y' : Fin n → ℂ => x' + y') (𝓝 0) (𝓝 x') :=
      (continuous_const.add continuous_id).tendsto' 0 x' (add_zero _)
    filter_upwards [h1, h2, h3.eventually hφgraph, h3.eventually (hiv' hhx), hii'x, hiii'x,
      hSle'x] with y' hy1 hy2 hy4 hy5 hy6 hy7 hy8
    rw [hSIp_def, hy1, mem_zeroSet_modelGensFinset_iff, hy2]
    have hpt' : (ULift.up (z'.1.1.down + L.symm y') : Kn.{u} ℂ n) =
        ULift.up (z.1.1.down + L.symm (x' + y')) := by
      rw [hp_down, map_add, add_assoc]
    rw [hpt', ← hy7, ← hy4]
    exact ⟨fun h => hy6 h hy5, fun h => hy8 h⟩
  have hIpJ : Ideal.comap (substEquiv L) (modelIdealAt G f z') = Ideal.span (Set.range
      fun j : {j : Fin n // j ∉ Set.range e} => convX ℂ j - convEmbed ℂ e (T j)) :=
    eq_of_isRadical_of_zeroSet_eventuallyEq (hIprad.comap _) hJprime.isRadical hSIp hSJ
      (by filter_upwards [hIpzero, hJzero] with y' h1 h2; rw [h1, h2])
  exact (isRegularLocalRing_quotient_comap_iff (substEquiv L) _).mp (by rw [hIpJ]; exact hJreg)

/-- The core of [Fre17, II 5.13] on a local model over `ℂ`: near a non-simple point `z` of a model
whose ideals are radical on an open `W ∋ z`, there are points of `W` with regular `𝒪_n/(f)_{z'}` in
every neighbourhood of `z` in `(localModel)|W` — given the local parametrization theorem (`h17a`,
`h17c` as hypotheses). -/
theorem exists_regular_pt_of_hyps
    (h17a : ∀ {n : ℕ} (P : Ideal (Analytic.Conv ℂ n)) [P.IsPrime], P ≠ ⊥ →
      ∃ (d : ℕ) (e : Fin d ↪ Fin n) (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)),
        Function.Injective (normMap ℂ P e L) ∧
        RingHom.Finite (A := Analytic.Conv ℂ d) (B := Analytic.Conv ℂ n ⧸ P)
          (normMap ℂ P e L : Analytic.Conv ℂ d →+* Analytic.Conv ℂ n ⧸ P) ∧
        ∃ (i₀ : Fin n) (_ : i₀ ∉ Set.range e) (Q : Polynomial (Analytic.Conv ℂ d))
            (A : Analytic.Conv ℂ d),
          Q.Monic ∧ Irreducible Q ∧ A ≠ 0 ∧
          (Q.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P ∧
          ∀ i, i ∉ Set.range e → ∃ B : Polynomial (Analytic.Conv ℂ d),
            convEmbed ℂ e A * convX ℂ i - (B.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈
              Ideal.comap (substEquiv L) P)
    (h17c : ∀ {n : ℕ} (P : Ideal (Analytic.Conv ℂ n)) [P.IsPrime] {d : ℕ} (e : Fin d ↪ Fin n)
      (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)), Function.Injective (normMap ℂ P e L) →
      RingHom.Finite (A := Analytic.Conv ℂ d) (B := Analytic.Conv ℂ n ⧸ P)
        (normMap ℂ P e L : Analytic.Conv ℂ d →+* Analytic.Conv ℂ n ⧸ P) →
      ∀ (i₀ : Fin n), i₀ ∉ Set.range e → ∀ (Q : Polynomial (Analytic.Conv ℂ d)),
          Q.Monic → Irreducible Q →
      (Q.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P →
      ∀ (A : Analytic.Conv ℂ d), A ≠ 0 → ∀ (B : Fin n → Polynomial (Analytic.Conv ℂ d)),
      (∀ i, i ∉ Set.range e → convEmbed ℂ e A * convX ℂ i -
        ((B i).map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P) →
      ∀ {S : Finset (Analytic.Conv ℂ n)},
      Ideal.span (S : Set (Analytic.Conv ℂ n)) = Ideal.comap (substEquiv L) P →
      ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), x ∈ zeroSet S →
        evalSeries ((A * resultant Q (derivative Q) : Analytic.Conv ℂ d) : MvPowerSeries (Fin d) ℂ)
            (x ∘ e)
          ≠ 0 →
        ∃ φ : (Fin d → ℂ) → (Fin n → ℂ), AnalyticAt ℂ φ (x ∘ e) ∧ φ (x ∘ e) = x ∧
          (∀ u, φ u ∘ e = u) ∧ ∀ᶠ y in 𝓝 x, (y ∈ zeroSet S ↔ y = φ (y ∘ e)))
    {W : Opens (localModel ℂ n G f)} {z : localModel ℂ n G f} (hzW : z ∈ W)
    (hrad : ∀ z' ∈ W, (modelIdealAt G f z').IsRadical)
    (hz : ¬ IsRegularLocalRing (Analytic.Conv ℂ n ⧸ modelIdealAt G f z))
    {N : Set ((localModel ℂ n G f).restrictOpen W)}
    (hN : N ∈ 𝓝 (⟨z, hzW⟩ : (localModel ℂ n G f).restrictOpen W)) :
    ∃ (z' : localModel ℂ n G f) (hz' : z' ∈ W),
      (⟨z', hz'⟩ : (localModel ℂ n G f).restrictOpen W) ∈ N ∧
        IsRegularLocalRing (Analytic.Conv ℂ n ⧸ modelIdealAt G f z') := by
  classical
  set I := modelIdealAt G f z with hI
  have hItop : I ≠ ⊤ := modelIdealAt_ne_top G f z
  have hIbot : I ≠ ⊥ := by
    intro hbot
    apply hz
    have hreg : IsRegularLocalRing (Analytic.Conv ℂ n) :=
      @IsRegularLocalRing.of_ringEquiv _ _ (isRegularLocalRing_stalk_affine ℂ n (ULift.up 0)) _ _
        (taylorAffine.{0} ℂ n (ULift.up 0))
    rw [hbot]
    exact @IsRegularLocalRing.of_ringEquiv _ _ hreg _ _ (RingEquiv.quotientBot
        (Analytic.Conv ℂ n)).symm
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_minimalPrimes hItop
  have hIP : I ≤ P := hP.1.2
  have hPbot : P ≠ ⊥ := fun h => hIbot (le_bot_iff.mp (h ▸ hIP))
  obtain ⟨L, S, g, hS, hg, hev⟩ :=
    eventually_regular_pt_of_minimalPrime G f h17a h17c hzW hrad hP hPbot
  have hPp : P.IsPrime := hP.1.1
  have : (Ideal.comap (substEquiv L) P).IsPrime := Ideal.comap_isPrime (substEquiv L) P
  have hfreq := frequently_mem_zeroSet_and_ne_zero hS hg
  obtain ⟨ON, hON, hONsub⟩ := exists_mem_nhds_of_mem_nhds_localModel_restrict G f hzW hN
  have hpt : Tendsto (fun x' : Fin n → ℂ => (ULift.up (z.1.1.down + L.symm x') : Kn.{u} ℂ n))
      (𝓝 0) (𝓝 z.1.1) := by
    have hc : Continuous fun x' : Fin n → ℂ =>
        (ULift.up (z.1.1.down + L.symm x') : Kn.{u} ℂ n) :=
      (ContinuousLinearEquiv.ulift : Kn.{u} ℂ n ≃L[ℂ] (Fin n → ℂ)).symm.continuous.comp
        (continuous_const.add L.symm.continuous)
    exact hc.tendsto' 0 z.1.1 (ULift.ext (by simp))
  obtain ⟨x', ⟨hev', hONx⟩, hxS, hgx⟩ :=
    ((hev.and (hpt.eventually hON)).and_frequently hfreq).exists
  obtain ⟨z', hz', hz'W, hreg⟩ := hev' hxS hgx
  exact ⟨z', hz'W, hONsub z' hz'W (by rw [hz']; exact hONx), hreg⟩

/-- **The simple points of a reduced complex analytic space are dense** [Fre17, II 5.13],
[Hir64, Introduction] — given the local parametrization theorem (`h17a`, `h17c` as hypotheses);
unconditionally, `Manifold.dense_reg_of_isReduced_complex` of
`Hironaka/Manifold/FiniteSuccession/Restrict/LiftRegDense.lean`. -/
theorem dense_reg_of_isReduced_of_hyps (X : AnalyticSpace.{u} ℂ) (hX : X.IsReduced)
    (h17a : ∀ {n : ℕ} (P : Ideal (Analytic.Conv ℂ n)) [P.IsPrime], P ≠ ⊥ →
      ∃ (d : ℕ) (e : Fin d ↪ Fin n) (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)),
        Function.Injective (normMap ℂ P e L) ∧
        RingHom.Finite (A := Analytic.Conv ℂ d) (B := Analytic.Conv ℂ n ⧸ P)
          (normMap ℂ P e L : Analytic.Conv ℂ d →+* Analytic.Conv ℂ n ⧸ P) ∧
        ∃ (i₀ : Fin n) (_ : i₀ ∉ Set.range e) (Q : Polynomial (Analytic.Conv ℂ d))
            (A : Analytic.Conv ℂ d),
          Q.Monic ∧ Irreducible Q ∧ A ≠ 0 ∧
          (Q.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P ∧
          ∀ i, i ∉ Set.range e → ∃ B : Polynomial (Analytic.Conv ℂ d),
            convEmbed ℂ e A * convX ℂ i - (B.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈
              Ideal.comap (substEquiv L) P)
    (h17c : ∀ {n : ℕ} (P : Ideal (Analytic.Conv ℂ n)) [P.IsPrime] {d : ℕ} (e : Fin d ↪ Fin n)
      (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)), Function.Injective (normMap ℂ P e L) →
      RingHom.Finite (A := Analytic.Conv ℂ d) (B := Analytic.Conv ℂ n ⧸ P)
        (normMap ℂ P e L : Analytic.Conv ℂ d →+* Analytic.Conv ℂ n ⧸ P) →
      ∀ (i₀ : Fin n), i₀ ∉ Set.range e → ∀ (Q : Polynomial (Analytic.Conv ℂ d)),
          Q.Monic → Irreducible Q →
      (Q.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P →
      ∀ (A : Analytic.Conv ℂ d), A ≠ 0 → ∀ (B : Fin n → Polynomial (Analytic.Conv ℂ d)),
      (∀ i, i ∉ Set.range e → convEmbed ℂ e A * convX ℂ i -
        ((B i).map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P) →
      ∀ {S : Finset (Analytic.Conv ℂ n)},
      Ideal.span (S : Set (Analytic.Conv ℂ n)) = Ideal.comap (substEquiv L) P →
      ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), x ∈ zeroSet S →
        evalSeries ((A * resultant Q (derivative Q) : Analytic.Conv ℂ d) : MvPowerSeries (Fin d) ℂ)
            (x ∘ e)
          ≠ 0 →
        ∃ φ : (Fin d → ℂ) → (Fin n → ℂ), AnalyticAt ℂ φ (x ∘ e) ∧ φ (x ∘ e) = x ∧
          (∀ u, φ u ∘ e = u) ∧ ∀ᶠ y in 𝓝 x, (y ∈ zeroSet S ↔ y = φ (y ∘ e)))
    : Dense (regularLocus X) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  rw [mem_closure_iff_nhds]
  intro t ht
  by_cases hx : x ∈ regularLocus X
  · exact ⟨x, mem_of_mem_nhds ht, hx⟩
  obtain ⟨U, hxU, n, k, G, f, W, ⟨e⟩⟩ := X.locallyModel x
  let ψ := KIso.homeomorph e
  have hψ : ∀ a, ψ a = e.hom.1.base a := fun _ => rfl
  set w : (localModel ℂ n G f).restrictOpen W := e.hom.1.base ⟨x, hxU⟩ with hw
  have hz : ¬ IsRegularLocalRing (Analytic.Conv ℂ n ⧸ modelIdealAt G f w.1) := by
    rwa [mem_reg_iff_isRegularLocalRing_quotient e hxU] at hx
  have hrad : ∀ z' ∈ W, (modelIdealAt G f z').IsRadical := by
    intro z' hz'
    have h1 := isRadical_modelIdealAt_of_isReduced hX e (ψ.symm ⟨z', hz'⟩).2
    have h2 : e.hom.1.base ⟨(ψ.symm ⟨z', hz'⟩).1, (ψ.symm ⟨z', hz'⟩).2⟩ = ⟨z', hz'⟩ := by
      change ψ (ψ.symm ⟨z', hz'⟩) = ⟨z', hz'⟩
      exact ψ.apply_symm_apply _
    rw [h2] at h1
    exact h1
  have hcont : Continuous fun z : (localModel ℂ n G f).restrictOpen W => (ψ.symm z).1 :=
    continuous_subtype_val.comp ψ.symm.continuous
  have hwx : (ψ.symm w).1 = x := by
    change (ψ.symm (ψ ⟨x, hxU⟩)).1 = x
    exact congrArg (fun a => a.1) (ψ.symm_apply_apply ⟨x, hxU⟩)
  have hN : (fun z : (localModel ℂ n G f).restrictOpen W => (ψ.symm z).1) ⁻¹' t ∈ 𝓝 w := by
    apply hcont.continuousAt.preimage_mem_nhds
    rw [hwx]
    exact ht
  obtain ⟨z', hz'W, hz'N, hreg⟩ := exists_regular_pt_of_hyps G f h17a h17c w.2 hrad hz hN
  refine ⟨(ψ.symm ⟨z', hz'W⟩).1, hz'N, ?_⟩
  rw [mem_reg_iff_isRegularLocalRing_quotient e (ψ.symm ⟨z', hz'W⟩).2]
  have h2 : e.hom.1.base ⟨(ψ.symm ⟨z', hz'W⟩).1, (ψ.symm ⟨z', hz'W⟩).2⟩ = ⟨z', hz'W⟩ := by
    change ψ (ψ.symm ⟨z', hz'W⟩) = ⟨z', hz'W⟩
    exact ψ.apply_symm_apply _
  rw [h2]
  exact hreg

end AnalyticSpace

end
