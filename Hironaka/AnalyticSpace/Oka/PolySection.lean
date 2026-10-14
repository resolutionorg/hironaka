/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Oka.Model
public import Hironaka.Analytic.Oka.DegLt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Polynomial sections in the distinguished coordinate over a product open

The third step of the proof of Oka's coherence theorem [Fre17, Ch. I, 10.3] writes the entries of
the matrix, after the preparation theorem, as Weierstrass polynomials in `z_n` "with coefficients
independent of `z_n`", and reads the relations of `z_n`-degree `< m` as vectors of
`𝒪(V)[z_n : m] ≅ 𝒪(V)^m`. On the model `Kᵐ⁺¹ = Kn K (m + 1)` with the distinguished coordinate `x_0`
and the projection `π : Kᵐ⁺¹ → Kᵐ` (`projKn`) this module provides, over the product open `π⁻¹ V`
(`baseOpens ψ V`):

* the coordinate sections `x0Sec`, the constant sections `cSec`, the shift
  `shiftSec V x₀ = x_0 − x₀`, and the pull-back `pullSec V w = w ∘ π` of a section `w` of the base,
  with their germs identified with the coordinate germs and the constants (`germ_x0Sec`,
  `germ_cSec`) and their Taylor series at every point `a` of `π⁻¹ V` (`TKn_germ_shiftSec`:
  `x_0 − x₀ ↦ X_0 − C (x₀ − a_0)`; `TKn_germ_pullSec`: `w ∘ π ↦ liftTail (T_{π a} w)`);
* the polynomial combinations `polyComb V x₀ w = Σ_k (w k ∘ π) (x_0 − x₀)^k` and the monic
  polynomial sections `polyMonic V x₀ e c = (x_0 − x₀)^e + Σ_j (c j ∘ π) (x_0 − x₀)^{e−1−j}` (the
  shape of a Weierstrass polynomial, `weierstrassPoly`), whose Taylor series at `a` are `ofPoly` of
  the corresponding polynomial over the tail ring composed with `X − C (x₀ − a_0)`
  (`TKn_germ_polyComb`, `TKn_germ_polyMonic`): a polynomial of `x_0`-degree `< N`, respectively
  monic of degree `e`, at every point of `π⁻¹ V`, which is why Oka's lemma applies pointwise with
  one degree bound;
* coefficient extraction: a polynomial combination has germ `0` at `a` iff all its coefficient
  sections have germ `0` at `π a` (`germ_polyComb_eq_zero_iff`), through the polynomial
  `polyOfCoeff c = Σ_k C (c k) X^k` with coefficient vector `c` over any commutative ring
  (`polyOfCoeff_eq_zero_iff`).

Every statement is bookkeeping for the induction of Oka's theorem
(`Hironaka.AnalyticSpace.Oka.Core`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Manifold
open Analytic
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace AnalyticSpace

section Algebra

variable {R : Type*} [CommRing R]

/-- `Σ_k C (c k) X^k`: the polynomial with coefficient vector `c` (degree `< N`). -/
def polyOfCoeff {N : ℕ} (c : Fin N → R) : Polynomial R :=
  ∑ k, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)

theorem coeff_polyOfCoeff {N : ℕ} (c : Fin N → R) (k : ℕ) :
    (polyOfCoeff c).coeff k = if h : k < N then c ⟨k, h⟩ else 0 := by
  unfold polyOfCoeff
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩
      (fun j _ hj => by rw [ite_eq_right (fun h' => hj (Fin.ext h'.symm))]) (by simp)]
    simp
  · exact Finset.sum_eq_zero fun j _ => by
      rw [ite_eq_right]
      intro h'
      exact h (by rw [h']; exact j.isLt)

theorem natDegree_polyOfCoeff_lt {N : ℕ} (c : Fin N → R) (hN : 0 < N) :
    (polyOfCoeff c).natDegree < N := by
  unfold polyOfCoeff
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun k _ => ?_)
    (Nat.sub_lt hN Nat.one_pos)
  have := k.isLt
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem polyOfCoeff_eq_zero_iff {N : ℕ} (c : Fin N → R) : polyOfCoeff c = 0 ↔ ∀ k, c k = 0 := by
  refine ⟨fun h k => ?_, fun h => by simp [polyOfCoeff, h]⟩
  simpa [coeff_polyOfCoeff] using congrArg (Polynomial.coeff · (k : ℕ)) h

end Algebra

variable {K : Type} [RCLike K]

section Sections

variable {n : ℕ} (ψ : Kn.{u} K n ≃L[K] (Fin n → K))

/-- The coordinate function `x_i = ψ_i` as a section of `𝒜_{Kⁿ}` over `W`. -/
def x0Sec (W : Opens (Kn.{u} K n)) (i : Fin n) : (sheafKn K n).presheaf.obj (op W) :=
  sectionOfContMDiffOn (fun y : Kn.{u} K n => ψ y i) W
    (((ContinuousLinearMap.proj (R := K) (φ := fun _ : Fin n => K) i).comp
      (ψ : Kn.{u} K n →L[K] (Fin n → K))).contMDiff.contMDiffOn)

theorem x0Sec_apply (W : Opens (Kn.{u} K n)) (i : Fin n) (y : W) :
    x0Sec ψ W i y = ψ (y : Kn.{u} K n) i := rfl

/-- The constant `t` as a section over `W`. -/
def cSec (W : Opens (Kn.{u} K n)) (t : K) : (sheafKn K n).presheaf.obj (op W) :=
  sectionOfContMDiffOn (fun _ => t) W contMDiffOn_const

theorem cSec_apply (W : Opens (Kn.{u} K n)) (t : K) (y : W) : cSec W t y = t := rfl

/-- The germ of the coordinate section is the coordinate germ `coordKn`. -/
theorem germ_x0Sec {W : Opens (Kn.{u} K n)} {a : Kn.{u} K n} (ha : a ∈ W) (i : Fin n) :
    (sheafKn K n).presheaf.germ W a ha (x0Sec ψ W i) = coordKn ψ a i := by
  apply stalkToGerm_injective 𝓘(K, Kn.{u} K n) ω (Kn.{u} K n) a
  unfold coordKn coord
  erw [stalkToGerm_germ, stalkToGerm_germ]
  apply Filter.Germ.coe_eq.mpr
  have h1 : ∀ᶠ y in 𝓝 a, y ∈ W := W.2.mem_nhds ha
  have h2 : ∀ᶠ y in 𝓝 a, y ∈ (chartAt (Kn.{u} K n) a).source :=
    (chartAt (Kn.{u} K n) a).open_source.mem_nhds (mem_chart_source _ a)
  filter_upwards [h1, h2] with y hy1 hy2
  rw [extendBy0_of_mem _ _ _ _ hy1, extendBy0_of_mem _ _ _ _ hy2]
  simp only [x0Sec, chartSection, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id]
  rfl

/-- The germ of the constant section is the constant. -/
theorem germ_cSec {W : Opens (Kn.{u} K n)} {a : Kn.{u} K n} (ha : a ∈ W) (t : K) :
    (sheafKn K n).presheaf.germ W a ha (cSec W t) = const K (Kn.{u} K n) (Kn.{u} K n) a t := by
  apply stalkToGerm_injective 𝓘(K, Kn.{u} K n) ω (Kn.{u} K n) a
  erw [const_apply, stalkToGerm_germ, stalkToGerm_germ]
  apply Filter.Germ.coe_eq.mpr
  have h1 : ∀ᶠ y in 𝓝 a, y ∈ W := W.2.mem_nhds ha
  filter_upwards [h1] with y hy1
  rw [extendBy0_of_mem _ _ _ _ hy1, extendBy0_of_mem _ _ _ _ (Opens.mem_top y)]
  rfl

theorem TKn_germ_x0Sec {W : Opens (Kn.{u} K n)} {a : Kn.{u} K n} (ha : a ∈ W) (i : Fin n) :
    TKn ψ a ((sheafKn K n).presheaf.germ W a ha (x0Sec ψ W i)) =
      MvPowerSeries.X i + MvPowerSeries.C (ψ a i) := by
  rw [germ_x0Sec]
  have := TKn_coord_sub_const ψ a i
  rw [map_sub, TKn_const, sub_eq_iff_eq_add] at this
  exact this

theorem TKn_germ_cSec {W : Opens (Kn.{u} K n)} {a : Kn.{u} K n} (ha : a ∈ W) (t : K) :
    TKn ψ a ((sheafKn K n).presheaf.germ W a ha (cSec W t)) = MvPowerSeries.C t := by
  rw [germ_cSec, TKn_const]

end Sections

section Product

variable {m : ℕ} (ψ : Kn.{u} K (m + 1) ≃L[K] (Fin (m + 1) → K))

/-- The product open `π⁻¹ V ⊆ Kᵐ⁺¹` over an open `V ⊆ Kᵐ` (Freitag's `V × (−r, r)` [Fre17, Ch. I,
10.3], here with the whole line as second factor). -/
abbrev baseOpens (V : Opens (Kn.{u} K m)) : Opens (Kn.{u} K (m + 1)) :=
  preimageOpens (projKn ψ) (contMDiff_projKn ψ) V

theorem mem_baseOpens {V : Opens (Kn.{u} K m)} {a : Kn.{u} K (m + 1)} :
    a ∈ baseOpens ψ V ↔ projKn ψ a ∈ V := Iff.rfl

/-- The shifted coordinate `x_0 − x₀` over `π⁻¹ V`. -/
def shiftSec (V : Opens (Kn.{u} K m)) (x0 : K) :
    (sheafKn K (m + 1)).presheaf.obj (op (baseOpens ψ V)) :=
  x0Sec ψ (baseOpens ψ V) 0 - cSec (baseOpens ψ V) x0

/-- The pull-back `w ∘ π` of a section of the base. -/
def pullSec (V : Opens (Kn.{u} K m)) (w : (sheafKn K m).presheaf.obj (op V)) :
    (sheafKn K (m + 1)).presheaf.obj (op (baseOpens ψ V)) :=
  comapSection (projKn ψ) (contMDiff_projKn ψ) w

variable {V : Opens (Kn.{u} K m)} {a : Kn.{u} K (m + 1)}

theorem TKn_germ_shiftSec (ha : a ∈ baseOpens ψ V) (x0 : K) :
    TKn ψ a ((sheafKn K (m + 1)).presheaf.germ (baseOpens ψ V) a ha (shiftSec ψ V x0)) =
      MvPowerSeries.X 0 - MvPowerSeries.C (x0 - ψ a 0) := by
  unfold shiftSec
  rw [map_sub, map_sub, TKn_germ_x0Sec, TKn_germ_cSec, map_sub]
  ring

theorem TKn_germ_pullSec (ha : a ∈ baseOpens ψ V) (w : (sheafKn K m).presheaf.obj (op V)) :
    TKn ψ a ((sheafKn K (m + 1)).presheaf.germ (baseOpens ψ V) a ha (pullSec ψ V w)) =
      liftTail (TKn (knCoord K m) (projKn ψ a) ((sheafKn K m).presheaf.germ V (projKn ψ a) ha w)) :=
  TKn_germ_comapSection ψ a ha w

/-- `Σ_k (w k ∘ π) (x_0 − x₀)^k`: a polynomial section of degree `< N` in the shifted coordinate. -/
def polyComb (V : Opens (Kn.{u} K m)) (x0 : K) {N : ℕ}
    (w : Fin N → (sheafKn K m).presheaf.obj (op V)) :
    (sheafKn K (m + 1)).presheaf.obj (op (baseOpens ψ V)) :=
  ∑ k, pullSec ψ V (w k) * shiftSec ψ V x0 ^ (k : ℕ)

/-- `(x_0 − x₀)^e + Σ_j (c j ∘ π) (x_0 − x₀)^{e−1−j}`: a monic polynomial section of degree `e`, the
shape of `weierstrassPoly e c`. -/
def polyMonic (V : Opens (Kn.{u} K m)) (x0 : K) (e : ℕ)
    (c : Fin e → (sheafKn K m).presheaf.obj (op V)) :
    (sheafKn K (m + 1)).presheaf.obj (op (baseOpens ψ V)) :=
  shiftSec ψ V x0 ^ e + ∑ j, pullSec ψ V (c j) * shiftSec ψ V x0 ^ (e - 1 - (j : ℕ))

theorem ofPoly_comp_X_sub_C (P : Polynomial (MvPowerSeries (Fin m) K)) (s : K) :
    ofPoly (P.comp (Polynomial.X - Polynomial.C (MvPowerSeries.C s))) =
      Polynomial.eval₂ (ofPolyHom.comp Polynomial.C) (MvPowerSeries.X 0 - MvPowerSeries.C s) P := by
  rw [Polynomial.comp, ofPoly, Polynomial.hom_eval₂]
  congr 1
  change ofPoly _ = _
  rw [sub_eq_add_neg, ofPoly_add, ofPoly_neg, ofPoly_X, ofPoly_C, liftTail, MvPowerSeries.rename_C,
    sub_eq_add_neg]

theorem ofPolyHom_comp_C (c : MvPowerSeries (Fin m) K) :
    (ofPolyHom.comp Polynomial.C) c = liftTail c :=
  ofPoly_C c

theorem ofPoly_polyOfCoeff_comp {N : ℕ} (c : Fin N → MvPowerSeries (Fin m) K) (s : K) :
    ofPoly ((polyOfCoeff c).comp (Polynomial.X - Polynomial.C (MvPowerSeries.C s))) =
      ∑ k, liftTail (c k) * (MvPowerSeries.X 0 - MvPowerSeries.C s) ^ (k : ℕ) := by
  rw [ofPoly_comp_X_sub_C, polyOfCoeff, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, ofPolyHom_comp_C]

theorem ofPoly_weierstrassPolynomial_comp {e : ℕ} (c : Fin e → MvPowerSeries (Fin m) K) (s : K) :
    ofPoly ((weierstrassPolynomial e c).comp (Polynomial.X - Polynomial.C (MvPowerSeries.C s))) =
      (MvPowerSeries.X 0 - MvPowerSeries.C s) ^ e +
        ∑ j, liftTail (c j) * (MvPowerSeries.X 0 - MvPowerSeries.C s) ^ (e - 1 - (j : ℕ)) := by
  rw [ofPoly_comp_X_sub_C, weierstrassPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, ofPolyHom_comp_C]

/-- The Taylor series at `a ∈ π⁻¹ V` of a polynomial combination: the polynomial with the Taylor
series of the coefficients at `π a`, composed with the shift `X − C (x₀ − a_0)`. -/
theorem TKn_germ_polyComb (ha : a ∈ baseOpens ψ V) (x0 : K) {N : ℕ}
    (w : Fin N → (sheafKn K m).presheaf.obj (op V)) :
    TKn ψ a ((sheafKn K (m + 1)).presheaf.germ (baseOpens ψ V) a ha (polyComb ψ V x0 w)) =
      ofPoly ((polyOfCoeff fun k =>
          TKn (knCoord K m) (projKn ψ a) ((sheafKn K m).presheaf.germ V _ ha (w k))).comp
        (Polynomial.X - Polynomial.C (MvPowerSeries.C (x0 - ψ a 0)))) := by
  rw [ofPoly_polyOfCoeff_comp, polyComb, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, TKn_germ_pullSec ψ ha, TKn_germ_shiftSec ψ ha]

/-- The Taylor series at `a ∈ π⁻¹ V` of a monic polynomial section: `weierstrassPolynomial e (T c)`
composed with the shift, monic of degree `e` at every point. -/
theorem TKn_germ_polyMonic (ha : a ∈ baseOpens ψ V) (x0 : K) (e : ℕ)
    (c : Fin e → (sheafKn K m).presheaf.obj (op V)) :
    TKn ψ a ((sheafKn K (m + 1)).presheaf.germ (baseOpens ψ V) a ha (polyMonic ψ V x0 e c)) =
      ofPoly ((weierstrassPolynomial e fun j => TKn (knCoord K m) (projKn ψ a)
          ((sheafKn K m).presheaf.germ V _ ha (c j))).comp
        (Polynomial.X - Polynomial.C (MvPowerSeries.C (x0 - ψ a 0)))) := by
  rw [ofPoly_weierstrassPolynomial_comp, polyMonic, map_add, map_add, map_pow, map_pow, map_sum,
    map_sum, TKn_germ_shiftSec ψ ha]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, TKn_germ_pullSec ψ ha, TKn_germ_shiftSec ψ ha]

theorem monic_weierstrassPolynomial_comp {e : ℕ} (c : Fin e → MvPowerSeries (Fin m) K) (s : K) :
    ((weierstrassPolynomial e c).comp (Polynomial.X - Polynomial.C (MvPowerSeries.C s))).Monic :=
  (monic_weierstrassPolynomial e c).comp_X_sub_C _

theorem natDegree_weierstrassPolynomial_comp {e : ℕ} (c : Fin e → MvPowerSeries (Fin m) K) (s : K) :
    ((weierstrassPolynomial e c).comp
      (Polynomial.X - Polynomial.C (MvPowerSeries.C s))).natDegree = e := by
  rw [Polynomial.natDegree_comp, natDegree_weierstrassPolynomial, Polynomial.natDegree_X_sub_C,
    mul_one]

/-- Composition with `X − C r` is injective on polynomials. -/
theorem comp_X_sub_C_eq_zero_iff {R : Type*} [CommRing R] (P : Polynomial R) (r : R) :
    P.comp (Polynomial.X - Polynomial.C r) = 0 ↔ P = 0 := by
  constructor
  · intro h
    have := congrArg (fun q => q.comp (Polynomial.X + Polynomial.C r)) h
    simp only [Polynomial.zero_comp] at this
    rwa [Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
      add_sub_cancel_right, Polynomial.comp_X] at this
  · rintro rfl; exact Polynomial.zero_comp

theorem ofPoly_injective : Function.Injective (ofPoly (K := K) (m := m)) := by
  intro P Q h
  have := congrArg (splitFirst K m) h
  rw [splitFirst_ofPoly, splitFirst_ofPoly] at this
  exact Polynomial.coe_inj.mp this

/-- Coefficient extraction: a polynomial combination has germ `0` at `a` iff every coefficient has
germ `0` at `π a`. -/
theorem germ_polyComb_eq_zero_iff (ha : a ∈ baseOpens ψ V) (x0 : K) {N : ℕ}
    (w : Fin N → (sheafKn K m).presheaf.obj (op V)) :
    (sheafKn K (m + 1)).presheaf.germ (baseOpens ψ V) a ha (polyComb ψ V x0 w) = 0 ↔
      ∀ k, (sheafKn K m).presheaf.germ V (projKn ψ a) ha (w k) = 0 := by
  rw [← (TKn_injective ψ a).eq_iff, map_zero, TKn_germ_polyComb ψ ha]
  rw [← ofPoly_zero, ofPoly_injective.eq_iff, comp_X_sub_C_eq_zero_iff, polyOfCoeff_eq_zero_iff]
  refine forall_congr' fun k => ?_
  rw [← (TKn_injective (knCoord K m) (projKn ψ a)).eq_iff, map_zero]

end Product

end AnalyticSpace
