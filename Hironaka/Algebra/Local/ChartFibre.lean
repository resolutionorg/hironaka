/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Algebra.Local.Order
import Hironaka.Algebra.Local.ChartGenericFibre
import Hironaka.Algebra.Local.PolynomialOrder
import Hironaka.Algebra.Local.Transform
import Hironaka.Algebra.Local.TransformOrder
import Mathlib.Combinatorics.Matroid.Init

/-!
# The order of the transform at every point of the fibre of the chart

[Kol07, Lemma 61] bounds the order of the birational transform `π⁻¹_*(I, m)` by `m` at every
point of the blow-up when `ord_Z I = max-ord I = m`. Kollár's proof computes at the origin of the
chart dividing by `x_r`, where an `f ∈ I` of order `m` has the transform
`x_r^{-m} f(y₁ x_r, …, y_{r−1} x_r, x_r, …)`, which contains a monomial of degree `≤ m`, and
reaches the other points by a linear change of coordinates. Such a change exists only for the
points of the fibre rational over the residue field `κ`; `Hironaka/Algebra/Local/Lemma61.lean`
treats exactly those, through the completion. This module obtains the bound at every prime of the
fibre, rational or not, by reading the computation in the fibre of the chart over the closed point.

Let `R` be a regular local ring with regular system of parameters `x`, `r` any index,
`P = (x₀, …, x_r)`, `R'` the chart ring dividing by `x_r`, and `𝔮` a prime of `R'` lying over `𝔪`.
For `f ∈ Pᵐ` of order exactly `m`, `f / x_rᵐ = Q(y)` with `Q` a polynomial of degree `≤ m` with a
coefficient outside `𝔪` (`exists_transformElem_eq_chartPresentation`), and modulo `𝔪R'`, in the
fibre `R'/𝔪R' ≅ κ[Y]` (`exists_quotient_map_maximalIdeal_ringEquiv`; both from
`Hironaka/Algebra/Local/ChartGenericFibre.lean`), it is the nonzero polynomial `Q̄` of degree `≤ m`.
The quotient map `R'_𝔮 → κ[Y]_𝔮̄` is a local homomorphism, along which orders do not decrease, and a
nonzero polynomial has order at most its degree at every prime of `κ[Y]`
(`ordElem_algebraMap_le_totalDegree`, `Hironaka/Algebra/Local/PolynomialOrder.lean`). Hence

* `ord_𝔮 (f / x_rᵐ) ≤ m` (`ordElem_algebraMap_transformElem_le`), and
* for `I ≤ Pᵐ` with `ord I = m`, `ord_𝔮 π⁻¹_*(I, m) ≤ m` (`ord_map_transformIdeal_le_of_le_comap`).

The argument at the non-rational points is the library's own. Used for Lemma 61 on schemes
(`Hironaka/Scheme/IdealSheaf/Order/Lemma61.lean`), for the order along the centre
(`Hironaka/Scheme/BlowUpSequence/OrderAlongCenter.lean`,
`Hironaka/Resolution/Algebraic/Hir64/Corollary1.lean`) and for the strict transform of a
hypersurface of maximal contact (`Hironaka/Resolution/Algebraic/MaximalContact/Transform.lean`).
-/

public section

namespace IsLocalRing

open IsLocalRing MvPolynomial

universe u

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {n : ℕ} (x : Fin n → R)
  (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
  (r : Fin n)

include hx hn

/-- **The order of a transform at every prime of the fibre** (the proof of [Kol07, Lemma 61]: "in
`π⁻¹_* f` we get a monomial of degree `≤ m`"; at the non-rational primes the argument is the
library's own): for `f ∈ Pᵐ` of order exactly `m`, the transform `f / x_rᵐ` has order `≤ m` in the
localization of the chart ring at every prime `𝔮` lying over `𝔪`. -/
theorem ordElem_algebraMap_transformElem_le (𝔮 : Ideal (chartRing x r)) [𝔮.IsPrime]
    (h𝔮 : maximalIdeal R ≤ 𝔮.comap (algebraMap R (chartRing x r))) {m : ℕ} {f : R}
    (hf : f ∈ chartCenter x r ^ m) (hord : ordElem f = m) :
    ordElem (algebraMap (chartRing x r) (Localization.AtPrime 𝔮) (transformElem x r f hf)) ≤ m := by
  classical
  obtain ⟨e, heC, heX⟩ := exists_quotient_map_maximalIdeal_ringEquiv x hx hn r
  obtain ⟨Q, hQ, hdeg, β, hβ⟩ := exists_transformElem_eq_chartPresentation x hx r hf hord
  -- the surjection `ψ : R' → κ[Y]` with kernel `𝔪R'`
  let ψ : chartRing x r →+* MvPolynomial (Fin r) (ResidueField R) :=
    e.toRingHom.comp (Ideal.Quotient.mk _)
  have hψ_surj : Function.Surjective ψ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hψ_apply : ∀ g, ψ g = e (Ideal.Quotient.mk _ g) := fun g => rfl
  have hker : RingHom.ker ψ = (maximalIdeal R).map (algebraMap R (chartRing x r)) := by
    ext g
    rw [RingHom.mem_ker, hψ_apply, map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hJ𝔮 : (maximalIdeal R).map (algebraMap R (chartRing x r)) ≤ 𝔮 :=
    Ideal.map_le_iff_le_comap.mpr h𝔮
  have hker𝔮 : RingHom.ker ψ ≤ 𝔮 := by
    rw [hker]
    exact hJ𝔮
  -- the image prime `𝔮̄ = ψ(𝔮)`, with `𝔮 = ψ⁻¹(𝔮̄)`
  have hprime : (𝔮.map ψ).IsPrime := Ideal.map_isPrime_of_surjective hψ_surj hker𝔮
  have hcomap : 𝔮 = (𝔮.map ψ).comap ψ := by
    rw [Ideal.comap_map_of_surjective _ hψ_surj, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker𝔮]
  -- `ψ (f/x_r^m)` is the fibre polynomial `Q̄`, nonzero of degree `≤ m`
  have hPC : ∀ a : R, chartPresentation x r (C a) = algebraMap R (chartRing x r) a := fun a =>
    (chartPresentation x r).commutes a
  have hPX : ∀ i : Fin r, chartPresentation x r (X i) = chartYR x r (Fin.castLE r.2.le i) :=
    fun i => MvPolynomial.aeval_X _ i
  have hψQ : ψ (transformElem x r f hf) = MvPolynomial.map (residue R) Q := by
    rw [hQ]
    have h : ψ.comp (chartPresentation x r).toRingHom = MvPolynomial.map (residue R) := by
      refine ringHom_ext (fun a => ?_) (fun i => ?_)
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hPC a, map_C,
          hψ_apply]
        exact heC a
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hPX i, map_X,
          hψ_apply]
        exact heX i
    have h' := RingHom.congr_fun h Q
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h'
    exact h'
  have hP0 : MvPolynomial.map (residue R) Q ≠ 0 := by
    intro h0
    have h1 := congrArg (AddMonoidAlgebra.coeff · β) h0
    rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
    exact hβ (Ideal.Quotient.eq_zero_iff_mem.mp h1)
  have hsub : (MvPolynomial.map (residue R) Q).support ⊆ Q.support :=
    support_map_subset (residue R) Q
  have hPdeg' : (MvPolynomial.map (residue R) Q).totalDegree ≤ Q.totalDegree := by
    unfold MvPolynomial.totalDegree
    exact Finset.sup_mono hsub
  have hPdeg : (MvPolynomial.map (residue R) Q).totalDegree ≤ m := hPdeg'.trans hdeg
  -- the local homomorphism `R'_𝔮 → κ[Y]_𝔮̄`
  have := hprime
  let Ψ : Localization.AtPrime 𝔮 →+* Localization.AtPrime (𝔮.map ψ) :=
    Localization.localRingHom 𝔮 (𝔮.map ψ) ψ hcomap
  have : IsLocalHom Ψ := Localization.isLocalHom_localRingHom 𝔮 (𝔮.map ψ) ψ hcomap
  have h1 : ordElem (algebraMap (chartRing x r) (Localization.AtPrime 𝔮) (transformElem x r f hf))
      ≤ ordElem (Ψ (algebraMap _ _ (transformElem x r f hf))) := ordElem_le_ordElem_map Ψ _
  have h2 : Ψ (algebraMap _ _ (transformElem x r f hf)) =
      algebraMap _ (Localization.AtPrime (𝔮.map ψ)) (MvPolynomial.map (residue R) Q) := by
    rw [← hψQ]
    exact Localization.localRingHom_to_map 𝔮 (𝔮.map ψ) ψ hcomap _
  have h3 : ordElem (algebraMap _ (Localization.AtPrime (𝔮.map ψ)) (MvPolynomial.map (residue R) Q))
      ≤ ((MvPolynomial.map (residue R) Q).totalDegree : ℕ∞) :=
    ordElem_algebraMap_le_totalDegree _ hP0
  refine h1.trans ?_
  rw [h2]
  exact h3.trans (by exact_mod_cast hPdeg)

/-- [Kol07, Lemma 61] in local form at every point of the fibre
(`Hironaka/Algebra/Local/Lemma61.lean` is the case of the `κ`-rational points): if `I ≤ Pᵐ` and `ord
I = m`, then `ord_𝔮 π⁻¹_*(I, m) ≤ m` at every prime `𝔮` of the chart ring lying over `𝔪`. -/
theorem ord_map_transformIdeal_le_of_le_comap (𝔮 : Ideal (chartRing x r)) [𝔮.IsPrime]
    (h𝔮 : maximalIdeal R ≤ 𝔮.comap (algebraMap R (chartRing x r))) {I : Ideal R} {m : ℕ}
    (hI : I ≤ chartCenter x r ^ m) (hord : ord I = m) :
    ord ((transformIdeal x r I m).map (algebraMap (chartRing x r) (Localization.AtPrime 𝔮))) ≤
      m := by
  obtain ⟨f, hfI, hf⟩ := exists_mem_ordElem_eq_of_ord_eq hord
  refine le_trans ?_ (ordElem_algebraMap_transformElem_le x hx hn r 𝔮 h𝔮 (hI hfI) hf)
  rw [← ord_span_singleton]
  exact ord_anti (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
    (Ideal.mem_map_of_mem _ (transformElem_mem_transformIdeal x r hfI (hI hfI)))))

end IsLocalRing
