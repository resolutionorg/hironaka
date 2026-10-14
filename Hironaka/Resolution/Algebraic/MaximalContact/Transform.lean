/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Algebra.Local.Order
public import Hironaka.Scheme.BlowUp.Transform
public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.Local.ChartGenericFibre
import Hironaka.Algebra.Local.PolynomialOrder
import Hironaka.Algebra.Local.QuotientParameters
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform.WeakTransform
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.RelativeDimension
import Hironaka.Scheme.Snc.SpreadSnc
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The birational transform of a smooth hypersurface through the centre

Kollár's proof of [Kol07, Theorem 80 (1)] passes from `𝒪_{X_i}(−H_i) ⊂ J_i` to
`𝒪_{X_{i+1}}(−H_{i+1}) ⊂ J_{i+1}` in one clause ("since … `H_0` is smooth, we see that …"). The
step it hides is [Wlo05, Lemma 2.7.4 (2)–(3)]: if the smooth centre `Z` lies in the smooth
hypersurface `H = (u = 0)`, then in a chart with exceptional coordinate `y` the function
`u' = u/y` is again a parameter, `V(u')` is the strict transform of `H`, and `u'` is the controlled
transform of `u` with control `1`. Coordinate-free:

* **the exceptional multiplicity of `π^* H` is one at every point of the exceptional divisor**
  (`stalkIdeal_comap_not_le_exceptionalDivisor_sq`; the multiplicity of [Kol07, 58.1] pointwise):
  at a point `q` of `B_Z X` over `z ∈ Z`, the chart bridge
  (`exists_stalk_equiv_localization_chart_of_smooth`) identifies `𝒪_{B,q}` with a localization of
  the chart ring `𝒪_{X,z}[y_i/y_ρ]` at a prime `𝔮` over `𝔪_z`, the exceptional divisor becoming
  `(y_ρ)`; the equation `h` of `H` has order one and lies in the centre, so `h = y_ρ · h'` with `h'`
  its controlled transform, and `h'` cannot lie in `(y_ρ)` there: modulo `𝔪_z` the chart ring is
  the polynomial ring `κ(z)[Y]` (`exists_quotient_map_maximalIdeal_ringEquiv`), in which `h'` is
  the leading form of `h`, a nonzero polynomial (`exists_transformElem_eq_chartPresentation`),
  while `(y_ρ)` maps to zero. This is the argument of the local form of [Kol07, Lemma 61]
  (`ordElem_algebraMap_transformElem_le`) with the inequality replaced by a non-membership.
* **the strict transform of `H` is the marked transform `(π)⁻¹_*(𝒪(−H), 1)`**
  (`strictTransform_eq_markedTransform_one`): the strict transform is the saturation of `π^* H` by
  the exceptional divisor `F`, the marked transform ([Kol07, 60.1]) its colon by `F`; stalkwise
  `π^* H = (y u')` with `y` the equation of `F`, prime because `F` is a smooth divisor of `B_Z X`
  (`isSmoothDivisor_exceptionalDivisor_of_smooth`), and `u' ∉ (y)` by the previous point, so every
  colon `(y u' : y^i)` is contained in `(y u' : y)` (`colon_pow_le_colon_of_prime`).
* **the strict transform of `H` is again a smooth hypersurface**
  (`isSmoothDivisor_strictTransform_of_le`): the morphism of blow-ups
  `blowUpMap H.subschemeι Z : B_{Z ∩ H} H ⟶ B_Z X` is a closed immersion with kernel the strict
  transform of `H` (the restriction of [Kol07, Definition 30.2]), so `V(H_1) ≅ B_{Z ∩ H} H`; the
  centre `Z ∩ H` is `Z` itself (`Z ⊆ H`), smooth; `H` is smooth of relative dimension `n − 1`, so
  `B_Z H` is smooth of relative dimension `n − 1` inside `B_Z X`, smooth of relative dimension `n`,
  which is what "smooth divisor" means. The route avoids adapted coordinates for the flag `Z ⊆ H`.
  The degenerate relative dimension `n = 0` (an étale `X`) has no smooth hypersurface but `⊤`: at
  a point of `V(H)` a generator in `𝔪 ∖ 𝔪²` would need `𝔪 ≠ 0`, while the stalk of an étale scheme
  over a field has Krull dimension `0` and is a field; the strict transform of `⊤` is `⊤`, a
  smooth divisor.

When `Z` is a component of `H` (a codimension-one centre; the blow-up is an isomorphism,
[Kol07, Warning 20]) the statements hold as well: the transform drops that component, on both
sides.

These results carry the hypersurface of maximal contact along a blow-up sequence
(`Hironaka/Resolution/Algebraic/MaximalContact/Sequence.lean`) and are used again in the
globalization (`Hironaka/Resolution/Algebraic/Kol07/MaximalContactGlobalization.lean`), in the
embedded resolution (`Hironaka/Resolution/`) and in boundary clearing
(`Hironaka/Resolution/Algebraic/BoundaryClearing/Restriction.lean`). -/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData IsLocalRing

namespace Hironaka.Local

open IsLocalRing

section Chart

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ} (x : Fin n → R)
  (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
  (r : Fin n)

include hx hn in
/-- The multiplicity of [Kol07, 58.1] at a point of the exceptional divisor of the chart: for
`f ∈ P^m` of order exactly `m`, the controlled transform `f / x_r^m` does not lie in the
exceptional ideal `(x_r)` at any prime `𝔮` of the chart ring over `𝔪`: modulo `𝔪 R'` the chart ring
is `κ[Y]`, in which `f / x_r^m` is the nonzero leading form of `f` while `x_r` vanishes; the
argument of `ordElem_algebraMap_transformElem_le`. -/
theorem algebraMap_transformElem_notMem_map_span_x (𝔮 : Ideal (chartRing x r)) [𝔮.IsPrime]
    (h𝔮 : maximalIdeal R ≤ 𝔮.comap (algebraMap R (chartRing x r))) {m : ℕ} {f : R}
    (hf : f ∈ chartCenter x r ^ m) (hord : ordElem f = m) :
    algebraMap (chartRing x r) (Localization.AtPrime 𝔮) (transformElem x r f hf) ∉
      (Ideal.span {algebraMap R (chartRing x r) (x r)}).map
        (algebraMap (chartRing x r) (Localization.AtPrime 𝔮)) := by
  classical
  intro hmem
  obtain ⟨e, heC, heX⟩ := exists_quotient_map_maximalIdeal_ringEquiv x hx hn r
  obtain ⟨Q, hQ, -, β, hβ⟩ := exists_transformElem_eq_chartPresentation x hx r hf hord
  let ψ : chartRing x r →+* MvPolynomial (Fin r) (ResidueField R) :=
    e.toRingHom.comp (Ideal.Quotient.mk _)
  have hψ_apply : ∀ g, ψ g = e (Ideal.Quotient.mk _ g) := fun g => rfl
  have hker : ∀ g, ψ g = 0 ↔ g ∈ (maximalIdeal R).map (algebraMap R (chartRing x r)) :=
    fun g => by rw [hψ_apply, map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hPC : ∀ a : R, chartPresentation x r (MvPolynomial.C a) = algebraMap R (chartRing x r) a :=
    fun a => (chartPresentation x r).commutes a
  have hPX : ∀ i : Fin r,
      chartPresentation x r (MvPolynomial.X i) = chartYR x r (Fin.castLE r.2.le i) :=
    fun i => MvPolynomial.aeval_X _ i
  have hψQ : ψ (transformElem x r f hf) = MvPolynomial.map (residue R) Q := by
    rw [hQ]
    have h : ψ.comp (chartPresentation x r).toRingHom = MvPolynomial.map (residue R) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hPC a,
          MvPolynomial.map_C, hψ_apply]
        exact heC a
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hPX i,
          MvPolynomial.map_X, hψ_apply]
        exact heX i
    have h' := RingHom.congr_fun h Q
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h'
    exact h'
  have hP0 : MvPolynomial.map (residue R) Q ≠ 0 := by
    intro h0
    have h1 := congrArg (AddMonoidAlgebra.coeff · β) h0
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at h1
    exact hβ (Ideal.Quotient.eq_zero_iff_mem.mp h1)
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hmul⟩ :=
    (IsLocalization.mem_map_algebraMap_iff 𝔮.primeCompl (Localization.AtPrime 𝔮)).mp hmem
  rw [← map_mul] at hmul
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists 𝔮.primeCompl (Localization.AtPrime 𝔮)).mp hmul
  have ha0 : ψ a = 0 := by
    refine (hker a).mpr ?_
    have hxr : algebraMap R (chartRing x r) (x r) ∈
        (maximalIdeal R).map (algebraMap R (chartRing x r)) := by
      refine Ideal.mem_map_of_mem _ ?_
      rw [hx]
      exact Ideal.subset_span ⟨r, rfl⟩
    exact (Ideal.span_singleton_le_iff_mem _).mpr hxr ha
  have hprod : ψ ((t : chartRing x r) * s) * ψ (transformElem x r f hf) = 0 := by
    have h := congrArg ψ ht
    rw [map_mul, map_mul, map_mul, ha0, mul_zero] at h
    rw [map_mul]
    calc ψ (t : chartRing x r) * ψ s * ψ (transformElem x r f hf)
        = ψ (t : chartRing x r) * (ψ (transformElem x r f hf) * ψ s) := by ring
      _ = 0 := h
  rcases mul_eq_zero.mp hprod with h0 | h0
  · have hmemq : (t : chartRing x r) * s ∈ 𝔮 :=
      Ideal.map_le_iff_le_comap.mpr h𝔮 ((hker _).mp h0)
    exact (𝔮.primeCompl.mul_mem t.2 hs) hmemq
  · rw [hψQ] at h0
    exact hP0 h0

end Chart

/-- In a commutative ring, for a prime nonzerodivisor `y` and `u'` not divisible by `y`, every colon
`(u' y : y^i)` lies in `(u' y : y)`: the saturation of the principal ideal `(u' y)` by `(y)`
stabilizes at the first step. -/
theorem colon_pow_le_colon_of_prime {S : Type*} [CommRing S] {y u' : S}
    (hy : y ∈ nonZeroDivisors S) (hprime : Prime y) (hu' : ¬ y ∣ u') (i : ℕ) :
    (Ideal.span {u' * y}).colon (↑(Ideal.span {y} ^ i) : Set S) ≤
      (Ideal.span {u' * y}).colon (↑(Ideal.span {y}) : Set S) := by
  have aux : ∀ j : ℕ, ∀ w t : S, w * y ^ j = t * u' → ∃ s, w = u' * s := by
    intro j
    induction j with
    | zero =>
      intro w t h
      rw [pow_zero, mul_one] at h
      exact ⟨t, by rw [h]; ring⟩
    | succ j ih =>
      intro w t h
      have hdvd : y ∣ t * u' := ⟨w * y ^ j, by rw [← h]; ring⟩
      rcases hprime.dvd_or_dvd hdvd with ⟨t', rfl⟩ | h2
      · refine ih w t' ?_
        have h3 : (w * y ^ j - t' * u') * y = 0 := by linear_combination h
        exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hy).2 _ h3)
      · exact absurd h2 hu'
  intro w hw
  rw [Submodule.mem_colon] at hw ⊢
  intro s hs
  rw [SetLike.mem_coe, Ideal.mem_span_singleton'] at hs
  obtain ⟨a, rfl⟩ := hs
  have hwi : w * y ^ i ∈ Ideal.span {u' * y} := by
    have := hw (y ^ i) (by
      rw [SetLike.mem_coe, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _)
    simpa [smul_eq_mul] using this
  rw [Ideal.mem_span_singleton'] at hwi
  obtain ⟨t, ht⟩ := hwi
  have hw' : ∃ s, w = u' * s := by
    rcases i with _ | i
    · rw [pow_zero, mul_one] at ht
      exact ⟨t * y, by rw [← ht]; ring⟩
    · refine aux i w t ?_
      have h3 : (w * y ^ i - t * u') * y = 0 := by linear_combination -ht
      exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hy).2 _ h3)
  obtain ⟨s, rfl⟩ := hw'
  rw [smul_eq_mul, Ideal.mem_span_singleton']
  exact ⟨s * a, by ring⟩

end Hironaka.Local

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A smooth hypersurface has order exactly one at every point of its support: its stalk there is
generated by an element of `𝔪 ∖ 𝔪²` (`ordElem_eq_one_iff`). -/
theorem IsSmoothDivisor.ord_eq_one {H : X.IdealSheafData} (hH : IsSmoothDivisor H) {x : X}
    (hx : x ∈ H.support) : H.ord x = 1 := by
  obtain ⟨a, ha, ha2, hspan⟩ := hH.2 x hx
  rw [Scheme.IdealSheafData.ord_eq_ord_stalkIdeal, hspan, ord_span_singleton]
  exact ordElem_eq_one_iff.mpr ⟨ha, ha2⟩

/-- A smooth hypersurface containing the centre `Z` (`H ≤ Z` as ideal sheaves) has order exactly
`1` along `Z`: at every generic point of `Z`, which lies on `H`. -/
theorem IsSmoothDivisor.ordAlongEq_one_of_le {H Z : X.IdealSheafData} (hH : IsSmoothDivisor H)
    (hZH : H ≤ Z) : H.OrdAlongEq Z.support ((1 : ℕ) : ℕ∞) := fun η hη => by
  rw [Nat.cast_one]
  exact hH.ord_eq_one (Scheme.IdealSheafData.support_antitone hZH hη.1)

/-- The unit ideal sheaf is a smooth divisor (the empty hypersurface): its closed subscheme has no
points. -/
theorem _root_.Hironaka.Snc.isSmoothDivisor_top : IsSmoothDivisor (⊤ : X.IdealSheafData) := by
  refine ⟨⟨fun z => ?_⟩, fun x hx => ?_⟩
  · have hz : (⊤ : X.IdealSheafData).subschemeι z ∈ ((⊤ : X.IdealSheafData).support : Set X) := by
      rw [← (⊤ : X.IdealSheafData).range_subschemeι]
      exact ⟨z, rfl⟩
    rw [Scheme.IdealSheafData.support_top] at hz
    exact hz.elim
  · rw [Scheme.IdealSheafData.support_top] at hx
    exact hx.elim

section Ambient

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [CharZero k] (n : ℕ)
  [SmoothOfRelativeDimension n f]

omit [CharZero k] in
include f n in
/-- The ideal sheaf of a smooth hypersurface is locally principal: on an affine neighbourhood of
every point it is generated by one section (at a point of `V(H)` the stalk generator spreads to a
basic open, `exists_basicOpen_ideal_eq_span`; off `V(H)` the ideal is the unit ideal). -/
theorem IsSmoothDivisor.locally_principal {H : X.IdealSheafData} (hH : IsSmoothDivisor H) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ s : Γ(X, U), H.ideal U = Ideal.span {s} := by
  classical
  have : IsLocallyNoetherian X :=
    Scheme.IdealSheafData.isLocallyNoetherian_of_smoothOfRelativeDimension f n
  by_cases hx : x ∈ H.support
  · obtain ⟨a, -, -, hspan⟩ := hH.2 x hx
    obtain ⟨W, hxW, s, hs⟩ := X.presheaf.exists_germ_eq a
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
    let s' : Γ(X, V) := X.presheaf.map (homOfLE hVW).op s
    have hs' : X.presheaf.germ V x hxV s' = a := by
      rw [← hs]
      exact X.presheaf.germ_res_apply (homOfLE hVW) x hxV s
    have hD : H.stalkIdeal x =
        Ideal.span ((X.presheaf.germ V x hxV).hom '' ({s'} : Set Γ(X, V))) := by
      rw [Set.image_singleton, hspan, hs']
    have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    obtain ⟨t, hxt, ht⟩ :=
      exists_basicOpen_ideal_eq_span H ⟨V, hV⟩ hxV {s'} (Set.finite_singleton _) hD
    refine ⟨⟨X.basicOpen t, hV.basicOpen t⟩, hxt,
      X.presheaf.map (homOfLE (X.basicOpen_le t)).op s', ?_⟩
    rw [ht, Set.image_singleton]
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVc⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (H.support : Set X)ᶜ from hx) H.support.isClosed.isOpen_compl
    refine ⟨⟨V, hV⟩, hxV, 1, ?_⟩
    rw [Ideal.span_singleton_one]
    refine Scheme.IdealSheafData.ideal_eq_top_of_forall_notMem H ⟨V, hV⟩ fun z hz => ?_
    have hmem : H.subschemeι z ∈ (H.support : Set X) := by
      rw [← H.range_subschemeι]
      exact ⟨z, rfl⟩
    exact hVc hz hmem

/-- In relative dimension `0` (an étale `X`) the only smooth hypersurface is the empty one: at a
point of `V(H)` a generator in `𝔪 ∖ 𝔪²` would need `𝔪 ≠ 0`, but the stalk has Krull dimension `0`
and is a field. -/
theorem IsSmoothDivisor.eq_top_of_smoothOfRelativeDimension_zero [SmoothOfRelativeDimension 0 f]
    {H : X.IdealSheafData} (hH : IsSmoothDivisor H) : H = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, x ∈ H.support := by
    by_contra h
    exact hne (le_antisymm (fun y hy => (h ⟨y, hy⟩).elim) bot_le)
  obtain ⟨a, ha, ha2, -⟩ := hH.2 x hx
  have hs : Smooth f := SmoothOfRelativeDimension.smooth 0 f
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f x
  have hdom : IsDomain (X.presheaf.stalk x) := isDomain_of_isRegularLocalRing _
  have hdim := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension f 0 x
  have hdim0 : ringKrullDim (X.presheaf.stalk x) = 0 := by
    have hle : ringKrullDim (X.presheaf.stalk x) ≤ 0 := by
      have h := hdim
      simp only [Nat.cast_zero] at h
      refine (le_add_of_nonneg_right ?_).trans h.le
      exact_mod_cast (zero_le : (0 : ℕ∞) ≤ _)
    exact le_antisymm hle ringKrullDim_nonneg_of_nontrivial
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
    (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr hdim0
  have hfield : IsField (X.presheaf.stalk x) := Ring.KrullDimLE.isField_of_isDomain
  have hmax : maximalIdeal (X.presheaf.stalk x) = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
  rw [hmax] at ha
  exact ha2 (by rw [(Ideal.mem_bot).mp ha]; exact zero_mem _)

end Ambient

end AlgebraicGeometry

namespace Hironaka.Sequence

open AlgebraicGeometry

section Exceptional

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CharZero k] (n : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]

include f n

/-- The exceptional divisor of the blow-up of a smooth scheme along a smooth centre of any shape is
a smooth divisor of the blow-up (`isSmoothDivisor_totalTransformFamily` for the empty divisor
family). -/
theorem isSmoothDivisor_exceptionalDivisor_of_smooth :
    IsSmoothDivisor Z.exceptionalDivisor := by
  classical
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  let E : Fin 0 → X.IdealSheafData := fun i => i.elim0
  have hE : ∀ x : X, ∃ (m : ℕ) (z : Fin m → X.presheaf.stalk x),
      (Ideal.span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (m : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      ∃ c : {i : Fin 0 // x ∈ (E i).support} → Fin m, Function.Injective c ∧
        ∀ i, (E i.1).stalkIdeal x = Ideal.span {z (c i)} := by
    intro x
    have hreg := isRegularLocalRing_stalk f x
    have : IsRegularLocalRing (X.presheaf.stalk x ⧸ (⊥ : Ideal (X.presheaf.stalk x))) :=
      IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot _).symm
    obtain ⟨m, -, z, -, hdim, hmax, -⟩ :=
      IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt
        (⊥ : Ideal (X.presheaf.stalk x))
    exact ⟨m, z, ⟨hmax.symm, hdim⟩, fun i => i.1.elim0, fun i => i.1.elim0, fun i => i.1.elim0⟩
  have hZ : ∀ x ∈ Z.support, ∃ (m : ℕ) (z : Fin m → X.presheaf.stalk x),
      (Ideal.span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (m : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      (∃ c : {i : Fin 0 // x ∈ (E i).support} → Fin m, Function.Injective c ∧
        ∀ i, (E i.1).stalkIdeal x = Ideal.span {z (c i)}) ∧
      ∃ s : Finset (Fin m), Z.stalkIdeal x = Ideal.span (z '' ↑s) := by
    intro x hx
    obtain ⟨m, c, y, -, hdim, hmax, hZx⟩ := exists_adaptedParameters_of_smooth f Z hx
    refine ⟨m, y, ⟨hmax.symm, hdim⟩, ⟨fun i => i.1.elim0, fun i => i.1.elim0, fun i => i.1.elim0⟩,
      Finset.univ.filter (fun j : Fin m => j.val < c), ?_⟩
    rw [hZx]
    congr 2
    ext j
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
  exact isSmoothDivisor_totalTransformFamily f E Z hE hZ (Sum.inr PUnit.unit)

omit [CharZero k] in
/-- The multiplicity of [Kol07, 58.1] at every point of the exceptional divisor: for a smooth
hypersurface `H` containing the smooth centre `Z`, the pull-back `π^* H` is not contained in `F²`
at any point `q` of `B_Z X` over the centre; the exceptional multiplicity of `π^* H` is exactly one.
Through the chart bridge at `q` (`exists_stalk_equiv_localization_chart_of_smooth`), this is
`algebraMap_transformElem_notMem_map_span_x` for the equation `h` of `H` at `π q`, which has order
one and lies in the centre. -/
theorem stalkIdeal_comap_not_le_exceptionalDivisor_sq {H : X.IdealSheafData}
    (hH : IsSmoothDivisor H) (hZH : H ≤ Z) (q : Z.blowUp)
        (hq : Z.blowUpπ q ∈ Z.support) :
    ¬ (H.comap Z.blowUpπ).stalkIdeal q ≤ Z.exceptionalDivisor.stalkIdeal q ^ 2 :=
        by
  classical
  intro hle
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hzH : Z.blowUpπ q ∈ H.support := Scheme.IdealSheafData.support_antitone hZH hq
  obtain ⟨h, hh, hh2, hspan⟩ := hH.2 _ hzH
  have hord : ordElem h = 1 := ordElem_eq_one_iff.mpr ⟨hh, hh2⟩
  have hreg : IsRegularLocalRing (X.presheaf.stalk (Z.blowUpπ q)) :=
    isRegularLocalRing_stalk f _
  obtain ⟨n', y, ρ, hn', hy, hZ', 𝔮, hprime, hle', e, he⟩ :=
    exists_stalk_equiv_localization_chart_of_smooth f Z q hq
  have hhZ : h ∈ chartCenter y ρ ^ 1 := by
    rw [pow_one, ← hZ']
    exact Scheme.IdealSheafData.stalkIdeal_mono hZH _ (hspan ▸ Ideal.mem_span_singleton_self h)
  have hcomp : e.toRingHom.comp (Z.blowUpπ.stalkMap q).hom =
      (algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)).comp
        (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ)) := RingHom.ext he
  -- `e` is used only through `e.toRingHom` (unifying through `⇑e` times out)
  have hψ : e.toRingHom (Z.blowUpπ.stalkMap q (y ρ)) =
      algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
        (algebraMap (X.presheaf.stalk (Z.blowUpπ q)) (chartRing y ρ) (y ρ)) :=
    RingHom.congr_fun hcomp (y ρ)
  -- `π^♯ h ∈ F^1 · F` at `q`
  have hmem0 : Z.blowUpπ.stalkMap q h ∈
      ((Z.comap Z.blowUpπ) ^ 1 * Z.exceptionalDivisor).stalkIdeal q := by
    rw [Scheme.IdealSheafData.stalkIdeal_mul, Scheme.IdealSheafData.stalkIdeal_pow, pow_one]
    have hZF : (Z.comap Z.blowUpπ).stalkIdeal q =
        Z.exceptionalDivisor.stalkIdeal q := rfl
    rw [hZF, ← sq]
    refine hle ?_
    rw [Scheme.IdealSheafData.stalkIdeal_comap, hspan]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self h)
  -- transport to the chart: `h / y_ρ ∈ e(F_q) = (y_ρ)`
  have hmem := algebraMap_transformElem_mem_map_of_mem q y hy hn' ρ hZ' 𝔮 e he
    Z.exceptionalDivisor hhZ hmem0
  have hF : Z.exceptionalDivisor.stalkIdeal q =
      Ideal.span {Z.blowUpπ.stalkMap q (y ρ)} :=
    stalkIdeal_comap_eq_span_of_chart q y ρ hZ' 𝔮 e he
  rw [hF, Ideal.map_span, Set.image_singleton, hψ] at hmem
  apply Hironaka.Local.algebraMap_transformElem_notMem_map_span_x y hy hn' ρ 𝔮 hle' hhZ hord
  rwa [Ideal.map_span, Set.image_singleton]

end Exceptional

end Hironaka.Sequence

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]
variable (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ f)) (H : X.IdealSheafData)
  (hH : IsSmoothDivisor H) (hZH : H ≤ Z)

include n hZ hH hZH

/-- [Wlo05, Lemma 2.7.4 (3)], the step hidden in the proof of [Kol07, Theorem 80 (1)]: for a smooth
centre `Z` contained in a smooth hypersurface `H`, the strict transform of `H` under the blow-up of
`Z` is the marked transform `(π)⁻¹_*(𝒪(−H), 1)`: stalkwise `π^* H = (u' y)` with `y` the (prime)
equation of the exceptional divisor and `u' ∉ (y)`
(`stalkIdeal_comap_not_le_exceptionalDivisor_sq`), so the saturation by `(y)` is the colon by `(y)`
(`colon_pow_le_colon_of_prime`). -/
theorem strictTransform_eq_markedTransform_one : H.strictTransform Z = H.markedTransform Z 1 := by
  classical
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := hZ
  have hF : Z.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π Z
  have hHF : H.comap Z.blowUpπ ≤ Z.exceptionalDivisor := by
    have hle1 : H.LeOrdAlong Z.support ((1 : ℕ) : ℕ∞) := fun η hη =>
      (hH.ordAlongEq_one_of_le hZH η hη).ge
    have := comap_le_pow_comap_of_leOrdAlong f n Z H hle1
    rwa [pow_one] at this
  have hFsm : IsSmoothDivisor Z.exceptionalDivisor :=
    Hironaka.Sequence.isSmoothDivisor_exceptionalDivisor_of_smooth f n Z
  have hπ : SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) :=
    smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n Z
  have hπs : Smooth (Z.blowUpπ ≫ f) := SmoothOfRelativeDimension.smooth n _
  refine le_antisymm ?_ ?_
  · refine le_of_stalkIdeal_le fun q => ?_
    change ((H.comap Z.blowUpπ).saturate
        Z.exceptionalDivisor).stalkIdeal q ≤
      ((H.comap Z.blowUpπ).colon (Z.exceptionalDivisor ^ 1)).stalkIdeal q
    rw [stalkIdeal_saturate_of_isInvertible _ hF, pow_one, stalkIdeal_colon_of_isInvertible _ hF]
    refine iSup_le fun i => ?_
    by_cases hq : Z.blowUpπ q ∈ Z.support
    · obtain ⟨y', hy', hFq⟩ := hF.exists_mem_nonZeroDivisors_stalkIdeal_eq_span q
      have hzH : Z.blowUpπ q ∈ H.support := support_antitone hZH hq
      obtain ⟨h, -, -, hspan⟩ := hH.2 _ hzH
      have hHq : (H.comap Z.blowUpπ).stalkIdeal q =
          Ideal.span {(Z.blowUpπ.stalkMap q).hom h} := by
        rw [stalkIdeal_comap, hspan, Ideal.map_span, Set.image_singleton]
      have hu : (Z.blowUpπ.stalkMap q).hom h ∈ Ideal.span {y'} := by
        rw [← hFq]
        exact stalkIdeal_mono hHF q (hHq ▸ Ideal.mem_span_singleton_self _)
      obtain ⟨u', hu'⟩ := Ideal.mem_span_singleton'.mp hu
      have hy0 : y' ≠ 0 := nonZeroDivisors.ne_zero hy'
      have hprime : Prime y' := by
        rw [← Ideal.span_singleton_prime hy0, ← hFq]
        have hqF : q ∈ Z.exceptionalDivisor.support :=
          (mem_support_comap_iff_apply Z _ q).mpr hq
        obtain ⟨a, ha, ha2, haspan⟩ := hFsm.2 q hqF
        rw [haspan]
        have hreg : IsRegularLocalRing (Z.blowUp.presheaf.stalk q) :=
          isRegularLocalRing_stalk (Z.blowUpπ ≫ f) q
        have hq1 := (IsRegularLocalRing.quotient_span_singleton ha ha2).1
        have hdom := isDomain_of_isRegularLocalRing (Z.blowUp.presheaf.stalk
            q ⧸ Ideal.span {a})
        exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom
      have hnd : ¬ y' ∣ u' := by
        rintro ⟨c, hc⟩
        apply Hironaka.Sequence.stalkIdeal_comap_not_le_exceptionalDivisor_sq f n Z hH hZH q hq
        rw [hHq, hFq, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
          Ideal.mem_span_singleton']
        exact ⟨c, by rw [← hu', hc]; ring⟩
      rw [hHq, hFq, ← hu']
      exact Hironaka.Local.colon_pow_le_colon_of_prime hy' hprime hnd i
    · have hFq : Z.exceptionalDivisor.stalkIdeal q = ⊤ := by
        change (Z.comap Z.blowUpπ).stalkIdeal q = ⊤
        rw [stalkIdeal_comap, stalkIdeal_eq_top_of_notMem_support Z hq, Ideal.map_top]
      rw [hFq, Ideal.top_pow]
  · exact colon_pow_le_saturate (I := H.comap Z.blowUpπ) (K :=
      Z.exceptionalDivisor) 1

/-- [Wlo05, Lemma 2.7.4 (2)], "`u' = u/y` is a parameter": the strict transform of a smooth
hypersurface containing the smooth centre is a smooth hypersurface of `B_Z X`: `V(H_1) ≅ B_Z H`
through the closed immersion `blowUpMap H.subschemeι Z`, smooth of relative dimension `n − 1`. -/
theorem isSmoothDivisor_strictTransform_of_le : IsSmoothDivisor (H.strictTransform Z) := by
  have := hZ
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    rw [hH.eq_top_of_smoothOfRelativeDimension_zero f, strictTransform_top_right]
    exact Hironaka.Snc.isSmoothDivisor_top
  · have : SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n Z
    have : SmoothOfRelativeDimension (n - 1) (H.subschemeι ≫ f) :=
      smoothOfRelativeDimension_of_isSmoothDivisor f n H hH
    obtain ⟨φ, hφ⟩ := exists_iso_subscheme_comap_of_ker_le H.subschemeι Z
      (by rwa [Scheme.IdealSheafData.ker_subschemeι])
    have : Smooth ((Z.comap H.subschemeι).subschemeι ≫ H.subschemeι ≫ f) := by
      rw [← Category.assoc, ← hφ, Category.assoc]
      infer_instance
    have : SmoothOfRelativeDimension (n - 1)
        ((Z.comap H.subschemeι).blowUpπ ≫ H.subschemeι ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth (H.subschemeι ≫ f) (n - 1)
        (Z.comap H.subschemeι)
    have hsq : Scheme.Hom.blowUpMap H.subschemeι Z ≫ Z.blowUpπ =
        (Z.comap H.subschemeι).blowUpπ ≫ H.subschemeι :=
      blowUpMap_π H.subschemeι Z
    have : IsClosedImmersion (Scheme.Hom.blowUpMap H.subschemeι Z) :=
      isClosedImmersion_blowUpMap H Z
    have hker : (Scheme.Hom.blowUpMap H.subschemeι Z).ker = H.strictTransform Z :=
      ker_blowUpMap_subschemeι H Z
    obtain ⟨e, he⟩ : ∃ e : (Z.comap H.subschemeι).blowUp ≅
        (H.strictTransform Z).subscheme,
        e.hom ≫ (H.strictTransform Z).subschemeι = Scheme.Hom.blowUpMap H.subschemeι Z := by
      rw [← hker]
      exact ⟨asIso (Scheme.Hom.blowUpMap H.subschemeι Z).toImage,
          (Scheme.Hom.blowUpMap H.subschemeι Z).toImage_imageι⟩
    have key : SmoothOfRelativeDimension (n - 1)
        (e.hom ≫ (H.strictTransform Z).subschemeι ≫ Z.blowUpπ ≫ f) := by
      rw [← Category.assoc, he, ← Category.assoc, hsq, Category.assoc]
      infer_instance
    have : SmoothOfRelativeDimension (n - 1)
        ((H.strictTransform Z).subschemeι ≫ Z.blowUpπ ≫ f) := by
      have h2 : SmoothOfRelativeDimension (0 + (n - 1))
          (e.inv ≫ e.hom ≫ (H.strictTransform Z).subschemeι ≫ Z.blowUpπ ≫ f) :=
              inferInstance
      rwa [e.inv_hom_id_assoc, Nat.zero_add] at h2
    exact isSmoothDivisor_of_smoothOfRelativeDimension (Z.blowUpπ ≫ f) n hn
        (H.strictTransform Z)

end AlgebraicGeometry.Scheme.IdealSheafData
