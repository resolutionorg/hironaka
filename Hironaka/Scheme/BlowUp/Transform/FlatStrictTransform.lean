/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Hironaka.Scheme.BlowUp.Transform.Defs
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.RingTheory.Ideal.Pure

/-!
# The strict transform in the flat case equals the total transform

If a scheme `X` over `S` is flat over `S` at all points lying over the centre `Z`, its strict
transform under the blow-up of `S` along `Z` is the base change `X ×_S S'` [Sta, Tag 080F]. Here
`Y = V(J) ⊆ X` is a closed subscheme, `π : B ⟶ X` a morphism whose inverse image `E = D.comap π`
of the centre is invertible (the blow-up and its exceptional ideal in the applications), and the
hypothesis is the flatness of the stalk maps `𝒪_{X, ι y} → 𝒪_{Y, y}` at the points `y` of `Y`
over `Z = V(D)`.

The strict transform `Jˢ = (J* : E^∞)` equals `J*` as soon as `(J* : E) = J*`
(`saturate_eq_self_of_colon_eq`). That inclusion is local on `B`: on an affine open `U' ⊆ B` over
an affine open `U ⊆ X`, with `E(U') = (e)`, `e` a nonzerodivisor, and `J*(U') = J(U)·Γ(U')`
(`ideal_comap_of_le`), it says that `u e ∈ J(U)Γ(U')` forces `u ∈ J(U)Γ(U')`. Membership in an
ideal is checked at every maximal ideal `Q` of `Γ(U')` in the elementary form "some `t ∉ Q` has
`t u` in the ideal" (`Ideal.mem_of_forall_exists_mul_mem`). If `e ∉ Q`, take `t = e`. If
`J(U)Γ(U') ⊄ Q`, take `t` in `J(U)Γ(U') ∖ Q`. Otherwise the point `b ∈ U'` of `Q` lies in the
exceptional divisor and in `V(J*)`, so `x = π b` lies in `Z ∩ V(J)` and is the image of a point `y`
of `Y` at which the closed immersion is flat. A flat surjective ring map out of a local ring is
injective — its kernel is a pure ideal (`Ideal.Pure`, [Sta, Tag 04PS]), and a pure ideal `K` of a
local ring is zero: `x ∈ K` has `x = x k` for some `k ∈ K ⊆ 𝔪`, and `1 − k` is a unit. Since the
sections of `J` over `U` vanish on `Y`, their germs at `x` are killed by the stalk map, hence are
zero: every `j ∈ J(U)` is annihilated by some `s ∉ 𝔭_x` (the stalk is the localization at `𝔭_x`).
Writing `u e = ∑ cᵢ φ(jᵢ)` with finitely many `jᵢ ∈ J(U)` and taking `s` the product of the
corresponding annihilators, `φ(s) u e = 0`, so `φ(s) u = 0` because `e` is a nonzerodivisor, and
`t = φ(s) ∉ Q` does the job.

This is a different proof from the Stacks Project's (which treats an arbitrary `X → S` through the
torsion of `N ⊗_A A[I/a]`): for a closed subscheme, flatness of the immersion at `y` forces the
ideal to vanish at `ι y`, which is what makes the total transform already saturated there.

## Main declarations

* `AlgebraicGeometry.injective_of_flat_of_surjective`: a flat surjective ring map from a local ring
  to a nontrivial ring is injective.
* `IdealSheafData.germ_eq_zero_of_flat_stalkMap`, `exists_mul_eq_zero_of_flat_stalkMap`: the
  sections of `J` over an affine open vanish at a point of `V(J)` where the closed immersion is
  flat.
* `Ideal.mem_of_forall_exists_mul_mem`: the elementary localization principle for membership.
* `AlgebraicGeometry.colon_comap_le_comap_of_flat`, `strictTransformAlong_eq_comap_of_flat` (for
  any `π` with invertible `D.comap π`).
-/

public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/-- A flat surjective ring homomorphism out of a local ring into a nontrivial ring is injective: its
kernel is a pure ideal [Sta, Tag 04PS], and a pure ideal of a local ring is zero. -/
theorem injective_of_flat_of_surjective {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [Nontrivial S] (f : R →+* S) (hf : f.Flat) (hs : Function.Surjective f) :
    Function.Injective f := by
  let _ : Algebra R S := f.toAlgebra
  have hflat : Module.Flat R S := hf
  have hsurj : Function.Surjective (Algebra.ofId R S) := hs
  have hpure : Module.Flat R (R ⧸ RingHom.ker f) :=
    Module.Flat.of_linearEquiv (Ideal.quotientKerAlgEquivOfSurjective hsurj).toLinearEquiv
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hxk : x ∈ RingHom.ker f := hx
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_eq_mul_of_pure hxk
  have hym : y ∈ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f) hy
  have hu : IsUnit (1 - y) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits y hym
  have hx0 : x * (1 - y) = 0 := by rw [mul_sub, mul_one, ← hxy, sub_self]
  exact hu.mul_left_eq_zero.mp hx0

/-- The elementary localization principle for membership in an ideal: `u ∈ I` as soon as every
maximal ideal `Q` admits `t ∉ Q` with `t u ∈ I` (the ideal `(I : u)` is then contained in no maximal
ideal, hence is the unit ideal). -/
theorem _root_.Ideal.mem_of_forall_exists_mul_mem {R : Type*} [CommRing R] {I : Ideal R} {u : R}
    (h : ∀ Q : Ideal R, Q.IsMaximal → ∃ t ∉ Q, t * u ∈ I) : u ∈ I := by
  by_contra hu
  have hne : I.colon ({u} : Set R) ≠ ⊤ := fun htop =>
    hu (by simpa using Submodule.mem_colon_singleton.mp ((Ideal.eq_top_iff_one _).mp htop))
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨t, htQ, htu⟩ := h Q hQ
  exact htQ (hle (Submodule.mem_colon_singleton.mpr (by simpa using htu)))

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- At a point `y` of the closed subscheme `V(J)` where the closed immersion is flat, the germs of
the sections of `J` vanish: the stalk map is flat and surjective out of a local ring, hence
injective, and it kills the germs of `J` because the sections of `J` restrict to zero on `V(J)`. -/
theorem germ_eq_zero_of_flat_stalkMap (J : X.IdealSheafData) (y : J.subscheme)
    (hflat : (J.subschemeι.stalkMap y).hom.Flat) (U : X.affineOpens) {x : X}
    (hxy : J.subschemeι y = x) (hx : x ∈ U.1) {j : Γ(X, U)} (hj : j ∈ J.ideal U) :
    X.presheaf.germ U.1 x hx j = 0 := by
  subst hxy
  have hinj : Function.Injective (J.subschemeι.stalkMap y).hom :=
    injective_of_flat_of_surjective _ hflat (J.subschemeι.stalkMap_surjective y)
  apply hinj
  rw [map_zero]
  have h1 := Scheme.Hom.germ_appLE_apply J.subschemeι U.1 (J.subschemeι ⁻¹ᵁ U.1) le_rfl
    (z := y) hx hx j
  rw [Scheme.Hom.appLE_eq_app] at h1
  have h2 : (J.subschemeι.app U.1) j = 0 := by
    rw [← RingHom.mem_ker, J.ker_subschemeι_app U]
    exact hj
  rw [← h1, h2, map_zero]

/-- The affine form: at the point `fromSpec q` of `U`, image of a point `y` of `V(J)` where the
closed immersion is flat, every section `j ∈ J(U)` is annihilated by some `s ∉ q`. -/
theorem exists_mul_eq_zero_of_flat_stalkMap (J : X.IdealSheafData) (U : X.affineOpens)
    (q : PrimeSpectrum Γ(X, U)) (y : J.subscheme) (hy : J.subschemeι y = U.2.fromSpec q)
    (hflat : (J.subschemeι.stalkMap y).hom.Flat) {j : Γ(X, U)} (hj : j ∈ J.ideal U) :
    ∃ s ∉ q.asIdeal, s * j = 0 := by
  have hU : IsAffineOpen U.1 := U.2
  have hq : hU.fromSpec q ∈ U.1 := by
    have : q ∈ hU.fromSpec ⁻¹ᵁ U.1 := by rw [hU.fromSpec_preimage_self]; trivial
    exact this
  have hgerm' : X.presheaf.germ U.1 (hU.fromSpec q) hq j = 0 :=
    germ_eq_zero_of_flat_stalkMap J y hflat U hy hq hj
  have hloc := hU.isLocalization_stalk' q hq
  have := (@IsLocalization.map_eq_zero_iff Γ(X, U) _ q.asIdeal.primeCompl
    (X.presheaf.stalk (hU.fromSpec q)) _
    (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, hq⟩) hloc j).mp hgerm'
  obtain ⟨⟨s, hs⟩, hsj⟩ := this
  exact ⟨s, hs, hsj⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme

variable {B X : Scheme.{u}}

/-- The local statement of [Sta, Tag 080F]: for `π : B ⟶ X` with
invertible `E = D.comap π`, if the closed immersion `V(J) → X` is flat at every point over
`Z = V(D)`, then `(J* : E) ≤ J*`. -/
theorem colon_comap_le_comap_of_flat (π : B ⟶ X) (D J : X.IdealSheafData)
    (hE : (D.comap π).IsInvertible)
    (hflat : ∀ y : J.subscheme, J.subschemeι y ∈ D.support →
      (J.subschemeι.stalkMap y).hom.Flat) :
    (J.comap π).colon (D.comap π) ≤ J.comap π := by
  classical
  -- a cover of `B` by affine opens `U'` over affine opens `U` of `X` on which `E` is generated by
  -- a nonzerodivisor
  have hcov : ∀ b : B, ∃ (U : X.affineOpens) (U' : B.affineOpens), b ∈ U'.1 ∧
      U'.1 ≤ π ⁻¹ᵁ U.1 ∧ ∃ e ∈ nonZeroDivisors Γ(B, U'), (D.comap π).ideal U' = Ideal.span {e} := by
    intro b
    obtain ⟨W, hbW, e₀, he₀, hEW⟩ := hE b
    obtain ⟨U, V, hbV, hVU⟩ := IdealSheafData.exists_affineOpens_le_preimage π b
    have hW : IsAffineOpen W.1 := W.2
    obtain ⟨f, hfle, hbf⟩ := hW.exists_basicOpen_le (V := W.1 ⊓ V.1) ⟨b, ⟨hbW, hbV⟩⟩ hbW
    obtain ⟨e, he, hEe⟩ :=
      IdealSheafData.exists_regular_generator_affineBasicOpen (D.comap π) W he₀ hEW f
    exact ⟨U, B.affineBasicOpen f, hbf, (hfle.trans inf_le_right).trans hVU, e, he, hEe⟩
  choose U U' hbU' hle e he hEe using hcov
  refine IdealSheafData.le_of_iSup_eq_top U' ?_ fun b => ?_
  · exact top_le_iff.mp fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hbU' z⟩
  -- the local statement on `U' b`
  set φ := π.appLE (U b).1 (U' b).1 (hle b) with hφ
  rw [IdealSheafData.ideal_colon_of_isInvertible _ _ hE (U' b), hEe b, Ideal.colon_span,
    IdealSheafData.ideal_comap_of_le J π (U b) (U' b) (hle b)]
  intro u hu
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hu
  refine Ideal.mem_of_forall_exists_mul_mem fun Q hQ => ?_
  by_cases heQ : e b ∈ Q
  · by_cases hJQ : (J.ideal (U b)).map φ.hom ≤ Q
    · -- the point of `Q` lies over `Z ∩ V(J)`: the flat case
      have hU : IsAffineOpen (U b).1 := (U b).2
      have hU' : IsAffineOpen (U' b).1 := (U' b).2
      let q : PrimeSpectrum Γ(B, U' b) := ⟨Q, hQ.isPrime⟩
      let p : PrimeSpectrum Γ(X, U b) := PrimeSpectrum.comap φ.hom q
      have hp : p.asIdeal = Q.comap φ.hom := rfl
      -- `π (fromSpec q) = fromSpec p`
      have hπ : π (hU'.fromSpec q) = hU.fromSpec p := by
        have := congrArg (fun g => g q) (IsAffineOpen.SpecMap_appLE_fromSpec π hU hU' (hle b))
        exact this.symm
      have hxU : hU.fromSpec p ∈ (U b).1 := by
        have : p ∈ hU.fromSpec ⁻¹ᵁ (U b).1 := by rw [hU.fromSpec_preimage_self]; trivial
        exact this
      have hJp : J.ideal (U b) ≤ p.asIdeal := Ideal.map_le_iff_le_comap.mp hJQ
      have hDp : D.ideal (U b) ≤ p.asIdeal := by
        refine Ideal.map_le_iff_le_comap.mp ?_
        rw [← IdealSheafData.ideal_comap_of_le D π (U b) (U' b) (hle b), hEe b, Ideal.span_le,
          Set.singleton_subset_iff]
        exact heQ
      have hxJ : hU.fromSpec p ∈ J.support := by
        rw [IdealSheafData.mem_support_iff_of_mem hxU, IdealSheafData.fromSpec_mem_zeroLocus_iff]
        exact hJp
      have hxD : hU.fromSpec p ∈ D.support := by
        rw [IdealSheafData.mem_support_iff_of_mem hxU, IdealSheafData.fromSpec_mem_zeroLocus_iff]
        exact hDp
      obtain ⟨y, hy⟩ : ∃ y, J.subschemeι y = hU.fromSpec p := by
        have : hU.fromSpec p ∈ Set.range J.subschemeι := by
          rw [IdealSheafData.range_subschemeι]; exact hxJ
        exact this
      have hfl := hflat y (hy ▸ hxD)
      -- `u e = ∑ cᵢ φ(jᵢ)` with `jᵢ ∈ J(U)`; each `jᵢ` is killed by some `sᵢ ∉ p`
      obtain ⟨T, hT, huT⟩ := Submodule.mem_span_finite_of_mem_span hu
      have hTJ : ∀ t ∈ T, ∃ j ∈ J.ideal (U b), φ.hom j = t := fun t ht => hT ht
      choose! jT hjT hφj using hTJ
      have hann : ∀ t ∈ T, ∃ s ∉ p.asIdeal, s * jT t = 0 := fun t ht =>
        IdealSheafData.exists_mul_eq_zero_of_flat_stalkMap J (U b) p y hy hfl (hjT t ht)
      choose! sT hsT hsj using hann
      set s := ∏ t ∈ T, sT t with hs
      have hsp : s ∉ p.asIdeal :=
        Submonoid.prod_mem (p.asIdeal.primeCompl)
          (fun t ht => hsT t ht : ∀ t ∈ T, sT t ∈ p.asIdeal.primeCompl)
      -- `φ(s) · (u e) = 0`
      have hzero : φ.hom s * (u * e b) = 0 := by
        obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp huT
        rw [← hc, Finset.mul_sum]
        refine Finset.sum_eq_zero fun t ht => ?_
        rw [smul_eq_mul, mul_left_comm, ← hφj t ht, ← map_mul, hs, ← Finset.prod_erase_mul _ _ ht,
          mul_assoc, hsj t ht, mul_zero, map_zero, mul_zero]
      have hsu : φ.hom s * u = 0 :=
        (mem_nonZeroDivisors_iff.mp (he b)).2 _ (by rw [mul_assoc]; exact hzero)
      refine ⟨φ.hom s, fun hsQ => hsp ?_, by rw [hsu]; exact zero_mem _⟩
      rw [hp, Ideal.mem_comap]
      exact hsQ
    · -- some `t ∈ J(U)Γ(U')` is outside `Q`
      obtain ⟨t, htI, htQ⟩ := IsConcreteLE.not_le_iff_exists.mp hJQ
      exact ⟨t, htQ, Ideal.mul_mem_right u _ htI⟩
  · -- `e ∉ Q`: take `t = e`
    exact ⟨e b, heQ, by rw [mul_comm]; exact hu⟩

/-- **The flat case of the strict transform** [Sta, Tag 080F]: if the closed immersion `V(J) → X`
is flat at every point over the centre, the strict transform of `J` along `π` is its total
transform. -/
theorem strictTransformAlong_eq_comap_of_flat (π : B ⟶ X) (D J : X.IdealSheafData)
    (hE : (D.comap π).IsInvertible)
    (hflat : ∀ y : J.subscheme, J.subschemeι y ∈ D.support →
      (J.subschemeι.stalkMap y).hom.Flat) :
    J.strictTransformAlong π (D.comap π) = J.comap π :=
  IdealSheafData.saturate_eq_self_of_colon_eq _ _
    (le_antisymm (colon_comap_le_comap_of_flat π D J hE hflat)
      (IdealSheafData.le_colon_self _ _))

end AlgebraicGeometry
