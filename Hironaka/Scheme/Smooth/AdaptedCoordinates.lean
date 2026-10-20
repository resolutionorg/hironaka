/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Stalk
public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Hironaka.Algebra.Local.QuotientParameters
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Scheme.Smooth.SubschemeStalk
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Local parameters adapted to a smooth center

`X` is a scheme over a field `k` (`f : X ⟶ Spec k`), `Z` an ideal sheaf with closed subscheme
`V(Z)`, `x ∈ V(Z)`, `Z_x = stalkIdeal Z x ⊆ 𝒪_{X,x}` the stalk of `Z`, and
`𝒪_{V(Z),x} = 𝒪_{X,x}/Z_x` (`stalkQuotientEquiv`). For `X` smooth of relative dimension `n` and
`V(Z)` smooth of relative dimension `n − r` over a perfect field, this file produces Kollár's
adapted local coordinates: a regular system of parameters of `𝒪_{X,x}` whose first `r` members
generate `Z_x` ("`Z = (z_{j_1} = ⋯ = z_{j_s} = 0)`", [Kol07, Definition 24, (4)]; the coordinates
"such that `Z = (x_1 = ⋯ = x_r = 0)`" of [Kol07, Definition 60]).

* `𝒪_{X,x}` is regular for `f` smooth ([Sta, Tag 00TT]; `Scheme.isRegularAt_of_mem_smoothLocus`
  at a point of the smooth locus, which is everything).
* `𝒪_{X,x}/Z_x ≅ 𝒪_{V(Z),x}` is regular for `V(Z)` smooth (the same for `V(Z)`); at a closed
  point of `V(Z)` smooth of relative dimension `n − r`, its dimension is `n − r`
  (`Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed` for `V(Z)`).
* At any `x ∈ V(Z)`, `dim 𝒪_{X,x}/Z_x + r = dim 𝒪_{X,x}`: the dimension formula
  `dim 𝒪 + trdeg_k κ = n` of `Hironaka/Algebra/RegularSmooth/SchemeForms.lean` for `X` and for
  `V(Z)` gives `dim 𝒪_{X,x} + t = n` and `dim 𝒪_{V(Z),x} + t' = n − r` with `t, t'` the
  transcendence degrees of the residue fields, which agree because the stalk map of the closed
  immersion induces a `k`-isomorphism of residue fields (`residueFieldStalkEquiv`, with the
  `k`-structures `Scheme.Hom.stalkAlgebra` compatible along `V(Z) ⟶ X ⟶ Spec k`).
* Adapted parameters: [Sta, Tag 00NR] in the form
  `IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt` of
  `Hironaka/Algebra/Local/QuotientParameters.lean`, applied to `R = 𝒪_{X,x}` and `I = Z_x`, gives a
  regular system of parameters `y` with `Z_x = (y_0, …, y_{c-1})`; `c = r` because `dim R/I + c =
  dim R` and `dim R/I + r = dim R`. At a closed point `dim R = n`, so `y` has `n` members
  (`exists_adaptedCoordinates`).

The differentials of these parameters form a basis of the differentials at the point
(`Hironaka/Scheme/Smooth/DifferentialBasis.lean`), which is how they are spread out to étale
coordinates adapted to the center on an affine neighbourhood
(`Hironaka/Scheme/Smooth/EtaleCoordinatesAdapted.lean`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing Scheme.IdealSheafData

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The stalks of a scheme smooth over a field are regular local rings (the last sentence of
[Sta, Tag 00TT]): every point lies in the smooth locus, and `Scheme.isRegularAt_of_mem_smoothLocus`
applies. -/
theorem isRegularLocalRing_stalk (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  Scheme.isRegularAt_of_mem_smoothLocus f
    (by rw [Scheme.Hom.smoothLocus_eq_top_iff.mpr inferInstance]; trivial)

variable (Z : X.IdealSheafData)

/-- If `V(Z)` is smooth over `k`, `𝒪_{X,x}/Z_x ≅ 𝒪_{V(Z),x}` is a regular local ring at every
`x ∈ V(Z)`. -/
theorem isRegularLocalRing_quotient_stalkIdeal (f : X ⟶ Spec (.of k))
    [Smooth (Z.subschemeι ≫ f)] {x : X} (hx : x ∈ Z.support) :
    IsRegularLocalRing (X.presheaf.stalk x ⧸ Z.stalkIdeal x) := by
  obtain ⟨z, rfl⟩ := Z.exists_subschemeι_eq hx
  have := isRegularLocalRing_stalk (Z.subschemeι ≫ f) z
  exact IsRegularLocalRing.of_ringEquiv (Z.stalkQuotientEquiv z).symm

/-- If `V(Z)` is smooth of relative dimension `d` over the perfect field `k`, then
`dim 𝒪_{X,x}/Z_x = d` at every closed point `x ∈ V(Z)` (the closed-point dimension formula,
applied to `V(Z)`). -/
theorem ringKrullDim_quotient_stalkIdeal_of_isClosed [PerfectField k] (f : X ⟶ Spec (.of k))
    (d : ℕ) [SmoothOfRelativeDimension d (Z.subschemeι ≫ f)] {x : X} (hxZ : x ∈ Z.support)
    (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x ⧸ Z.stalkIdeal x) = d := by
  obtain ⟨z, rfl⟩ := Z.exists_subschemeι_eq hxZ
  rw [ringKrullDim_eq_of_ringEquiv (Z.stalkQuotientEquiv z)]
  exact Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed (Z.subschemeι ≫ f) d
    (Z.isClosed_singleton_of_subschemeι_eq rfl hx)

/-- The `k`-algebra structures `Scheme.Hom.stalkAlgebra` of `𝒪_{X,ι z}` (through `f`) and of
`𝒪_{V(Z),z}` (through `ι ≫ f`) are compatible with the stalk map of `ι : V(Z) ⟶ X`. -/
theorem stalkMap_subschemeι_algebraMap (f : X ⟶ Spec (.of k)) (z : Z.subscheme) (c : k) :
    letI := f.stalkAlgebra (Z.subschemeι z)
    letI := (Z.subschemeι ≫ f).stalkAlgebra z
    Z.subschemeι.stalkMap z (algebraMap k (X.presheaf.stalk (Z.subschemeι z)) c) =
      algebraMap k (Z.subscheme.presheaf.stalk z) c := by
  let := f.stalkAlgebra (Z.subschemeι z)
  let := (Z.subschemeι ≫ f).stalkAlgebra z
  have hx₁ : Z.subschemeι z ∈ f ⁻¹ᵁ ⊤ := trivial
  have hz₁ : z ∈ (Z.subschemeι ≫ f) ⁻¹ᵁ ⊤ := trivial
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫
        X.presheaf.germ (f ⁻¹ᵁ ⊤) (Z.subschemeι z) hx₁ ≫ Z.subschemeι.stalkMap z =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ f).app ⊤ ≫
        Z.subscheme.presheaf.germ ((Z.subschemeι ≫ f) ⁻¹ᵁ ⊤) z hz₁ := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_app]
    rfl
  have h' := congrArg (fun φ : CommRingCat.of k ⟶ Z.subscheme.presheaf.stalk z => φ.hom c) h
  change (Z.subschemeι.stalkMap z).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫
    X.presheaf.germ (f ⁻¹ᵁ ⊤) (Z.subschemeι z) hx₁).hom c) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ f).app ⊤ ≫
        Z.subscheme.presheaf.germ ((Z.subschemeι ≫ f) ⁻¹ᵁ ⊤) z hz₁).hom c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h' ⊢
  exact h'

/-- The residue fields of `𝒪_{X,ι z}` and `𝒪_{V(Z),z}` have the same transcendence degree over
`k` (they are `k`-isomorphic through the stalk map of the closed immersion). -/
theorem trdeg_residueField_stalk_subschemeι (f : X ⟶ Spec (.of k)) (z : Z.subscheme) :
    letI := f.stalkAlgebra (Z.subschemeι z)
    letI := (Z.subschemeι ≫ f).stalkAlgebra z
    Algebra.trdeg k (ResidueField (Z.subscheme.presheaf.stalk z)) =
      Algebra.trdeg k (ResidueField (X.presheaf.stalk (Z.subschemeι z))) := by
  let := f.stalkAlgebra (Z.subschemeι z)
  let := (Z.subschemeι ≫ f).stalkAlgebra z
  let e : ResidueField (X.presheaf.stalk (Z.subschemeι z)) ≃ₐ[k]
      ResidueField (Z.subscheme.presheaf.stalk z) :=
    AlgEquiv.ofRingEquiv (f := Z.residueFieldStalkEquiv z) fun c => by
      change Z.residueFieldStalkEquiv z (IsLocalRing.residue _ (algebraMap k _ c)) =
        IsLocalRing.residue _ (algebraMap k _ c)
      rw [Z.residueFieldStalkEquiv_residue, stalkMap_subschemeι_algebraMap Z f z c]
  exact e.trdeg_eq.symm

/-- Cancellation in `WithBot ℕ∞`: from `a + t = n` and `b + t = m` with `m + r = n` (all finite
except possibly `t`, which is then finite too), `b + r = a`. -/
theorem natCast_add_natCast_eq_of_add_eq {a b n m r : ℕ} {t : ℕ∞}
    (hX : ((a : ℕ) : WithBot ℕ∞) + (t : WithBot ℕ∞) = (n : WithBot ℕ∞))
    (hZ : ((b : ℕ) : WithBot ℕ∞) + (t : WithBot ℕ∞) = (m : WithBot ℕ∞)) (hm : m + r = n) :
    ((b : ℕ) : WithBot ℕ∞) + (r : WithBot ℕ∞) = (a : WithBot ℕ∞) := by
  have ht : t ≠ ⊤ := by
    rintro rfl
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, add_top, ← WithBot.coe_natCast] at hX
    exact ENat.top_ne_natCast n (WithBot.coe_inj.mp hX)
  lift t to ℕ using ht with t' ht'
  have h1 : a + t' = n := by exact_mod_cast hX
  have h2 : b + t' = m := by exact_mod_cast hZ
  have h3 : b + r = a := by omega
  exact_mod_cast h3

/-- For `X` smooth of relative dimension `n` and `V(Z)` smooth of relative dimension `n − r` over
the perfect field `k` (`r ≤ n`), at every `x ∈ V(Z)`, `dim 𝒪_{X,x}/Z_x + r = dim 𝒪_{X,x}`: the
dimension formula `dim 𝒪 + trdeg_k κ = n` of [Sta, Tag 0A21, (10)] for `X` and for `V(Z)`, whose
residue fields at `x` agree. -/
theorem ringKrullDim_quotient_stalkIdeal_add [PerfectField k] (f : X ⟶ Spec (.of k)) (n r : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)]
    (hrn : r ≤ n) {x : X} (hxZ : x ∈ Z.support) :
    ringKrullDim (X.presheaf.stalk x ⧸ Z.stalkIdeal x) + r = ringKrullDim (X.presheaf.stalk x) := by
  obtain ⟨z, rfl⟩ := Z.exists_subschemeι_eq hxZ
  have hX := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension f n
    (Z.subschemeι z)
  have hZ := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension
    (Z.subschemeι ≫ f) (n - r) z
  simp only at hX hZ
  rw [trdeg_residueField_stalk_subschemeι Z f z] at hZ
  rw [ringKrullDim_eq_of_ringEquiv (Z.stalkQuotientEquiv z)]
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hs' : Smooth (Z.subschemeι ≫ f) :=
    SmoothOfRelativeDimension.smooth (n - r) (Z.subschemeι ≫ f)
  have := isRegularLocalRing_stalk f (Z.subschemeι z)
  have := isRegularLocalRing_stalk (Z.subschemeι ≫ f) z
  obtain ⟨a, ha⟩ :=
    exists_ringKrullDim_eq_natCast (X.presheaf.stalk (Z.subschemeι z))
  obtain ⟨b, hb⟩ := exists_ringKrullDim_eq_natCast (Z.subscheme.presheaf.stalk z)
  rw [ha] at hX ⊢
  rw [hb] at hZ ⊢
  exact natCast_add_natCast_eq_of_add_eq hX hZ (Nat.sub_add_cancel hrn)

/-- Adapted parameters at any point `x ∈ V(Z)`: a regular system of parameters `y` of `𝒪_{X,x}`
(with `dim 𝒪_{X,x}` members) whose first `r` members generate `Z_x` ([Sta, Tag 00NR] together with
the dimension count `ringKrullDim_quotient_stalkIdeal_add`). -/
theorem exists_adaptedParameters [PerfectField k] (f : X ⟶ Spec (.of k)) (n r : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)]
    (hrn : r ≤ n) {x : X} (hxZ : x ∈ Z.support) :
    ∃ (m : ℕ) (y : Fin m → X.presheaf.stalk x),
      (m : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) ∧
      maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y) ∧
      Z.stalkIdeal x = Ideal.span (y '' {j | j.val < r}) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hs' : Smooth (Z.subschemeι ≫ f) :=
    SmoothOfRelativeDimension.smooth (n - r) (Z.subschemeι ≫ f)
  have := isRegularLocalRing_stalk f x
  have := isRegularLocalRing_quotient_stalkIdeal Z f hxZ
  obtain ⟨m, c, y, hcm, hm, hspan, hI⟩ :=
    IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt
      (Z.stalkIdeal x)
  have hdim := ringKrullDim_quotient_stalkIdeal_add Z f n r hrn hxZ
  have hdim' := ringKrullDim_quotient_span_image_lt y hspan hm hcm
  rw [← hI] at hdim'
  obtain ⟨q, hq⟩ :=
    exists_ringKrullDim_eq_natCast (X.presheaf.stalk x ⧸ Z.stalkIdeal x)
  rw [hq, ← hm] at hdim hdim'
  have h1 : q + r = m := by exact_mod_cast hdim
  have h2 : q + c = m := by exact_mod_cast hdim'
  obtain rfl : c = r := by omega
  exact ⟨m, y, hm, hspan, hI⟩

/-- Adapted local coordinates at a closed point `x ∈ V(Z)`: a regular system of parameters
`y_0, …, y_{n-1}` of `𝒪_{X,x}` with `Z_x = (y_0, …, y_{r-1})`, Kollár's coordinates with
`Z = (x_1 = ⋯ = x_r = 0)` ([Kol07, Definition 24, (4)] and [Kol07, Definition 60]). -/
theorem exists_adaptedCoordinates [PerfectField k] (f : X ⟶ Spec (.of k)) (n r : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)]
    (hrn : r ≤ n) {x : X} (hxZ : x ∈ Z.support) (hx : IsClosed ({x} : Set X)) :
    ∃ y : Fin n → X.presheaf.stalk x, (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) ∧
      maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y) ∧
      Z.stalkIdeal x = Ideal.span (y '' {j | j.val < r}) := by
  obtain ⟨m, y, hm, hspan, hI⟩ := exists_adaptedParameters Z f n r hrn hxZ
  have hn := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed f n hx
  rw [hn] at hm
  obtain rfl : m = n := by exact_mod_cast hm
  exact ⟨y, hn.symm, hspan, hI⟩

end AlgebraicGeometry
