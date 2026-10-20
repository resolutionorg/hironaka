/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Principal
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.Local.CohenIso
import Hironaka.Algebra.Local.PolynomialOrder
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.MaximalContact.Restrict
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.MaximalContact.Transform
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Local existence of hypersurfaces of maximal contact

[Kol07, Theorem 80 (2)]: for `m = max-ord I`, every point of `X` has a neighbourhood on which a
smooth hypersurface of maximal contact exists. Kollár's proof is three sentences: at a point `x`
with `ord_x I = m`, `ord_x MC(I) = 1` by [Kol07, Lemma 74 (3)]; so some local section of `MC(I)`
has order `1` at `x`; and its zero divisor is smooth near `x`. This file carries them out on
ideal sheaves, and adds the two things the printed proof does not spell out: the points where
`ord_x I < m` (there `MC(I)` is the unit ideal sheaf near `x`, and the empty hypersurface `⊤`
works) and the transport of the equation from the affine open where it is found to the open where
its zero divisor is smooth. [Kol07, Aside 81] notes that such an `H` exists locally but usually
not globally; only the local statement is proved here.

* **The ideal sheaf of a section.** `principal h`
  (`Hironaka/Resolution/Algebraic/MaximalContact/Principal.lean`) is described by `principal_ideal`,
  `stalkIdeal_principal`, `principal_le_iff`, `principal_one` and `ord_principal`; `comap_principal`
  says that it restricts as the section does, `(principal h).comap g = principal (g^* h)`
  (stalkwise: the germ of `g^* h` at `y` is the image of the germ of `h` at `g y`, Mathlib's
  `germ_stalkMap_apply`).
* **From the stalk to a section.** `ord_x MC(I) = 1` gives an element `a ∈ MC(I)_x` with
  `a ∈ 𝔪_x ∖ 𝔪_x²` (`ordElem_eq_one_iff`); the stalk is the localization of `MC(I)(U)` at `x` for
  an affine `U ∋ x` (Mathlib's `IsAffineOpen.isLocalization_stalk`), so `a · germ u = germ s` with
  `s ∈ MC(I)(U)` and `u` invertible at `x`; multiplying by a unit does not change the order
  (`ordElem_mul_of_isUnit`), so `ordElem (germ s) = 1`.
* **The smooth locus of an equation.** For a global section `h` of order `1` at `x`, the set
  `{y | ord_y (h) < 2}` is open (upper semicontinuity of the order, which is where smoothness in
  characteristic zero enters) and contains `x`; on it, at every point of `V(h)`, the germ of `h`
  lies in `𝔪 ∖ 𝔪²` (order exactly `1`), which is the generator clause of `IsSmoothDivisor`, and
  `𝒪_y/(h)` is regular (`IsRegularLocalRing.quotient_span_singleton`), which gives the regularity
  of `V(h)`. The order of the restricted sheaf is read off with `ord_comap_ι`.
* **The unit case.** Where `ord_x I < m`, the open `{ord I < m}` has `ord MC(I) = 0` at every
  point, so `MC(I|_U) = (MC I)|_U = 𝒪_U`.
* **Assembly.** Under `max-ord I = m`, `ord_x I ≤ m`; if `m = 0` then `I = 𝒪_X` and `U = X`,
  `h = 1`; if `ord_x I < m`, the unit case and `h = 1`; if `ord_x I = m ≥ 1`, the section of
  order one lives on an affine `U₁` and is viewed as a global section `h₂` of the open subscheme
  `U₁` (Mathlib's `Opens.topIso`), whose germ at `x` has order `1` (the stalks of `U₁` are those
  of `X`, `Opens.stalkIso`) and whose ideal sheaf lies in `MC(I|_{U₁})`; the smooth locus of `h₂`
  is an open `V ∋ x` of `U₁`; the final open is the range of `V ⟶ U₁ ⟶ X`, identified with `V` by
  Mathlib's `isoOpensRange`, along which `principal`, `IsSmoothDivisor` and `IsMaximalContact`
  are transported by `comap`.
* **The dynamic form.** `IsOrderSeq.strictTransformSeq_le_center_of_le_MC` turns the static
  hypersurface into a dynamic one on every open immersion, exactly as in
  `isDynamicMaximalContact_of_isMaximalContact`, without Kollár's `I|_H ≠ 0` (which a local `H`
  need not satisfy).

The local hypersurfaces are the input of the globalization of blow-up sequences
([Kol07, Theorem 105], `Hironaka/Resolution/Algebraic/Kol07/MaximalContactGlobalization.lean`),
which patches the order reduction on the opens `U` into one on `X`. -/

public section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Hironaka.Local

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Multiplying by a unit does not change the order of an element. -/
theorem ordElem_mul_of_isUnit {a v : R} (hv : IsUnit v) : ordElem (a * v) = ordElem a := by
  rw [← ord_span_singleton, ← ord_span_singleton, Ideal.span_singleton_mul_right_unit hv]

end Hironaka.Local

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-! ### The ideal sheaf of a section: the five unfoldings and restriction -/

/-- On every affine open `U` the ideal sheaf generated by `h` is the principal ideal `(h|_U)`
(Mathlib's `ofIdealTop_ideal`: the image of the ideal `(h)` of the global sections). -/
theorem principal_ideal (h : Γ(X, ⊤)) (U : X.affineOpens) :
    (principal h).ideal U = Ideal.span {X.presheaf.map (homOfLE le_top).op h} := by
  rw [ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]

/-- The stalk of `(h)` at `x` is generated by the germ of `h`. -/
theorem stalkIdeal_principal (h : Γ(X, ⊤)) (x : X) :
    (principal h).stalkIdeal x = Ideal.span {X.presheaf.germ ⊤ x trivial h} := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hxU, principal_ideal, Ideal.map_span, Set.image_singleton,
    X.presheaf.germ_res_apply]

/-- `h` is a section of `J` iff `(h) ≤ J`. -/
theorem principal_le_iff (h : Γ(X, ⊤)) (J : X.IdealSheafData) :
    principal h ≤ J ↔ ∀ U : X.affineOpens, X.presheaf.map (homOfLE le_top).op h ∈ J.ideal U := by
  simp only [le_def, principal_ideal, Ideal.span_singleton_le_iff_mem]

/-- The unit section generates the unit ideal sheaf. -/
theorem principal_one : principal (1 : Γ(X, ⊤)) = (⊤ : X.IdealSheafData) :=
  IdealSheafData.ext (funext fun U => by simp [Ideal.map_top])

/-- The order of `(h)` at `x` is the order of the germ of `h`. -/
theorem ord_principal (h : Γ(X, ⊤)) (x : X) :
    (principal h).ord x = ordElem (X.presheaf.germ ⊤ x trivial h) := by
  rw [ord_eq_ord_stalkIdeal, stalkIdeal_principal, ord_span_singleton]

/-- The ideal sheaf of a section restricts as the section does: along `g : Y ⟶ X`, `(h)` pulls
back to `(g^* h)`. Stalkwise, the germ of `g^* h` at `y` is the image of the germ of `h` at `g y`
(`germ_stalkMap_apply`). -/
theorem comap_principal {Y : Scheme.{u}} (g : Y ⟶ X) (h : Γ(X, ⊤)) :
    (principal h).comap g = principal (g.appTop h) := by
  have key : ∀ y : Y, ((principal h).comap g).stalkIdeal y =
      (principal (g.appTop h)).stalkIdeal y := fun y => by
    rw [stalkIdeal_comap, stalkIdeal_principal, stalkIdeal_principal, Ideal.map_span,
      Set.image_singleton]
    congr 2
    exact g.germ_stalkMap_apply ⊤ y trivial h
  exact le_antisymm (le_of_stalkIdeal_le fun y => (key y).le)
    (le_of_stalkIdeal_le fun y => (key y).ge)


/-! ### The section of order one, and the unit case, on a smooth scheme -/

section Smooth

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [CharZero k] (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n

omit [CharZero k] in
/-- If `MC(I)` has order `0` at every point of an open `U`, then `MC` of the restriction `I|_U` is
the unit ideal sheaf: `MC` commutes with the (smooth) open immersion, and an ideal sheaf whose
stalks are all the unit ideal is `⊤`. -/
theorem MC_comap_eq_top_of_forall_ord_eq_zero (I : X.IdealSheafData) (m : ℕ) (U : X.Opens)
    (hU : ∀ u : U, (MC f I m).ord (U.ι u) = 0) : MC (U.ι ≫ f) (I.comap U.ι) m = ⊤ := by
  rw [MC_comap_of_smooth f n U.ι I m]
  refine top_le_iff.mp (le_of_stalkIdeal_le fun u => ?_)
  have h0 : ((MC f I m).comap U.ι).ord u = 0 := (ord_comap_ι (MC f I m) U u).trans (hU u)
  rw [ord_eq_ord_stalkIdeal, IsLocalRing.ord_eq_zero_iff] at h0
  rw [h0]
  exact le_top

/-- The points the proof of [Kol07, Theorem 80 (2)] passes over: at a point where `ord_x I < m`,
the open `{ord I < m}` carries `MC(I|_U) = 𝒪_U`, since `MC(I)` has order `0` there. -/
theorem exists_opens_MC_comap_eq_top_of_ord_lt (I : X.IdealSheafData) {m : ℕ} {x : X}
    (hx : I.ord x < m) :
    ∃ U : X.Opens, x ∈ U ∧ MC (U.ι ≫ f) (I.comap U.ι) m = ⊤ := by
  have hopen : IsOpen {y : X | I.ord y < m} := by
    convert (isClosed_setOf_le_ord f n I m).isOpen_compl using 1
    ext y
    change I.ord y < m ↔ ¬ (m : ℕ∞) ≤ I.ord y
    exact not_le.symm
  refine ⟨⟨_, hopen⟩, hx, ?_⟩
  exact MC_comap_eq_top_of_forall_ord_eq_zero f n I m _ fun u => ord_MC_eq_zero f n I u.2

/-- The first two sentences of the proof of [Kol07, Theorem 80 (2)]: at a point of order `m ≥ 1`
of `I`, `ord_x MC(I) = 1`, so `MC(I)_x` contains an element `a` of `𝔪_x ∖ 𝔪_x²`; the stalk is the
localization of `MC(I)(U)` at `x` for an affine `U ∋ x`, so `a · germ u = germ s` with
`s ∈ MC(I)(U)` and `u` invertible at `x`, and `germ s` has order `1` as well. -/
theorem exists_mem_ideal_MC_ordElem_eq_one (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m) {x : X}
    (hx : I.ord x = m) :
    ∃ (U : X.affineOpens) (hxU : x ∈ U.1) (h : Γ(X, U.1)),
      h ∈ (MC f I m).ideal U ∧ ordElem (X.presheaf.germ U.1 x hxU h) = 1 := by
  have h1 : IsLocalRing.ord ((MC f I m).stalkIdeal x) = 1 := by
    rw [← ord_eq_ord_stalkIdeal]
    exact ord_MC_eq_one f n I hm hx
  have hle : (MC f I m).stalkIdeal x ≤ maximalIdeal (X.presheaf.stalk x) := by
    have := (IsLocalRing.le_ord_iff (r := 1)).mp (by rw [h1, Nat.cast_one])
    rwa [pow_one] at this
  have hnle : ¬ (MC f I m).stalkIdeal x ≤ maximalIdeal (X.presheaf.stalk x) ^ 2 := by
    intro h2
    have := (IsLocalRing.le_ord_iff (r := 2)).mpr h2
    rw [h1] at this
    have h21 : (2 : ℕ) ≤ 1 := by exact_mod_cast this
    omega
  obtain ⟨a, haJ, ha2⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have ha1 : ordElem a = 1 := ordElem_eq_one_iff.mpr ⟨hle haJ, ha2⟩
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  let _ : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U.1)
  have hloc := U.2.isLocalization_stalk ⟨x, hxU⟩
  rw [stalkIdeal_eq_map_germ _ U hxU] at haJ
  obtain ⟨⟨s, u⟩, hsu⟩ := (IsLocalization.mem_map_algebraMap_iff
    (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x)).mp haJ
  have hu : IsUnit (X.presheaf.germ U.1 x hxU u.1) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
      (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal u.1).mpr u.2
  refine ⟨U, hxU, s.1, s.2, ?_⟩
  have hs : X.presheaf.germ U.1 x hxU s.1 = a * X.presheaf.germ U.1 x hxU u.1 := hsu.symm
  rw [hs, Hironaka.Local.ordElem_mul_of_isUnit hu, ha1]

end Smooth

/-! ### The smooth locus of an equation of order one -/

section SmoothLocus

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [CharZero k] (n : ℕ)
  [SmoothOfRelativeDimension n f]

include f n

/-- The last sentence of the proof of [Kol07, Theorem 80 (2)], "its zero divisor is smooth in a
neighborhood of `x`": for a global section `h` whose germ at `x` has order exactly `1`, the open
set `U := {y | ord_y (h) < 2}` contains `x`, and on it the ideal sheaf `(h)` is a smooth divisor:
at every point of `V(h) ∩ U` the germ of `h` lies in `𝔪 ∖ 𝔪²` (order exactly `1`,
`ordElem_eq_one_iff`), and the quotient of the regular stalk by it is regular
(`IsRegularLocalRing.quotient_span_singleton`), so `V(h) ∩ U` is regular. -/
theorem exists_opens_isSmoothDivisor_comap_principal (h : Γ(X, ⊤)) {x : X}
    (hord : ordElem (X.presheaf.germ ⊤ x trivial h) = 1) :
    ∃ U : X.Opens, x ∈ U ∧ IsSmoothDivisor ((principal h).comap U.ι) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  let U : X.Opens := ⟨{y | ((2 : ℕ) : ℕ∞) ≤ (principal h).ord y}ᶜ,
    (isClosed_setOf_le_ord f n (principal h) 2).isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · change ¬ ((2 : ℕ) : ℕ∞) ≤ (principal h).ord x
    rw [ord_principal, hord]
    intro h2
    have h21 : (2 : ℕ) ≤ 1 := by exact_mod_cast h2
    omega
  · -- the generator clause at every point of the support
    have key : ∀ u ∈ ((principal h).comap U.ι).support,
        ∃ a : U.toScheme.presheaf.stalk u, a ∈ maximalIdeal _ ∧ a ∉ maximalIdeal _ ^ 2 ∧
          ((principal h).comap U.ι).stalkIdeal u = Ideal.span {a} := by
      intro u hu
      have hstalk := stalkIdeal_comap (principal h) U.ι u
      rw [stalkIdeal_principal, Ideal.map_span, Set.image_singleton] at hstalk
      have hord1 : ((principal h).comap U.ι).ord u = 1 := by
        have hlt : ¬ ((2 : ℕ) : ℕ∞) ≤ ((principal h).comap U.ι).ord u := by
          rw [ord_comap_ι (principal h) U u]
          exact u.2
        have hge : 1 ≤ ((principal h).comap U.ι).ord u := (one_le_ord_iff _ _).mpr hu
        obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (not_le.mp hlt))
        rw [← hj] at hlt hge ⊢
        have h1 : 1 ≤ j := by exact_mod_cast hge
        have h2 : ¬ 2 ≤ j := by exact_mod_cast hlt
        have hj1 : j = 1 := by omega
        rw [hj1, Nat.cast_one]
      have hoa : IsLocalRing.ord (((principal h).comap U.ι).stalkIdeal u) = 1 := by
        rw [← ord_eq_ord_stalkIdeal]
        exact hord1
      rw [hstalk, ord_span_singleton] at hoa
      exact ⟨_, (ordElem_eq_one_iff.mp hoa).1,
        (ordElem_eq_one_iff.mp hoa).2, hstalk⟩
    refine ⟨?_, key⟩
    refine isRegular_subscheme_of_isRegularLocalRing_quotient _ fun w hw => ?_
    obtain ⟨a, ha, ha2, hspan⟩ := key w hw
    have hreg : IsRegularLocalRing (U.toScheme.presheaf.stalk w) :=
      isRegularLocalRing_stalk (U.ι ≫ f) w
    rw [hspan]
    exact (IsRegularLocalRing.quotient_span_singleton ha ha2).1

end SmoothLocus

/-! ### Theorem 80 (2): the assembly and its corollaries -/

section Assembly

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [CharZero k] (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n

/-- **[Kol07, Theorem 80 (2)]**: for `m = max-ord I`, every point has an open neighbourhood `U`
with a section `h ∈ 𝒪(U)` whose zero divisor `(h)` is a smooth hypersurface of `U` with
`(h) ⊆ MC(I|_U)`. Where `ord_x I < m` (or `m = 0`, when `I = 𝒪_X`), `h = 1` on the open where
`MC(I|_U) = 𝒪_U`; where `ord_x I = m ≥ 1`, `exists_mem_ideal_MC_ordElem_eq_one` gives the
equation on an affine open `U₁`, viewed as a global section of the open subscheme `U₁`,
`exists_opens_isSmoothDivisor_comap_principal` gives the open `V ⊆ U₁` where its zero divisor is
smooth, and the data are transported to the open `V ⟶ U₁ ⟶ X` of `X` along Mathlib's
`isoOpensRange`. -/
theorem exists_opens_principal_isSmoothDivisor_isMaximalContact (I : X.IdealSheafData) {m : ℕ}
    (hI : I.maxOrd = m) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ h : Γ(U, ⊤), IsSmoothDivisor (principal h) ∧
      IsMaximalContact (U.ι ≫ f) (I.comap U.ι) m (principal h) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  -- the empty hypersurface `h = 1` on an open where `MC(I|_U) = 𝒪_U`
  have top_case : ∀ U : X.Opens, x ∈ U → MC (U.ι ≫ f) (I.comap U.ι) m = ⊤ →
      ∃ U : X.Opens, x ∈ U ∧ ∃ h : Γ(U, ⊤), IsSmoothDivisor (principal h) ∧
        IsMaximalContact (U.ι ≫ f) (I.comap U.ι) m (principal h) := by
    intro U hxU hMC
    refine ⟨U, hxU, 1, ?_, ?_⟩
    · rw [principal_one]
      exact Hironaka.Snc.isSmoothDivisor_top
    · unfold IsMaximalContact
      rw [principal_one, hMC]
  have hxle : I.ord x ≤ m := (le_maxOrd I x).trans hI.le
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · -- `m = 0`: `I = 𝒪_X`
    subst hm0
    refine top_case ⊤ trivial (MC_comap_eq_top_of_forall_ord_eq_zero f n I 0 ⊤ fun u => ?_)
    rw [MC_zero]
    have := (le_maxOrd I ((⊤ : X.Opens).ι u)).trans hI.le
    rw [Nat.cast_zero] at this
    exact le_antisymm this zero_le
  rcases hxle.lt_or_eq with hlt | heq
  · obtain ⟨U, hxU, hMC⟩ := exists_opens_MC_comap_eq_top_of_ord_lt f n I hlt
    exact top_case U hxU hMC
  -- the main case `ord_x I = m ≥ 1`: the equation on an affine open `U₁`
  obtain ⟨U₁, hxU₁, h₁, hh₁, hord₁⟩ := exists_mem_ideal_MC_ordElem_eq_one f n I hm heq
  let g : U₁.1.toScheme ⟶ X := U₁.1.ι
  have hg : SmoothOfRelativeDimension (0 + n) (g ≫ f) := inferInstance
  let h₂ : Γ(U₁.1.toScheme, ⊤) := U₁.1.topIso.inv h₁
  let x₀ : U₁.1.toScheme := ⟨x, hxU₁⟩
  have hy : ∀ y : U₁.1.toScheme, g y ∈ U₁.1 := fun y => y.2
  -- the germs of `h₂` are the germs of `h₁`
  have hgerm : ∀ y : U₁.1.toScheme,
      (U₁.1.stalkIso y).hom
          (U₁.1.toScheme.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top y) h₂) =
        X.presheaf.germ U₁.1 (g y) (hy y) h₁ := by
    intro y
    have hcomp :=
      Scheme.Opens.germ_stalkIso_hom U₁.1 (V := ⊤) y (TopologicalSpace.Opens.mem_top y)
    have h1 : (U₁.1.stalkIso y).hom
          (U₁.1.toScheme.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top y) h₂) =
        X.presheaf.germ (U₁.1.ι ''ᵁ ⊤) (g y)
          ⟨y, TopologicalSpace.Opens.mem_top y, rfl⟩ h₂ :=
      congrArg (fun φ => (ConcreteCategory.hom φ) h₂) hcomp
    rw [h1]
    simp only [h₂, Scheme.Opens.topIso_inv]
    exact X.presheaf.germ_res_apply _ _ _ _
  -- (β) `h₂` has order one at `x`
  have hβ :
      ordElem (U₁.1.toScheme.presheaf.germ ⊤ x₀ (TopologicalSpace.Opens.mem_top x₀) h₂) = 1 := by
    rw [← ordElem_ringEquiv (U₁.1.stalkIso x₀).commRingCatIsoToRingEquiv]
    have : (U₁.1.stalkIso x₀).commRingCatIsoToRingEquiv
        (U₁.1.toScheme.presheaf.germ ⊤ x₀ (TopologicalSpace.Opens.mem_top x₀) h₂) =
          X.presheaf.germ U₁.1 x hxU₁ h₁ :=
      hgerm x₀
    rw [this, hord₁]
  -- (α) `(h₂) ⊆ MC(I|_{U₁})`
  have hα : principal h₂ ≤ MC (g ≫ f) (I.comap g) m := by
    rw [MC_comap_of_smooth f n g I m]
    refine le_of_stalkIdeal_le fun y => ?_
    rw [stalkIdeal_principal, stalkIdeal_comap, Ideal.span_singleton_le_iff_mem]
    have hmem : X.presheaf.germ U₁.1 (g y) (hy y) h₁ ∈ (MC f I m).stalkIdeal (g y) := by
      rw [stalkIdeal_eq_map_germ _ U₁ (hy y)]
      exact Ideal.mem_map_of_mem _ hh₁
    have hinv : ∀ a, (U₁.1.ι.stalkMap y) ((U₁.1.stalkIso y).hom a) = a := fun a => by
      have h := Scheme.Opens.stalkIso_inv U₁.1 y
      exact h ▸ Iso.hom_inv_id_apply (U₁.1.stalkIso y) a
    convert Ideal.mem_map_of_mem (g.stalkMap y).hom hmem using 1
    rw [← hgerm y]
    exact (hinv _).symm
  -- the smooth locus of `h₂` on `U₁`
  obtain ⟨V, hx₀V, hVsm⟩ :=
    exists_opens_isSmoothDivisor_comap_principal (g ≫ f) (0 + n) h₂ hβ
  -- the final open of `X`: the range of `V ⟶ U₁ ⟶ X`
  let ι' : V.toScheme ⟶ X := V.ι ≫ g
  let e : V.toScheme ≅ ι'.opensRange.toScheme := ι'.isoOpensRange
  have heW : (e.inv ≫ V.ι) ≫ g = ι'.opensRange.ι := by
    rw [Category.assoc]
    exact ι'.isoOpensRange_inv_comp
  refine ⟨ι'.opensRange, ⟨⟨x₀, hx₀V⟩, rfl⟩, (e.inv ≫ V.ι).appTop h₂, ?_, ?_⟩
  · rw [← comap_principal, comap_comp]
    exact hVsm.comap_of_isOpenImmersion e.inv
  · have := IsMaximalContact.comap (g ≫ f) (0 + n) hα (e.inv ≫ V.ι)
    unfold IsMaximalContact at this ⊢
    rw [← comap_comp, ← Category.assoc, heW] at this
    rwa [← comap_principal]

/-- [Kol07, Theorem 80 (2)] with the hypersurface as an ideal sheaf: for `m = max-ord I`, every
point has an open neighbourhood carrying a smooth divisor that is a static hypersurface of maximal
contact for the restricted ideal. -/
theorem exists_opens_isSmoothDivisor_isMaximalContact (I : X.IdealSheafData) {m : ℕ}
    (hI : I.maxOrd = m) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ H : (U : Scheme.{u}).IdealSheafData, IsSmoothDivisor H ∧
      IsMaximalContact (U.ι ≫ f) (I.comap U.ι) m H := by
  obtain ⟨U, hxU, h, hsm, hmc⟩ := exists_opens_principal_isSmoothDivisor_isMaximalContact f n I hI x
  exact ⟨U, hxU, principal h, hsm, hmc⟩

/-- [Kol07, Theorem 80 (1) and (2)] together: for `m = max-ord I ≥ 1`, every point has an open
neighbourhood carrying a smooth divisor that is a hypersurface of maximal contact in the static and
the dynamic sense; the dynamic form is `IsOrderSeq.strictTransformSeq_le_center_of_le_MC` on every
open immersion, exactly as in `isDynamicMaximalContact_of_isMaximalContact`, and needs no
`I|_H ≠ 0`. -/
theorem exists_opens_isSmoothDivisor_isDynamicMaximalContact (I : X.IdealSheafData) {m : ℕ}
    (hI : I.maxOrd = m) (hm : 1 ≤ m) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ H : (U : Scheme.{u}).IdealSheafData, IsSmoothDivisor H ∧
      IsMaximalContact (U.ι ≫ f) (I.comap U.ι) m H ∧
        IsDynamicMaximalContact (U.ι ≫ f) (I.comap U.ι) m H := by
  obtain ⟨U, hxU, H, hsm, hmc⟩ := exists_opens_isSmoothDivisor_isMaximalContact f n I hI x
  refine ⟨U, hxU, H, hsm, hmc, ?_⟩
  intro Y j _ S hS i
  have : SmoothOfRelativeDimension (0 + n) (U.ι ≫ f) := inferInstance
  have : SmoothOfRelativeDimension (0 + (0 + n)) (j ≫ U.ι ≫ f) := inferInstance
  exact Hironaka.Sequence.IsOrderSeq.strictTransformSeq_le_center_of_le_MC (j ≫ U.ι ≫ f)
    (0 + (0 + n)) hm hS (hsm.comap_of_isOpenImmersion j) (hmc.comap (U.ι ≫ f) (0 + n) j) i

end Assembly

end AlgebraicGeometry.Scheme.IdealSheafData
