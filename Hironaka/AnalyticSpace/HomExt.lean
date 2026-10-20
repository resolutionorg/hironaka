/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace
public import Hironaka.AnalyticSpace.Model
public import Hironaka.Manifold.StructureSheaf
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.Sheaf.LocalRing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Morphisms into `(Kⁿ, 𝒜_{Kⁿ})` are determined by their coordinate functions

A local `Kⁿ`-coordination is a `K`-morphism `h : X|U → (Kⁿ, 𝒜_{Kⁿ})` [Hir64, Ch. 0, §1, p. 120],
and such a morphism is determined by the `n` coordinate functions `h^*z_i`. This file proves that
(`hom_ext_of_coord`) for any `K`-local-ringed space with Noetherian stalks, and establishes the
Noetherianity of the stalks of analytic `K`-spaces on the way. Not stated in the sources; the
argument:

1. **Noetherian stalks.** The stalk `𝒪_{X,x}` of an analytic `K`-space is a Noetherian local
   ring: through the local-model isomorphism it is `𝒜_{G,z}/𝓘_z`, a quotient of a stalk of
   `𝒜_{Kⁿ}`, which is Noetherian by Rückert's basis theorem (`isNoetherianRing_stalk` of
   `Hironaka/Manifold/Germ/StalkNoetherian.lean`).
2. **Base maps.** For a `K`-morphism `χ : X → (Kⁿ, 𝒜)` the stalk map `χ_x : 𝒜_{Kⁿ,χ(x)} → 𝒪_{X,x}`
   is local and carries constants to constants, so `χ_x(z_i - χ(x)_i) ∈ 𝔪_x`, i.e. the germ of the
   pulled-back coordinate function `χ^*z_i` is congruent to the constant `χ(x)_i` modulo `𝔪_x`.
   Two morphisms with the same `χ^*z_i` therefore have `φ(x)_i - ψ(x)_i ∈ 𝔪_x` as a constant; a
   nonzero constant is a unit, so `φ(x) = ψ(x)`.
3. **Stalk maps.** Two local ring homomorphisms `α, β : 𝒜_{Kⁿ,q} → R` into a Noetherian local
   ring that agree on the constants and on the coordinate germs agree: by Hadamard's lemma
   (`exists_eq_sum_coord_mul'`) every germ is, modulo `𝔪_q^N`, a polynomial in the coordinate
   germs with constant coefficients, on which `α` and `β` agree; local homomorphisms map `𝔪_q^N`
   into `𝔪_R^N`; so `α s - β s ∈ ⋂_N 𝔪_R^N = 0` by Krull's intersection theorem
   (`Ideal.iInf_pow_eq_bot_of_isLocalRing`) — `ringHom_ext_of_coord`.
4. **Sheaf maps.** With equal base maps, the components of the sheaf maps agree because a
   section of a sheaf is determined by its germs (`TopCat.Presheaf.section_ext`) and the germ of
   `χ.c.app U s` at `x` is `χ_x` of the germ of `s` (`stalkMap_germ_apply`) — `hom_ext_of_coord`.

This is the uniqueness half of the description of morphisms into `Kⁿ` by coordinate functions;
it is used wherever such a morphism is specified by its coordinates, for instance for morphisms
built from sections of the structure sheaf (`Hironaka/AnalyticSpace/HomOfSectionsCompat.lean`) and
for the uniqueness of monoidal transformations (`Hironaka/AnalyticSpace/MonoidalUnique.lean`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open AnalyticSpace KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

variable (K : Type) [RCLike K] (n : ℕ)

/-- The coordinate germs `z_i` of `Kⁿ` at `q` (in the identity chart). -/
abbrev coordAt (q : Kn.{u} K n) (i : Fin n) :
    (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q :=
  coord (Kn.{u} K n) ContinuousLinearEquiv.ulift (chartAt (Kn.{u} K n) q)
    (IsManifold.chart_mem_maximalAtlas q) (mem_chart_source _ q) i

/-- The coordinate germ `coordAt q i` is the germ at `q` of the coordinate section `z_i`. -/
theorem coordAt_eq_germ (q : Kn.{u} K n) (i : Fin n) :
    coordAt K n q i =
      (affine K n).toLocallyRingedSpace.presheaf.germ ⊤ q (Opens.mem_top q) (coordSection K n i) :=
  rfl

/-- The value at `q` of the coordinate germ `z_i` is `q_i`. -/
theorem eval_coordAt (q : Kn.{u} K n) (i : Fin n) :
    Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) q (coordAt K n q i) = q.down i :=
  eval_coord _ _ _ _ _ i

/-- The constants of `𝒜_{Kⁿ,q}` given by the `K`-structure of `(Kⁿ, 𝒜_{Kⁿ})` are the constant
germs `const`. -/
theorem affine_germ_algebraMap (q : Kn.{u} K n) (c : K) :
    (affine K n).toLocallyRingedSpace.presheaf.germ ⊤ q (Opens.mem_top q)
      ((affine K n).algebraMap c) = const K (Kn.{u} K n) (Kn.{u} K n) q c :=
  rfl

/-- `z_i − z_i(q) ∈ 𝔪_q`. -/
theorem mem_maximalIdeal_coordAt_sub (q : Kn.{u} K n) (i : Fin n) :
    coordAt K n q i - const K (Kn.{u} K n) (Kn.{u} K n) q
      (Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) q (coordAt K n q i)) ∈
      IsLocalRing.maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have h' := (contMDiffSheafCommRing.isUnit_stalk_iff 𝓘(K, Kn.{u} K n) ω (Kn.{u} K n) _).mp h
  apply h'
  change Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) q _ = 0
  rw [map_sub, eval_const, sub_self]

variable {K n}

/-- Two local ring homomorphisms from `𝒜_{Kⁿ,q}` into a Noetherian local ring that agree on the
constants and on the coordinate germs agree: a convergent series is the `𝔪`-adic limit of its
truncations, and Krull's intersection theorem applies in the target. -/
theorem ringHom_ext_of_coord {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (q : Kn.{u} K n)
    (α β : (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q →+* R)
    [IsLocalHom α] [IsLocalHom β]
    (hc : ∀ c : K, α (const K (Kn.{u} K n) (Kn.{u} K n) q c) =
      β (const K (Kn.{u} K n) (Kn.{u} K n) q c))
    (hz : ∀ i, α (coordAt K n q i) = β (coordAt K n q i)) : α = β := by
  set E := RingHom.eqLocus α β
  have hcE : ∀ c, const K (Kn.{u} K n) (Kn.{u} K n) q c ∈ E := hc
  have hzE : ∀ i, coordAt K n q i ∈ E := hz
  have approx : ∀ N : ℕ, ∀ s : (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q,
      ∃ P ∈ E, s - P ∈ (IsLocalRing.maximalIdeal
        ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)) ^ N := by
    intro N
    induction N with
    | zero => intro s; exact ⟨0, E.zero_mem, by simp⟩
    | succ N ih =>
      intro s
      obtain ⟨g, hg⟩ := exists_eq_sum_coord_mul' (Kn.{u} K n) ContinuousLinearEquiv.ulift
        (chartAt (Kn.{u} K n) q) (mem_chart_source _ q) (IsManifold.chart_mem_maximalAtlas q)
        (s - const K (Kn.{u} K n) (Kn.{u} K n) q (Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) q s))
        (by rw [map_sub, eval_const, sub_self])
      choose P hPE hP using fun i => ih (g i)
      refine ⟨const K (Kn.{u} K n) (Kn.{u} K n) q (Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) q s) +
        ∑ i, (coordAt K n q i - const K (Kn.{u} K n) (Kn.{u} K n) q
          (Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) q (coordAt K n q i))) * P i, ?_, ?_⟩
      · exact E.add_mem (hcE _)
          (E.sum_mem fun i _ => E.mul_mem (E.sub_mem (hzE i) (hcE _)) (hPE i))
      · have : s - (const K (Kn.{u} K n) (Kn.{u} K n) q (Manifold.eval K (Kn.{u} K n)
          (Kn.{u} K n) q s) +
            ∑ i, (coordAt K n q i - const K (Kn.{u} K n) (Kn.{u} K n) q
              (Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) q (coordAt K n q i))) * P i) =
            ∑ i, (coordAt K n q i - const K (Kn.{u} K n) (Kn.{u} K n) q
              (Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) q (coordAt K n q i))) * (g i - P i) := by
          rw [← sub_sub, hg, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
        rw [this, pow_succ']
        exact Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_mul (mem_maximalIdeal_coordAt_sub K n q i) (hP i)
  have hmap : ∀ (γ : (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q →+* R)
      [IsLocalHom γ] (N : ℕ) (t : (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q),
      t ∈ (IsLocalRing.maximalIdeal
        ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)) ^ N →
        γ t ∈ (IsLocalRing.maximalIdeal R) ^ N := by
    intro γ _ N t ht
    have hle : Ideal.map γ (IsLocalRing.maximalIdeal
        ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)) ≤
        IsLocalRing.maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      exact fun hu => ha ((isUnit_map_iff γ a).mp hu)
    have := Ideal.pow_right_mono hle N
    rw [← Ideal.map_pow] at this
    exact this (Ideal.mem_map_of_mem γ ht)
  ext s
  have hdiff : ∀ N, α s - β s ∈ (IsLocalRing.maximalIdeal R) ^ N := by
    intro N
    obtain ⟨P, hPE, hP⟩ := approx N s
    have h1 : α s - β s = α (s - P) - β (s - P) := by
      rw [map_sub, map_sub, (hPE : α P = β P)]
      ring
    rw [h1]
    exact Ideal.sub_mem _ (hmap α N _ hP) (hmap β N _ hP)
  have hmem : α s - β s ∈ ⨅ N, (IsLocalRing.maximalIdeal R) ^ N := Ideal.mem_iInf.mpr hdiff
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hmem
  exact sub_eq_zero.mp hmem


/-! ### Noetherian stalks -/

namespace QuotientSpace

variable (X : LocallyRingedSpace.{u}) (J : IdealSheaf X.𝒪)

/-- The stalks of the quotient `(S(𝒥), (𝒪_X/𝒥)|_{S(𝒥)})` are Noetherian when those of `X` are
(through `stalkEquiv`). -/
theorem isNoetherianRing_stalk [∀ x : X, IsNoetherianRing (X.presheaf.stalk x)]
    (z : support X J) : IsNoetherianRing ((quotientSpace X J).presheaf.stalk z) :=
  isNoetherianRing_of_ringEquiv _ (stalkEquiv X J z).symm

end QuotientSpace

variable (K n)

/-- The stalks `𝒜_{Kⁿ,q}` are Noetherian (Rückert's basis theorem). -/
theorem isNoetherianRing_stalk_affine (q : Kn.{u} K n) :
    IsNoetherianRing ((affine K n).toLocallyRingedSpace.presheaf.stalk q) :=
  inferInstanceAs
    (IsNoetherianRing ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q))

/-- The stalks of `(G, 𝒜_G)` are Noetherian (`restrictStalkIso`). -/
theorem isNoetherianRing_stalk_analyticSpaceOfOpen (G : Opens (Kn.{u} K n))
    (x : analyticSpaceOfOpen K n G) :
    IsNoetherianRing ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.stalk x) :=
  @isNoetherianRing_of_ringEquiv _ _ _ _
    ((affine K n).toLocallyRingedSpace.restrictStalkIso
      (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G)
        x).symm.commRingCatIsoToRingEquiv
    (isNoetherianRing_stalk_affine K n x.1)

/-- The stalks of a local model `(S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})` are Noetherian. -/
theorem isNoetherianRing_stalk_localModel (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) (z : localModel K n G f) :
    IsNoetherianRing ((localModel K n G f).toLocallyRingedSpace.presheaf.stalk z) :=
  have : ∀ x : (analyticSpaceOfOpen K n G).toLocallyRingedSpace,
      IsNoetherianRing ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.stalk x) :=
    isNoetherianRing_stalk_analyticSpaceOfOpen K n G
  QuotientSpace.isNoetherianRing_stalk _ (modelIdeal K n G f) z

variable {K n}

namespace KLocallyRingedSpace

/-- Noetherianity of a stalk passes from `X` to the open subspace `X|U`. -/
theorem isNoetherianRing_stalk_restrictOpen (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (x : X.restrictOpen U) (h : IsNoetherianRing (X.toLocallyRingedSpace.presheaf.stalk x.1)) :
    IsNoetherianRing ((X.restrictOpen U).toLocallyRingedSpace.presheaf.stalk x) :=
  @isNoetherianRing_of_ringEquiv _ _ _ _
    (X.toLocallyRingedSpace.restrictStalkIso
      (Opens.isOpenEmbedding U) x).symm.commRingCatIsoToRingEquiv h

/-- Noetherianity of a stalk passes from the open subspace `X|U` to `X`. -/
theorem isNoetherianRing_stalk_of_restrictOpen (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (x : X.restrictOpen U)
    (h : IsNoetherianRing ((X.restrictOpen U).toLocallyRingedSpace.presheaf.stalk x)) :
    IsNoetherianRing (X.toLocallyRingedSpace.presheaf.stalk x.1) :=
  @isNoetherianRing_of_ringEquiv _ _ _ _
    (X.toLocallyRingedSpace.restrictStalkIso
      (Opens.isOpenEmbedding U) x).commRingCatIsoToRingEquiv h

/-- Noetherianity of stalks transports along a `K`-isomorphism (its stalk maps are
isomorphisms). -/
theorem isNoetherianRing_stalk_of_kIso {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (a : A)
    (h : IsNoetherianRing (B.toLocallyRingedSpace.presheaf.stalk (e.hom.1.base a))) :
    IsNoetherianRing (A.toLocallyRingedSpace.presheaf.stalk a) :=
  isNoetherianRing_of_ringEquiv _ (asIso (e.hom.1.stalkMap a)).commRingCatIsoToRingEquiv

end KLocallyRingedSpace


/-- The stalks of an analytic `K`-space are Noetherian: every point has a neighbourhood isomorphic
to an open of a local model, whose stalks are quotients of stalks of `𝒜_{Kⁿ}`. -/
theorem isNoetherianRing_stalk (X : AnalyticSpace.{u} K) (x : X) :
    IsNoetherianRing (X.toLocallyRingedSpace.presheaf.stalk x) := by
  obtain ⟨U, hxU, n, k, G, f, W, ⟨e⟩⟩ := X.locallyModel x
  refine KLocallyRingedSpace.isNoetherianRing_stalk_of_restrictOpen X.toKLocallyRingedSpace U
    ⟨x, hxU⟩ ?_
  refine KLocallyRingedSpace.isNoetherianRing_stalk_of_kIso e ⟨x, hxU⟩ ?_
  refine KLocallyRingedSpace.isNoetherianRing_stalk_restrictOpen (localModel K n G f) W _ ?_
  exact isNoetherianRing_stalk_localModel K n G f _

/-! ### A `K`-morphism into `(Kⁿ, 𝒜_{Kⁿ})` is determined by its coordinate functions -/

/-- The constants of the stalk `𝒪_{X,x}`: the germs of the global constants, `K →+* 𝒪_{X,x}`. -/
def KLocallyRingedSpace.constAt (X : KLocallyRingedSpace.{u} K) (x : X) :
    K →+* X.toLocallyRingedSpace.presheaf.stalk x :=
  (X.toLocallyRingedSpace.presheaf.germ ⊤ x (Opens.mem_top x)).hom.comp X.algebraMap

/-- A nonzero constant is a unit of every stalk. -/
theorem KLocallyRingedSpace.isUnit_constAt (X : KLocallyRingedSpace.{u} K)
    (x : X) {c : K} (hc : c ≠ 0) : IsUnit (KLocallyRingedSpace.constAt X x c) :=
  (isUnit_iff_ne_zero.mpr hc).map (KLocallyRingedSpace.constAt X x)

/-- The stalk map at `x` of a `K`-morphism `χ : X → Kⁿ` carries the coordinate germ `z_i` at
`χ(x)` to the germ at `x` of the pullback `χ^*z_i`. -/
theorem stalkMap_coordAt (X : KLocallyRingedSpace.{u} K) (χ : X ⟶ affine K n) (x : X)
    (i : Fin n) :
    (χ.1.stalkMap x) (coordAt K n (χ.1.base x) i) =
      X.toLocallyRingedSpace.presheaf.germ ⊤ x (Opens.mem_top x)
        (χ.pullbackΓ (coordSection K n i)) := by
  rw [coordAt_eq_germ]
  erw [PresheafedSpace.stalkMap_germ_apply]
  rfl

/-- The stalk map of a `K`-morphism `χ : X → Kⁿ` carries the constants to the constants. -/
theorem stalkMap_const (X : KLocallyRingedSpace.{u} K) (χ : X ⟶ affine K n) (x : X) (c : K) :
    (χ.1.stalkMap x) (const K (Kn.{u} K n) (Kn.{u} K n) (χ.1.base x) c) =
      KLocallyRingedSpace.constAt X x c :=
  χ.algebraMap_stalk x c

/-- Two `K`-morphisms `X → Kⁿ` with the same pullbacks of the coordinate functions have the same
underlying map: the constant `φ(x)_i − ψ(x)_i` lies in `𝔪_x`, and a nonzero constant is a unit
(`isUnit_constAt`). -/
theorem KLocallyRingedSpace.base_apply_eq_of_pullbackΓ_coord
    (X : KLocallyRingedSpace.{u} K) (φ ψ : X ⟶ affine K n)
    (h : ∀ i, φ.pullbackΓ (coordSection K n i) = ψ.pullbackΓ (coordSection K n i)) (x : X) :
    φ.1.base x = ψ.1.base x := by
  apply ULift.ext
  funext i
  have key : ∀ χ : X ⟶ affine K n,
      X.toLocallyRingedSpace.presheaf.germ ⊤ x (Opens.mem_top x)
        (χ.pullbackΓ (coordSection K n i)) -
        KLocallyRingedSpace.constAt X x ((χ.1.base x).down i) ∈
        IsLocalRing.maximalIdeal (X.toLocallyRingedSpace.presheaf.stalk x) := by
    intro χ
    rw [← stalkMap_coordAt, ← stalkMap_const, ← map_sub]
    have hm := mem_maximalIdeal_coordAt_sub K n (χ.1.base x) i
    rw [eval_coordAt] at hm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
    exact fun hu => hm ((isUnit_map_iff (χ.1.stalkMap x).hom _).mp hu)
  have hmem := Ideal.sub_mem _ (key φ) (key ψ)
  rw [h i, sub_sub_sub_cancel_left, ← map_sub] at hmem
  by_contra hne
  exact ((IsLocalRing.mem_maximalIdeal _).mp hmem)
    (KLocallyRingedSpace.isUnit_constAt X x (sub_ne_zero.mpr (Ne.symm hne)))

/-- Two `K`-morphisms from an analytic `K`-space to `Kⁿ` with the same pullbacks of the coordinate
functions have the same underlying map (the special case of
`KLocallyRingedSpace.base_apply_eq_of_pullbackΓ_coord`). -/
theorem base_apply_eq_of_pullbackΓ_coord (X : AnalyticSpace.{u} K)
    (φ ψ : X.toKLocallyRingedSpace ⟶ affine K n)
    (h : ∀ i, φ.pullbackΓ (coordSection K n i) = ψ.pullbackΓ (coordSection K n i)) (x : X) :
    φ.1.base x = ψ.1.base x :=
  KLocallyRingedSpace.base_apply_eq_of_pullbackΓ_coord X.toKLocallyRingedSpace φ ψ h x

/-- A `K`-morphism from a `K`-local-ringed space with Noetherian stalks into `(Kⁿ, 𝒜_{Kⁿ})` is
determined by the pullbacks of the coordinate functions (a local `Kⁿ`-coordination
[Hir64, Ch. 0, §1, p. 120] is such a morphism; the uniqueness itself is not stated in the
sources). The proof uses the analytic-space structure only through the Noetherianity of the
stalks, hence the general form. -/
theorem KLocallyRingedSpace.hom_ext_of_coord
    (X : KLocallyRingedSpace.{u} K)
    (hN : ∀ x : X, IsNoetherianRing (X.toLocallyRingedSpace.presheaf.stalk x))
    (φ ψ : X ⟶ affine K n)
    (h : ∀ i, φ.pullbackΓ (coordSection K n i) = ψ.pullbackΓ (coordSection K n i)) : φ = ψ := by
  have hb : φ.1.base = ψ.1.base :=
    TopCat.ext fun x => KLocallyRingedSpace.base_apply_eq_of_pullbackΓ_coord X φ ψ h x
  obtain ⟨⟨⟨b₁, c₁⟩, p₁⟩, hφ⟩ := φ
  obtain ⟨⟨⟨b₂, c₂⟩, p₂⟩, hψ⟩ := ψ
  change b₁ = b₂ at hb
  subst hb
  let f₁ : X.toLocallyRingedSpace ⟶ (affine K n).toLocallyRingedSpace := ⟨⟨b₁, c₁⟩, p₁⟩
  let f₂ : X.toLocallyRingedSpace ⟶ (affine K n).toLocallyRingedSpace := ⟨⟨b₁, c₂⟩, p₂⟩
  have hc : c₁ = c₂ := by
    ext U s
    apply TopCat.Presheaf.section_ext X.toLocallyRingedSpace.𝒪
    intro x hx
    have hN := hN x
    have i₁ : IsLocalHom (f₁.stalkMap x).hom := p₁ x
    have i₂ : IsLocalHom (f₂.stalkMap x).hom := p₂ x
    have key := @ringHom_ext_of_coord K _ n _ _ _ hN (b₁ x) (f₁.stalkMap x).hom
      (f₂.stalkMap x).hom
      i₁ i₂
      (fun c => (stalkMap_const X ⟨f₁, hφ⟩ x c).trans
        (stalkMap_const X ⟨f₂, hψ⟩ x c).symm)
      (fun i => (stalkMap_coordAt X ⟨f₁, hφ⟩ x i).trans
        ((congrArg _ (h i)).trans (stalkMap_coordAt X ⟨f₂, hψ⟩ x i).symm))
    refine (PresheafedSpace.stalkMap_germ_apply f₁.toHom U x hx s).symm.trans ?_
    refine Eq.trans ?_ (PresheafedSpace.stalkMap_germ_apply f₂.toHom U x hx s)
    exact DFunLike.congr_fun key _
  subst hc
  rfl

/-- A `K`-morphism from an analytic `K`-space into `(Kⁿ, 𝒜_{Kⁿ})` is determined by the pullbacks
of the coordinate functions: the special case of `KLocallyRingedSpace.hom_ext_of_coord`, the
stalks of an analytic space being Noetherian. -/
theorem hom_ext_of_coord (X : AnalyticSpace.{u} K) (φ ψ : X.toKLocallyRingedSpace ⟶ affine K n)
    (h : ∀ i, φ.pullbackΓ (coordSection K n i) = ψ.pullbackΓ (coordSection K n i)) : φ = ψ :=
  KLocallyRingedSpace.hom_ext_of_coord X.toKLocallyRingedSpace X.isNoetherianRing_stalk φ ψ h


end AnalyticSpace
