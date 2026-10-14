/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.ParameterSubset
import Hironaka.Scheme.Snc.RestrictHypersurface
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Simple normal crossings along a hypersurface: the lifting direction

The proof of [Kol07, Corollary 85]: adding `E` to `(X, I)` and `E|_H` to `(H, I|_H, m)` "poses the
same restriction on order reduction" — a centre `Z ⊆ H` has simple normal crossings with `E` in `X`
iff it has simple normal crossings with `H + E` in `X` iff `Z|_H` has simple normal crossings with
`E|_H` in `H`. The restriction direction, from `X` to `H`, is
`hasSncWith_comap_of_isClosedImmersion` of `Hironaka.Scheme.Snc.RestrictHypersurface`; the passage
from `E` to `H + E` is `hasSncWith_append_of_le` of
`Hironaka.Scheme.BlowUpSequence.RestrictDivisors`. This module proves the two remaining directions
and the two equivalences, which `Hironaka.Resolution.Algebraic.Kol07.GoingUp` uses to pass between
the snc clause of a sequence on `X` and that of its restriction to `H`.

* `hasSncWith_append_of_comap_of_isClosedImmersion` — the lifting direction, for any closed
  immersion `g : Y ↪ X` with `H := g.ker` and regular stalks on `X`: adapted coordinates on `H` lift
  along the surjection `φ : 𝒪_{X,x} → 𝒪_{X,x}/(h) = 𝒪_{H,y}` (`ker_stalkMap_of_isClosedImmersion`).
  Given a regular system of parameters `z'` of `𝒪_{H,y}` adapted to `E|_H` with
  `Z|_H = (z'_t : t ∈ s')`, and a regular system `w` of `𝒪_{X,x}` adapted to `H + E` (from
  `(E.append H).IsSnc`) with `h = w_{h₀}` the equation of `H`: the components `E^i` through `x` are
  principal, `E^i_x = (a_i)`, and `(φ a_i) = (z'_{c'(i)})` in the domain `𝒪_{H,y}`, so
  `z'_{c'(i)} = φ a_i · u_i` for a unit `u_i`, which lifts to a unit `v_i` of `𝒪_{X,x}`; the lifted
  coordinates are `ℓ_{c'(i)} := a_i v_i` at the `E`-indices and arbitrary preimages of the `z'_t`
  elsewhere (`Function.extend`), and the new system is `z := (h, ℓ)`. It is a regular system of
  parameters (`𝔪_X = (h) + (ℓ)` because `φ(𝔪_X) = 𝔪_H = (φ ℓ)`; `n' + 1 = dim 𝒪_{X,x}` because
  `dim 𝒪_{H,y} = dim 𝒪_{X,x} − 1`, `natCast_sub_card_eq_ringKrullDim_of_ker` of
  `Hironaka.Scheme.Snc.ParameterSubset`), adapted to `H + E` (`H_x = (h)`, `E^i_x = (a_i) = (a_i
  v_i)`), and `Z_x = (h) + (ℓ_t : t ∈ s')` because `φ(Z_x) = (Z|_H)_y = (z'_t : t ∈ s')` and `(h) ⊆
  Z_x`.
* `HasSncWith.of_append` — the sub-family direction (from `H + E` to `E`): the same coordinates with
  the index map restricted to the members of `E`.
* `hasSncWith_iff_hasSncWith_append`, `hasSncWith_append_iff_hasSncWith_comap` — the two
  equivalences on a smooth `X`, from the four directions.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Simple normal crossings with `E + J` implies simple normal crossings with the sub-family `E` —
the same adapted coordinates, the index map restricted to the members of `E` (the proof of
[Kol07, Corollary 85]). -/
theorem HasSncWith.of_append {E : DivisorFamily X} {J Z : X.IdealSheafData}
    (h : (E.append J).HasSncWith Z) : E.HasSncWith Z := by
  intro x hx
  obtain ⟨n, z, ⟨hrsp, c, hcinj, hc⟩, s, hs⟩ := h x hx
  refine ⟨n, z, ⟨hrsp, fun i => c ⟨toLex (Sum.inl (i.1 : E.ι)), i.2⟩, fun i i' hii' => ?_,
    fun i => hc ⟨toLex (Sum.inl (i.1 : E.ι)), i.2⟩⟩, s, hs⟩
  exact Subtype.ext (Sum.inl_injective (toLex.injective (congrArg Subtype.val (hcinj hii'))))

/-- A point of the closed subscheme `V(ker g)` of a closed immersion `g` lies in the image of `g`
(the image is closed, so Mathlib's `support_ker` needs no closure). -/
theorem exists_eq_of_mem_support_ker (g : Y ⟶ X) [IsClosedImmersion g] {x : X}
    (hx : x ∈ g.ker.support) : ∃ y : Y, g y = x := by
  have h := Scheme.Hom.support_ker g
  rw [(Scheme.Hom.isClosedEmbedding g).isClosed_range.closure_eq] at h
  have : x ∈ Set.range g.base := by rw [← h]; exact hx
  exact this

/-- The lifting direction of the proof of [Kol07, Corollary 85] ([Kol07, Definition 24]): for a
closed immersion `g : Y ↪ X` with `H := g.ker`, if `H + E` has simple normal crossings, `H ≤ Z` and
`Z|_H` has simple normal crossings with `E|_H` in `H`, then `Z` has simple normal crossings with
`H + E` in `X`. Adapted coordinates on `H` lift along `𝒪_{X,x} → 𝒪_{X,x}/(h)` to adapted coordinates
on `X` with `h` as the extra parameter; see the module docstring. -/
theorem hasSncWith_append_of_comap_of_isClosedImmersion (g : Y ⟶ X) [IsClosedImmersion g]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) {E : DivisorFamily X}
    {Z : X.IdealSheafData} (hEH : (E.append g.ker).IsSnc) (hle : g.ker ≤ Z)
    (hZ : (E.comap g).HasSncWith (Z.comap g)) : (E.append g.ker).HasSncWith Z := by
  classical
  intro x hx
  have hxH : x ∈ g.ker.support := Scheme.IdealSheafData.support_antitone hle hx
  obtain ⟨y, rfl⟩ := exists_eq_of_mem_support_ker g hxH
  have hy : y ∈ (Z.comap g).support := by
    rw [Scheme.IdealSheafData.support_comap]; exact hx
  have := hreg (g y)
  -- the adapted coordinates on `H` at `y`
  obtain ⟨n', z', ⟨⟨hz'span, hz'dim⟩, c', hc'inj, hc'⟩, s', hs'⟩ := hZ y hy
  -- a regular system of parameters of `X` at `g y` adapted to `H + E`, with `h = w h0`
  obtain ⟨N, w, ⟨hwspan, hwdim⟩, cw, hcwinj, hcw⟩ := hEH.2 (g y)
  have hxH' : g y ∈ ((E.append g.ker).component (toLex (Sum.inr PUnit.unit))).support := hxH
  set h0 : Fin N := cw ⟨toLex (Sum.inr PUnit.unit), hxH'⟩ with hh0
  have hker : g.ker.stalkIdeal (g y) = span {w h0} := hcw ⟨toLex (Sum.inr PUnit.unit), hxH'⟩
  -- the stalk map: surjective with kernel `(h)`
  set φ : X.presheaf.stalk (g y) →+* Y.presheaf.stalk y := (g.stalkMap y).hom with hφdef
  have hφ : Function.Surjective φ := g.stalkMap_surjective y
  have hlocφ : IsLocalHom φ := by rw [hφdef]; infer_instance
  have hkerφ : RingHom.ker φ = span (w '' ↑({h0} : Finset (Fin N))) := by
    rw [hφdef, ker_stalkMap_of_isClosedImmersion, hker, Finset.coe_singleton,
      Set.image_singleton]
  have hkerφ' : RingHom.ker φ = span {w h0} := by
    rw [hkerφ, Finset.coe_singleton, Set.image_singleton]
  have hregY : IsRegularLocalRing (Y.presheaf.stalk y) :=
    isRegularLocalRing_of_ker_eq_span_image hwspan.symm hwdim hφ hkerφ
  -- the dimension count: `n' = N − 1`
  have hdimY : ((N - 1 : ℕ) : WithBot ℕ∞) = ringKrullDim (Y.presheaf.stalk y) := by
    have := natCast_sub_card_eq_ringKrullDim_of_ker hwspan.symm hwdim hφ hkerφ
    simpa using this
  have hn' : n' = N - 1 := by exact_mod_cast hz'dim.trans hdimY.symm
  have hN : 1 ≤ N := Fin.pos h0
  have hNn' : n' + 1 = N := by omega
  -- the components of `E` through `y` are the components of `E` through `g y`, principal there
  have hEx : ∀ i : {i : (E.comap g).ι // y ∈ ((E.comap g).component i).support},
      g y ∈ ((E.append g.ker).component (toLex (Sum.inl (i.1 : E.ι)))).support := fun i => by
    have hi := i.2
    rwa [show (E.comap g).component i.1 = (E.component i.1).comap g from rfl,
      Scheme.IdealSheafData.support_comap] at hi
  set a : {i : (E.comap g).ι // y ∈ ((E.comap g).component i).support} → X.presheaf.stalk (g y) :=
    fun i => w (cw ⟨toLex (Sum.inl (i.1 : E.ι)), hEx i⟩) with ha_def
  have ha : ∀ i, (E.component i.1).stalkIdeal (g y) = span {a i} := fun i =>
    hcw ⟨toLex (Sum.inl (i.1 : E.ι)), hEx i⟩
  -- `(φ a_i) = (z'_{c' i})`, so `z'_{c' i} = φ a_i · u_i` with `u_i` a unit lifting to a unit `v_i`
  have hassoc : ∀ i : {i : (E.comap g).ι // y ∈ ((E.comap g).component i).support},
      ∃ v : X.presheaf.stalk (g y), IsUnit v ∧ φ (a i * v) = z' (c' i) := by
    intro i
    have h1 : ((E.comap g).component i.1).stalkIdeal y = span {φ (a i)} := by
      change ((E.component i.1).comap g).stalkIdeal y = _
      rw [Scheme.IdealSheafData.stalkIdeal_comap, ha i, Ideal.map_span, Set.image_singleton]
    have h2 : span {φ (a i)} = span {z' (c' i)} := h1.symm.trans (hc' i)
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h2
    obtain ⟨v, hv⟩ := hφ (u : Y.presheaf.stalk y)
    refine ⟨v, (isUnit_map_iff φ v).mp (hv ▸ u.isUnit), ?_⟩
    rw [map_mul, hv]
    exact hu
  choose v hvunit hφv using hassoc
  -- the lifted coordinates `ℓ`: `a_i v_i` at the `E`-indices, arbitrary preimages elsewhere
  set ℓ : Fin n' → X.presheaf.stalk (g y) :=
    Function.extend c' (fun i => a i * v i) (fun t => Function.surjInv hφ (z' t)) with hℓ
  have hℓE : ∀ i, ℓ (c' i) = a i * v i := fun i => by
    rw [hℓ, hc'inj.extend_apply]
  have hφℓ : ∀ t, φ (ℓ t) = z' t := by
    intro t
    by_cases ht : ∃ i, c' i = t
    · obtain ⟨i, rfl⟩ := ht
      rw [hℓE]
      exact hφv i
    · rw [hℓ, Function.extend_apply' _ _ _ ht]
      exact Function.surjInv_eq hφ _
  have hℓm : ∀ t, ℓ t ∈ maximalIdeal (X.presheaf.stalk (g y)) := fun t => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have : IsUnit (z' t) := hφℓ t ▸ hu.map φ
    exact (IsLocalRing.mem_maximalIdeal _).mp (hz'span ▸ subset_span ⟨t, rfl⟩) this
  have hhm : w h0 ∈ maximalIdeal (X.presheaf.stalk (g y)) := hwspan ▸ subset_span ⟨h0, rfl⟩
  -- the new system `z = (h, ℓ)`
  set z : Fin (n' + 1) → X.presheaf.stalk (g y) := Fin.cons (w h0) ℓ with hz
  have hz0 : z 0 = w h0 := Fin.cons_zero _ _
  have hzs : ∀ t, z t.succ = ℓ t := fun t => Fin.cons_succ _ _ t
  have hrange : Set.range z = insert (w h0) (Set.range ℓ) := Fin.range_cons _ _
  -- `φ` maps `span (range ℓ)` onto `𝔪_Y`
  have hmapℓ : Ideal.map φ (span (Set.range ℓ)) = maximalIdeal (Y.presheaf.stalk y) := by
    rw [Ideal.map_span, ← Set.range_comp, show (⇑φ ∘ ℓ) = z' from funext hφℓ]
    exact hz'span
  -- (1) a regular system of parameters
  have hzspan : span (Set.range z) = maximalIdeal (X.presheaf.stalk (g y)) := by
    rw [hrange, Ideal.span_insert]
    apply le_antisymm
    · exact sup_le (span_le.mpr (Set.singleton_subset_iff.mpr hhm))
        (span_le.mpr (Set.range_subset_iff.mpr hℓm))
    · intro m hm
      have hφm : φ m ∈ Ideal.map φ (span (Set.range ℓ)) := by
        rw [hmapℓ, ← IsLocalRing.map_maximalIdeal_of_surjective φ hφ]
        exact Ideal.mem_map_of_mem φ hm
      obtain ⟨b, hb, hbm⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hφm
      have hdiff : m - b ∈ span {w h0} := by
        rw [← hkerφ', RingHom.mem_ker, map_sub, hbm, sub_self]
      have : m = (m - b) + b := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hdiff) (Ideal.mem_sup_right hb)
  have hzdim : ((n' + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (g y)) := by
    rw [hNn']
    exact hwdim
  -- (2) the index map into the new system: `H ↦ 0`, `E^i ↦ succ (c' i)`
  have hcases : ∀ i : {i : (E.append g.ker).ι //
      g y ∈ ((E.append g.ker).component i).support},
      (∃ e : {e : (E.comap g).ι // y ∈ ((E.comap g).component e).support},
        i.1 = toLex (Sum.inl (e.1 : E.ι))) ∨ i.1 = toLex (Sum.inr PUnit.unit) := by
    rintro ⟨i, hi⟩
    rcases hi' : ofLex i with e | u
    · left
      have hie : i = toLex (Sum.inl e) := congrArg toLex hi'
      have hex : g y ∈ (E.component e).support := by
        have := hi
        rwa [hie] at this
      refine ⟨⟨e, ?_⟩, hie⟩
      change y ∈ ((E.component e).comap g).support
      rwa [Scheme.IdealSheafData.support_comap]
    · right
      cases u
      exact congrArg toLex hi'
  let cidx : {i : (E.append g.ker).ι // g y ∈ ((E.append g.ker).component i).support} →
      Fin (n' + 1) := fun i =>
    if h : ∃ e : {e : (E.comap g).ι // y ∈ ((E.comap g).component e).support},
        i.1 = toLex (Sum.inl (e.1 : E.ι))
    then (c' h.choose).succ else 0
  have hcidx_inl : ∀ (i) (e : {e : (E.comap g).ι // y ∈ ((E.comap g).component e).support})
      (he : i.1 = toLex (Sum.inl (e.1 : E.ι))), cidx i = (c' e).succ := by
    intro i e he
    have hex : ∃ e' : {e : (E.comap g).ι // y ∈ ((E.comap g).component e).support},
        i.1 = toLex (Sum.inl (e'.1 : E.ι)) := ⟨e, he⟩
    simp only [cidx, dite_eq_left hex]
    congr 1
    apply congrArg c'
    apply Subtype.ext
    have h1 : i.1 = toLex (Sum.inl (hex.choose.1 : E.ι)) := hex.choose_spec
    have h2 : toLex (Sum.inl (e.1 : E.ι)) = toLex (Sum.inl (hex.choose.1 : E.ι)) :=
      he.symm.trans h1
    exact (Sum.inl_injective (toLex.injective h2)).symm
  have hcidx_inr : ∀ i, i.1 = toLex (Sum.inr PUnit.unit) → cidx i = 0 := by
    intro i hi
    have hnex : ¬ ∃ e : {e : (E.comap g).ι // y ∈ ((E.comap g).component e).support},
        i.1 = toLex (Sum.inl (e.1 : E.ι)) := by
      rintro ⟨e, he⟩
      rw [hi] at he
      exact Sum.inr_ne_inl (toLex.injective he)
    simp only [cidx, dite_eq_right hnex]
  refine ⟨n' + 1, z, ⟨⟨hzspan, hzdim⟩, cidx, ?_, ?_⟩, ?_⟩
  · -- injectivity of the index map
    intro i i' hii'
    rcases hcases i with ⟨e, he⟩ | hi
    · rcases hcases i' with ⟨e', he'⟩ | hi'
      · rw [hcidx_inl i e he, hcidx_inl i' e' he'] at hii'
        have hee' : e = e' := hc'inj (Fin.succ_injective _ hii')
        exact Subtype.ext (he.trans (hee' ▸ he'.symm))
      · rw [hcidx_inl i e he, hcidx_inr i' hi'] at hii'
        exact absurd hii' (Fin.succ_ne_zero _)
    · rcases hcases i' with ⟨e', he'⟩ | hi'
      · rw [hcidx_inr i hi, hcidx_inl i' e' he'] at hii'
        exact absurd hii'.symm (Fin.succ_ne_zero _)
      · exact Subtype.ext (hi.trans hi'.symm)
  · -- each component is generated by its coordinate
    intro i
    rcases hcases i with ⟨e, he⟩ | hi
    · rw [hcidx_inl i e he, hzs, hℓE]
      have hcomp : (E.append g.ker).component i.1 = E.component e.1 := by rw [he]; rfl
      change ((E.append g.ker).component i.1).stalkIdeal (g y) = _
      rw [hcomp, ha e, Ideal.span_singleton_mul_right_unit (hvunit e)]
    · rw [hcidx_inr i hi, hz0]
      have hcomp : (E.append g.ker).component i.1 = g.ker := by rw [hi]; rfl
      change ((E.append g.ker).component i.1).stalkIdeal (g y) = _
      rw [hcomp, hker]
  · -- `Z_x = (h) + (ℓ_t : t ∈ s')`
    refine ⟨insert 0 (s'.image Fin.succ), ?_⟩
    have hs'' : (Z.comap g).stalkIdeal y = span (z' '' ↑s') := hs'
    rw [Scheme.IdealSheafData.stalkIdeal_comap] at hs''
    -- `φ (Z_x) = φ (span (ℓ '' s'))`
    have himg : z' '' (↑s' : Set (Fin n')) = φ '' (ℓ '' ↑s') := by
      rw [Set.image_image]
      exact Set.image_congr fun t _ => (hφℓ t).symm
    have hmap : Ideal.map φ (Z.stalkIdeal (g y)) = Ideal.map φ (span (ℓ '' ↑s')) := by
      rw [Ideal.map_span, ← himg]
      exact hs''
    have hkerle : span {w h0} ≤ Z.stalkIdeal (g y) :=
      hker ▸ Scheme.IdealSheafData.stalkIdeal_mono hle (g y)
    have hcomap := congrArg (Ideal.comap φ) hmap
    rw [Ideal.comap_map_of_surjective φ hφ, Ideal.comap_map_of_surjective φ hφ,
      ← RingHom.ker_eq_comap_bot, hkerφ', sup_eq_left.mpr hkerle] at hcomap
    rw [hcomap, Finset.coe_insert, Finset.coe_image, Set.image_insert_eq, hz0, Set.image_image,
      Ideal.span_insert, sup_comm]
    congr 2

end AlgebraicGeometry

namespace AlgebraicGeometry

open AlgebraicGeometry

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [Smooth f]

include f in
/-- The first equivalence of the proof of [Kol07, Corollary 85]: for `Z ⊆ H` on a smooth `X` with
`H + E` snc, `Z` has simple normal crossings with `E` iff it has simple normal crossings with
`H + E` — `hasSncWith_append_of_le` and `HasSncWith.of_append`. -/
theorem hasSncWith_iff_hasSncWith_append {E : DivisorFamily X} {H Z : X.IdealSheafData}
    (hE : (E.append H).IsSnc) (hle : H ≤ Z) : E.HasSncWith Z ↔ (E.append H).HasSncWith Z :=
  ⟨fun h => hasSncWith_append_of_le f hE h hle, HasSncWith.of_append⟩

include f in
/-- The second equivalence of the proof of [Kol07, Corollary 85]: for `Z ⊆ H` on a smooth `X` with
`H + E` snc, `Z` has simple normal crossings with `H + E` in `X` iff `Z|_H` has simple normal
crossings with `E|_H` in `H` — `hasSncWith_comap_of_isClosedImmersion` and the lifting direction
`hasSncWith_append_of_comap_of_isClosedImmersion`, along `H.subschemeι` whose kernel is `H`. -/
theorem hasSncWith_append_iff_hasSncWith_comap {E : DivisorFamily X} {H Z : X.IdealSheafData}
    (hE : (E.append H).IsSnc) (hle : H ≤ Z) :
    (E.append H).HasSncWith Z ↔ (E.comap H.subschemeι).HasSncWith (Z.comap H.subschemeι) := by
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := fun x =>
    isRegularLocalRing_stalk f x
  have hker : H.subschemeι.ker = H := Scheme.IdealSheafData.ker_subschemeι H
  have hle' : H.subschemeι.ker ≤ Z := by rw [hker]; exact hle
  constructor
  · intro h
    refine hasSncWith_comap_of_isClosedImmersion H.subschemeι hreg ?_ hle'
    rw [hker]
    exact h
  · intro h
    have := hasSncWith_append_of_comap_of_isClosedImmersion H.subschemeι hreg
      (E := E) (Z := Z) (by rw [hker]; exact hE) hle' h
    rwa [hker] at this

end AlgebraicGeometry
