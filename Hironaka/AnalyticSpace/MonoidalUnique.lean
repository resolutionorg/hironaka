/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.HomExt
public import Hironaka.AnalyticSpace.QuotientMap
public import Hironaka.Manifold.BlowUp.Defs
import Hironaka.Algebra.InvertibleSpan
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.AnalyticSpace.Manifold.FullyFaithful
import Hironaka.Manifold.BlowUp.CoordGerm
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Uniqueness of lifts through the charted blow-up

Hironaka's universal property (**) of the blowing-up [Hir64, Ch. 0, §2, p. 123] for the charted
blow-up `π : M' → M` of an analytic manifold along a closed submanifold `Y` ([BM88, 4.1]), the
uniqueness half: two `K`-morphisms `g₁ g₂ : Y' → Sp(M')` from an analytic `K`-space with
`g₁ ≫ Sp(π) = g₂ ≫ Sp(π) = f'`, where the inverse image of the centre along `f'` is invertible,
coincide (`lift_unique_of_comp_eq`). Not proved in the sources; the argument:

The proof reads the blow-up charts ([BM88, 4.1 (2)]): in a chart `Φ` of index `i` over an adapted
chart `φ` of `Y`, `π^* z_{σ i} = u_{σ i}`, `π^* z_{σ k} = u_{σ i} · u_{σ k}` for `k ≠ i` and
`π^* z_j = u_j` off the block. Hence the coordinates of a lift `g` in `Φ` are forced by
`f' = g ≫ Sp(π)` (`pullback_coord_self`, `pullback_coord_of_ne`, `pullback_coord_off`): the
scaling coordinate is `f'^* z_{σ i}`, which generates the (invertible) inverse-image ideal of the
centre and is therefore a non-zero-divisor (`stalkIdeal_comap_comp_eq_span`,
`mem_nonZeroDivisors_pullback_coord`), so the ratio coordinates are recovered by cancellation and
the off-block ones directly (`stalkMap_coord_eq_of_mem_source`). The same cancellation shows that
`g₂ z` lies in the chart containing `g₁ z` (`mem_source_of_lift`). Equal coordinate germs give
equal base points, since a nonzero constant is a unit (`base_eq_of_coord`), and two `K`-morphisms
into `Sp(M')` with the same base point and the same coordinate germs have the same stalk map by
`ringHom_ext_of_coord'` (`Hironaka/AnalyticSpace/Manifold/FullyFaithful.lean`;
`stalkMap_eq_of_coord`). Off the centre `π` is a local diffeomorphism and the coordinates of a
transported chart are forced directly (`germMap_coord_transportChart`).

General lemmas: `hom_ext_of_coord_chart` — two `K`-morphisms from an analytic space into `Sp(M)`
that agree on the coordinate germs of a chart at every point are equal — with its ingredients
`base_eq_of_coord` and `stalkMap_eq_of_coord`, the composite stalk-map formula
`stalkMap_comp_ofManifoldHom_apply`, and the residue toolkit `stalkMap_coord_sub_constAt_mem`,
`eq_of_sub_constAt_mem`, `mul_sub_constAt_mem` (a germ's residue is the constant it is congruent
to modulo `𝔪_x`). Used by `Hironaka/Resolution/Analytic/Kol07Thm45/PieceLemma39.lean` and
`PieceLemma39Hom.lean`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ}
  {ψ : E ≃L[K] (Fin n → K)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] {Z : AnalyticSpace.{u} K}

/-- The stalk map of `g ≫ Sp(π)` at `z` is the stalk map of `g` after the germ map `germMap π` at
`g z` (`stalkMap_ofManifoldHom_eq_germMap`). -/
theorem stalkMap_comp_ofManifoldHom_apply {π : M' → M} (hπ : ContMDiff 𝓘(K, E) 𝓘(K, E) ω π)
    (g : Z.toKLocallyRingedSpace ⟶ ofManifold K E M') (z : Z)
    (t : (structureSheaf K E M).presheaf.stalk (π (g.1.base z))) :
    ((g ≫ ofManifoldHom π hπ).1.stalkMap z).hom t =
      (g.1.stalkMap z).hom (germMap π hπ (g.1.base z) t) := by
  change ((g.1 ≫ (ofManifoldHom π hπ).1).stalkMap z).hom t = _
  have e := congrArg (fun φ => φ.hom t)
    (LocallyRingedSpace.stalkMap_comp g.1 (ofManifoldHom π hπ).1 z)
  refine e.trans ?_
  change (g.1.stalkMap z).hom (((ofManifoldHom π hπ).1.stalkMap (g.1.base z)).hom t) = _
  rw [stalkMap_ofManifoldHom_eq_germMap]

/-- Transport of a pulled-back coordinate germ along an equality of morphisms into `Sp(M)`. -/
theorem stalkMap_apply_coord_congr {F₁ F₂ : Z.toKLocallyRingedSpace ⟶ ofManifold K E M}
    (hF : F₁ = F₂) {φ : OpenPartialHomeomorph M E} (hφ : φ ∈ maximalAtlas 𝓘(K, E) ω M) (z : Z)
    (h₁ : F₁.1.base z ∈ φ.source) (h₂ : F₂.1.base z ∈ φ.source) (j : Fin n) :
    (F₁.1.stalkMap z).hom (coord E ψ φ hφ h₁ j) = (F₂.1.stalkMap z).hom (coord E ψ φ hφ h₂ j) := by
  subst hF
  rfl

/-- Two morphisms into `Sp(M')` over the same morphism into `Sp(M)` have base points with the same
image under `π`. -/
theorem base_comp_eq {π : M' → M} (hπ : ContMDiff 𝓘(K, E) 𝓘(K, E) ω π)
    {g₁ g₂ : Z.toKLocallyRingedSpace ⟶ ofManifold K E M'}
    (h₂ : g₂ ≫ ofManifoldHom π hπ = g₁ ≫ ofManifoldHom π hπ) (z : Z) :
    π (g₂.1.base z) = π (g₁.1.base z) :=
  congrArg (fun F : Z.toKLocallyRingedSpace ⟶ ofManifold K E M => F.1.base z) h₂

section ChartExt

/-- Two `K`-morphisms into `Sp(M')` with the same base point at `z` and the same action on the
constants and on the coordinate germs of a chart at that point have the same stalk map at `z`
(`ringHom_ext_of_coord'`; the stalks of an analytic space are Noetherian; compare the local
coordinations of [Hir64, Ch. 0, §1, p. 120]). -/
theorem stalkMap_eq_of_coord {Φ : OpenPartialHomeomorph M' E}
    (hΦ : Φ ∈ maximalAtlas 𝓘(K, E) ω M') (g : Z.toKLocallyRingedSpace ⟶ ofManifold K E M')
    (z : Z) (hp : g.1.base z ∈ Φ.source) {y : M'} (e : g.1.base z = y) (hy : y ∈ Φ.source)
    (β : (ofManifold K E M').toLocallyRingedSpace.presheaf.stalk y ⟶
      Z.toLocallyRingedSpace.presheaf.stalk z) [hβ : IsLocalHom β.hom]
    (hc : ∀ c : K, β.hom (const K E M' y c) = constAt Z.toKLocallyRingedSpace z c)
    (hz : ∀ j, β.hom (coord E ψ Φ hΦ hy j) = (g.1.stalkMap z).hom (coord E ψ Φ hΦ hp j)) :
    g.1.stalkMap z =
      ((ofManifold K E M').toLocallyRingedSpace.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫
        β := by
  subst e
  change g.1.stalkMap z =
    (ofManifold K E M').toLocallyRingedSpace.presheaf.stalkSpecializes (specializes_refl _) ≫ β
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  have := AnalyticSpace.isNoetherianRing_stalk Z z
  refine CommRingCat.hom_ext
    (ringHom_ext_of_coord' ψ hΦ hp (g.1.stalkMap z).hom β.hom (g.1.prop z) hβ ?_ ?_)
  · intro c
    exact (g.algebraMap_stalk z c).trans (hc c).symm
  · intro j
    exact (hz j).symm

/-- Residues along a `K`-morphism into `Sp(M')`: a coordinate germ `u_j` of a chart `Φ` pulled back
along `g` is congruent modulo `𝔪_x` to the constant `u_j(g x)`. -/
theorem stalkMap_coord_sub_constAt_mem {X : KLocallyRingedSpace.{u} K}
    {Φ : OpenPartialHomeomorph M' E} (hΦ : Φ ∈ maximalAtlas 𝓘(K, E) ω M')
    (g : X ⟶ ofManifold K E M') {x : X} (hp : g.1.base x ∈ Φ.source) (j : Fin n) :
    (g.1.stalkMap x).hom (coord E ψ Φ hΦ hp j) - constAt X x (ψ (Φ (g.1.base x)) j) ∈
      maximalIdeal (X.toLocallyRingedSpace.presheaf.stalk x) := by
  have hm : coord E ψ Φ hΦ hp j - const K E M' (g.1.base x) (ψ (Φ (g.1.base x)) j) ∈
      maximalIdeal ((structureSheaf K E M').presheaf.stalk (g.1.base x)) :=
    (mem_maximalIdeal_iff_eval E _).mpr (by rw [map_sub, eval_coord, eval_const, sub_self])
  have hloc : IsLocalHom (g.1.stalkMap x).hom := g.1.prop x
  rw [show constAt X x (ψ (Φ (g.1.base x)) j) =
    (g.1.stalkMap x).hom (const K E M' (g.1.base x) (ψ (Φ (g.1.base x)) j)) from
    (g.algebraMap_stalk x _).symm, ← map_sub]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
  exact fun hu => hm (isUnit_of_map_unit _ _ hu)

/-- Residues are unique: a germ congruent modulo `𝔪_x` to two constants has equal constants (a
nonzero constant is a unit, `isUnit_constAt`). -/
theorem eq_of_sub_constAt_mem {X : KLocallyRingedSpace.{u} K} {x : X}
    {s : X.toLocallyRingedSpace.presheaf.stalk x} {a b : K}
    (ha : s - constAt X x a ∈ maximalIdeal (X.toLocallyRingedSpace.presheaf.stalk x))
    (hb : s - constAt X x b ∈ maximalIdeal (X.toLocallyRingedSpace.presheaf.stalk x)) : a = b := by
  have h3 := Ideal.sub_mem _ hb ha
  rw [sub_sub_sub_cancel_left, ← map_sub] at h3
  by_contra hne
  exact ((IsLocalRing.mem_maximalIdeal _).mp h3) (isUnit_constAt _ x (sub_ne_zero.mpr hne))

/-- Residues are multiplicative. -/
theorem mul_sub_constAt_mem {X : KLocallyRingedSpace.{u} K} {x : X}
    {s t : X.toLocallyRingedSpace.presheaf.stalk x} {a b : K}
    (ha : s - constAt X x a ∈ maximalIdeal (X.toLocallyRingedSpace.presheaf.stalk x))
    (hb : t - constAt X x b ∈ maximalIdeal (X.toLocallyRingedSpace.presheaf.stalk x)) :
    s * t - constAt X x (a * b) ∈ maximalIdeal (X.toLocallyRingedSpace.presheaf.stalk x) := by
  have : s * t - constAt X x (a * b) =
      (s - constAt X x a) * t + constAt X x a * (t - constAt X x b) := by
    rw [map_mul]; ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)

/-- Two `K`-morphisms into `Sp(M')` whose images of `z` lie in a chart `Φ` and which pull the
coordinate germs of `Φ` back to the same germs have the same base point at `z` — the constant
`u_j(g₁ z) - u_j(g₂ z)` lies in `𝔪_z`, and a nonzero constant is a unit (`isUnit_constAt`). -/
theorem base_eq_of_coord {Φ : OpenPartialHomeomorph M' E} (hΦ : Φ ∈ maximalAtlas 𝓘(K, E) ω M')
    (g₁ g₂ : Z.toKLocallyRingedSpace ⟶ ofManifold K E M') {z : Z} (hp₁ : g₁.1.base z ∈ Φ.source)
    (hp₂ : g₂.1.base z ∈ Φ.source)
    (hz : ∀ j, (g₂.1.stalkMap z).hom (coord E ψ Φ hΦ hp₂ j) =
      (g₁.1.stalkMap z).hom (coord E ψ Φ hΦ hp₁ j)) :
    g₁.1.base z = g₂.1.base z := by
  have hval : ∀ j, ψ (Φ (g₁.1.base z)) j = ψ (Φ (g₂.1.base z)) j := by
    intro j
    have h2 := stalkMap_coord_sub_constAt_mem (ψ := ψ) hΦ g₂ hp₂ j
    rw [hz j] at h2
    exact eq_of_sub_constAt_mem (stalkMap_coord_sub_constAt_mem (ψ := ψ) hΦ g₁ hp₁ j) h2
  exact Φ.injOn hp₁ hp₂ (ψ.injective (funext hval))

/-- Two `K`-morphisms from an analytic `K`-space into `Sp(M')` that agree, at every point `z`, on
the coordinate germs of some chart containing both images of `z` are equal — base points by
`base_eq_of_coord`, stalk maps by `stalkMap_eq_of_coord`, then Mathlib's
`SheafedSpace.hom_stalk_ext`. -/
theorem hom_ext_of_coord_chart (g₁ g₂ : Z.toKLocallyRingedSpace ⟶ ofManifold K E M')
    (h : ∀ z : Z, ∃ (Φ : OpenPartialHomeomorph M' E) (hΦ : Φ ∈ maximalAtlas 𝓘(K, E) ω M')
      (hp₁ : g₁.1.base z ∈ Φ.source) (hp₂ : g₂.1.base z ∈ Φ.source),
      ∀ j, (g₂.1.stalkMap z).hom (coord E ψ Φ hΦ hp₂ j) =
        (g₁.1.stalkMap z).hom (coord E ψ Φ hΦ hp₁ j)) : g₁ = g₂ := by
  have hb : ∀ z, g₁.1.base z = g₂.1.base z := fun z => by
    obtain ⟨Φ, hΦ, hp₁, hp₂, hz⟩ := h z
    exact base_eq_of_coord hΦ g₁ g₂ hp₁ hp₂ hz
  apply Hom.ext
  apply LocallyRingedSpace.Hom.ext'
  refine congrArg (fun f => f.hom) (SheafedSpace.hom_stalk_ext g₁.1.toShHom g₂.1.toShHom
    (TopCat.ext fun z => hb z) fun z => ?_)
  obtain ⟨Φ, hΦ, hp₁, hp₂, hz⟩ := h z
  exact stalkMap_eq_of_coord hΦ g₁ z hp₁ (hb z) hp₂ (g₂.1.stalkMap z)
    (fun c => g₂.algebraMap_stalk z c) hz

end ChartExt

section Forced

variable {c : ℕ} {π : M' → M} (hπ : ContMDiff 𝓘(K, E) 𝓘(K, E) ω π)
  {φ : OpenPartialHomeomorph M E} (hφ : φ ∈ maximalAtlas 𝓘(K, E) ω M) {σ : Fin c ↪ Fin n}
  {i : Fin c} {Φ : OpenPartialHomeomorph M' E} (hΦ : IsBlowUpChart ψ π φ σ i Φ)
  (g : Z.toKLocallyRingedSpace ⟶ ofManifold K E M') {z : Z} (hp : g.1.base z ∈ Φ.source)

/-- The scaling coordinate is forced ([BM88, 4.1 (2)], `germMap_coord_self`):
`(g ≫ π)^* z_{σ i} = g^* u_{σ i}`. -/
theorem pullback_coord_self :
    ((g ≫ ofManifoldHom π hπ).1.stalkMap z).hom
        (coord E ψ φ hφ (hΦ.source_subset hp) (σ i)) =
      (g.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp (σ i)) :=
  (stalkMap_comp_ofManifoldHom_apply hπ g z _).trans
    (congrArg _ (hΦ.germMap_coord_self hπ hφ hp))

/-- A ratio coordinate (`germMap_coord_of_ne`): `(g ≫ π)^* z_{σ k} = g^* u_{σ i} · g^* u_{σ k}` for
`k ≠ i`. -/
theorem pullback_coord_of_ne {k : Fin c} (hk : k ≠ i) :
    ((g ≫ ofManifoldHom π hπ).1.stalkMap z).hom
        (coord E ψ φ hφ (hΦ.source_subset hp) (σ k)) =
      (g.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp (σ i)) *
        (g.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp (σ k)) :=
  (stalkMap_comp_ofManifoldHom_apply hπ g z _).trans
    ((congrArg _ (hΦ.germMap_coord_of_ne hπ hφ hp hk)).trans (map_mul _ _ _))

/-- An off-block coordinate (`germMap_coord_off`): `(g ≫ π)^* z_j = g^* u_j`. -/
theorem pullback_coord_off {j : Fin n} (hj : ∀ k, σ k ≠ j) :
    ((g ≫ ofManifoldHom π hπ).1.stalkMap z).hom
        (coord E ψ φ hφ (hΦ.source_subset hp) j) =
      (g.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp j) :=
  (stalkMap_comp_ofManifoldHom_apply hπ g z _).trans
    (congrArg _ (hΦ.germMap_coord_off hπ hφ hp hj))

/-- If the stalk of the centre's ideal sheaf `D` at `π (g z)` is spanned by the adapted coordinates,
the stalk at `z` of the inverse image of `D` along `g ≫ π` is generated by the pulled-back scaling
coordinate `(g ≫ π)^* z_{σ i}` — every other generator is a multiple of it by a ratio coordinate
([Hir64, Ch. 0, §2, p. 123]; [BM88, 4.1]). -/
theorem stalkIdeal_comap_comp_eq_span {D : IdealSheaf (structureSheaf K E M)}
    (hspan : D.stalkIdeal ((g ≫ ofManifoldHom π hπ).1.base z) =
      Ideal.span (Set.range fun k => coord E ψ φ hφ (hΦ.source_subset hp) (σ k))) :
    (QuotientSpace.comap (g ≫ ofManifoldHom π hπ).1 D).stalkIdeal z =
      Ideal.span
        {((g ≫ ofManifoldHom π hπ).1.stalkMap z).hom
          (coord E ψ φ hφ (hΦ.source_subset hp) (σ i))} := by
  refine (QuotientSpace.stalkIdeal_comap (X := (ofManifold K E M).toLocallyRingedSpace)
    (g ≫ ofManifoldHom π hπ).1 D z).trans ?_
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr (hspan.le.trans (Ideal.span_le.mpr ?_)))
    (Ideal.span_le.mpr ?_)
  · rintro _ ⟨k, rfl⟩
    change ((g ≫ ofManifoldHom π hπ).1.stalkMap z).hom
        (coord E ψ φ hφ (hΦ.source_subset hp) (σ k)) ∈
      Ideal.span
        {((g ≫ ofManifoldHom π hπ).1.stalkMap z).hom (coord E ψ φ hφ (hΦ.source_subset hp) (σ i))}
    by_cases hk : k = i
    · subst hk
      exact Ideal.mem_span_singleton_self _
    · rw [pullback_coord_of_ne hπ hφ hΦ g hp hk, ← pullback_coord_self hπ hφ hΦ g hp]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rintro _ rfl
    exact Ideal.mem_map_of_mem _ (hspan.ge (Ideal.subset_span ⟨i, rfl⟩))

/-- Under Hironaka's invertibility hypothesis on the test pair [Hir64, Ch. 0, §2, p. 123] the
pulled-back scaling coordinate is a non-zero-divisor — it generates the same stalk ideal as a
non-zero-divisor, so it differs from it by a unit
(`exists_unit_mul_eq_of_span_range_eq_span_singleton`). -/
theorem mem_nonZeroDivisors_pullback_coord {D : IdealSheaf (structureSheaf K E M)}
    (hspan : D.stalkIdeal ((g ≫ ofManifoldHom π hπ).1.base z) =
      Ideal.span (Set.range fun k => coord E ψ φ hφ (hΦ.source_subset hp) (σ k)))
    (hinv : ∃ a ∈ nonZeroDivisors (Z.toLocallyRingedSpace.presheaf.stalk z),
      (QuotientSpace.comap (g ≫ ofManifoldHom π hπ).1 D).stalkIdeal z = Ideal.span {a}) :
    ((g ≫ ofManifoldHom π hπ).1.stalkMap z).hom (coord E ψ φ hφ (hΦ.source_subset hp) (σ i)) ∈
      nonZeroDivisors (Z.toLocallyRingedSpace.presheaf.stalk z) := by
  obtain ⟨a, ha, hspan'⟩ := hinv
  rw [stalkIdeal_comap_comp_eq_span hπ hφ hΦ g hp hspan] at hspan'
  obtain ⟨_, u, hu, hb⟩ := Algebra.exists_unit_mul_eq_of_span_range_eq_span_singleton
    (fun _ : Unit => ((g ≫ ofManifoldHom π hπ).1.stalkMap z).hom
      (coord E ψ φ hφ (hΦ.source_subset hp) (σ i))) a ha
    (by rw [Set.range_const]; exact hspan')
  rw [hb]
  exact Submonoid.mul_mem _ hu.mem_nonZeroDivisors ha

end Forced

section Unique

variable [IsManifold 𝓘(K, E) ω M'] [T2Space M'] [SecondCountableTopology M'] {Y : Set M} {c : ℕ}
  {π : M' → M}
  (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
  {D : IdealSheaf (structureSheaf K E M)} (hD : IsIdealSheafOf ψ Y c D)
  (g₁ g₂ : Z.toKLocallyRingedSpace ⟶ ofManifold K E M')
  (hinv : ∀ z, ∃ a ∈ nonZeroDivisors (Z.toLocallyRingedSpace.presheaf.stalk z),
    (QuotientSpace.comap (g₁ ≫ ofManifoldHom π h.contMDiff).1 D).stalkIdeal z = Ideal.span {a})
  (h₂ : g₂ ≫ ofManifoldHom π h.contMDiff = g₁ ≫ ofManifoldHom π h.contMDiff)

include hinv h₂ in
/-- In a blow-up chart containing the images of `z` under both lifts, the lifts pull the chart's
coordinate germs back to the same germs — the scaling coordinate is `f'^* z_{σ i}` for both, the
ratio coordinates follow by cancelling that non-zero-divisor, the off-block ones are `f'^* z_j`
for both. -/
theorem stalkMap_coord_eq_of_mem_source {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ maximalAtlas 𝓘(K, E) ω M) {σ : Fin c ↪ Fin n} {i : Fin c}
    {Φ : OpenPartialHomeomorph M' E} (hΦ : IsBlowUpChart ψ π φ σ i Φ) {z : Z}
    (hp₁ : g₁.1.base z ∈ Φ.source) (hp₂ : g₂.1.base z ∈ Φ.source)
    (hspan : D.stalkIdeal ((g₁ ≫ ofManifoldHom π h.contMDiff).1.base z) =
      Ideal.span (Set.range fun k => coord E ψ φ hφ (hΦ.source_subset hp₁) (σ k))) (j : Fin n) :
    (g₂.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp₂ j) =
      (g₁.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp₁ j) := by
  have hnzd := mem_nonZeroDivisors_pullback_coord h.contMDiff hφ hΦ g₁ hp₁ hspan (hinv z)
  rw [pullback_coord_self h.contMDiff hφ hΦ g₁ hp₁] at hnzd
  have hi : (g₂.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp₂ (σ i)) =
      (g₁.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp₁ (σ i)) :=
    (pullback_coord_self h.contMDiff hφ hΦ g₂ hp₂).symm.trans
      ((stalkMap_apply_coord_congr h₂ hφ z (hΦ.source_subset hp₂) (hΦ.source_subset hp₁)
        (σ i)).trans (pullback_coord_self h.contMDiff hφ hΦ g₁ hp₁))
  by_cases hj : ∃ k, σ k = j
  · obtain ⟨k, rfl⟩ := hj
    by_cases hk : k = i
    · subst hk
      exact hi
    · have e := (pullback_coord_of_ne h.contMDiff hφ hΦ g₂ hp₂ hk).symm.trans
        ((stalkMap_apply_coord_congr h₂ hφ z (hΦ.source_subset hp₂) (hΦ.source_subset hp₁)
          (σ k)).trans (pullback_coord_of_ne h.contMDiff hφ hΦ g₁ hp₁ hk))
      rw [hi] at e
      exact sub_eq_zero.mp
        ((mem_nonZeroDivisors_iff.mp hnzd).1 _ (by rw [mul_sub, e, sub_self]))
  · push Not at hj
    exact (pullback_coord_off h.contMDiff hφ hΦ g₂ hp₂ hj).symm.trans
      ((stalkMap_apply_coord_congr h₂ hφ z (hΦ.source_subset hp₂) (hΦ.source_subset hp₁)
        j).trans (pullback_coord_off h.contMDiff hφ hΦ g₁ hp₁ hj))

include hY hD hinv h₂ in
/-- The second lift's image lies in the blow-up chart `Φᵢ` containing the first lift's image. In a
blow-up chart `Φₖ` containing `g₂ z` the coordinate `u_{σ i}` pulls back to a unit — its product
with `g₁^* u_{σ k}` is `1` after cancelling the non-zero-divisor `f'^* z_{σ i}` — so its value at
`g₂ z` is nonzero and the chart change `mem_source_of_coord_ne_zero` lands `g₂ z` in `Φᵢ`; for
`k = i` the two charts have the same source. -/
theorem mem_source_of_lift {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
    (hφa : IsAdaptedChart ψ Y φ σ) {i : Fin c} {Φ : OpenPartialHomeomorph M' E}
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {z : Z} (hp₁ : g₁.1.base z ∈ Φ.source)
    (hzY : π (g₁.1.base z) ∈ Y) : g₂.1.base z ∈ Φ.source := by
  have hφ : φ ∈ maximalAtlas 𝓘(K, E) ω M := hφa.1
  have hπ₂ := base_comp_eq h.contMDiff h₂ z
  obtain ⟨k, Φk, hΦk, hp₂⟩ := h.cover φ σ hφa (g₂.1.base z : M')
    (Set.mem_of_eq_of_mem hπ₂ (hΦ.source_subset hp₁))
  by_cases hk : k = i
  · exact IsBlowUp.mem_source_of_same_index (M' := M') hY h (hk ▸ hΦk) hΦ hp₂
  have hspan : D.stalkIdeal ((g₁ ≫ ofManifoldHom π h.contMDiff).1.base z) =
      Ideal.span (Set.range fun k => coord E ψ φ hφ (hΦ.source_subset hp₁) (σ k)) :=
    hD.2 φ σ hφa _ (hΦ.source_subset hp₁) hzY
  have hnzd := mem_nonZeroDivisors_pullback_coord h.contMDiff hφ hΦ g₁ hp₁ hspan (hinv z)
  have e1 : ((g₁ ≫ ofManifoldHom π h.contMDiff).1.stalkMap z).hom
      (coord E ψ φ hφ (hΦ.source_subset hp₁) (σ i)) =
      (g₂.1.stalkMap z).hom (coord E ψ Φk hΦk.mem_maximalAtlas hp₂ (σ k)) *
        (g₂.1.stalkMap z).hom (coord E ψ Φk hΦk.mem_maximalAtlas hp₂ (σ i)) :=
    (stalkMap_apply_coord_congr h₂.symm hφ z (hΦ.source_subset hp₁) (hΦk.source_subset hp₂)
      (σ i)).trans (pullback_coord_of_ne h.contMDiff hφ hΦk g₂ hp₂ (Ne.symm hk))
  have e2 : (g₂.1.stalkMap z).hom (coord E ψ Φk hΦk.mem_maximalAtlas hp₂ (σ k)) =
      ((g₁ ≫ ofManifoldHom π h.contMDiff).1.stalkMap z).hom
        (coord E ψ φ hφ (hΦ.source_subset hp₁) (σ i)) *
        (g₁.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp₁ (σ k)) :=
    (pullback_coord_self h.contMDiff hφ hΦk g₂ hp₂).symm.trans
      ((stalkMap_apply_coord_congr h₂ hφ z (hΦk.source_subset hp₂) (hΦ.source_subset hp₁)
        (σ k)).trans ((pullback_coord_of_ne h.contMDiff hφ hΦ g₁ hp₁ hk).trans
          (congrArg (· * _) (pullback_coord_self h.contMDiff hφ hΦ g₁ hp₁).symm)))
  have hC : IsUnit ((g₂.1.stalkMap z).hom (coord E ψ Φk hΦk.mem_maximalAtlas hp₂ (σ i))) := by
    suffices hCB : (g₂.1.stalkMap z).hom (coord E ψ Φk hΦk.mem_maximalAtlas hp₂ (σ i)) *
        (g₁.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp₁ (σ k)) = 1 from
      ⟨⟨_, _, hCB, by rw [mul_comm]; exact hCB⟩, rfl⟩
    have e3 : ((g₁ ≫ ofManifoldHom π h.contMDiff).1.stalkMap z).hom
        (coord E ψ φ hφ (hΦ.source_subset hp₁) (σ i)) *
        ((g₂.1.stalkMap z).hom (coord E ψ Φk hΦk.mem_maximalAtlas hp₂ (σ i)) *
          (g₁.1.stalkMap z).hom (coord E ψ Φ hΦ.mem_maximalAtlas hp₁ (σ k)) - 1) = 0 := by
      rw [mul_sub, mul_one, mul_left_comm, mul_comm, ← e2, ← e1, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hnzd).1 _ e3)
  have hloc : IsLocalHom (g₂.1.stalkMap z).hom := g₂.1.prop z
  have hu : IsUnit (coord E ψ Φk hΦk.mem_maximalAtlas hp₂ (σ i)) :=
    isUnit_of_map_unit (g₂.1.stalkMap z).hom _ hC
  refine IsBlowUp.mem_source_of_coord_ne_zero (M' := M') hY h hΦk hΦ hp₂
    fun h0 => ?_
  refine (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp ?_)) hu
  rw [mem_maximalIdeal_iff_eval, eval_coord]
  exact h0

include hY hD hinv h₂ in
/-- **Uniqueness of the lift** through the charted blow-up (Hironaka's (**),
[Hir64, Ch. 0, §2, p. 123]; [BM88, 4.1]): two `K`-morphisms `g₁ g₂ : Y' → Sp(M')` with
`g₁ ≫ Sp(π) = g₂ ≫ Sp(π)`, the inverse image of the centre along that composite being invertible,
coincide. Over the centre the chart coordinates are forced (`stalkMap_coord_eq_of_mem_source`);
off it `π` is a local diffeomorphism and the transported chart's coordinates are forced
directly. -/
theorem lift_unique_of_comp_eq [IsManifold 𝓘(K, E) ω M] : g₁ = g₂ := by
  refine hom_ext_of_coord_chart (ψ := ψ) g₁ g₂ fun z => ?_
  by_cases hzY : π (g₁.1.base z) ∈ Y
  · obtain ⟨φ, σ, haφ, hφa⟩ := hY.exists_adaptedChart _ hzY
    obtain ⟨i, Φ, hΦ, hp₁⟩ := h.cover φ σ hφa (g₁.1.base z : M') haφ
    have hp₂ := mem_source_of_lift hY h hD g₁ g₂ hinv h₂ hφa hΦ hp₁ hzY
    exact ⟨Φ, hΦ.mem_maximalAtlas, hp₁, hp₂,
      stalkMap_coord_eq_of_mem_source h g₁ g₂ hinv h₂ hφa.1 hΦ hp₁ hp₂
        (hD.2 φ σ hφa _ (hΦ.source_subset hp₁) hzY)⟩
  · obtain ⟨Φ₀, hp₀, hΦ₀⟩ :=
      (h.isLocalDiffeomorphOn_compl ⟨g₁.1.base z, hzY⟩).exists_partialDiffeomorph
    have hp₀ : g₁.1.base z ∈ Φ₀.source := hp₀
    have hπ₂ := base_comp_eq h.contMDiff h₂ z
    have hb : g₁.1.base z = g₂.1.base z := by
      have h₂' : g₂.1.base z ∈ π ⁻¹' Yᶜ := by
        change π (g₂.1.base z) ∉ Y
        rw [hπ₂]
        exact hzY
      exact h.bijOn_compl.injOn hzY h₂' hπ₂.symm
    have hφ : chartAt E (π (g₁.1.base z)) ∈ maximalAtlas 𝓘(K, E) ω M :=
      IsManifold.chart_mem_maximalAtlas _
    have hπp₁ : π (g₁.1.base z) ∈ (chartAt E (π (g₁.1.base z))).source := mem_chart_source E _
    have hp₀' : g₂.1.base z ∈ Φ₀.source := hb ▸ hp₀
    have hπp₂ : π (g₂.1.base z) ∈ (chartAt E (π (g₁.1.base z))).source := hπ₂ ▸ hπp₁
    have hp₁' : g₁.1.base z ∈ (transportChart Φ₀.symm (chartAt E (π (g₁.1.base z)))).source :=
      ⟨hp₀, by
        change Φ₀ (g₁.1.base z) ∈ (chartAt E (π (g₁.1.base z))).source
        rw [← hΦ₀ hp₀]; exact hπp₁⟩
    have hp₂' : g₂.1.base z ∈ (transportChart Φ₀.symm (chartAt E (π (g₁.1.base z)))).source :=
      ⟨hp₀', by
        change Φ₀ (g₂.1.base z) ∈ (chartAt E (π (g₁.1.base z))).source
        rw [← hΦ₀ hp₀']; exact hπp₂⟩
    refine ⟨transportChart Φ₀.symm _, transportChart_mem_maximalAtlas Φ₀.symm hφ, hp₁', hp₂',
      fun j => ?_⟩
    rw [← germMap_coord_transportChart h.contMDiff hφ Φ₀ hΦ₀ hp₀' hπp₂ j,
      ← germMap_coord_transportChart h.contMDiff hφ Φ₀ hΦ₀ hp₀ hπp₁ j,
      ← stalkMap_comp_ofManifoldHom_apply h.contMDiff g₂ z,
      ← stalkMap_comp_ofManifoldHom_apply h.contMDiff g₁ z]
    exact stalkMap_apply_coord_congr h₂ hφ z hπp₂ hπp₁ j

end Unique

end AnalyticSpace.KLocallyRingedSpace
