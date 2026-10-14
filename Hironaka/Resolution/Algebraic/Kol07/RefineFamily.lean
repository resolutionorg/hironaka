/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Collapse
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Subdivisions of divisor families

The refinement of a blow-up sequence to irreducible centers
(`Hironaka/Resolution/Algebraic/Kol07/RefineIrreducible.lean`) replaces the blow-up of a center `Z =
⊔ Z_k` by the componentwise sequence of its components, so
the exceptional divisor `f⁻¹(Z)` of the original sequence reappears in the refined one as the `c`
exceptional divisors of the components, and every later total transform of the refined sequence is
a *subdivision* of the corresponding total transform of the original: at each point, each of its
components has the stalk of a component of the original family, injectively. Kollár's simple
normal crossing condition [Kol07, Definition 24 (4)] only sees the components through a point and
their stalks, so it passes from a family to any subdivision (`hasSncWith_of_subdivides`), and with
it the order condition of [Kol07, Definition 66] (`isOrderSeq_of_subdivides`,
`isOrderGeSeq_of_subdivides`). This module sets up the relation and its stability under inverse
images, total transforms (the stalk of a strict transform depends only on the stalk of the
transformed ideal, the stalk formula for saturations) and open covers, and shows that a family
subdivides its collapse along pairwise disjoint members (`subdivides_collapse`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Scheme.IdealSheafData IdealSheafData

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}}

/-- The divisor family `F` **subdivides** `G` if at every point `x` there is an assignment `q` of
components of `F` to components of `G`, sending each component of `F` through `x` to a component
of `G` with the same stalk at `x`, injective on the components through `x`. The exceptional
divisor of the blow-up of a disjoint union `⊔ Z_k` is subdivided by the exceptional divisors of the
`Z_k`. Not in the sources; the relation along which simple normal crossings are transported to the
refinement of a sequence to irreducible centers. -/
def Subdivides (F G : DivisorFamily X) : Prop :=
  ∀ x : X, ∃ q : F.ι → Option G.ι,
    (∀ j j', x ∈ (F.component j).support → x ∈ (F.component j').support → q j = q j' → j = j') ∧
    ∀ j, x ∈ (F.component j).support →
      ∃ i, q j = some i ∧ (F.component j).stalkIdeal x = (G.component i).stalkIdeal x

end AlgebraicGeometry.Scheme.DivisorFamily

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A point with unit stalk ideal is off the support (the stalk ideal at a point of the support
lies in the maximal ideal, `mem_support_iff_stalkIdeal_le_maximalIdeal`). -/
theorem notMem_support_of_stalkIdeal_eq_top {I : X.IdealSheafData} {x : X}
    (h : I.stalkIdeal x = ⊤) : x ∉ I.support := by
  intro hx
  have hle := (mem_support_iff_stalkIdeal_le_maximalIdeal I x).mp hx
  rw [h] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

/-- Two ideal sheaves with the same stalk at `x` have `x` in both supports or in neither. -/
theorem mem_support_of_stalkIdeal_eq {I J : X.IdealSheafData} {x : X} (hx : x ∈ I.support)
    (h : I.stalkIdeal x = J.stalkIdeal x) : x ∈ J.support := by
  by_contra hJ
  exact notMem_support_of_stalkIdeal_eq_top (h.trans (stalkIdeal_eq_top_of_notMem_support J hJ)) hx

/-- Every family subdivides itself. -/
theorem subdivides_refl (F : DivisorFamily X) : F.Subdivides F := fun _ =>
  ⟨some, fun _ _ _ _ h => Option.some_injective _ h, fun j _ => ⟨j, rfl, rfl⟩⟩

/-- Subdivisions compose. -/
theorem subdivides_trans {F G H : DivisorFamily X} (h₁ : F.Subdivides G) (h₂ : G.Subdivides H) :
    F.Subdivides H := by
  intro x
  obtain ⟨q₁, hq₁, hs₁⟩ := h₁ x
  obtain ⟨q₂, hq₂, hs₂⟩ := h₂ x
  refine ⟨fun j => (q₁ j).bind q₂, ?_, ?_⟩
  · intro j j' hj hj' heq
    obtain ⟨i, hi, hsi⟩ := hs₁ j hj
    obtain ⟨i', hi', hsi'⟩ := hs₁ j' hj'
    change (q₁ j).bind q₂ = (q₁ j').bind q₂ at heq
    rw [hi, hi'] at heq
    have hii : i = i' := hq₂ i i' (mem_support_of_stalkIdeal_eq hj hsi)
      (mem_support_of_stalkIdeal_eq hj' hsi') heq
    exact hq₁ j j' hj hj' (hi.trans (by rw [hii]; exact hi'.symm))
  · intro j hj
    obtain ⟨i, hi, hsi⟩ := hs₁ j hj
    obtain ⟨l, hl, hsl⟩ := hs₂ i (mem_support_of_stalkIdeal_eq hj hsi)
    exact ⟨l, by change (q₁ j).bind q₂ = some l; rw [hi]; exact hl, hsi.trans hsl⟩

/-- Subdivisions pull back along any morphism: the components through `y` of the inverse image are
the inverse images of the components through `g y` (`mem_support_comap_iff_apply`), with the
mapped stalks (`stalkIdeal_comap`). -/
theorem subdivides_comap {Y : Scheme.{u}} {F G : DivisorFamily X} (h : F.Subdivides G)
    (g : Y ⟶ X) : (F.comap g).Subdivides (G.comap g) := by
  intro y
  obtain ⟨q, hq, hs⟩ := h (g y)
  refine ⟨q, fun j j' hj hj' => hq j j' ?_ ?_, fun j hj => ?_⟩
  · exact (mem_support_comap_iff_apply _ g y).mp hj
  · exact (mem_support_comap_iff_apply _ g y).mp hj'
  · obtain ⟨i, hi, hsi⟩ := hs j ((mem_support_comap_iff_apply _ g y).mp hj)
    refine ⟨i, hi, ?_⟩
    change ((F.component j).comap g).stalkIdeal y = ((G.component i).comap g).stalkIdeal y
    rw [stalkIdeal_comap, stalkIdeal_comap, hsi]

/-- The subdivision relation is local: it holds as soon as it holds after restriction to the
members of an open cover (the stalks at `ι w` and at `w` correspond under the stalk isomorphism of
the open immersion, `stalkIdeal_eq_map_symm_stalkIdeal_comap`). -/
theorem subdivides_of_cover {σ : Type*} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] (hcov : ∀ x, ∃ i w, ι i w = x) {F G : DivisorFamily X}
    (h : ∀ i, (F.comap (ι i)).Subdivides (G.comap (ι i))) : F.Subdivides G := by
  intro x
  obtain ⟨i, w, rfl⟩ := hcov x
  obtain ⟨q, hq, hs⟩ := h i w
  refine ⟨q, fun j j' hj hj' => hq j j' ?_ ?_, fun j hj => ?_⟩
  · exact (mem_support_comap_iff_apply _ (ι i) w).mpr hj
  · exact (mem_support_comap_iff_apply _ (ι i) w).mpr hj'
  · obtain ⟨l, hl, hsl⟩ := hs j ((mem_support_comap_iff_apply _ (ι i) w).mpr hj)
    refine ⟨l, hl, ?_⟩
    rw [stalkIdeal_eq_map_symm_stalkIdeal_comap (ι i) (F.component j) w,
      stalkIdeal_eq_map_symm_stalkIdeal_comap (ι i) (G.component l) w]
    exact congrArg _ hsl

/-- Simple normal crossings with `Z` [Kol07, Definition 24 (4)] pass from a family to any
subdivision of it: the components of the subdivision through `x` are assigned injectively to
components of the coarser family through `x` with the same stalks, so the same coordinates and the
composed assignment work. -/
theorem hasSncWith_of_subdivides {F G : DivisorFamily X} (h : F.Subdivides G)
    {Z : X.IdealSheafData} (hZ : G.HasSncWith Z) : F.HasSncWith Z := by
  intro x hx
  obtain ⟨n, z, ⟨hz, c, hc, hcz⟩, s, hs⟩ := hZ x hx
  obtain ⟨q, hq, hs'⟩ := h x
  choose i hi hsi using hs'
  have hmem : ∀ j : {j : F.ι // x ∈ (F.component j).support},
      x ∈ (G.component (i j.1 j.2)).support :=
    fun j => mem_support_of_stalkIdeal_eq j.2 (hsi j.1 j.2)
  let c' : {j : F.ι // x ∈ (F.component j).support} → Fin n := fun j => c ⟨i j.1 j.2, hmem j⟩
  have hc' : Function.Injective c' := by
    intro j j' heq
    have h2 : i j.1 j.2 = i j'.1 j'.2 := congrArg Subtype.val (hc heq)
    have h3 : q j.1 = q j'.1 := by rw [hi j.1 j.2, hi j'.1 j'.2, h2]
    exact Subtype.ext (hq j.1 j'.1 j.2 j'.2 h3)
  refine ⟨n, z, ⟨hz, c', hc', fun j => ?_⟩, s, hs⟩
  exact (hsi j.1 j.2).trans (hcz ⟨i j.1 j.2, hmem j⟩)

/-- Subdivisions are preserved by the total transform [Kol07, Definition 25] along a morphism `π`
with an invertible distinguished divisor `K`: a strict transform through `y` comes from a
component through `π y`, and the stalk of the strict transform `((I.comap π) : K^∞)` at `y`
depends only on the stalk of `I` at `π y` (the stalk formula `stalkIdeal_saturate_of_isInvertible`);
the distinguished divisor is assigned to itself. -/
theorem subdivides_totalTransformAlong {F G : DivisorFamily X} (h : F.Subdivides G)
    {B : Scheme.{u}} (π : B ⟶ X) {K : B.IdealSheafData} (hK : K.IsInvertible) :
    (F.totalTransformAlong π K).Subdivides (G.totalTransformAlong π K) := by
  intro y
  obtain ⟨q, hq, hs⟩ := h (π y)
  have hmem : ∀ j : F.ι, y ∈ ((F.component j).strictTransformAlong π K).support →
      π y ∈ (F.component j).support := by
    intro j hj
    by_contra hn
    refine notMem_support_of_stalkIdeal_eq_top ?_ hj
    rw [strictTransformAlong, stalkIdeal_saturate_of_isInvertible _ hK, stalkIdeal_comap,
      stalkIdeal_eq_top_of_notMem_support _ hn, Ideal.map_top]
    simp only [Submodule.top_colon, iSup_const]
  have hstalk : ∀ (j : F.ι) (i : G.ι),
      (F.component j).stalkIdeal (π y) = (G.component i).stalkIdeal (π y) →
      ((F.component j).strictTransformAlong π K).stalkIdeal y =
        ((G.component i).strictTransformAlong π K).stalkIdeal y := by
    intro j i hji
    rw [strictTransformAlong, strictTransformAlong, stalkIdeal_saturate_of_isInvertible _ hK,
      stalkIdeal_saturate_of_isInvertible _ hK, stalkIdeal_comap, stalkIdeal_comap, hji]
  refine ⟨fun j' => Sum.elim (fun j => (q j).map fun i => toLex (Sum.inl i))
    (fun _ => some (toLex (Sum.inr PUnit.unit))) (ofLex j'), ?_, ?_⟩
  · rintro (j | u) (j' | u') hj hj' heq
    · change y ∈ ((F.component j).strictTransformAlong π K).support at hj
      change y ∈ ((F.component j').strictTransformAlong π K).support at hj'
      change (q j).map _ = (q j').map _ at heq
      obtain ⟨i, hi, -⟩ := hs j (hmem j hj)
      obtain ⟨i', hi', -⟩ := hs j' (hmem j' hj')
      rw [hi, hi'] at heq
      have hii : i = i' := Sum.inl.inj (Option.some_injective _ heq)
      have hjj : j = j' := hq j j' (hmem j hj) (hmem j' hj') (hi.trans (by rw [hii, hi']))
      exact congrArg (fun j => (toLex (Sum.inl j) : (F.totalTransformAlong π K).ι)) hjj
    · change y ∈ ((F.component j).strictTransformAlong π K).support at hj
      change (q j).map _ = some _ at heq
      obtain ⟨i, hi, -⟩ := hs j (hmem j hj)
      rw [hi] at heq
      exact absurd (Option.some_injective _ heq) Sum.inl_ne_inr
    · change y ∈ ((F.component j').strictTransformAlong π K).support at hj'
      change some _ = (q j').map _ at heq
      obtain ⟨i', hi', -⟩ := hs j' (hmem j' hj')
      rw [hi'] at heq
      exact absurd (Option.some_injective _ heq) Sum.inr_ne_inl
    · exact congrArg (fun u => (toLex (Sum.inr u) : (F.totalTransformAlong π K).ι))
        (Subsingleton.elim u u')
  · rintro (j | u) hj
    · change y ∈ ((F.component j).strictTransformAlong π K).support at hj
      obtain ⟨i, hi, hsi⟩ := hs j (hmem j hj)
      refine ⟨toLex (Sum.inl i), ?_, hstalk j i hsi⟩
      change (q j).map _ = some _
      rw [hi]
      rfl
    · exact ⟨toLex (Sum.inr PUnit.unit), rfl, rfl⟩

/-- Subdivisions are preserved by the total transform under a blow-up [Kol07, Definition 25]. -/
theorem subdivides_totalTransform {F G : DivisorFamily X} (h : F.Subdivides G)
    (D : X.IdealSheafData) : (F.totalTransform D).Subdivides (G.totalTransform D) :=
  subdivides_totalTransformAlong h D.blowUpπ (blowUp.isInvertible_comap_π D)

/-- A smooth blow-up sequence of order `d` [Kol07, Definition 66] for the family `E` is one for
every subdivision `F` of `E`: stage by stage, the induced families of `F` subdivide those of `E`
(`subdivides_totalTransform`) and the snc conditions descend (`hasSncWith_of_subdivides`); the
smoothness and order conditions do not involve the family. -/
theorem isOrderSeq_of_subdivides {k : Type u} [Field k] {S : BlowUpSequence X}
    (f : X ⟶ Spec (.of k)) {J : X.IdealSheafData} {E F : DivisorFamily X} {d : ℕ}
    (hFE : F.Subdivides E) (hS : S.IsOrderSeq f J E d) : S.IsOrderSeq f J F d := by
  induction S with
  | nil X => exact ⟨hS.1, fun i => i.elim0⟩
  | cons X D rest ih =>
    rw [isOrderSeq_cons_iff] at hS ⊢
    exact ⟨⟨hS.1.1, hasSncWith_of_subdivides hFE hS.1.2.1, hS.1.2.2⟩,
      ih _ (subdivides_totalTransform hFE D) hS.2⟩

/-! ### Subdivision by a collapse, and the marked form of `isOrderSeq_of_subdivides` -/

section M20


/-- A family subdivides its collapse along pairwise disjoint members (the collapse of the disjoint
members of the boundary into one divisor in the proof of [Kol07, Theorem 35] given in [Kol07, 72]):
a collapsed member is assigned to the collapsed divisor `⊥`, whose stalk at a point is the stalk of
the one collapsed member through it (`exists_stalkIdeal_prod_eq_of_disjoint`); the other members
are unchanged. -/
theorem subdivides_collapse (F : DivisorFamily X) (p : F.ι → Prop) [DecidablePred p]
    (hp : ∀ (x : X) (a b : F.ι), p a → p b → x ∈ (F.component a).support →
      x ∈ (F.component b).support → a = b) :
    F.Subdivides (F.collapse p) := by
  intro x
  -- the assignment, typed on the index type of the collapse written out (`(F.collapse p).ι` is
  -- `WithBot {a // ¬ p a}` only by unfolding)
  let q : F.ι → Option (WithBot {a : F.ι // ¬ p a}) := fun j =>
    if hj : p j then some ⊥ else some ((⟨j, hj⟩ : {a : F.ι // ¬ p a}) : WithBot {a : F.ι // ¬ p a})
  have hq_pos : ∀ j (hj : p j), q j = some ⊥ := fun j hj => dite_eq_left hj
  have hq_neg : ∀ j (hj : ¬ p j),
      q j = some ((⟨j, hj⟩ : {a : F.ι // ¬ p a}) : WithBot {a : F.ι // ¬ p a}) :=
    fun j hj => dite_eq_right hj
  refine ⟨q, ?_, ?_⟩
  · change ∀ j j', x ∈ (F.component j).support → x ∈ (F.component j').support → q j = q j' →
      j = j'
    intro j j' hxj hxj' hq
    by_cases hj : p j
    · by_cases hj' : p j'
      · exact hp x j j' hj hj' hxj hxj'
      · rw [hq_pos j hj, hq_neg j' hj'] at hq
        exact absurd (Option.some.inj hq) WithBot.bot_ne_coe
    · by_cases hj' : p j'
      · rw [hq_neg j hj, hq_pos j' hj'] at hq
        exact absurd (Option.some.inj hq) WithBot.coe_ne_bot
      · rw [hq_neg j hj, hq_neg j' hj'] at hq
        exact congrArg Subtype.val (WithBot.coe_injective (Option.some.inj hq))
  · change ∀ j, x ∈ (F.component j).support → ∃ i : WithBot {a : F.ι // ¬ p a}, q j = some i ∧
      (F.component j).stalkIdeal x = ((F.collapse p).component i).stalkIdeal x
    intro j hxj
    by_cases hj : p j
    · refine ⟨⊥, hq_pos j hj, ?_⟩
      have hx : x ∈ (∏ a : {a : F.ι // p a}, F.component a.1).support :=
        (mem_support_finset_prod_iff _ _ _).mpr ⟨⟨j, hj⟩, Finset.mem_univ _, hxj⟩
      obtain ⟨a, hxa, heq⟩ := exists_stalkIdeal_prod_eq_of_disjoint
        (G := fun a : {a : F.ι // p a} => F.component a.1) (collapse_disjoint hp) hx
      have ha : a = ⟨j, hj⟩ := Subtype.ext (hp x a.1 j a.2 hj hxa hxj)
      subst ha
      rw [collapse_component_bot]
      exact heq.symm
    · exact ⟨((⟨j, hj⟩ : {a : F.ι // ¬ p a}) : WithBot {a : F.ι // ¬ p a}), hq_neg j hj, rfl⟩

/-- The marked form of `isOrderSeq_of_subdivides`: a smooth blow-up sequence of order `≥ m`
[Kol07, Definition 66] for the family `E` is one for every subdivision `F` of `E`. Stage by stage
the induced families of `F` subdivide those of `E` (`subdivides_totalTransform`) and simple normal
crossings descend (`hasSncWith_of_subdivides`); the smoothness and order conditions do not involve
the family. -/
theorem isOrderGeSeq_of_subdivides {k : Type u} [Field k] {S : BlowUpSequence X}
    (f : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {m : ℕ} {E F : DivisorFamily X}
    (hFE : F.Subdivides E) (hS : S.IsOrderGeSeq f I m E) : S.IsOrderGeSeq f I m F := by
  induction S with
  | nil X => exact ⟨hS.1, fun i => i.elim0⟩
  | cons X D rest ih =>
    rw [isOrderGeSeq_cons_iff] at hS ⊢
    exact ⟨⟨hS.1.1, hasSncWith_of_subdivides hFE hS.1.2.1, hS.1.2.2⟩,
      ih _ (subdivides_totalTransform hFE D) hS.2⟩

end M20

end Hironaka.Sequence
