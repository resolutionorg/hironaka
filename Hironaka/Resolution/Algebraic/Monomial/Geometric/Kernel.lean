/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Local
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Chart
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Snc.ComponentStalks
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.TotalTransformOnCentre
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The nerve transition: the geometric transition realises the combinatorial one

The central fact of the geometric realisation of [Kol07, 111, Step 3]: after blowing up a centre
`S` of the state, the nerve of the transported piece family `blowUpPieces` is the nerve
`MonomialState.blowUpNerve` that the combinatorial transition prescribes
(`nerve_blowUpPieces`), so that the state of the transported family is the combinatorial
transition of the state, a literal equality (`toState_blowUpPieces`), and the transported
family realises the total transform of the boundary through the extended label isomorphism
(`realizes_blowUpPieces`). Not in the sources; Kollár describes the new `r`-fold intersections
in one sentence of [Kol07, 111, Step 3.r]: they are the `E^{i₁} ∩ ⋯ ∩ E^{i_{r-1}} ∩ E^{j_ℓ}` with
`E^{i₁} ∩ ⋯ ∩ E^{i_{r-1}} ≠ ∅`.

On a smooth `k`-scheme `X`, for the blow-up `π : B_Z X → X` of a centre `Z = centerOf S` of the
state, three set-level facts are proved first:

* `faceSet_blowUpPieces_of_mem`: the strict transforms of the pieces of a face `P` of the
  centre have empty common intersection. A common point `x'` lies over `x ∈ Z_P`, on the
  exceptional divisor; by Nakayama (`exists_stalkIdeal_comap_eq_span_of_mem_support` of
  `Hironaka/Resolution/Algebraic/Monomial/Geometric/Chart.lean`) some `π^* z_c`, `c` the coordinate
  of a piece of `P`, generates the exceptional ideal at `x'`, and then the strict transform of that
  piece misses `x'` (`Hironaka/Scheme/Snc/TotalTransformSnc.lean`).
* `faceSet_blowUpPieces_ne_bot_iff`: a nonempty set of old pieces has nonempty intersection
  after the blow-up iff it had one before and contains no face of the centre. The existence
  half uses the origin of a chart (`exists_π_eq_mem_faceSet_blowUpPieces`).
* `faceSet_blowUpPieces_insert_newComp_ne_bot_iff`: the new piece `F_P = π⁻¹(Z_P)` meets the
  strict transforms of the old pieces `T₁` iff `T₁ ∪ P` is a face and `P ⊄ T₁`.

A face of the new family contains at most one new piece, two new pieces `π⁻¹(Z_P)`,
`π⁻¹(Z_Q)` being disjoint, and the last two facts identify the faces without and with a new
piece. The module also records piece death (`blowUpPieces_piece_eq_bot_iff`: an old piece
disappears exactly when its singleton is a face of the centre, the trivial blow-up of
[Kol07, Warning 20]) and the bridge `strictTransformCloseds_eq_support` between the closed-set
and the ideal-sheaf strict transforms. The results are used along the whole run in
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Realize.lean`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal
  Scheme.IdealSheafData Scheme IdealSheafData

namespace Hironaka.Monomial.PieceFamily

open AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
  (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}

/-! ### The set/ideal bridge -/

omit [Smooth f] in
include f in
/-- The strict transform of a closed set (the closure of `π⁻¹(C ∖ Z)`) is the support of the
strict transform of its vanishing ideal (`coe_support_strictTransform` of
`Hironaka/Resolution/Algebraic/Snc/DictionaryBoundary.lean`, on the locally Noetherian `X`). -/
theorem strictTransformCloseds_eq_support [LocallyOfFiniteType f] (D : X.IdealSheafData)
    (C : Closeds X) : strictTransformCloseds D C =
      ((vanishingIdeal C).strictTransformAlong (IdealSheafData.blowUpπ D)
          (D.comap (IdealSheafData.blowUpπ D))).support := by
  have : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  apply Closeds.ext
  have h := Hironaka.Sequence.coe_support_strictTransform D (vanishingIdeal C)
  rw [Hironaka.Sequence.support_vanishingIdeal_eq] at h
  change closure ((IdealSheafData.blowUpπ D) ⁻¹' ((C : Set X) \ (D.support : Set X))) =
    (((vanishingIdeal C).strictTransform D).support : Set (IdealSheafData.blowUp D))
  rw [h, Set.preimage_sdiff]

/-- The family of the pieces' vanishing ideals, indexed by the live components. -/
noncomputable def pieceIdeal (c : Fin Φ.nextComp) : X.IdealSheafData := vanishingIdeal (Φ.piece c)

theorem support_pieceIdeal (c : Fin Φ.nextComp) : (Φ.pieceIdeal c).support = Φ.piece c :=
  Hironaka.Sequence.support_vanishingIdeal_eq _

variable {n m : ℕ} {hV : Φ.IsValid n m}

/-- Kollár's snc data (the hypothesis of `Hironaka/Scheme/Snc/TotalTransformSnc.lean`) for the
family of the pieces' vanishing ideals at a point of the centre of a centre of the state: the pieces
through the point have distinct labels, hence distinct members and distinct coordinates. -/
theorem sncData_pieceIdeal (hE : E.IsSnc) (hΦ : Φ.Realizes E e) {S : Finset (Finset ℕ)}
    (hS : (Φ.toState n m hV).IsCenter S) :
    ∀ x ∈ (Φ.centerOf S).support, ∃ (nx : ℕ) (z : Fin nx → X.presheaf.stalk x),
      (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (nx : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      (∃ c : {i : Fin Φ.nextComp // x ∈ (Φ.pieceIdeal i).support} → Fin nx,
        Function.Injective c ∧ ∀ i, (Φ.pieceIdeal i.1).stalkIdeal x = span {z (c i)}) ∧
      ∃ s : Finset (Fin nx), (Φ.centerOf S).stalkIdeal x = span (z '' ↑s) := by
  intro x hx
  obtain ⟨nx, z, hz⟩ := hE.2 x
  obtain ⟨hrsp, cE, hcinj, hcE⟩ := id hz
  have hpiece : ∀ i : {i : Fin Φ.nextComp // x ∈ (Φ.pieceIdeal i).support}, x ∈ Φ.piece i.1 :=
    fun i => by
      have := i.2
      rwa [Φ.support_pieceIdeal] at this
  have hmemE : ∀ i : {i : Fin Φ.nextComp // x ∈ (Φ.pieceIdeal i).support},
      x ∈ (E.component (Φ.memberOf e i.1 i.1.2)).support :=
    fun i => Φ.mem_support_component_of_mem_piece hΦ i.1.2 (hpiece i)
  refine ⟨nx, z, hrsp, ⟨fun i => cE ⟨Φ.memberOf e i.1 i.1.2, hmemE i⟩, ?_, ?_⟩,
    Φ.exists_stalkIdeal_centerOf_eq_span hE hΦ hS hx hz⟩
  · intro i j hij
    have hmem := hcinj hij
    have hlab : Φ.label i.1 = Φ.label j.1 := by
      have := congrArg (fun a : {i : E.ι // x ∈ (E.component i).support} => ((e a.1 : Fin _) : ℕ))
        hmem
      simpa [Φ.coe_apply_memberOf] using this
    by_contra hne
    exact Φ.not_mem_piece_of_label_eq hΦ i.1.2 j.1.2 (fun h => hne (Subtype.ext (Fin.ext h)))
      hlab (hpiece i) (hpiece j)
  · intro i
    have h1 : (E.component (Φ.memberOf e i.1 i.1.2)).stalkIdeal x =
        span {z (cE ⟨Φ.memberOf e i.1 i.1.2, hmemE i⟩)} := hcE ⟨Φ.memberOf e i.1 i.1.2, hmemE i⟩
    exact (Φ.stalkIdeal_vanishingIdeal_piece hE hΦ i.1.2 (hpiece i)).trans h1

/-! ### The strict transforms of a face of the centre have empty intersection -/

include f in
/-- The strict transforms of the pieces of a face of the centre have empty common intersection:
a common point lies over a point of `Z_P`, on the exceptional divisor; some coordinate `z_c` of
a piece of `P` generates the exceptional ideal there (Nakayama), and the strict transform of
that piece misses the point. -/
theorem faceSet_blowUpPieces_of_mem [PerfectField k] (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {P : Finset ℕ} (hP : P ∈ S) :
    (Φ.blowUpPieces S m).faceSet P = ⊥ := by
  by_contra hne
  obtain ⟨x', hx'⟩ := Closeds.coe_nonempty.mpr hne
  have hPn : ∀ c ∈ P, c < Φ.nextComp := fun c hc => Φ.lt_nextComp_of_mem_nerve (hS.1 hP) hc
  -- `x'` lies on the strict transform of every piece of `P`
  have hst : ∀ c ∈ P, x' ∈ ((vanishingIdeal (Φ.piece c)).strictTransformAlong
      (IdealSheafData.blowUpπ (Φ.centerOf S)) ((Φ.centerOf S).comap
      (IdealSheafData.blowUpπ (Φ.centerOf S)))).support := by
    intro c hc
    have hmem := (Φ.blowUpPieces S m).mem_faceSet.mp hx' c hc
    rwa [Φ.blowUpPieces_piece_of_lt S (hPn c hc), strictTransformCloseds_eq_support f] at hmem
  -- so `π x'` lies on `Z_P`, on the center, and `x'` on the exceptional divisor
  have hxP : IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ Φ.faceSet P :=
      Φ.mem_faceSet.mpr fun c hc => by
    have := π_mem_support_of_mem_support_strictTransformAlong (Φ.centerOf S) _ x' (hst c hc)
    rwa [Hironaka.Sequence.support_vanishingIdeal_eq] at this
  have hxZ : IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ (Φ.centerOf S).support :=
    Φ.faceSet_le_support_centerOf hP hxP
  have hx'F : x' ∈ ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).support :=
    (mem_support_comap_iff' (Φ.centerOf S) _ x').mpr hxZ
  -- Kollár's coordinates at `π x'`: `Z_x = (z_j : j ∈ s)`, each `z_j` the coordinate of a piece
  -- of `P`
  obtain ⟨nx, z, hz⟩ := hE.2 (IdealSheafData.blowUpπ (Φ.centerOf S) x')
  obtain ⟨s, hs, -, hsP⟩ := Φ.exists_stalkIdeal_faceIdeal_eq_span hE hΦ hPn hxP hz
  have hZs : (Φ.centerOf S).stalkIdeal (IdealSheafData.blowUpπ (Φ.centerOf S) x') = span
      (z '' ↑s) :=
    (Φ.stalkIdeal_centerOf_eq_faceIdeal hS hP hxP).trans hs
  -- Nakayama: some `π^* z_j`, `j ∈ s`, generates the exceptional ideal at `x'`
  obtain ⟨j, hj, hF⟩ := exists_stalkIdeal_comap_eq_span_of_mem_support f Φ.pieceIdeal (Φ.centerOf S)
    (Φ.sncData_pieceIdeal hE hΦ hS) x' hx'F hZs fun j hj => by
      obtain ⟨c, hc, hcj⟩ := hsP j hj
      exact ⟨⟨c, hPn c hc⟩, hcj⟩
  obtain ⟨c, hc, hcj⟩ := hsP j hj
  -- and the strict transform of that piece misses `x'`
  exact notMem_support_strictTransformAlong_of_stalkIdeal_eq (Φ.centerOf S)
    (vanishingIdeal (Φ.piece c)) x'
    hcj hF (hst c hc)

/-! ### Points over the pieces: the image of a point of a strict transform -/

omit [Smooth f] in
include f in
/-- A point of the strict transform of a piece lies over a point of the piece. -/
theorem π_mem_piece_of_mem_blowUpPieces_piece [LocallyOfFiniteType f] {S : Finset (Finset ℕ)}
    {c : ℕ} (hc : c < Φ.nextComp) {x' : IdealSheafData.blowUp (Φ.centerOf S)} (hx' : x' ∈
        (Φ.blowUpPieces S m).piece c) :
    IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ Φ.piece c := by
  rw [Φ.blowUpPieces_piece_of_lt S hc, strictTransformCloseds_eq_support f] at hx'
  have := π_mem_support_of_mem_support_strictTransformAlong (Φ.centerOf S) _ x' hx'
  rwa [Hironaka.Sequence.support_vanishingIdeal_eq] at this

omit [Smooth f] in
include f in
/-- A point of the intersection of the strict transforms of old pieces lies over a point of their
intersection. -/
theorem π_mem_faceSet_of_mem_faceSet_blowUpPieces [LocallyOfFiniteType f] {S : Finset (Finset ℕ)}
    {T : Finset ℕ} (hT : ∀ c ∈ T, c < Φ.nextComp) {x' : IdealSheafData.blowUp (Φ.centerOf S)}
    (hx' : x' ∈ (Φ.blowUpPieces S m).faceSet T) : IdealSheafData.blowUpπ
        (Φ.centerOf S) x' ∈ Φ.faceSet T :=
  Φ.mem_faceSet.mpr fun c hc =>
    Φ.π_mem_piece_of_mem_blowUpPieces_piece f (hT c hc)
      ((Φ.blowUpPieces S m).mem_faceSet.mp hx' c hc)

/-! ### Two pieces through a point with the same stalk ideal coincide -/

include f in
/-- Two pieces through `x` whose vanishing ideals have the same stalk at `x` coincide: pieces of one
label through `x` coincide (`Realizes.disjoint`), and two members through `x` have distinct
coordinates, hence distinct stalk ideals (`IsSncAt`, in the regular local ring `𝒪_{X,x}`). -/
theorem eq_of_stalkIdeal_vanishingIdeal_piece_eq (hE : E.IsSnc) (hΦ : Φ.Realizes E e) {c c' : ℕ}
    (hc : c < Φ.nextComp) (hc' : c' < Φ.nextComp) {x : X} (hx : x ∈ Φ.piece c)
    (hx' : x ∈ Φ.piece c')
    (h : (vanishingIdeal (Φ.piece c)).stalkIdeal x = (vanishingIdeal (Φ.piece c')).stalkIdeal x) :
    c = c' := by
  by_contra hne
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f x
  obtain ⟨nx, z, hz⟩ := hE.2 x
  obtain ⟨hrsp, cE, hcinj, hcE⟩ := id hz
  have hm : x ∈ (E.component (Φ.memberOf e c hc)).support :=
    Φ.mem_support_component_of_mem_piece hΦ hc hx
  have hm' : x ∈ (E.component (Φ.memberOf e c' hc')).support :=
    Φ.mem_support_component_of_mem_piece hΦ hc' hx'
  have h1 : (E.component (Φ.memberOf e c hc)).stalkIdeal x =
      span {z (cE ⟨Φ.memberOf e c hc, hm⟩)} := hcE ⟨Φ.memberOf e c hc, hm⟩
  have h2 : (E.component (Φ.memberOf e c' hc')).stalkIdeal x =
      span {z (cE ⟨Φ.memberOf e c' hc', hm'⟩)} := hcE ⟨Φ.memberOf e c' hc', hm'⟩
  rw [Φ.stalkIdeal_vanishingIdeal_piece hE hΦ hc hx,
    Φ.stalkIdeal_vanishingIdeal_piece hE hΦ hc' hx', h1, h2] at h
  -- the two coordinates coincide, so the members and then the labels coincide
  have hcoord : cE ⟨Φ.memberOf e c hc, hm⟩ = cE ⟨Φ.memberOf e c' hc', hm'⟩ := by
    by_contra hne'
    exact notMem_span_singleton_of_ne hrsp.1 hrsp.2 hne' (h ▸ Ideal.mem_span_singleton_self _)
  have hmem := hcinj hcoord
  have hlab : Φ.label c = Φ.label c' := by
    have := congrArg (fun a : {i : E.ι // x ∈ (E.component i).support} => ((e a.1 : Fin _) : ℕ))
      hmem
    simpa [Φ.coe_apply_memberOf] using this
  exact Φ.not_mem_piece_of_label_eq hΦ hc hc' hne hlab hx hx'

/-! ### A generator of the exceptional ideal is a regular parameter -/

include f in
/-- At a point of the exceptional divisor over the centre of a centre of the state, a generator
of the exceptional ideal does not lie in `𝔪²`: the exceptional ideal is `(z'_j)` for a regular
system of parameters `z'` (`Hironaka/Scheme/Snc/TotalTransformData.lean`). -/
theorem notMem_sq_of_stalkIdeal_comap_eq_span [PerfectField k] (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {x' : IdealSheafData.blowUp
        (Φ.centerOf S)}
    (hx' : x' ∈ ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).support)
    {g : (IdealSheafData.blowUp (Φ.centerOf S)).presheaf.stalk x'}
    (hg : ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).stalkIdeal x' = span {g}) :
    g ∉ maximalIdeal ((IdealSheafData.blowUp (Φ.centerOf S)).presheaf.stalk x') ^ 2 := by
  obtain ⟨hdata, -⟩ := exists_totalTransformData_of_mem_support f Φ.pieceIdeal (Φ.centerOf S)
    (Φ.sncData_pieceIdeal hE hΦ hS) x' hx'
  obtain ⟨hreg, m', z', ⟨hspan', hdim'⟩, j, -, hF, -, -⟩ := hdata
  have := hreg
  intro hg2
  -- `z'_j ∈ (g)` and `g ∈ 𝔪²`, so `z'_j ∈ 𝔪²`
  have hzj : z' j ∈ span {g} := hg ▸ hF ▸ Ideal.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hzj
  exact notMem_sq_of_span_eq z' hspan'.symm hdim' j
    (hv ▸ Ideal.mul_mem_left _ v hg2)

/-! ### The witness over a point of the center: the origin of a chart -/

include f in
/-- The existence half of the nerve transition at a point `x` of `Z_Q` (`Q` a face of the
centre): for a set `T` of old pieces through `x` missing some piece `kc` of `Q`, the origin of the
chart of `kc`'s coordinate lies over `x` on the strict transform of every piece of `T`.
Transversal pieces (coordinate not among those of `Z`) contain the whole fibre, and for a piece
`c ∈ Q ∖ {kc}` the strict transform has stalk `(u)` with `π^* z_c = u · π^* z_{kc}`, where `u`
is not a unit since `π^* z_c ∈ 𝔪²` at the origin while `π^* z_{kc}`, a generator of the
exceptional ideal, is not. -/
theorem exists_π_eq_mem_faceSet_blowUpPieces [PerfectField k] (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {Q : Finset ℕ} (hQ : Q ∈ S)
    {x : X} (hxQ : x ∈ Φ.faceSet Q) {kc : ℕ} (hkc : kc ∈ Q) {T : Finset ℕ}
    (hT : ∀ c ∈ T, c < Φ.nextComp) (hxT : x ∈ Φ.faceSet T) (hkT : kc ∉ T) :
    ∃ x' : IdealSheafData.blowUp (Φ.centerOf S), IdealSheafData.blowUpπ (Φ.centerOf S) x' = x ∧
      x' ∈ (Φ.blowUpPieces S m).faceSet T := by
  have hQn : ∀ c ∈ Q, c < Φ.nextComp := fun c hc => Φ.lt_nextComp_of_mem_nerve (hS.1 hQ) hc
  have hxZ : x ∈ (Φ.centerOf S).support := Φ.faceSet_le_support_centerOf hQ hxQ
  -- Kollár's coordinates at `x`: `Z_x = (z_j : j ∈ s)`, `s` the coordinates of the pieces of `Q`
  obtain ⟨nx, z, hz⟩ := hE.2 x
  obtain ⟨s, hs, hsQ, hsQ'⟩ := Φ.exists_stalkIdeal_faceIdeal_eq_span hE hΦ hQn hxQ hz
  have hZs : (Φ.centerOf S).stalkIdeal x = span (z '' ↑s) :=
    (Φ.stalkIdeal_centerOf_eq_faceIdeal hS hQ hxQ).trans hs
  obtain ⟨jk, hjk, hjk_eq⟩ := hsQ kc hkc
  -- the origin of the chart of `z_{jk}`
  obtain ⟨x', rfl, hF, hsq⟩ :=
    exists_chartOrigin_point_of_mem f (Φ.centerOf S) x z hz.1.2 hz.1.1.symm hZs hjk
  have hF' : ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).stalkIdeal x' =
      span {(IdealSheafData.blowUpπ (Φ.centerOf S)).stalkMap x' (z jk)} := hF
  have hx'F : x' ∈ ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).support :=
    (mem_support_comap_iff' (Φ.centerOf S) _ x').mpr hxZ
  have hZp := Φ.sncData_pieceIdeal hE hΦ hS
  refine ⟨x', rfl, (Φ.blowUpPieces S m).mem_faceSet.mpr fun c hc => ?_⟩
  have hcn := hT c hc
  have hxc : IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ Φ.piece c := Φ.mem_faceSet.mp hxT c hc
  rw [Φ.blowUpPieces_piece_of_lt S hcn, strictTransformCloseds_eq_support f]
  obtain ⟨jc, hjc⟩ := Φ.exists_stalkIdeal_vanishingIdeal_piece_eq_span hE hΦ hcn hxc hz
  by_cases hjcs : jc ∈ s
  · -- `c` is a piece of `Q` other than `kc`: `π^* z_c ∈ 𝔪²`
    obtain ⟨c', hc'Q, hc'⟩ := hsQ' jc hjcs
    have hcc' : c = c' := Φ.eq_of_stalkIdeal_vanishingIdeal_piece_eq f hE hΦ hcn (hQn c' hc'Q) hxc
      (Φ.mem_faceSet.mp hxQ c' hc'Q) (hjc.trans hc'.symm)
    subst hcc'
    have hjcjk : jc ≠ jk := by
      rintro rfl
      exact hkT (Φ.eq_of_stalkIdeal_vanishingIdeal_piece_eq f hE hΦ (hQn kc hkc) hcn
        (Φ.mem_faceSet.mp hxQ kc hkc) hxc (hjk_eq.trans hjc.symm) ▸ hc)
    have hsq' : (IdealSheafData.blowUpπ (Φ.centerOf S)).stalkMap x' (z jc) ∈
        maximalIdeal ((IdealSheafData.blowUp (Φ.centerOf S)).presheaf.stalk x') ^ 2 :=
      hsq jc hjcs hjcjk
    obtain ⟨u, hu, hstalk⟩ := exists_stalkIdeal_strictTransformAlong_eq_span_of_mem f
      Φ.pieceIdeal (Φ.centerOf S) hZp ⟨c, hcn⟩ x' hx'F hz.1 hZs hjc hjcs hF'
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal]
    change ((Φ.pieceIdeal ⟨c, hcn⟩).strictTransformAlong (IdealSheafData.blowUpπ (Φ.centerOf S))
        ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S)))).stalkIdeal x' ≤ _
    rw [hstalk, Ideal.span_singleton_le_iff_mem]
    -- `u` is not a unit: otherwise the exceptional generator would lie in `𝔪²`
    by_contra hu'
    have hunit : IsUnit u := by
      by_contra h
      exact hu' ((IsLocalRing.mem_maximalIdeal u).mpr h)
    apply Φ.notMem_sq_of_stalkIdeal_comap_eq_span f hE hΦ hS hx'F hF'
    have : (IdealSheafData.blowUpπ (Φ.centerOf S)).stalkMap x' (z jk) =
        ↑hunit.unit⁻¹ * (IdealSheafData.blowUpπ (Φ.centerOf S)).stalkMap x' (z jc) := by
      rw [hu, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hsq'
  · -- `c` is transversal to the centre: its strict transform contains the fibre
    have := (mem_support_strictTransformAlong_iff_of_notMem f Φ.pieceIdeal (Φ.centerOf S) hZp
      ⟨c, hcn⟩ x' hx'F hz.1 hZs hjc hjcs).mpr (by rw [Φ.support_pieceIdeal]; exact hxc)
    exact this

/-! ### The faces without and with a new piece -/

include f in
/-- A nonempty set `T` of old pieces has nonempty intersection after the blow-up iff it had one
before and contains no face of the centre. -/
theorem faceSet_blowUpPieces_ne_bot_iff [PerfectField k] (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {T : Finset ℕ}
    (hT : ∀ c ∈ T, c < Φ.nextComp) (_hne : T.Nonempty) :
    (Φ.blowUpPieces S m).faceSet T ≠ ⊥ ↔ Φ.faceSet T ≠ ⊥ ∧ ∀ P ∈ S, ¬ P ⊆ T := by
  constructor
  · intro h
    obtain ⟨x', hx'⟩ := Closeds.coe_nonempty.mpr h
    refine ⟨Closeds.coe_nonempty.mp ⟨_, Φ.π_mem_faceSet_of_mem_faceSet_blowUpPieces f hT hx'⟩,
      fun P hP hPT => ?_⟩
    have hmem := (Φ.blowUpPieces S m).faceSet_anti hPT hx'
    rw [Φ.faceSet_blowUpPieces_of_mem f hE hΦ hS hP, ← SetLike.mem_coe, Closeds.coe_bot] at hmem
    exact hmem
  · rintro ⟨hTb, hnot⟩
    obtain ⟨x, hx⟩ := Closeds.coe_nonempty.mpr hTb
    by_cases hxZ : x ∈ (Φ.centerOf S).support
    · obtain ⟨Q, hQ, hxQ⟩ := (Φ.mem_support_centerOf_iff S x).mp hxZ
      obtain ⟨kc, hkc, hkT⟩ := Finset.not_subset.mp (hnot Q hQ)
      obtain ⟨x', -, hx'⟩ :=
        Φ.exists_π_eq_mem_faceSet_blowUpPieces f hE hΦ hS hQ hxQ hkc hT hx hkT
      exact Closeds.coe_nonempty.mp ⟨x', hx'⟩
    · obtain ⟨x', rfl⟩ := exists_π_eq_of_notMem_support (Φ.centerOf S) hxZ
      have hx'F : x' ∉ ((Φ.centerOf S).comap (IdealSheafData.blowUpπ (Φ.centerOf S))).support :=
          fun h =>
        hxZ ((mem_support_comap_iff' _ _ x').mp h)
      refine Closeds.coe_nonempty.mp ⟨x', (Φ.blowUpPieces S m).mem_faceSet.mpr fun c hc => ?_⟩
      rw [Φ.blowUpPieces_piece_of_lt S (hT c hc), strictTransformCloseds_eq_support f]
      refine (mem_support_strictTransformAlong_iff_of_notMem_support _ _ hx'F).mpr ?_
      rw [Hironaka.Sequence.support_vanishingIdeal_eq]
      exact Φ.mem_faceSet.mp hx c hc

include f in
/-- The new piece `F_P = π⁻¹(Z_P)` meets the strict transforms of the old pieces `T₁` iff
`T₁ ∪ P` is a face and `P ⊄ T₁`. -/
theorem faceSet_blowUpPieces_insert_newComp_ne_bot_iff [PerfectField k] (hE : E.IsSnc)
    (hΦ : Φ.Realizes E e) {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S)
    {P : Finset ℕ} (hP : P ∈ S) {T₁ : Finset ℕ} (hT₁ : ∀ c ∈ T₁, c < Φ.nextComp) :
    (Φ.blowUpPieces S m).faceSet (insert (Φ.newComp S P) T₁) ≠ ⊥ ↔
      Φ.faceSet (T₁ ∪ P) ≠ ⊥ ∧ ¬ P ⊆ T₁ := by
  have hPn : ∀ c ∈ P, c < Φ.nextComp := fun c hc => Φ.lt_nextComp_of_mem_nerve (hS.1 hP) hc
  constructor
  · intro h
    obtain ⟨x', hx'⟩ := Closeds.coe_nonempty.mpr h
    have hnew := (Φ.blowUpPieces S m).mem_faceSet.mp hx' _ (Finset.mem_insert_self _ _)
    rw [Φ.blowUpPieces_piece_newComp S hP] at hnew
    have hxP : IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ Φ.faceSet P := hnew
    have hT₁' : x' ∈ (Φ.blowUpPieces S m).faceSet T₁ :=
      (Φ.blowUpPieces S m).faceSet_anti (Finset.subset_insert _ _) hx'
    refine ⟨Closeds.coe_nonempty.mp ⟨IdealSheafData.blowUpπ (Φ.centerOf S) x',
        Φ.mem_faceSet.mpr fun c hc => ?_⟩,
      fun hPT => ?_⟩
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact Φ.mem_faceSet.mp (Φ.π_mem_faceSet_of_mem_faceSet_blowUpPieces f hT₁ hT₁') c hc
      · exact Φ.mem_faceSet.mp hxP c hc
    · have hmem := (Φ.blowUpPieces S m).faceSet_anti hPT hT₁'
      rw [Φ.faceSet_blowUpPieces_of_mem f hE hΦ hS hP, ← SetLike.mem_coe, Closeds.coe_bot] at hmem
      exact hmem
  · rintro ⟨hTb, hnot⟩
    obtain ⟨x, hx⟩ := Closeds.coe_nonempty.mpr hTb
    obtain ⟨kc, hkc, hkT⟩ := Finset.not_subset.mp hnot
    have hxP : x ∈ Φ.faceSet P := Φ.faceSet_anti Finset.subset_union_right hx
    have hxT : x ∈ Φ.faceSet T₁ := Φ.faceSet_anti Finset.subset_union_left hx
    obtain ⟨x', hπ, hx'⟩ :=
      Φ.exists_π_eq_mem_faceSet_blowUpPieces f hE hΦ hS hP hxP hkc hT₁ hxT hkT
    refine Closeds.coe_nonempty.mp ⟨x', (Φ.blowUpPieces S m).mem_faceSet.mpr fun c hc => ?_⟩
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rw [Φ.blowUpPieces_piece_newComp S hP]
      change IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ Φ.faceSet P
      rw [hπ]
      exact hxP
    · exact (Φ.blowUpPieces S m).mem_faceSet.mp hx' c hc

/-! ### The nerve transition -/

/-- Membership in a new piece: the point lies over `Z_P` for the face `P` allocated to the index. -/
theorem mem_blowUpPieces_piece_of_le {S : Finset (Finset ℕ)} {c : ℕ} (hc : Φ.nextComp ≤ c)
    {x' : IdealSheafData.blowUp (Φ.centerOf S)} :
    x' ∈ (Φ.blowUpPieces S m).piece c ↔
      ∃ P ∈ S, Φ.newComp S P = c ∧ IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ Φ.faceSet P := by
  have hlt : ¬ c < Φ.nextComp := not_lt.mpr hc
  change x' ∈ (if c < Φ.nextComp then strictTransformCloseds (Φ.centerOf S) (Φ.piece c) else
    (S.filter fun P => Φ.newComp S P = c).sup fun P =>
      (Φ.faceSet P).preimage (Φ.centerOf S).blowUpπ.continuous) ↔ _
  rw [ite_eq_right hlt, mem_finset_sup_iff]
  constructor
  · rintro ⟨P, hP, hx⟩
    exact ⟨P, (Finset.mem_filter.mp hP).1, (Finset.mem_filter.mp hP).2, hx⟩
  · rintro ⟨P, hP, hPc, hx⟩
    exact ⟨P, Finset.mem_filter.mpr ⟨hP, hPc⟩, hx⟩

include f in
/-- *The nerve transition*: the nerve after the blow-up of a centre of the state is
`MonomialState.blowUpNerve` of the nerve. A face of the new family contains at most one new
piece (two new pieces `π⁻¹(Z_P)`, `π⁻¹(Z_Q)` are disjoint), and
`faceSet_blowUpPieces_ne_bot_iff` and `faceSet_blowUpPieces_insert_newComp_ne_bot_iff` identify
the faces without and with a new piece. -/
theorem nerve_blowUpPieces [PerfectField k] (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) :
    (Φ.blowUpPieces S m).nerve = MonomialState.blowUpNerve Φ.nerve S (Φ.newComp S) := by
  classical
  ext T
  rw [(Φ.blowUpPieces S m).mem_nerve, MonomialState.mem_blowUpNerve, Φ.blowUpPieces_nextComp]
  constructor
  · rintro ⟨hTr, hTne, hTb⟩
    obtain ⟨x', hx'⟩ := Closeds.coe_nonempty.mpr hTb
    set T₀ := T.filter fun c => c < Φ.nextComp with hT₀
    set T₁ := T.filter fun c => ¬ c < Φ.nextComp with hT₁
    have hTsplit : T₀ ∪ T₁ = T := by
      ext c
      simp only [hT₀, hT₁, Finset.mem_union, Finset.mem_filter]
      tauto
    have hT₀n : ∀ c ∈ T₀, c < Φ.nextComp := fun c hc => (Finset.mem_filter.mp hc).2
    -- every new index of `T` is the index allocated to the unique face of `S` through `π x'`
    have hnew : ∀ c ∈ T₁, ∃ P ∈ S, Φ.newComp S P = c ∧
        IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ Φ.faceSet P := fun c hc =>
      (Φ.mem_blowUpPieces_piece_of_le (not_lt.mp (Finset.mem_filter.mp hc).2)).mp
        ((Φ.blowUpPieces S m).mem_faceSet.mp hx' c (Finset.mem_filter.mp hc).1)
    have hT₀' : x' ∈ (Φ.blowUpPieces S m).faceSet T₀ :=
      (Φ.blowUpPieces S m).faceSet_anti (Finset.filter_subset _ _) hx'
    rcases T₁.eq_empty_or_nonempty with hT₁e | ⟨c₀, hc₀⟩
    · -- no new piece: an old face containing no face of the centre
      left
      have hTT₀ : T = T₀ := by rw [← hTsplit, hT₁e, Finset.union_empty]
      rw [hTT₀] at hTb hTne ⊢
      obtain ⟨hb, hnot⟩ := (Φ.faceSet_blowUpPieces_ne_bot_iff f hE hΦ hS hT₀n hTne).mp hTb
      exact ⟨Φ.mem_nerve.mpr ⟨fun c hc => Finset.mem_range.mpr (hT₀n c hc), hTne, hb⟩, hnot⟩
    · -- exactly one new piece, the one of the face `P₀` through `π x'`
      right
      obtain ⟨P₀, hP₀, hc₀P, hxP₀⟩ := hnew c₀ hc₀
      have hT₁s : T₁ = {c₀} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hc₀, fun c hc => ?_⟩
        obtain ⟨P, hP, hcP, hxP⟩ := hnew c hc
        rw [← hcP, ← hc₀P, Φ.eq_of_mem_faceSet_of_isCenter hS hP hP₀ hxP hxP₀]
      have hTeq : T = insert (Φ.newComp S P₀) T₀ := by
        rw [← hTsplit, hT₁s, hc₀P, Finset.union_comm, ← Finset.insert_eq]
      rw [hTeq] at hTb
      obtain ⟨hb, hnot⟩ :=
        (Φ.faceSet_blowUpPieces_insert_newComp_ne_bot_iff f hE hΦ hS hP₀ hT₀n).mp hTb
      have hP₀n : ∀ c ∈ P₀, c < Φ.nextComp := fun c hc =>
        Φ.lt_nextComp_of_mem_nerve (hS.1 hP₀) hc
      have hTP : T₀ ∪ P₀ ∈ Φ.nerve := Φ.mem_nerve.mpr ⟨fun c hc => Finset.mem_range.mpr
        ((Finset.mem_union.mp hc).elim (hT₀n c) (hP₀n c)),
        ((Φ.mem_nerve.mp (hS.1 hP₀)).2.1).mono Finset.subset_union_right, hb⟩
      refine ⟨P₀, hP₀, T₀, ?_, hTP, fun Q hQ hQT => ?_, hTeq⟩
      · rcases T₀.eq_empty_or_nonempty with h | h
        · exact Or.inl h
        · exact Or.inr ((Φ.toState n m hV).mem_nerve_of_subset hTP Finset.subset_union_left h)
      · exact hnot (MonomialState.eq_of_isCenter_of_subset (st := Φ.toState n m hV) (S := S) hS hQ
          hP₀ hTP (hQT.trans Finset.subset_union_left) Finset.subset_union_right ▸ hQT)
  · rintro (⟨hTN, hnot⟩ | ⟨P, hP, T₁, -, hTP, hnot, rfl⟩)
    · -- an old face without a face of the centre survives
      obtain ⟨hTr, hTne, hTb⟩ := Φ.mem_nerve.mp hTN
      have hTn : ∀ c ∈ T, c < Φ.nextComp := fun c hc => Finset.mem_range.mp (hTr hc)
      refine ⟨fun c hc => Finset.mem_range.mpr ((hTn c hc).trans_le (Nat.le_add_right _ _)), hTne,
        (Φ.faceSet_blowUpPieces_ne_bot_iff f hE hΦ hS hTn hTne).mpr ⟨hTb, hnot⟩⟩
    · -- the new piece of `P` with old pieces `T₁`
      obtain ⟨hTr, -, hTb⟩ := Φ.mem_nerve.mp hTP
      have hT₁n : ∀ c ∈ T₁, c < Φ.nextComp := fun c hc =>
        Finset.mem_range.mp (hTr (Finset.mem_union_left _ hc))
      refine ⟨fun c hc => Finset.mem_range.mpr ?_, Finset.insert_nonempty _ _,
        (Φ.faceSet_blowUpPieces_insert_newComp_ne_bot_iff f hE hΦ hS hP hT₁n).mpr
          ⟨hTb, hnot P hP⟩⟩
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact (Φ.toState n m hV).newComp_lt hP
      · exact (hT₁n c hc).trans_le (Nat.le_add_right _ _)

/-! ### The transported family is valid and its state is the transition -/

include f in
/-- The transported family's data are `Valid`: they are the data of the state `blowUp S`, whose
invariants are proved in `Hironaka/Resolution/Algebraic/Monomial/State.lean`. -/
theorem valid_blowUpPieces [PerfectField k] (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) :
    (Φ.blowUpPieces S m).IsValid n m := by
  have h := ((Φ.toState n m hV).blowUp S).valid_self
  rw [MonomialState.blowUp_nerve] at h
  rw [IsValid, Φ.nerve_blowUpPieces f hE hΦ hS]
  exact h

include f in
/-- *The transported piece family's state is the combinatorial transition of the state*, a
literal equality of `MonomialState`s. -/
theorem toState_blowUpPieces [PerfectField k] (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hV' : (Φ.blowUpPieces S m).IsValid n m)
    (hS : (Φ.toState n m hV).IsCenter S) :
    (Φ.blowUpPieces S m).toState n m hV' = (Φ.toState n m hV).blowUp S :=
  Φ.toState_blowUpPieces_of_nerve_eq S (Φ.nerve_blowUpPieces f hE hΦ hS)

/-! ### Piece death -/

/-- A generic point of a piece is a generic point of the support of its member: a point of the
member generizing it lies on a piece of the same label, which is the piece itself (two pieces of one
label being disjoint). -/
theorem mem_genericPoints_support_of_mem_genericPoints_piece (hΦ : Φ.Realizes E e) {c : ℕ}
    (hc : c < Φ.nextComp) {η : X} (hη : η ∈ (Φ.piece c).genericPoints) :
    η ∈ (E.component (Φ.memberOf e c hc)).support.genericPoints := by
  refine ⟨Φ.mem_support_component_of_mem_piece hΦ hc hη.1, fun η' hη' hη'η => hη.2 ?_ hη'η⟩
  rw [hΦ.support_eq, mem_finset_sup_iff] at hη'
  obtain ⟨c', hc', hη'c'⟩ := hη'
  obtain ⟨hc'r, hlab⟩ := Finset.mem_filter.mp hc'
  rw [Φ.coe_apply_memberOf] at hlab
  by_cases hcc : c' = c
  · exact hcc ▸ hη'c'
  · exfalso
    have hηc' : η ∈ Φ.piece c' := (Φ.piece c').isClosed.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hη'c') (specializes_iff_mem_closure.mp hη'η)
    exact Φ.not_mem_piece_of_label_eq hΦ (Finset.mem_range.mp hc'r) hc hcc hlab hηc' hη.1

include f in
/-- Through a generic point of a piece passes no other piece: a piece of the same label is the
piece itself, and no other member passes through a generic point of a component
(`notMem_support_of_ne` of `Hironaka/Resolution/Algebraic/Snc/ComponentStalks.lean`). -/
theorem eq_of_mem_piece_of_mem_genericPoints (hE : E.IsSnc) (hΦ : Φ.Realizes E e) {c : ℕ}
    (hc : c < Φ.nextComp) {η : X} (hη : η ∈ (Φ.piece c).genericPoints) {c' : ℕ}
    (hc' : c' < Φ.nextComp) (hη' : η ∈ Φ.piece c') : c' = c := by
  have hgen := Φ.mem_genericPoints_support_of_mem_genericPoints_piece hΦ hc hη
  have hmem' := Φ.mem_support_component_of_mem_piece hΦ hc' hη'
  by_contra hne
  by_cases hlab : Φ.label c' = Φ.label c
  · exact Φ.not_mem_piece_of_label_eq hΦ hc' hc hne hlab hη' hη.1
  · have hji : Φ.memberOf e c' hc' ≠ Φ.memberOf e c hc := fun h => hlab (by
      have := congrArg (fun a : E.ι => ((e a : Fin _) : ℕ)) h
      simpa [Φ.coe_apply_memberOf] using this)
    exact Hironaka.BMO.Snc.notMem_support_of_ne f E hE hji hgen hmem'

theorem faceSet_singleton (c : ℕ) : Φ.faceSet {c} = Φ.piece c := Finset.inf_singleton

include f in
/-- Piece death (the trivial blow-up of [Kol07, Warning 20]): a nonempty piece lies in the centre
iff its singleton is a face of the centre. At a generic point of the piece only that piece
passes, so the face of the centre through it is the singleton. -/
theorem piece_le_support_centerOf_iff (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {c : ℕ} (hc : c < Φ.nextComp)
    (hne : Φ.piece c ≠ ⊥) : Φ.piece c ≤ (Φ.centerOf S).support ↔ {c} ∈ S := by
  constructor
  · intro hle
    obtain ⟨x, hx⟩ := Closeds.coe_nonempty.mpr hne
    obtain ⟨η, hη, -⟩ := Closeds.exists_mem_genericPoints_specializes _ hx
    obtain ⟨P, hP, hηP⟩ := (Φ.mem_support_centerOf_iff S η).mp (hle hη.1)
    have hPn : ∀ c' ∈ P, c' < Φ.nextComp := fun c' hc' =>
      Φ.lt_nextComp_of_mem_nerve (hS.1 hP) hc'
    have hall : ∀ c' ∈ P, c' = c := fun c' hc' =>
      Φ.eq_of_mem_piece_of_mem_genericPoints f hE hΦ hc hη (hPn c' hc')
        (Φ.mem_faceSet.mp hηP c' hc')
    have hPc : P = {c} := by
      obtain ⟨c', hc'⟩ := (Φ.mem_nerve.mp (hS.1 hP)).2.1
      exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hall c' hc' ▸ hc', hall⟩
    exact hPc ▸ hP
  · intro hcS
    rw [← Φ.faceSet_singleton]
    exact Φ.faceSet_le_support_centerOf hcS

include f in
/-- Piece death: the strict transform of an old piece is empty iff the piece was empty or its
singleton is a face of the centre. -/
theorem blowUpPieces_piece_eq_bot_iff (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {c : ℕ} (hc : c < Φ.nextComp) :
    (Φ.blowUpPieces S m).piece c = ⊥ ↔ Φ.piece c = ⊥ ∨ {c} ∈ S := by
  rw [Φ.blowUpPieces_piece_of_lt S hc]
  constructor
  · intro h
    by_cases hb : Φ.piece c = ⊥
    · exact Or.inl hb
    · right
      rw [← Φ.piece_le_support_centerOf_iff f hE hΦ hS hc hb]
      intro x hx
      by_contra hxZ
      obtain ⟨x', rfl⟩ := exists_π_eq_of_notMem_support _ hxZ
      have hmem : x' ∈ strictTransformCloseds (Φ.centerOf S) (Φ.piece c) :=
        subset_closure (show IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈
          (Φ.piece c : Set X) \ ((Φ.centerOf S).support : Set X) from ⟨hx, hxZ⟩)
      rw [h, ← SetLike.mem_coe, Closeds.coe_bot] at hmem
      exact hmem
  · intro h
    have hle : (Φ.piece c : Set X) \ ((Φ.centerOf S).support : Set X) = ∅ := by
      rcases h with hb | hcS
      · rw [hb, Closeds.coe_bot, Set.empty_sdiff]
      · refine Set.sdiff_eq_empty.mpr ?_
        rw [← Φ.faceSet_singleton]
        exact Φ.faceSet_le_support_centerOf hcS
    apply Closeds.ext
    change closure ((IdealSheafData.blowUpπ (Φ.centerOf S)) ⁻¹' ((Φ.piece c : Set X) \
      ((Φ.centerOf S).support : Set X))) = _
    rw [hle, Set.preimage_empty, closure_empty, Closeds.coe_bot]

/-! ### The transported family realizes the total transform -/

/-- The old pieces of the transported family with a given label below `nextLabel` are the old
pieces of that label. -/
theorem filter_label_blowUpPieces_of_lt {S : Finset (Finset ℕ)} {l : ℕ} (hl : l < Φ.nextLabel) :
    ((Finset.range (Φ.nextComp + S.card)).filter fun c => (Φ.blowUpPieces S m).label c = l) =
      (Finset.range Φ.nextComp).filter fun c => Φ.label c = l := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hc, hlab⟩
    by_cases hck : c < Φ.nextComp
    · rw [Φ.blowUpPieces_label_of_lt S hck] at hlab
      exact ⟨hck, hlab⟩
    · exfalso
      have : (Φ.blowUpPieces S m).label c = Φ.nextLabel := ite_eq_right hck
      omega
  · rintro ⟨hck, hlab⟩
    exact ⟨hck.trans_le (Nat.le_add_right _ _), (Φ.blowUpPieces_label_of_lt S hck).trans hlab⟩

/-- The pieces of the transported family with the new label are the new pieces. -/
theorem mem_filter_label_blowUpPieces_nextLabel {S : Finset (Finset ℕ)} {c : ℕ} :
    c ∈ ((Finset.range (Φ.nextComp + S.card)).filter fun c =>
        (Φ.blowUpPieces S m).label c = Φ.nextLabel) ↔
      Φ.nextComp ≤ c ∧ c < Φ.nextComp + S.card := by
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hc, hlab⟩
    refine ⟨?_, hc⟩
    by_contra hck
    rw [Φ.blowUpPieces_label_of_lt S (not_le.mp hck)] at hlab
    exact absurd hlab (Φ.label_lt c (not_le.mp hck)).ne
  · rintro ⟨hck, hc⟩
    exact ⟨hc, ite_eq_right (not_lt.mpr hck)⟩

omit [Smooth f] in
include f in
/-- The transported piece family realises the total transform `π^{-1}_{tot} E` of
[Kol07, Definition 65] through the extended label isomorphism: the strict transform of a member
is the union of the strict transforms of its pieces (closure commutes with finite unions), the
exceptional divisor is the union of the new pieces `π⁻¹(Z_P)`, and pieces of one label stay
disjoint. -/
theorem realizes_blowUpPieces [LocallyOfFiniteType f] (_hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) :
    (Φ.blowUpPieces S m).Realizes (E.totalTransform (Φ.centerOf S)) (extendIso e) where
  support_eq j := by
    classical
    have : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    rcases j with i | u
    · -- an old member: the strict transform is the union of the strict transforms of its pieces
      change ((E.component i).strictTransform (Φ.centerOf S)).support =
        ((Finset.range (Φ.nextComp + S.card)).filter fun c =>
          (Φ.blowUpPieces S m).label c = (e i : ℕ)).sup (Φ.blowUpPieces S m).piece
      rw [Φ.filter_label_blowUpPieces_of_lt (e i).isLt]
      apply Closeds.ext
      rw [Hironaka.Sequence.coe_support_strictTransform, hΦ.support_eq i, Closeds.coe_finset_sup,
        Finset.sup_eq_iSup, Closeds.coe_finset_sup, Finset.sup_eq_iSup]
      simp only [Set.iSup_eq_iUnion, Function.comp_apply, Set.preimage_iUnion, Set.iUnion_sdiff]
      rw [Finset.closure_biUnion]
      refine Set.iUnion₂_congr fun c hc => ?_
      rw [Φ.blowUpPieces_piece_of_lt S (Finset.mem_range.mp (Finset.mem_filter.mp hc).1)]
      change _ = closure ((IdealSheafData.blowUpπ (Φ.centerOf S)) ⁻¹' ((Φ.piece c : Set X) \
        ((Φ.centerOf S).support : Set X)))
      rw [Set.preimage_sdiff]
    · -- the exceptional divisor: the union of the new pieces `π⁻¹(Z_P)`
      change ((Φ.centerOf S).comap (Φ.centerOf S).blowUpπ).support =
        ((Finset.range (Φ.nextComp + S.card)).filter fun c =>
          (Φ.blowUpPieces S m).label c = Φ.nextLabel).sup (Φ.blowUpPieces S m).piece
      rw [support_comap]
      apply Closeds.ext
      ext x'
      rw [SetLike.mem_coe, SetLike.mem_coe, mem_finset_sup_iff]
      change IdealSheafData.blowUpπ (Φ.centerOf S) x' ∈ (Φ.centerOf S).support ↔ _
      rw [Φ.mem_support_centerOf_iff]
      constructor
      · rintro ⟨P, hP, hxP⟩
        refine ⟨Φ.newComp S P, Φ.mem_filter_label_blowUpPieces_nextLabel.mpr
          ⟨Nat.le_add_right _ _, (Φ.toState n m hV).newComp_lt hP⟩, ?_⟩
        rw [Φ.blowUpPieces_piece_newComp S hP]
        exact hxP
      · rintro ⟨c, hc, hx'⟩
        obtain ⟨hck, -⟩ := Φ.mem_filter_label_blowUpPieces_nextLabel.mp hc
        obtain ⟨P, hP, -, hxP⟩ := (Φ.mem_blowUpPieces_piece_of_le hck).mp hx'
        exact ⟨P, hP, hxP⟩
  disjoint c c' hc hc' hne hlab := by
    rw [Φ.blowUpPieces_nextComp] at hc hc'
    rw [disjoint_iff_inf_le]
    intro x' hx'
    rw [← SetLike.mem_coe, Closeds.coe_inf] at hx'
    obtain ⟨h1, h2⟩ := hx'
    exfalso
    by_cases hck : c < Φ.nextComp
    · by_cases hck' : c' < Φ.nextComp
      · -- two old pieces of one label: their images lie on two disjoint pieces
        rw [Φ.blowUpPieces_label_of_lt S hck, Φ.blowUpPieces_label_of_lt S hck'] at hlab
        exact Φ.not_mem_piece_of_label_eq hΦ hck hck' hne hlab
          (Φ.π_mem_piece_of_mem_blowUpPieces_piece f hck h1)
          (Φ.π_mem_piece_of_mem_blowUpPieces_piece f hck' h2)
      · -- an old and a new piece have different labels
        rw [Φ.blowUpPieces_label_of_lt S hck] at hlab
        have : (Φ.blowUpPieces S m).label c' = Φ.nextLabel := ite_eq_right hck'
        exact absurd (hlab.trans this) (Φ.label_lt c hck).ne
    · by_cases hck' : c' < Φ.nextComp
      · rw [Φ.blowUpPieces_label_of_lt S hck'] at hlab
        have : (Φ.blowUpPieces S m).label c = Φ.nextLabel := ite_eq_right hck
        exact absurd (this.symm.trans hlab) (Φ.label_lt c' hck').ne'
      · -- two new pieces: their faces pass through a common point, so they coincide
        obtain ⟨P, hP, hPc, hxP⟩ := (Φ.mem_blowUpPieces_piece_of_le (not_lt.mp hck)).mp h1
        obtain ⟨Q, hQ, hQc, hxQ⟩ := (Φ.mem_blowUpPieces_piece_of_le (not_lt.mp hck')).mp h2
        exact hne (hPc ▸ hQc ▸ congrArg (Φ.newComp S)
          (Φ.eq_of_mem_faceSet_of_isCenter hS hP hQ hxP hxQ))

end Hironaka.Monomial.PieceFamily
