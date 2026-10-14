/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Step3Phases
public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.BlowUpSequence.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Piece families: the geometric state of the monomial procedure

Kollár's Step 3 ([Kol07, 111, Step 3]) runs on the combinatorial state of
`Hironaka/Resolution/Algebraic/Monomial/State.lean`. Its realisation on a scheme carries a *labelled
piece family* along the run: for each component index `c < nextComp` a closed set `piece c` of the
ambient scheme (a nonempty disjoint union of irreducible components of the member `E^{label c}`, or
empty when the component is dead), its label (the index of its member through an order
isomorphism `E.ι ≃o Fin nextLabel`) and its exponent. At the input the pieces are the
irreducible components of the members (`ofDivisorFamily`); after the blow-up of a centre `S` (a
finset of faces) the old pieces become their strict transforms and each face `P ∈ S`
contributes one new piece `π⁻¹(Z_P)` under the new label, Kollár's new divisor put last
([Kol07, Definition 65]): one smooth, possibly reducible, divisor per blow-up, its irreducible
components pairwise disjoint and carrying the common exponent `a(P) − m`. A "component" of the
state is therefore an irreducible component at the input only. This is what makes the nerve
transition an equality: for `E⁰ = V(y)` and `E¹ = V(y − x² + 1)` in `𝔸²` the face `{E⁰, E¹}`
has a disconnected centre (two points) and a reducible exceptional divisor, and tracking its
two components separately would break the correspondence with the combinatorial rule. Not in
the sources in this form.

* `PieceFamily`: the data; `faceSet` (the intersection of the pieces of a face), `nerve` (the
  nonempty faces below `nextComp` with nonempty intersection), `IsValid n m` (the invariants
  of the combinatorial state for the family's data, discharged from the geometric hypotheses in
  `Hironaka/Resolution/Algebraic/Monomial/Geometric/Nerve.lean`), `toState n m hV` (the
  combinatorial state; every data field is the family's, definitionally).
* `faceIdeal`, `centerOf`: the ideal sheaves of `Z_P = ⋂_{c ∈ P} piece c` and
  `Z_S = ⋃_{P ∈ S} Z_P`.
* `newComp`, `blowUpPieces`: the transition, the strict transforms of the old pieces and
  `π⁻¹(Z_P)` for the new piece of `P`, with labels and exponents by the formulas of the
  combinatorial transition, so that `toState (Φ.blowUpPieces S m) = (toState Φ).blowUp S` is a
  literal equality once the nerves agree (`toState_blowUpPieces_of_nerve_eq`; the nerves agree
  by `nerve_blowUpPieces` of `Hironaka/Resolution/Algebraic/Monomial/Geometric/Kernel.lean`).
* `exponentAt`, `faceAt`: the exponent function of the marked monomial ideal
  `E.monomial Φ.exponentAt` (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/MonomialPart.lean`)
  and the face of the pieces through a point.
* `Realizes E e`: the piece family realises the boundary `E`, each member being the disjoint
  union of its pieces.
* `RefinesAlong`, `restrictNerve`, `restrictState`: the refinement relation along a morphism
  `h : Y ⟶ X` and the state restricted to the faces meeting the image of `h`, the geometric
  forms of `Refines` and `Sub` of `Hironaka/Resolution/Algebraic/Monomial/Restrict.lean`.
* `Components`, `ofDivisorFamily`: the input piece family (the irreducible components).
* `extendIso`: the label isomorphism extended along the index type of the total transform.
* `realizeAux`, `stagePieces`, `realize`: the fold of a list of centres (the combinatorial run
  `(step3 st).2`) into a blow-up sequence, carrying the piece family; `realize` is the
  geometric Step 3, the third step of `BMO_{n,m}`
  (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Input.lean`).
-/

@[expose] public section

universe u v

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
  Scheme.IdealSheafData Hironaka.Monomial

namespace Hironaka.Monomial

/-- A *labelled piece family* on `X`: for each component index `c < nextComp` a closed set
`piece c`, a label `label c < nextLabel` and an exponent `a c`; the values above `nextComp` are
irrelevant (as for `MonomialState`). -/
structure PieceFamily (X : Scheme.{u}) where
  /-- Components are `0, …, nextComp - 1`. -/
  nextComp : ℕ
  /-- Labels are `0, …, nextLabel - 1`. -/
  nextLabel : ℕ
  /-- The closed set of a component (empty for a dead component). -/
  piece : ℕ → Closeds X
  /-- The label of a component: the index of its member. -/
  label : ℕ → ℕ
  /-- The exponent of a component. -/
  a : ℕ → ℕ
  label_lt : ∀ c, c < nextComp → label c < nextLabel

namespace PieceFamily

variable {X : Scheme.{u}} (Φ : PieceFamily X)

/-! ### Faces, the nerve and the state -/

/-- The closed set `Z_T = ⋂_{c ∈ T} piece c` of a set of components (`⊤ = X` for `T = ∅`). -/
def faceSet (T : Finset ℕ) : Closeds X := T.inf Φ.piece

theorem faceSet_anti {T T' : Finset ℕ} (h : T' ⊆ T) : Φ.faceSet T ≤ Φ.faceSet T' :=
  Finset.inf_mono h

theorem coe_faceSet (T : Finset ℕ) : (Φ.faceSet T : Set X) = ⋂ c ∈ T, (Φ.piece c : Set X) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [faceSet]
  | insert c T hc ih =>
    rw [faceSet, Finset.inf_insert, Closeds.coe_inf, ← faceSet, ih]
    simp

theorem mem_faceSet {T : Finset ℕ} {x : X} : x ∈ Φ.faceSet T ↔ ∀ c ∈ T, x ∈ Φ.piece c := by
  rw [← SetLike.mem_coe, coe_faceSet]
  simp

/-- The *nerve* of the piece family: the nonempty sets of components below `nextComp` with
nonempty common intersection. -/
noncomputable def nerve : Finset (Finset ℕ) :=
  open scoped Classical in
  (Finset.range Φ.nextComp).powerset.filter fun T => T.Nonempty ∧ Φ.faceSet T ≠ ⊥

theorem mem_nerve {T : Finset ℕ} :
    T ∈ Φ.nerve ↔ T ⊆ Finset.range Φ.nextComp ∧ T.Nonempty ∧ Φ.faceSet T ≠ ⊥ := by
  classical
  simp only [nerve, Finset.mem_filter, Finset.mem_powerset]

/-- The invariants of the combinatorial state (`MonomialState.Valid`) for the family's data:
`1 ≤ m`, faces nonempty, below `nextComp`, labels below `nextLabel`, the nerve down-closed,
faces of size `≤ n` with injective labels.
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Nerve.lean` discharges it from the geometric
hypotheses (`valid_of_realizes`). -/
abbrev IsValid (n m : ℕ) : Prop :=
  MonomialState.Valid n m Φ.nextComp Φ.nextLabel Φ.label Φ.nerve

/-- *The combinatorial state of a piece family*: `MonomialState.ofValid` on the family's
counters, labels, exponents and nerve, so that every data field of the state is the family's by
`rfl`. -/
noncomputable def toState (n m : ℕ) (hV : Φ.IsValid n m) : MonomialState :=
  MonomialState.ofValid n m Φ.nextComp Φ.nextLabel Φ.label Φ.a Φ.nerve hV

variable {n m : ℕ} {hV : Φ.IsValid n m}

@[simp] theorem toState_n : (Φ.toState n m hV).n = n := rfl
@[simp] theorem toState_m : (Φ.toState n m hV).m = m := rfl
@[simp] theorem toState_nextComp : (Φ.toState n m hV).nextComp = Φ.nextComp := rfl
@[simp] theorem toState_nextLabel : (Φ.toState n m hV).nextLabel = Φ.nextLabel := rfl
@[simp] theorem toState_label : (Φ.toState n m hV).label = Φ.label := rfl
@[simp] theorem toState_a : (Φ.toState n m hV).a = Φ.a := rfl
@[simp] theorem toState_nerve : (Φ.toState n m hV).nerve = Φ.nerve := rfl

/-- The sum `a(T)` of the exponents of a set of components (`MonomialState.total` on the
family). -/
def total (T : Finset ℕ) : ℕ := ∑ c ∈ T, Φ.a c

theorem toState_total (T : Finset ℕ) : (Φ.toState n m hV).total T = Φ.total T := rfl

/-! ### Centres -/

/-- The ideal sheaf of the closed subscheme `Z_P = ⋂_{c ∈ P} piece c` with its reduced structure:
the sum of the vanishing ideal sheaves of the pieces (the scheme-theoretic intersection of
reduced subschemes; Kollár's `E^{j₁} ∩ ⋯ ∩ E^{j_r}` of [Kol07, 111, Step 3.r]). -/
noncomputable def faceIdeal (P : Finset ℕ) : X.IdealSheafData :=
  ⨆ c ∈ P, IdealSheafData.vanishingIdeal (Φ.piece c)

/-- *The centre of a finset of faces* `Z_S = ⋃_{P ∈ S} Z_P`, as the product of the ideal sheaves
of the (pairwise disjoint, for a centre of the state) intersections `Z_P`. -/
noncomputable def centerOf (S : Finset (Finset ℕ)) : X.IdealSheafData :=
  ∏ P ∈ S, Φ.faceIdeal P

/-! ### The transition -/

/-- The new component of the face `P` of the centre `S`, numbered `nextComp + rank S P` as in
`MonomialState.newComp`, so that the combinatorial and the geometric transitions allocate the
same numbers. -/
def newComp (S : Finset (Finset ℕ)) (P : Finset ℕ) : ℕ := Φ.nextComp + MonomialState.rank S P

theorem toState_newComp (S : Finset (Finset ℕ)) (P : Finset ℕ) :
    (Φ.toState n m hV).newComp S P = Φ.newComp S P := rfl

/-- The strict transform of a closed set under the blow-up of `X` with centre `D`: the closure
of the preimage of its part off the centre (the support of the strict transform of its
vanishing ideal, `coe_support_strictTransform` of
`Hironaka/Resolution/Algebraic/Snc/DictionaryBoundary.lean`). -/
noncomputable def strictTransformCloseds (D : X.IdealSheafData) (C : Closeds X) :
    Closeds D.blowUp :=
  Closeds.closure (D.blowUpπ ⁻¹' ((C : Set X) \ (D.support : Set X)))

/-- *The transition of the piece family under the blow-up of the centre `S`*
([Kol07, Definition 65] and [Kol07, 111, Step 3.2 and 3.r]): the old pieces become their strict
transforms, the face `P ∈ S` contributes the new piece `π⁻¹(Z_P)` at the index `newComp S P`
with the new label `nextLabel` and the exponent `a(P) − m`; the label and exponent functions
are those of `MonomialState.blowUp`. -/
noncomputable def blowUpPieces (S : Finset (Finset ℕ)) (m : ℕ) :
    PieceFamily (Φ.centerOf S).blowUp where
  nextComp := Φ.nextComp + S.card
  nextLabel := Φ.nextLabel + 1
  piece c :=
    if c < Φ.nextComp then strictTransformCloseds (Φ.centerOf S) (Φ.piece c)
    else (S.filter fun P => Φ.newComp S P = c).sup fun P =>
      (Φ.faceSet P).preimage (Φ.centerOf S).blowUpπ.continuous
  label c := if c < Φ.nextComp then Φ.label c else Φ.nextLabel
  a c := if c < Φ.nextComp then Φ.a c
    else (S.filter fun P => Φ.newComp S P = c).sup fun P => Φ.total P - m
  label_lt c _ := by
    split_ifs with h
    · exact (Φ.label_lt c h).trans (Nat.lt_succ_self _)
    · exact Nat.lt_succ_self _

variable (S : Finset (Finset ℕ))

@[simp] theorem blowUpPieces_nextComp : (Φ.blowUpPieces S m).nextComp = Φ.nextComp + S.card := rfl
@[simp] theorem blowUpPieces_nextLabel : (Φ.blowUpPieces S m).nextLabel = Φ.nextLabel + 1 := rfl

theorem blowUpPieces_piece_of_lt {c : ℕ} (hc : c < Φ.nextComp) :
    (Φ.blowUpPieces S m).piece c = strictTransformCloseds (Φ.centerOf S) (Φ.piece c) :=
  ite_eq_left hc

theorem blowUpPieces_label_of_lt {c : ℕ} (hc : c < Φ.nextComp) :
    (Φ.blowUpPieces S m).label c = Φ.label c := ite_eq_left hc

theorem blowUpPieces_a_of_lt {c : ℕ} (hc : c < Φ.nextComp) :
    (Φ.blowUpPieces S m).a c = Φ.a c := ite_eq_left hc

theorem blowUpPieces_label_newComp (P : Finset ℕ) :
    (Φ.blowUpPieces S m).label (Φ.newComp S P) = Φ.nextLabel :=
  ite_eq_right (not_lt.mpr (Nat.le_add_right _ _))

/-- The new piece of a face `P ∈ S`: the preimage `π⁻¹(Z_P)`. -/
theorem blowUpPieces_piece_newComp {P : Finset ℕ} (hP : P ∈ S) :
    (Φ.blowUpPieces S m).piece (Φ.newComp S P) =
      (Φ.faceSet P).preimage (Φ.centerOf S).blowUpπ.continuous := by
  have hlt : ¬ Φ.newComp S P < Φ.nextComp := not_lt.mpr (Nat.le_add_right _ _)
  change (if Φ.newComp S P < Φ.nextComp then _ else
    (S.filter fun Q => Φ.newComp S Q = Φ.newComp S P).sup fun Q =>
      (Φ.faceSet Q).preimage (Φ.centerOf S).blowUpπ.continuous) = _
  rw [ite_eq_right hlt]
  have : (S.filter fun Q => Φ.newComp S Q = Φ.newComp S P) = {P} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hP, rfl⟩, fun Q hQ =>
      MonomialState.rank_injOn S (Finset.mem_filter.mp hQ).1 hP
        (Nat.add_left_cancel (Finset.mem_filter.mp hQ).2)⟩
  rw [this, Finset.sup_singleton]

/-- The new piece of a face `P ∈ S` has the exponent `a(P) − m`. -/
theorem blowUpPieces_a_newComp {P : Finset ℕ} (hP : P ∈ S) :
    (Φ.blowUpPieces S m).a (Φ.newComp S P) = Φ.total P - m := by
  have hlt : ¬ Φ.newComp S P < Φ.nextComp := not_lt.mpr (Nat.le_add_right _ _)
  change (if Φ.newComp S P < Φ.nextComp then Φ.a (Φ.newComp S P) else
    (S.filter fun Q => Φ.newComp S Q = Φ.newComp S P).sup fun Q => Φ.total Q - m) = _
  rw [ite_eq_right hlt]
  have : (S.filter fun Q => Φ.newComp S Q = Φ.newComp S P) = {P} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hP, rfl⟩, fun Q hQ =>
      MonomialState.rank_injOn S (Finset.mem_filter.mp hQ).1 hP
        (Nat.add_left_cancel (Finset.mem_filter.mp hQ).2)⟩
  rw [this, Finset.sup_singleton]

/-- Every data field of the transported state other than the nerve agrees with
`MonomialState.blowUp` by `rfl` (the formulas are the same); the nerve is the content of
`nerve_blowUpPieces` in `Hironaka/Resolution/Algebraic/Monomial/Geometric/Kernel.lean`, and
`MonomialState.ext` (proof fields by proof irrelevance) gives the literal equality of states. -/
theorem toState_blowUpPieces_of_nerve_eq {hV' : (Φ.blowUpPieces S m).IsValid n m}
    (h : (Φ.blowUpPieces S m).nerve = ((Φ.toState n m hV).blowUp S).nerve) :
    (Φ.blowUpPieces S m).toState n m hV' = (Φ.toState n m hV).blowUp S :=
  MonomialState.ext rfl rfl rfl rfl rfl rfl h

/-! ### The exponent function and the face through a point -/

/-- The set of components whose piece passes through `x`. -/
noncomputable def faceAt (x : X) : Finset ℕ :=
  open scoped Classical in
  (Finset.range Φ.nextComp).filter fun c => x ∈ Φ.piece c

theorem mem_faceAt {x : X} {c : ℕ} : c ∈ Φ.faceAt x ↔ c < Φ.nextComp ∧ x ∈ Φ.piece c := by
  classical
  simp [faceAt]

/-- *The exponent function* of the marked monomial ideal `E.monomial Φ.exponentAt` (one exponent
per generic point of a member, the convention of
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/MonomialPart.lean`): the largest exponent of a
piece through `x`. At a generic point of a member of a realised snc boundary exactly one piece
passes. -/
noncomputable def exponentAt (x : X) : ℕ := (Φ.faceAt x).sup Φ.a

/-! ### Realisation of a boundary -/

/-- *The piece family realises the boundary `E`* through the label isomorphism `e`: every member
is the union of the pieces of its label, and pieces of one label are pairwise disjoint (so every
irreducible component of a member lies in exactly one piece). -/
structure Realizes (E : DivisorFamily X) (e : E.ι ≃o Fin Φ.nextLabel) : Prop where
  support_eq : ∀ j : E.ι, (E.component j).support =
    ((Finset.range Φ.nextComp).filter fun c => Φ.label c = e j).sup Φ.piece
  disjoint : ∀ c c', c < Φ.nextComp → c' < Φ.nextComp → c ≠ c' → Φ.label c = Φ.label c' →
    Disjoint (Φ.piece c) (Φ.piece c')

/-- *The piece family `Φ'` on `Y` refines `Φ` along `h : Y ⟶ X` through the parent map `ρ`*: the
same label count, labels and exponents through `ρ`, every piece of `Φ'` inside the preimage of
its parent, and the preimage of every piece of `Φ` the union of its children (pairwise
disjoint: the children are the irreducible components of the preimage). The geometric form of
`MonomialState.Refines`, used for smooth surjections `h` in
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Refinement.lean`. -/
structure RefinesAlong {Y : Scheme.{u}} (Φ' : PieceFamily Y) (h : Y ⟶ X) (ρ : ℕ → ℕ)
    (Φ : PieceFamily X) : Prop where
  nextLabel_eq : Φ'.nextLabel = Φ.nextLabel
  lt : ∀ c, c < Φ'.nextComp → ρ c < Φ.nextComp
  label_eq : ∀ c, c < Φ'.nextComp → Φ.label (ρ c) = Φ'.label c
  a_eq : ∀ c, c < Φ'.nextComp → Φ.a (ρ c) = Φ'.a c
  piece_le : ∀ c, c < Φ'.nextComp → Φ'.piece c ≤ (Φ.piece (ρ c)).preimage h.continuous
  preimage_eq : ∀ c, c < Φ.nextComp → (Φ.piece c).preimage h.continuous =
    ((Finset.range Φ'.nextComp).filter fun c' => ρ c' = c).sup Φ'.piece
  disjoint : ∀ c c', c < Φ'.nextComp → c' < Φ'.nextComp → c ≠ c' → ρ c = ρ c' →
    Disjoint (Φ'.piece c) (Φ'.piece c')

end PieceFamily

/-! ### The restriction of the state along a morphism -/

namespace PieceFamily

variable {X Y : Scheme.{u}} (Φ : PieceFamily X) (h : Y ⟶ X)

/-- The faces of the nerve whose face set meets the image of `h : Y ⟶ X`: the nerve of the
boundary `h⁻¹E` when the pieces stay irreducible under `h`. -/
noncomputable def restrictNerve : Finset (Finset ℕ) :=
  open scoped Classical in
  Φ.nerve.filter fun T => (Φ.faceSet T).preimage h.continuous ≠ ⊥

theorem mem_restrictNerve {T : Finset ℕ} :
    T ∈ Φ.restrictNerve h ↔ T ∈ Φ.nerve ∧ (Φ.faceSet T).preimage h.continuous ≠ ⊥ := by
  classical
  simp only [restrictNerve, Finset.mem_filter]

theorem restrictNerve_subset : Φ.restrictNerve h ⊆ Φ.nerve :=
  fun _ hT => ((Φ.mem_restrictNerve h).mp hT).1

/-- The restricted data are `Valid`: a subfamily of a valid nerve, down-closed because a smaller
face has a larger face set (`faceSet_anti`), whose preimage is then nonempty too. -/
theorem valid_restrictNerve {n m : ℕ} (hV : Φ.IsValid n m) :
    MonomialState.Valid n m Φ.nextComp Φ.nextLabel Φ.label (Φ.restrictNerve h) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hV
  have hsub := Φ.restrictNerve_subset h
  refine ⟨h1, fun T hT => h2 T (hsub hT), fun T hT => h3 T (hsub hT), h4, ?_,
    fun T hT => h6 T (hsub hT), fun T hT => h7 T (hsub hT)⟩
  intro T hT T' hT' hne
  obtain ⟨hTN, hTne⟩ := (Φ.mem_restrictNerve h).mp hT
  refine (Φ.mem_restrictNerve h).mpr ⟨h5 T hTN T' hT' hne, fun hbot => hTne ?_⟩
  have hle : (Φ.faceSet T).preimage h.continuous ≤ (Φ.faceSet T').preimage h.continuous :=
    fun _ hy => Φ.faceSet_anti (Finset.mem_powerset.mp hT') hy
  rw [hbot] at hle
  exact le_bot_iff.mp hle

/-- *The state of `Φ` restricted along `h : Y ⟶ X`*: `MonomialState.ofValid` on the family's
counters, labels and exponents and the faces meeting the image of `h`. It is `Sub` the state
`toState` (its data fields are `toState`'s by `rfl`), and it is the state that a refining
family on `Y` refines (`Hironaka/Resolution/Algebraic/Monomial/Geometric/Refinement.lean`). -/
noncomputable def restrictState (n m : ℕ) (hV : Φ.IsValid n m) : MonomialState :=
  MonomialState.ofValid n m Φ.nextComp Φ.nextLabel Φ.label Φ.a (Φ.restrictNerve h)
    (Φ.valid_restrictNerve h hV)

variable {n m : ℕ} {hV : Φ.IsValid n m}

@[simp] theorem restrictState_n : (Φ.restrictState h n m hV).n = n := rfl
@[simp] theorem restrictState_m : (Φ.restrictState h n m hV).m = m := rfl
@[simp] theorem restrictState_nextComp : (Φ.restrictState h n m hV).nextComp = Φ.nextComp := rfl
@[simp] theorem restrictState_nextLabel :
    (Φ.restrictState h n m hV).nextLabel = Φ.nextLabel := rfl
@[simp] theorem restrictState_label : (Φ.restrictState h n m hV).label = Φ.label := rfl
@[simp] theorem restrictState_a : (Φ.restrictState h n m hV).a = Φ.a := rfl
@[simp] theorem restrictState_nerve :
    (Φ.restrictState h n m hV).nerve = Φ.restrictNerve h := rfl

end PieceFamily

/-! ### The input piece families -/

namespace PieceFamily

variable {X : Scheme.{u}} (E : DivisorFamily X)

/-- The irreducible components of the members of `E`: the generic points of their supports
(finite on a Noetherian scheme), tagged by their member. -/
def Components : Type u := Σ j : E.ι, ↥(E.component j).support.genericPoints

/-- *The input piece family* of [Kol07, 111, Step 3]: the irreducible components of the members,
enumerated by `σ`, with the label of their member through `e` and the exponent `a` at their
generic point. Each component carries its own exponent, the fine form of
[Kol07, Definition–Lemma 110]
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/MonomialPart.lean`). -/
noncomputable def ofDivisorFamily {k L : ℕ} (a : X → ℕ) (e : E.ι ≃o Fin L)
    (σ : Fin k ≃ Components E) : PieceFamily X where
  nextComp := k
  nextLabel := L
  piece c := if h : c < k then Closeds.closure {((σ ⟨c, h⟩).2 : X)} else ⊥
  label c := if h : c < k then (e (σ ⟨c, h⟩).1 : ℕ) else 0
  a c := if h : c < k then a ((σ ⟨c, h⟩).2 : X) else 0
  label_lt c hc := by
    simp only [dite_eq_left hc]
    exact (e _).isLt

end PieceFamily

/-! ### The label isomorphism along the total transform -/

/-- `Fin L ⊕ₗ PUnit → Fin (L + 1)`: `inl i ↦ castSucc i`, `inr () ↦ last L`. -/
def finSuccFun (L : ℕ) (x : Fin L ⊕ₗ PUnit.{v + 1}) : Fin (L + 1) :=
  Sum.elim Fin.castSucc (fun _ => Fin.last L) (ofLex x)

theorem finSuccFun_strictMono (L : ℕ) : StrictMono (finSuccFun.{v} L) := by
  rintro (x | x) (y | y) hxy
  · exact Fin.castSucc_lt_castSucc_iff.mpr (Sum.Lex.inl_lt_inl_iff.mp hxy)
  · exact Fin.castSucc_lt_last x
  · exact absurd hxy Sum.Lex.not_inr_lt_inl
  · exact absurd (Sum.Lex.inr_lt_inr_iff.mp hxy) (lt_irrefl _)

theorem finSuccFun_surjective (L : ℕ) : Function.Surjective (finSuccFun.{v} L) := fun i =>
  Fin.lastCases (motive := fun i => ∃ x, finSuccFun.{v} L x = i) ⟨toLex (Sum.inr PUnit.unit), rfl⟩
    (fun j => ⟨toLex (Sum.inl j), rfl⟩) i

/-- `Fin L ⊕ₗ PUnit ≃o Fin (L + 1)`: `inl i ↦ castSucc i`, `inr () ↦ last L`. -/
noncomputable def finSuccOrderIso (L : ℕ) : (Fin L ⊕ₗ PUnit.{v + 1}) ≃o Fin (L + 1) :=
  (finSuccFun_strictMono L).orderIsoOfSurjective _ (finSuccFun_surjective L)

/-- *The label isomorphism extended along the index type `E.ι ⊕ₗ PUnit` of the total transform*:
the old labels through `e`, the exceptional divisor `inr ()` to the new label `L`, added as the
last divisor as in [Kol07, Definition 65]. -/
noncomputable def extendIso {ι : Type u} [LinearOrder ι] {L : ℕ} (e : ι ≃o Fin L) :
    (ι ⊕ₗ PUnit.{u + 1}) ≃o Fin (L + 1) :=
  (OrderIso.sumLexCongr e (OrderIso.refl PUnit.{u + 1})).trans (finSuccOrderIso L)

theorem extendIso_inl {ι : Type u} [LinearOrder ι] {L : ℕ} (e : ι ≃o Fin L) (i : ι) :
    extendIso e (toLex (Sum.inl i)) = (e i).castSucc := rfl

theorem extendIso_inr {ι : Type u} [LinearOrder ι] {L : ℕ} (e : ι ≃o Fin L) :
    extendIso e (toLex (Sum.inr PUnit.unit)) = Fin.last L := rfl

/-! ### The realisation: the fold of a list of centres -/

namespace PieceFamily

/-- *The fold of a list of centres into a blow-up sequence*, carrying the piece family:
structural recursion on the list, no recursion on schemes. The centre at each step is `Z_S` of
the current family and the family is transported by `blowUpPieces`. -/
noncomputable def realizeAux : {X : Scheme.{u}} → PieceFamily X → ℕ → List (Finset (Finset ℕ)) →
    BlowUpSequence X
  | X, _, _, [] => .nil X
  | X, Φ, m, S :: L => .cons X (Φ.centerOf S) (realizeAux (Φ.blowUpPieces S m) m L)

/-- The piece family at stage `i` of the fold. -/
noncomputable def stagePieces : {X : Scheme.{u}} → (Φ : PieceFamily X) → (m : ℕ) →
    (L : List (Finset (Finset ℕ))) → (i : Fin ((realizeAux Φ m L).length + 1)) →
    PieceFamily ((realizeAux Φ m L).stage i)
  | _, Φ, _, [], _ => Φ
  | _, Φ, _, _ :: _, ⟨0, _⟩ => Φ
  | _, Φ, m, S :: L, ⟨j + 1, h⟩ =>
    stagePieces (Φ.blowUpPieces S m) m L ⟨j, Nat.lt_of_succ_lt_succ h⟩

variable {X : Scheme.{u}} (Φ : PieceFamily X) (m : ℕ)

@[simp] theorem realizeAux_nil : realizeAux Φ m [] = .nil X := rfl

@[simp] theorem realizeAux_cons (S : Finset (Finset ℕ)) (L : List (Finset (Finset ℕ))) :
    realizeAux Φ m (S :: L) = .cons X (Φ.centerOf S) (realizeAux (Φ.blowUpPieces S m) m L) := rfl

theorem realizeAux_length (L : List (Finset (Finset ℕ))) :
    (realizeAux Φ m L).length = L.length := by
  induction L generalizing X with
  | nil => rfl
  | cons S L ih => exact congrArg (· + 1) (ih _)

theorem stagePieces_nil (i : Fin ((realizeAux Φ m []).length + 1)) :
    stagePieces Φ m [] i = Φ := rfl

theorem stagePieces_cons_zero (S : Finset (Finset ℕ)) (L : List (Finset (Finset ℕ)))
    (h : 0 < (realizeAux Φ m (S :: L)).length + 1) : stagePieces Φ m (S :: L) ⟨0, h⟩ = Φ := rfl

theorem stagePieces_succ (S : Finset (Finset ℕ)) (L : List (Finset (Finset ℕ))) (j : ℕ)
    (h : j + 1 < (realizeAux Φ m (S :: L)).length + 1) :
    stagePieces Φ m (S :: L) ⟨j + 1, h⟩ =
      stagePieces (Φ.blowUpPieces S m) m L ⟨j, Nat.lt_of_succ_lt_succ h⟩ := rfl

end PieceFamily

namespace PieceFamily

/-- The label isomorphism at stage `i` of the fold: `e` extended by `extendIso` once per
blow-up. -/
noncomputable def stageIso : {X : Scheme.{u}} → (Φ : PieceFamily X) → (m : ℕ) →
    (E : DivisorFamily X) → (E.ι ≃o Fin Φ.nextLabel) → (L : List (Finset (Finset ℕ))) →
    (i : Fin ((realizeAux Φ m L).length + 1)) →
    ((realizeAux Φ m L).totalTransformSeq E i).ι ≃o Fin ((stagePieces Φ m L i).nextLabel)
  | _, _, _, _, e, [], _ => e
  | _, _, _, _, e, _ :: _, ⟨0, _⟩ => e
  | _, Φ, m, E, e, S :: L, ⟨j + 1, h⟩ =>
    stageIso (Φ.blowUpPieces S m) m (E.totalTransform (Φ.centerOf S)) (extendIso e) L
      ⟨j, Nat.lt_of_succ_lt_succ h⟩

variable {X : Scheme.{u}} (Φ : PieceFamily X) (m : ℕ)

/-- *The geometric Step 3* of [Kol07, 111]: the fold of the combinatorial run
`(step3 (toState Φ)).2` into a blow-up sequence of `X`. -/
noncomputable def realize (n m : ℕ) (hV : Φ.IsValid n m) : BlowUpSequence X :=
  realizeAux Φ m (MonomialState.step3 (Φ.toState n m hV)).2

end PieceFamily

end Hironaka.Monomial
