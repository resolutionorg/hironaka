/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
public import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
public import Hironaka.Scheme.Snc.Dictionary
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Włodarczyk's embedded desingularization sequence `BED`

The sequence of blow-ups of Włodarczyk's embedded desingularization theorem with smooth centres
[Wlo05, Theorem 1.0.2], in the strengthened form of Bravo–Villamayor [Wlo05, Theorem 4.7.1]: for a
reduced closed subscheme `Y = ⋃ Yᵢ` of a smooth variety `X`, a sequence of blow-ups in smooth
centres after which the strict transforms `Ỹᵢ` of the components are smooth and disjoint, and the
full transform of `I_Y` is its monomial part times `I_Ỹ`. Włodarczyk's proof runs the canonical
resolution of the marked ideal `(X, I_Y, ∅, 1)` [Wlo05, 4.6] with a modification: the procedure
is run until "the strict transform of one of the components `Yᵢ` is the center"; at that moment,
by the Claim of the proof of Theorem 4.7.1, the controlled transform of
`(I_Y, 1)` agrees with `I_Ỹᵢ` near `Ỹᵢ`; these strict transforms are isolated, the procedure
continues "ignoring these isolated components", and at the end any components not meeting the
strict transforms are principalized.

Kollár's blow-up sequence functors expose neither Włodarczyk's invariant nor his "moment", so the
modification is transcribed as an outer loop around the order reduction functor `BMO_1` of
[Kol07, Theorem 69] (`Hironaka.Stage.BMO_m`): run `BMO_1` on the marked triple; at the first stage
whose centre contains the strict transform of one of the components not yet isolated, truncate
the run before that blow-up, replace the ideal by its colon by the reduced ideal of the absorbed
strict transforms (the isolation), and restart on the modified marked triple with the remaining
components. Włodarczyk's reordering of the monomial part (his Step 2b, which terminates by his
invariant) is not transcribed; the stop rule alone is. Włodarczyk's Claim fails for this
order of the steps (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`), and the clauses of
the theorem are instead proved from the local form of the ideal near an isolated component
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative` and the modules `EmbeddedCP*`).

## The construction

* `bmoOneRun T hm` — the run of `BMO_1` on a marked triple `T` of mark `1`; it is a smooth
  blow-up sequence of order `≥ 1` for `T` (`isOrderGeSeq_bmoOneRun`).
* `HasAbsorptionAt T hm C n` — the stop rule: at stage `n` of the run the centre CONTAINS the
  strict transform of some member of the finite set `C` of (the strict transforms of) the
  components not yet isolated (`CenterContains`; Kollár's "some blow-up center must contain
  `η_X`" in the proof of [Kol07, Corollary 22]). Stage `0` is "before the first blow-up of the
  round".
* `stageTriple T hm n` — the marked triple induced at stage `n` of the run truncated there
  (`MarkedTriple.induced`; a prefix of a sequence of order `≥ 1` is one). `isolatedTriple T hm C n`
  — that triple with its ideal replaced by the colon `I_n : I_Γ`, `I_Γ` the REDUCED ideal of the
  union of the absorbed strict transforms: `I : I_Γ` is `𝒪` near `Γ` where `I = I_Γ`, and `I`
  away from `Γ`; it is canonical, with no choice of a neighbourhood. `remainingComponents T hm C n`
  — the strict transforms of the other members of `C` at stage `n`. Both are the constructions
  `isolatedAt` and `remainingAt` for an arbitrary run and arbitrary absorbed and remaining families,
  at the truncated run.
* `bedAux T hm C` — the loop: run `BMO_1` on `T`; if some stage has an absorption, take the FIRST
  such stage `n₀` (`Nat.find`), truncate the run BEFORE the absorbing blow-up (`take n₀`), isolate,
  and recurse on the isolated triple with the remaining components (well-founded on the number of
  remaining components, the absorbed set being nonempty); if no stage has one, the round is the
  whole run and the loop stops. The restart on the modified marked triple IS the definition: no
  stability property of Kollár's functors is assumed, and the exhaustiveness "every remaining
  component is eventually absorbed" ([Wlo05, 4.6]: otherwise the generic points would be
  transformed isomorphically) is a theorem about this object, not a clause of it.
* `BED T` — Włodarczyk's embedded desingularization sequence of the triple `T = (X, I_Y, E)`: the
  loop from the marked triple `(X, I_Y, 1, E)` with the components of `V(I_Y)` (their reduced
  ideals, `componentIdeals`). The theorem concerns `E = ∅` and reduced `Y`; the definition needs
  neither.

## Where the stop happens

At mark `1` every absorption of a strict transform happens in the `d = 1` round of Step 1 of
[Kol07, Theorem 107] (`Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart`),
inside Step 2.2 of [Kol07, Theorem 103] (the modules `Hironaka.OrderReduction.Step22*`: Lemma 102 at
the position of the maximal-contact hypersurface), and at the bottom of the maximal-contact chain it
is the opening trivial blow-up `π_{-1}` of [Kol07, Lemma 102]
(`Hironaka.BD.piMinusOne`) of the hypersurface `Ỹ_c ⊂ H_{r-1}`, pushed
forward through the chain. The strict transform of the absorbed component along that blow-up is
EMPTY (`strictTransformAlong` saturates by the exceptional ideal, which is the component's own
ideal), so the stop is what keeps `Ỹ` alive: Włodarczyk's termination in his Step 1ba is "no
`π_{-1}` at a maximal-contact position", and the truncation before the absorbing blow-up is exactly
that.

The clauses of [Wlo05, Theorem 1.0.2] for `BED` — smooth centres and the simple normal crossing
clauses, the centres disjoint from the smooth points of `Y`, the final strict transform smooth and
snc with the boundary, the fine form of the full transform, and the behaviour under smooth
morphisms of the ambient — are proved in the modules
`Hironaka.Resolution.Algebraic.Wlo05.Embedded*`, collected for the functor `EDFunctor` in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`, and stated as the theorem
`AlgebraicGeometry.exists_functorial_embeddedDesingularization` at the end of that module.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Stage

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### The run of `BMO_1` on a marked triple of mark `1` -/

/-- The run of the order reduction functor `BMO_1` of [Kol07, Theorem 69] (`Hironaka.Stage.BMO_m`
at mark `1`) on a marked triple of mark `1`: the canonical resolution of the marked ideal
`(X, I_Y, ∅, 1)` of [Wlo05, 4.6] in Kollár's form. -/
noncomputable def bmoOneRun (T : MarkedTriple k) (hm : T.m = 1) : BlowUpSequence T.X.left :=
  (BMO_m 1 k).seq T ⟨le_rfl, hm⟩

/-- The run is a smooth blow-up sequence of order `≥ 1` for `(X, I, 1, E)` ([Kol07, Theorem 69],
the defining property of the functor). -/
theorem isOrderGeSeq_bmoOneRun (T : MarkedTriple k) (hm : T.m = 1) :
    (bmoOneRun T hm).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
  (BMO_m 1 k).isOrderGeSeq T ⟨le_rfl, hm⟩

/-! ### One round: the stop rule, the truncated run, the isolated triple -/

section Round

/-- **The stop rule**: at stage `n` of the run of `BMO_1` on `T` the centre contains the strict
transform of some member of `C` (`CenterContains`: the centre's ideal is contained in the strict
transform's) — Włodarczyk's stop rule, "the strict transform of one of the components `Yᵢ` is
the center" [Wlo05, Theorem 4.7.1, proof]; compare "some blow-up center must
contain `η_X`" in the proof of [Kol07, Corollary 22]. Stage `0` is "before the first blow-up of
the round". -/
def HasAbsorptionAt (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData) (n : ℕ)
    : Prop :=
  ∃ c ∈ C, CenterContains (bmoOneRun T hm) c n

/-- The marked triple induced at stage `n` of the run of `BMO_1` on `T`, truncated at `n`
(`MarkedTriple.induced`; the prefix of a sequence of order `≥ 1` is one). -/
noncomputable def stageTriple (T : MarkedTriple k) (hm : T.m = 1) (n : ℕ) : MarkedTriple k :=
  T.induced ((bmoOneRun T hm).take n)
    (isOrderGeSeq_take _ _ _ _ (isOrderGeSeq_bmoOneRun T hm) n) (Fin.last _)

/-- The isolated marked triple at the end of a run `Q` of order `≥ 1`, with `F` the absorbed
members: the induced marked triple with its ideal replaced by the colon by the reduced ideal of the
union of the strict transforms of the members of `F`. -/
noncomputable def isolatedAt (T : MarkedTriple k) (Q : BlowUpSequence T.X.left)
    (hQ : Q.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (F : Finset T.X.left.IdealSheafData) :
    MarkedTriple k :=
  { T.induced Q hQ (Fin.last _) with
    I := (T.induced Q hQ (Fin.last _)).I.colon
      (IdealSheafData.vanishingIdeal (⨆ c ∈ F, (Q.strictTransformSeq c (Fin.last _)).support))
    isNonzeroEverywhere :=
      Hironaka.BMO.isNonzeroEverywhere_of_le (IdealSheafData.le_colon_self _ _)
        (T.induced Q hQ (Fin.last _)).isNonzeroEverywhere }

open Classical in
/-- The strict transforms at the end of `Q` of the members of `G`. -/
noncomputable def remainingAt {X : Scheme.{u}} (Q : BlowUpSequence X)
    (G : Finset X.IdealSheafData) : Finset (Q.stage (Fin.last _)).IdealSheafData :=
  G.image fun c => Q.strictTransformSeq c (Fin.last _)

open Classical in
/-- **The isolated marked triple** at stage `n` — the marked triple induced at stage `n` of the
truncated run, with its ideal replaced by the colon by the REDUCED ideal of the union of the strict
transforms of the members of `C` absorbed at `n` (`I : I_Γ`, which is `𝒪` near `Γ` where `I = I_Γ`
and `I` away from `Γ`): Włodarczyk's isolated components, which the procedure continues
"ignoring" [Wlo05, Theorem 4.7.1, proof]. -/
noncomputable def isolatedTriple (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (n : ℕ) : MarkedTriple k :=
  isolatedAt T ((bmoOneRun T hm).take n)
    (isOrderGeSeq_take _ _ _ _ (isOrderGeSeq_bmoOneRun T hm) n)
    (C.filter fun c => CenterContains (bmoOneRun T hm) c n)

open Classical in
/-- The strict transforms, at stage `n`, of the members of `C` NOT absorbed there — the components
the next round still has to handle. -/
noncomputable def remainingComponents (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (n : ℕ) :
    Finset (isolatedTriple T hm C n).X.left.IdealSheafData :=
  remainingAt ((bmoOneRun T hm).take n) (C.filter fun c => ¬ CenterContains (bmoOneRun T hm) c n)

open Classical in
/-- The loop's measure: an absorption at the first stage where one exists removes at least one
member of `C`. -/
theorem card_remainingComponents_lt (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (h : ∃ n, HasAbsorptionAt T hm C n) :
    (remainingComponents T hm C (Nat.find h)).card < C.card := by
  obtain ⟨c, hc, habs⟩ := Nat.find_spec h
  exact Finset.card_image_le.trans_lt
    (Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨c, hc, fun hn => hn habs⟩))

end Round

/-! ### The loop -/

open Classical in
/-- **The modified run** from the marked triple `T` of mark `1` with `C` the strict transforms of
the components not yet isolated: run `BMO_1` on `T`; if some stage has an absorption, truncate the
run BEFORE the first absorbing blow-up (stage `0` allowed: before any blow-up), isolate, and
continue from the isolated marked triple with the remaining components; otherwise the round is the
whole run and the loop stops. Well-founded on the number of remaining components
(`card_remainingComponents_lt`). This is the transcription of the proof of [Wlo05, Theorem 4.7.1]
described in the module docstring. -/
noncomputable def bedAux (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData) :
    BlowUpSequence T.X.left :=
  if h : ∃ n, HasAbsorptionAt T hm C n then
    ((bmoOneRun T hm).take (Nat.find h)).concat
      (bedAux (isolatedTriple T hm C (Nat.find h)) hm (remainingComponents T hm C (Nat.find h)))
  else bmoOneRun T hm
termination_by C.card
decreasing_by exact card_remainingComponents_lt T hm C h

open Classical in
/-- The loop unrolled once at a round with an absorption. -/
theorem bedAux_of_exists (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
    (h : ∃ n, HasAbsorptionAt T hm C n) :
    bedAux T hm C =
      ((bmoOneRun T hm).take (Nat.find h)).concat
        (bedAux (isolatedTriple T hm C (Nat.find h)) hm
          (remainingComponents T hm C (Nat.find h))) := by
  rw [bedAux, dite_eq_left h]

open Classical in
/-- The loop at a round without an absorption: the whole run, and the loop stops. -/
theorem bedAux_of_not_exists (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData)
    (h : ¬ ∃ n, HasAbsorptionAt T hm C n) : bedAux T hm C = bmoOneRun T hm := by
  rw [bedAux, dite_eq_right h]

/-! ### The components of `Y` and the sequence `BED` -/

open Classical in
/-- The reduced ideals of the irreducible components of `V(I)` — the closures of the generic points
of the support (`Closeds.genericPoints`, finite on the Noetherian `X`): Włodarczyk's decomposition
`Y = ⋃ Yᵢ` into irreducible components [Wlo05, Theorem 4.7.1]. -/
noncomputable def componentIdeals (T : Triple k) : Finset T.X.left.IdealSheafData :=
  haveI := Hironaka.BD.noetherianSpace_triple T
  (T.I.support.genericPoints_finite).toFinset.image fun η =>
    IdealSheafData.vanishingIdeal (Closeds.closure {η})

/-- **Włodarczyk's embedded desingularization sequence** `BED(X, I_Y, E)` [Wlo05, Theorem 4.7.1;
Theorem 1.0.2]: the modified run from the marked triple `(X, I_Y, 1, E)` with the components of
`V(I_Y)`. The theorem concerns `E = ∅` and reduced `Y`; the definition needs neither. -/
noncomputable def BED (T : Triple k) : BlowUpSequence T.X.left :=
  bedAux ⟨T, 1⟩ rfl (componentIdeals T)

theorem BED_eq (T : Triple k) : BED T = bedAux ⟨T, 1⟩ rfl (componentIdeals T) := rfl

end Hironaka.Resolution
