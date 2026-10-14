/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Independence
public import Hironaka.Scheme.BlowUpSequence.AffineCover
public import Hironaka.Scheme.ReducedEquidimensional
public import Hironaka.Scheme.BlowUpSequence.Assignment
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Descent
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Assembly
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Kollár's resolution functor on reduced equidimensional schemes

The resolution functor `BR` of [Kol07, Theorem 36], the witness of
`AlgebraicGeometry.exists_functorial_resolution`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36`), on the class `IsReducedEquidimensional k X`
of reduced schemes whose smooth locus over `k` is smooth of one relative dimension
(`Hironaka.Scheme.Resolution.Defs`); the irreducible components may meet. Kollár constructs
`BR` first on affine schemes and then glues by the descent of [Kol07, Proposition 37]; this file
follows him.

## The construction

* On an affine scheme `X` over `k` (`BRAffine`): embed `X` by an admissible embedding `X ↪ A`
  (`AdmissibleEmbedding`: a closed immersion over `k` into a smooth affine `A` with the ideal of the
  triple the ideal of `X` and empty boundary), run the single principalization sequence
  `BP(A, I_X, ∅)` and restrict it to `X`, truncated at the first centre containing the strict
  transform of `X` — the embedding-free affine resolution `BR_affine' k X` of
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.Independence`, independent of the admissible pair by
  `BR_affine'_eq` ("`BR(X)` is independent of the choice of the embedding", [Kol07, Theorem 36,
  proof]) — and delete its globally empty steps (`eraseEmpty`, below). On a reduced `X` whose
  smooth locus has one relative dimension, the first centre containing the strict transform of `X`
  is the first centre containing the strict transform of EACH irreducible component
  (`Hironaka.Resolution.Algebraic.Kol07.Thm36.EqualAbsorbingIndex`), so this single truncation is
  the step by which Kollár's `BR` is "defined on (possibly reducible) affine schemes"; no component
  is blown up along itself.
* On any member (`BR`): the descent of [Kol07, Proposition 37] of `BRAffine (∐ Uᵢ)` along the
  smooth surjection `g : ∐ Uᵢ → X` from the finite affine cover
  (`Hironaka.Scheme.BlowUpSequence.AffineCover`; `∐ Uᵢ` is affine and in the class), `BRDescends`,
  chosen by `Classical.choose`, with the globally empty steps deleted; `nil X` otherwise
  (`BR_eq_of_descends`, `BR_eq_nil_of_not_descends`, `BR_eq_nil_of_not_class`; the descent holds on
  every member, `Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent`).
* `BRFunctor k : ResolutionAssignment k` packages `BR k`.

## The deletion of the globally empty steps

Kollár's convention [Kol07, 32] is that the outputs of the named blow-up sequence functors
contain no empty blow-up. His list omits `BR`, but his (34.1) at the identity morphism demands it:
clause (4a) of `exists_functorial_resolution` at `Y := X`, `h := 𝟙 X` reads `BR X = (BR
X).eraseEmpty`. The affine resolution does not satisfy this by itself: a stage of the global run
whose centre misses the strict transform of `X` (a stratum of the exceptional divisors away from
the strict transform of `X`) restricts to the centre `⊤` on `X`, and `BR_affine` keeps such steps.
So both branches delete the globally empty steps. The deletion is compatible with the clauses of
the theorem: it commutes with pullback along flat surjective morphisms
(`eraseEmpty_pullback_of_flat_surjective`), it is idempotent (`eraseEmpty_eraseEmpty`), and `(nil
X).eraseEmpty = nil X`.

The empty scheme is in the class; both definitions return the empty sequence on the nose
(`BRAffine_eq_nil_of_isEmpty`, `BR_empty`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Hironaka BlowUpSequence

namespace Hironaka.Resolution

/-! ### Blow-up sequences on an empty scheme -/

/-- On the empty scheme every ideal sheaf is `⊤`, so every blow-up sequence deletes to the empty
sequence. -/
theorem eraseEmpty_eq_nil_of_isEmpty {X : Scheme.{u}} (S : BlowUpSequence X) (hX : IsEmpty X) :
    S.eraseEmpty = nil X := by
  induction S with
  | nil X => rfl
  | cons X D rest ih =>
    have hD : D = ⊤ := Scheme.IdealSheafData.ext_stalkIdeal fun x => (hX.false x).elim
    subst hD
    rw [eraseEmpty_cons_top, ih ⟨fun y => hX.false ((⊤ : X.IdealSheafData).blowUpπ y)⟩,
        pullback_nil]

/-- On an empty scheme two blow-up sequences of the same length are equal: every ideal sheaf on an
empty scheme is `⊤` and the blow-up of an empty scheme is empty. -/
theorem _root_.AlgebraicGeometry.Scheme.BlowUpSequence.eq_of_length_eq_of_isEmpty :
    ∀ {Z : Scheme.{u}} [IsEmpty Z] (S S' : BlowUpSequence Z), S.length = S'.length → S = S'
  | _, _, nil _, nil _, _ => rfl
  | _, _, nil _, cons _ _ rest, h => (Nat.succ_ne_zero rest.length h.symm).elim
  | _, _, cons _ _ rest, nil _, h => (Nat.succ_ne_zero rest.length h).elim
  | Z, _, cons _ D rest, cons _ D' rest', h => by
    have hD : D = D' := Scheme.IdealSheafData.ext_stalkIdeal fun x => isEmptyElim x
    subst hD
    have : IsEmpty D.blowUp := ⟨fun y => IsEmpty.false (D.blowUpπ y)⟩
    have h' : rest.length = rest'.length := Nat.succ.inj h
    rw [AlgebraicGeometry.Scheme.BlowUpSequence.eq_of_length_eq_of_isEmpty rest rest' h']

variable (k : Type u) [Field k] [CharZero k]

section Affine

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

/-- The resolution of an affine scheme `X` over `k` ("we have now defined `BR` on (possibly
reducible) affine schemes", [Kol07, Theorem 36, proof]): the embedding-free affine resolution
`BR_affine' k X` — the global run `BP(A, I_X, ∅)` of an admissible embedding `X ↪ A`, restricted
to `X` and truncated at the first centre containing the strict transform of `X` — with its globally
empty steps deleted (the convention of [Kol07, 32] on the output, forced by (34.1) at the identity;
see the module docstring). The value does not depend on the admissible pair
(`BRAffine_eq_eraseEmpty_BR_affine`); without an admissible embedding (never on an affine scheme of
finite type over `k`, `exists_admissibleEmbedding`) it is `nil X`. -/
noncomputable def BRAffine : BlowUpSequence X := (BR_affine' k X).eraseEmpty

/-- `BRAffine` through any admissible pair: the affine resolution `BR_affine TA emb` with its
globally empty steps deleted (`BR_affine'_eq`). -/
theorem BRAffine_eq_eraseEmpty_BR_affine (TA : Triple k) (emb : X ⟶ TA.X.left)
    (h : AdmissibleEmbedding k X TA emb) : BRAffine k X = (BR_affine TA emb).eraseEmpty := by
  unfold BRAffine
  rw [BR_affine'_eq TA emb h]

/-- `BRAffine` has no empty blow-up. -/
theorem eraseEmpty_BRAffine : (BRAffine k X).eraseEmpty = BRAffine k X :=
  eraseEmpty_eraseEmpty _

/-- On an empty scheme the affine value is the empty sequence. -/
theorem BRAffine_eq_nil_of_isEmpty [IsEmpty X] : BRAffine k X = nil X :=
  eraseEmpty_eq_nil_of_isEmpty _ ‹_›

end Affine

section Class

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))]

/-- The descent along the finite affine cover [Kol07, Proposition 37]: a blow-up sequence on `X`
whose pullback along `g : ∐ Uᵢ → X` is the affine value on `∐ Uᵢ`. -/
abbrev BRDescends : Prop :=
  haveI : CompactSpace X := compactSpace_of_quasiCompact_over k X
  ∃ T : BlowUpSequence X,
    T.pullback (affineCoverDesc X) =
      BRAffine k (affineCoverScheme X)

open Classical in
/-- Kollár's resolution functor on a reduced equidimensional scheme [Kol07, Theorem 36;
Proposition 37]: the descended sequence of `BRDescends` with its globally empty steps deleted (the
convention of [Kol07, 32] on the output, forced by clause (4a) at the identity; a no-op when
the descended sequence has no empty step, `eraseEmpty_eraseEmpty`); `nil X` off the class or when
the descent does not hold (the latter never on a member of the class,
`Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent`). -/
noncomputable def BR : BlowUpSequence X :=
  if X.IsReducedEquidimensional k then
    if hT : BRDescends k X then hT.choose.eraseEmpty else nil X
  else nil X

/-- On a member of the class for which the descent holds, `BR` is the chosen descended sequence
with its globally empty steps deleted. -/
theorem BR_eq_of_descends (hX : X.IsReducedEquidimensional k)
    (hT : BRDescends k X) : BR k X = hT.choose.eraseEmpty := by
  unfold BR
  rw [ite_eq_left hX, dite_eq_left hT]

/-- On a member of the class without the cover descent, `BR` is the empty sequence (a branch never
taken, since the descent holds on every member of the class). -/
theorem BR_eq_nil_of_not_descends (hX : X.IsReducedEquidimensional k)
    (hT : ¬ BRDescends k X) : BR k X = nil X := by
  unfold BR
  rw [ite_eq_left hX, dite_eq_right hT]

/-- Off the class `BR` is the empty sequence. -/
theorem BR_eq_nil_of_not_class (hX : ¬ X.IsReducedEquidimensional k) : BR k X = nil X := by
  unfold BR
  rw [ite_eq_right hX]

/-- `BR` has no empty blow-up (both branches of the definition). -/
theorem eraseEmpty_BR : (BR k X).eraseEmpty = BR k X := by
  by_cases hX : X.IsReducedEquidimensional k
  · by_cases hT : BRDescends k X
    · rw [BR_eq_of_descends k X hX hT, eraseEmpty_eraseEmpty]
    · rw [BR_eq_nil_of_not_descends k X hX hT]
      rfl
  · rw [BR_eq_nil_of_not_class k X hX]
    rfl

/-- On a member for which the descent holds, the pullback of `BR` along the finite affine cover is
the affine value on the cover scheme (the deletion of empty steps commutes with the pullback along
the flat surjection `g`, and `BRAffine` has no empty step). -/
theorem BR_pullback_affineCoverDesc_of_descends [CompactSpace X]
    (hX : X.IsReducedEquidimensional k) (hT : BRDescends k X) :
    (BR k X).pullback (affineCoverDesc X) = BRAffine k (affineCoverScheme X) := by
  rw [BR_eq_of_descends k X hX hT,
    ← eraseEmpty_pullback_of_flat_surjective _ _ (surjective_affineCoverDesc X), hT.choose_spec,
    eraseEmpty_BRAffine]

/-- The uniqueness in the descent: a sequence `T` on a member whose pullback along the finite
affine cover is the affine value on the cover scheme has `BR k X = T.eraseEmpty` (a blow-up
sequence is determined by its pullbacks to an open cover, `eq_of_pullback_of_covers`). -/
theorem BR_eq_eraseEmpty_of_pullback_eq [CompactSpace X] (hX : X.IsReducedEquidimensional k)
    (T : BlowUpSequence X)
    (hT : T.pullback (affineCoverDesc X) = BRAffine k (affineCoverScheme X)) :
    BR k X = T.eraseEmpty := by
  have hD : BRDescends k X := ⟨T, hT⟩
  rw [BR_eq_of_descends k X hX hD]
  congr 1
  rcases isEmpty_or_nonempty (finiteAffineCover X).I₀ with hσ | hσ
  · have : IsEmpty X := ⟨fun x => hσ.false ((finiteAffineCover X).idx x)⟩
    apply BlowUpSequence.eq_of_length_eq_of_isEmpty
    have h1 := congrArg BlowUpSequence.length hD.choose_spec
    have h2 := congrArg BlowUpSequence.length hT
    rw [length_pullback] at h1 h2
    exact h1.trans h2.symm
  · refine eq_of_pullback_of_covers hD.choose T (finiteAffineCover X).f
      (fun x => ⟨(finiteAffineCover X).idx x, (finiteAffineCover X).covers x⟩) (fun i => ?_)
    have hi : (finiteAffineCover X).f i =
        Sigma.ι (fun i => (finiteAffineCover X).X i) i ≫ affineCoverDesc X :=
      (ι_comp_affineCoverDesc X i).symm
    rw [hi, pullback_comp, pullback_comp, hD.choose_spec, hT]

end Class

/-- Kollár's resolution functor `BR`, packaged as a `ResolutionFunctor k`: the witness of
`AlgebraicGeometry.exists_functorial_resolution`. -/
noncomputable def BRFunctor : ResolutionAssignment k where
  seq X _ _ _ := BR k X

/-! ### The empty scheme -/

/-- The finite affine cover scheme of an empty scheme is empty. -/
instance isEmpty_affineCoverScheme (X : Scheme.{u}) [IsEmpty X] :
    IsEmpty (affineCoverScheme X) :=
  ⟨fun x' => IsEmpty.false (affineCoverDesc X x')⟩

/-- On an empty scheme, a member of the class, the resolution functor is the empty sequence, on
the nose. -/
theorem BR_empty (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsEmpty X] : BR k X = nil X := by
  have : CompactSpace X := compactSpace_of_quasiCompact_over k X
  by_cases hX : X.IsReducedEquidimensional k
  · by_cases hT : BRDescends k X
    · rw [BR_eq_of_descends k X hX hT]
      have h1 : (hT.choose.pullback (affineCoverDesc X)).length =
          (BRAffine k (affineCoverScheme X)).length :=
        congrArg length hT.choose_spec
      have h2 : (BRAffine k (affineCoverScheme X)).length = 0 := by
        rw [BRAffine_eq_nil_of_isEmpty]
        rfl
      rw [length_pullback] at h1
      have h0 : hT.choose = nil X := Hironaka.Sequence.eq_nil_of_length_eq_zero (h1.trans h2)
      rw [h0]
      rfl
    · exact BR_eq_nil_of_not_descends k X hX hT
  · exact BR_eq_nil_of_not_class k X hX

end Hironaka.Resolution
