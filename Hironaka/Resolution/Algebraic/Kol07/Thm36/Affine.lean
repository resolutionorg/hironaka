/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization
public import Hironaka.Scheme.BlowUpSequence.Truncate
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The resolution of an embedded affine scheme

Kollár constructs the resolution `BR(X)` of an affine scheme `X` from a closed embedding `X ↪ A`
into a smooth affine scheme with `dim A ≥ dim X + 2` and the principalization sequence
`BP(A, I_X, ∅)` of the ideal of `X` [Kol07, Theorem 36, first paragraph of the proof]. The proof
of [Kol07, Corollary 22] says how: since `I_X` is not locally principal at the generic point
`η_X` of `X`, some centre of `BP(A, I_X, ∅)` contains `η_X`; for the first such index `j` the
composite `π_0 ⋯ π_{j-1}` is a local isomorphism near `η_X`, `η_X` is the generic point of the
centre `Z_j`, and `π_0 ⋯ π_{j-1} : Z_j → X̄` is the resolution. As [Kol07, Warning 23] remarks,
this exhibits the resolution as the composite of the blow-ups of `X` with centres `Z_i ∩ X_i`,
`i < j`, that is, as the restriction of the truncated sequence to the closed subscheme `X` in the
sense of [Kol07, Definition 30, 30.2], realised here as the pullback of the sequence along the
closed immersion (the stage embeddings `X_i ↪ A_i` are closed immersions with kernel the strict
transform of `X`).

## Main definitions

* `CenterContains S I n`: the centre at position `n` of the blow-up sequence `S` contains the
  strict transform of `V(I)` at that stage, as closed subschemes of the stage.
* `firstCenterIndex S I`: the first index `j` at which the centre of `S` contains the strict
  transform of `V(I)`, or `S.length` if there is none.
* `BR_affine TA emb`: for a triple `TA = (A, I_X, ∅)` and a closed immersion `emb : X ⟶ A`, the
  restriction to `X` of the first `firstCenterIndex (BP TA) TA.I` steps of `BP TA`.

## Conventions

The truncation is essential. Restricting the whole sequence to `X` would give an empty end
result: at step `j` the centre contains the strict transform `X̄_j` of `X`, so the restricted
centre is all of `X̄_j`, and the strict transform of `X̄_j` under its own blow-up is empty, whereas
Kollár's `BR(X)` stops at `j` with end result `X̄_j`. The hypotheses under which `BR_affine`
realises clauses (1)–(3) of [Kol07, Theorem 36] (`X` integral, `E = ∅`, `I_X = ker emb`,
codimension `≥ 2` at the generic point) are the hypotheses of the theorems that establish those
clauses for it later in this directory; the definition itself needs none of them.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme Hironaka BlowUpSequence

namespace Hironaka.Resolution

variable {A : Scheme.{u}}

/-- The centre at position `n` of the blow-up sequence `S` contains the strict transform of `V(I)`
at that stage, as closed subschemes of `S.stage n` (the centre's ideal is contained in the strict
transform's): "some blow-up center must contain `η_X`" in the proof of [Kol07, Corollary 22]. -/
def CenterContains (S : BlowUpSequence A) (I : A.IdealSheafData) (n : ℕ) : Prop :=
  ∃ hn : n < S.length, S.center ⟨n, hn⟩ ≤ S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn⟩

open Classical in
/-- The first index `n` at which the centre of `S` contains the strict transform of `V(I)`
(`CenterContains S I n`), or `S.length` if there is none: the index `j` of the proof of
[Kol07, Corollary 22]: the unique `j` such that `π_0 ⋯ π_{j−1}` is a local isomorphism around
`η_X` while the centre `Z_j` of `π_j` contains `η_X`. -/
noncomputable def firstCenterIndex (S : BlowUpSequence A) (I : A.IdealSheafData) : ℕ :=
  if h : ∃ n, CenterContains S I n then Nat.find h else S.length

open Classical in
theorem firstCenterIndex_of_exists {S : BlowUpSequence A} {I : A.IdealSheafData}
    (h : ∃ n, CenterContains S I n) : CenterContains S I (firstCenterIndex S I) := by
  unfold firstCenterIndex
  rw [dite_eq_left h]
  exact Nat.find_spec h

open Classical in
theorem not_centerContains_of_lt_firstCenterIndex {S : BlowUpSequence A} {I : A.IdealSheafData}
    (h : ∃ n, CenterContains S I n) {n : ℕ} (hn : n < firstCenterIndex S I) :
    ¬ CenterContains S I n := by
  unfold firstCenterIndex at hn
  rw [dite_eq_left h] at hn
  exact Nat.find_min h hn

theorem firstCenterIndex_lt_length {S : BlowUpSequence A} {I : A.IdealSheafData}
    (h : ∃ n, CenterContains S I n) : firstCenterIndex S I < S.length :=
  (firstCenterIndex_of_exists h).1

open Classical in
theorem firstCenterIndex_le_length (S : BlowUpSequence A) (I : A.IdealSheafData) :
    firstCenterIndex S I ≤ S.length := by
  unfold firstCenterIndex
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

variable {k : Type u} [Field k] [CharZero k]

/-- The resolution of an affine scheme `X` embedded in the ambient of the triple `TA = (A, I, ∅)`
by the closed immersion `emb : X ⟶ A` [Kol07, Theorem 36, proof; Corollary 22, proof;
Warning 23]: the restriction to `X` (the pullback along `emb`, [Kol07, Definition 30, 30.2]) of
the first `firstCenterIndex (BP TA) TA.I` steps of the principalization sequence `BP TA` of the
ideal `TA.I`. -/
noncomputable def BR_affine (TA : Triple k) {X : Scheme.{u}} (emb : X ⟶ TA.X.left) :
    BlowUpSequence X :=
  ((Hironaka.Sequence.BP TA).take
    (firstCenterIndex (Hironaka.Sequence.BP TA) TA.I)).pullback emb

theorem BR_affine_eq (TA : Triple k) {X : Scheme.{u}} (emb : X ⟶ TA.X.left) :
    BR_affine TA emb =
      ((Hironaka.Sequence.BP TA).take
        (firstCenterIndex (Hironaka.Sequence.BP TA) TA.I)).pullback emb := rfl

/-- The length of `BR(X)` is the first-centre index (bounded by the length of `BP TA`). -/
theorem length_BR_affine (TA : Triple k) {X : Scheme.{u}} (emb : X ⟶ TA.X.left) :
    (BR_affine TA emb).length =
      min (firstCenterIndex (Hironaka.Sequence.BP TA) TA.I) (Hironaka.Sequence.BP TA).length := by
  rw [BR_affine, length_pullback, length_take]

end Hironaka.Resolution
