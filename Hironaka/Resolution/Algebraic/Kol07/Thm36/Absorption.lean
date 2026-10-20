/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.IdealSheaf.Invertible
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# A generic point of codimension at least two is absorbed by some centre

In the proof of [Kol07, Corollary 22] the ideal sheaf `I` of `X`, of codimension `≥ 2`, is not
locally principal at `η_X`, so "some blow-up center must contain `η_X`". This file proves
the statement in a general form, per generic point and without integrality of `V(I)`, as the
embedded desingularization needs it for each component of a reducible subscheme: for a blow-up
sequence `S` on a locally Noetherian scheme `A` whose composite makes `I` invertible (clause (2) of
[Kol07, Theorem 35], a hypothesis here), and a generic point `η` of an irreducible component of
`V(I)` with `dim 𝒪_{A,η} ≥ 2`, some centre of `S` has a point over `η`.

Proof. If no centre had a point over `η`, each blow-up would be an isomorphism near the unique
point over `η` (`isIso_stalkMap_π_of_notMem_support`), so the stalk map of the composite at the
point `η'` over `η` would be an isomorphism `𝒪_{A,η} ≅ 𝒪_{A_r,η'}` carrying `I_η` to the stalk
of `I·𝒪_{A_r}`, which is principal since `I·𝒪_{A_r}` is invertible. So `I_η` would be principal;
the maximal ideal `𝔪_η` is a minimal prime over `I_η` (`η` being a generic point of a component of
`V(I)`), hence of height `≤ 1` by Krull's principal ideal theorem, that is, `dim 𝒪_{A,η} ≤ 1`,
against the hypothesis.

For an integral `V(I)` the conclusion is sharpened to the existence of a centre containing the
whole strict transform (`exists_centerContains_of_isInvertible_comap_composite`): at the least
centre with a point over `η`, that point is the generic point of the strict transform
(`Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral`), so the centre's support contains the
whole reduced irreducible strict transform and the ideal inequality `CenterContains` follows. The
embedded form `exists_centerContains_BP_of_isInvertible`, for the principalization sequence of the
ambient triple, is the input of `Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence IsLocalRing

namespace Hironaka.Resolution

variable {A : Scheme.{u}}

/-! ### No center over `η`: the composite is a local isomorphism at the unique point over `η` -/

/-- If no center of `S` has a point over `η`, then at every stage there is a unique point `η'` over
`η`, and the stage map is an isomorphism of stalks at it (each blow-up is an isomorphism off its
center). Structural recursion on the sequence, ℕ-indexed. -/
theorem exists_unique_stageMap_eq_and_isIso_stalkMap_of_forall_notMem_mk (S : BlowUpSequence A)
    {η : A}
    (h : ∀ (n : ℕ) (hn : n < S.length) (y : S.stage ⟨n, Nat.lt_succ_of_lt hn⟩),
      S.stageMap ⟨n, Nat.lt_succ_of_lt hn⟩ y = η → y ∉ (S.center ⟨n, hn⟩).support)
    (n : ℕ) (hn : n < S.length + 1) :
    ∃ η' : S.stage ⟨n, hn⟩, S.stageMap ⟨n, hn⟩ η' = η ∧
      (∀ y, S.stageMap ⟨n, hn⟩ y = η → y = η') ∧ IsIso ((S.stageMap ⟨n, hn⟩).stalkMap η') := by
  induction S generalizing n with
  | nil X =>
    have h0 : (nil X).length = 0 := rfl
    obtain rfl : n = 0 := by omega
    refine ⟨η, rfl, fun y hy => hy, ?_⟩
    change IsIso ((𝟙 X : X ⟶ X).stalkMap η)
    exact isIso_stalkMap_id X η
  | cons X D rest ih =>
    cases n with
    | zero =>
      refine ⟨η, rfl, fun y hy => hy, ?_⟩
      change IsIso ((𝟙 X : X ⟶ X).stalkMap η)
      exact isIso_stalkMap_id X η
    | succ n =>
      -- the center `D` has no point over `η`: `η ∉ V(D)`
      have hηD : η ∉ D.support := h 0 (Nat.succ_pos _) η rfl
      obtain ⟨η₁, hη₁, huniq₁⟩ :=
        IdealSheafData.blowUp.existsUnique_preimage_of_notMem_support D hηD
      -- the hypothesis for `rest` at `η₁`
      have hrest : ∀ (m : ℕ) (hm : m < rest.length) (y : rest.stage ⟨m, Nat.lt_succ_of_lt hm⟩),
          rest.stageMap ⟨m, Nat.lt_succ_of_lt hm⟩ y = η₁ → y ∉ (rest.center ⟨m, hm⟩).support := by
        intro m hm y hy
        have := h (m + 1) (Nat.succ_lt_succ hm) y
        exact this (by
          change IdealSheafData.blowUpπ D (rest.stageMap ⟨m, Nat.lt_succ_of_lt hm⟩ y) = η
          rw [hy, hη₁])
      obtain ⟨η', hmap', huniq', hiso'⟩ := ih hrest n (Nat.lt_of_succ_lt_succ hn)
      refine ⟨η', ?_, fun y hy => ?_, ?_⟩
      · change IdealSheafData.blowUpπ D (rest.stageMap ⟨n, Nat.lt_of_succ_lt_succ hn⟩ η') = η
        rw [hmap', hη₁]
      · change IdealSheafData.blowUpπ D (rest.stageMap ⟨n, Nat.lt_of_succ_lt_succ hn⟩ y) = η at hy
        exact huniq' y (huniq₁ _ hy)
      · -- the stalk map of `rest.stageMap ≫ π` at `η'` is the composite of two isomorphisms
        have hnot : rest.stageMap ⟨n, Nat.lt_of_succ_lt_succ hn⟩ η' ∉
            (D.comap (IdealSheafData.blowUpπ D)).support := by
          rw [mem_support_comap_iff_apply, hmap', hη₁]
          exact hηD
        have hπ : IsIso ((IdealSheafData.blowUpπ D).stalkMap
            (rest.stageMap ⟨n, Nat.lt_of_succ_lt_succ hn⟩ η')) :=
          isIso_stalkMap_π_of_notMem_support D hnot
        change IsIso ((rest.stageMap ⟨n, Nat.lt_of_succ_lt_succ hn⟩ ≫ D.blowUpπ).stalkMap η')
        rw [Scheme.Hom.stalkMap_comp]
        exact @IsIso.comp_isIso _ _ _ _ _ _ _ hπ hiso'

/-! ### The algebra: a principal `I_η` at a generic point of a component forces `dim ≤ 1` -/

/-- Krull's principal ideal theorem at a generic point of a component of `V(I)`: if the stalk `I_η`
is principal then `dim 𝒪_{A,η} ≤ 1`, the maximal ideal `𝔪_η` being a minimal prime over `I_η`
(`stalkIdeal_vanishingIdeal_mem_minimalPrimes` at `x = η`), hence of height `≤ 1`. -/
theorem ringKrullDim_stalk_le_one_of_isPrincipal_stalkIdeal [IsLocallyNoetherian A]
    (I : A.IdealSheafData) {η : A} (hη : η ∈ I.support.genericPoints)
    (hprin : (I.stalkIdeal η).IsPrincipal) : ringKrullDim (A.presheaf.stalk η) ≤ 1 := by
  have hmin : maximalIdeal (A.presheaf.stalk η) ∈ (I.stalkIdeal η).minimalPrimes := by
    have := stalkIdeal_vanishingIdeal_mem_minimalPrimes I hη (specializes_refl η)
    rwa [Hironaka.BMO.stalkIdeal_vanishingIdeal_closure_self] at this
  have hht : (maximalIdeal (A.presheaf.stalk η)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (I.stalkIdeal η) _ hmin
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast hht

/-! ### The absorption -/

/-- The absorption of a generic point of codimension `≥ 2` [Kol07, Corollary 22, proof], general
form: on a locally Noetherian scheme, if the composite of the blow-up sequence `S` makes `I`
invertible (clause (2) of [Kol07, Theorem 35] as a hypothesis) and `η` is a generic point of an
irreducible component of `V(I)` with `dim 𝒪_{A,η} ≥ 2`, then some centre of `S` has a point over
`η`. -/
theorem exists_mem_center_support_of_isInvertible_comap_stageMap_last [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) {η : A} (hη : η ∈ I.support.genericPoints)
    (hdim : 2 ≤ ringKrullDim (A.presheaf.stalk η))
    (hinv : (I.comap (S.stageMap (Fin.last _))).IsInvertible) :
    ∃ (i : Fin S.length) (y : S.stage i.castSucc),
      S.stageMap i.castSucc y = η ∧ y ∈ (S.center i).support := by
  by_contra hno
  have h : ∀ (n : ℕ) (hn : n < S.length) (y : S.stage ⟨n, Nat.lt_succ_of_lt hn⟩),
      S.stageMap ⟨n, Nat.lt_succ_of_lt hn⟩ y = η → y ∉ (S.center ⟨n, hn⟩).support :=
    fun n hn y hy hmem => hno ⟨⟨n, hn⟩, y, hy, hmem⟩
  obtain ⟨η', hmap, -, hiso⟩ :=
    exists_unique_stageMap_eq_and_isIso_stalkMap_of_forall_notMem_mk S h S.length
      (Nat.lt_succ_self _)
  -- read at `Fin.last` (definitionally `⟨S.length, _⟩`), and replace `η` by `Π η'` throughout
  have hmap' : S.stageMap (Fin.last S.length) η' = η := hmap
  have hiso' : IsIso ((S.stageMap (Fin.last S.length)).stalkMap η') := hiso
  clear hmap hiso h hno
  subst hmap'
  set f := S.stageMap (Fin.last S.length) with hf
  -- the stalk of the invertible `I·𝒪_{A_r}` at `η'` is principal
  obtain ⟨g, -, hg⟩ := hinv.exists_ne_zero_stalkIdeal_eq_span η'
  -- transport along the stalk isomorphism: `I_{f η'}` is principal
  have hcomap : (I.comap f).stalkIdeal η' = (I.stalkIdeal (f η')).map (f.stalkMap η').hom :=
    IdealSheafData.stalkIdeal_comap I f η'
  let e : A.presheaf.stalk (f η') ≃+* (S.stage (Fin.last S.length)).presheaf.stalk η' :=
    (asIso (f.stalkMap η')).commRingCatIsoToRingEquiv
  have he : e.toRingHom = (f.stalkMap η').hom := by
    rw [RingEquiv.toRingHom_eq_coe]
    exact CategoryTheory.Iso.commRingCatIsoToRingEquiv_toRingHom _
  have h1 : (I.stalkIdeal (f η')).map e.toRingHom = Ideal.span {g} := by
    rw [he, ← hcomap, hg]
  have h2 : I.stalkIdeal (f η') =
      ((I.stalkIdeal (f η')).map e.toRingHom).map e.symm.toRingHom := by
    rw [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id]
  have hprin : (I.stalkIdeal (f η')).IsPrincipal :=
    ⟨⟨e.symm g, by rw [h2, h1, Ideal.map_span, Set.image_singleton]; rfl⟩⟩
  have hle := ringKrullDim_stalk_le_one_of_isPrincipal_stalkIdeal I hη hprin
  have : (2 : WithBot ℕ∞) ≤ 1 := hdim.trans hle
  exact absurd this (by decide)

/-! ### From a center with a point over `η` to a center containing the strict transform -/

/-- From a centre with a point over the generic point to a centre containing the strict transform
[Kol07, Corollary 22, proof], for an integral `V(I)`: if some centre has a point over the generic
point `η` of `V(I)`, the least such centre contains the whole strict transform `X̄_n`. Before it no
centre contains the strict transform (its generic point `η_m` lies over `η`), so the point over
`η` at stage `n` is `η_n`, and `X̄_n = closure {η_n} ⊆ Z_n` gives the ideal inequality
`CenterContains S I n` (`le_of_support_subset`, `X̄_n` being reduced). -/
theorem exists_centerContains_of_exists_mem_center_support [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) [IsIntegral I.subscheme] {η : A}
    (hη : IsGenericPoint η (I.support : Set A))
    (h : ∃ (i : Fin S.length) (y : S.stage i.castSucc),
      S.stageMap i.castSucc y = η ∧ y ∈ (S.center i).support) :
    ∃ n, CenterContains S I n := by
  classical
  have hex : ∃ n, ∃ (hn : n < S.length) (y : S.stage ⟨n, Nat.lt_succ_of_lt hn⟩),
      S.stageMap ⟨n, Nat.lt_succ_of_lt hn⟩ y = η ∧ y ∈ (S.center ⟨n, hn⟩).support := by
    obtain ⟨⟨n, hn⟩, y, hy, hmem⟩ := h
    exact ⟨n, hn, y, hy, hmem⟩
  obtain ⟨hn, y, hy, hmem⟩ := Nat.find_spec hex
  set n := Nat.find hex with hn_def
  have hX : IsLocallyNoetherian A := inferInstance
  have hJ : IsIntegral I.subscheme := inferInstance
  have hred : IsReduced I.subscheme := inferInstance
  -- before `n`, no center contains the strict transform
  have hbefore : ∀ m (hm : m < n),
      ¬ S.center ⟨m, lt_trans hm hn⟩ ≤
        S.strictTransformSeq I ⟨m, Nat.lt_succ_of_lt (lt_trans hm hn)⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm hle
      have hprev : ∀ m' (hm' : m' < m),
          ¬ S.center ⟨m', lt_trans hm' (lt_trans hm hn)⟩ ≤
            S.strictTransformSeq I ⟨m', Nat.lt_succ_of_lt (lt_trans hm' (lt_trans hm hn))⟩ :=
        fun m' hm' => ih m' hm' (lt_trans hm' hm)
      obtain ⟨η', hgen, hmap, -⟩ :=
        exists_isGenericPoint_strictTransformSeq_mk hX S I hη hred m
          (Nat.lt_succ_of_lt (lt_trans hm hn)) hprev
      have hmemZ : η' ∈ (S.center ⟨m, lt_trans hm hn⟩).support :=
        IdealSheafData.support_antitone hle hgen.mem
      exact Nat.find_min hex hm ⟨lt_trans hm hn, η', hmap, hmemZ⟩
  -- at `n`, the center point over `η` is the generic point of `X̄_n`
  obtain ⟨η', hgen, -, huniq⟩ :=
    exists_isGenericPoint_strictTransformSeq_mk hX S I hη hred n (Nat.lt_succ_of_lt hn) hbefore
  have hint : IsIntegral (S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn⟩).subscheme :=
    isIntegral_strictTransformSeq_mk hX S I hJ n (Nat.lt_succ_of_lt hn) hbefore
  obtain rfl : y = η' := huniq y hy
  refine ⟨n, hn, ?_⟩
  refine le_of_support_subset _ _ ?_
  rw [← hgen.def]
  exact closure_minimal (Set.singleton_subset_iff.mpr hmem) (S.center ⟨n, hn⟩).support.isClosed

/-! ### The absorption lemma in the `composite` form and the assembly -/

/-- A generic point of an irreducible closed subset is one of its generic points in the sense of
`Closeds.genericPoints` (the points maximal for specialisation). -/
theorem mem_genericPoints_of_isGenericPoint {Z : Closeds A} {η : A}
    (hη : IsGenericPoint η (Z : Set A)) : η ∈ Z.genericPoints :=
  ⟨hη.mem, fun _ hη' hsp => (hsp.antisymm (hη.specializes hη')).eq⟩

/-- The absorption of a generic point in the form used by the embedded desingularization
[Kol07, Corollary 22, proof]: at a generic point `η` of `V(I)` where `𝒪_{A,η}` has dimension
`≥ 2`, if the pullback `Π^* I` along the composite `Π` of `S` is invertible, some centre of `S` has
a point over `η`. Neither `A` nor `V(I)` need be integral. -/
theorem exists_mem_center_support_of_isInvertible_comap_composite [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) {η : A} (hη : η ∈ I.support.genericPoints)
    (hdim : 2 ≤ ringKrullDim (A.presheaf.stalk η)) (hinv : (I.comap S.composite).IsInvertible) :
    ∃ (i : Fin S.length) (y : S.stage i.castSucc),
      S.stageMap i.castSucc y = η ∧ y ∈ (S.center i).support :=
  exists_mem_center_support_of_isInvertible_comap_stageMap_last S I hη hdim hinv

/-- The absorption assembled for an integral `V(I)` [Kol07, Corollary 22, proof]: if the pullback
`Π^* I` along the composite of `S` is invertible (clause (2) of [Kol07, Theorem 35] for the
principalization sequence) and `V(I)` has codimension `≥ 2` at its generic point, some centre of
`S` contains the strict transform of `V(I)` at its stage. -/
theorem exists_centerContains_of_isInvertible_comap_composite [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) [IsIntegral I.subscheme] {η : A}
    (hη : IsGenericPoint η (I.support : Set A)) (hdim : 2 ≤ ringKrullDim (A.presheaf.stalk η))
    (hinv : (I.comap S.composite).IsInvertible) : ∃ n, CenterContains S I n :=
  exists_centerContains_of_exists_mem_center_support S I hη
    (exists_mem_center_support_of_isInvertible_comap_composite S I
      (mem_genericPoints_of_isGenericPoint hη) hdim hinv)

/-! ### The embedded situation `X ↪ A` -/

section Embedded

variable {X : Scheme.{u}} (emb : X ⟶ A) [IsClosedImmersion emb]

/-- The scheme-theoretic image of a closed immersion of an integral scheme is integral (the image
is isomorphic to the source, Mathlib's `Scheme.Hom.toImage`). -/
theorem isIntegral_image [IsIntegral X] : IsIntegral emb.image := by
  have : Nonempty emb.image := ⟨emb.toImage (Nonempty.some inferInstance)⟩
  have : IsOpenImmersion (inv emb.toImage) := IsOpenImmersion.of_isIso _
  exact isIntegral_of_isOpenImmersion (inv emb.toImage)

/-- The image of the generic point of an irreducible `X` under a closed immersion is a generic point
of the support of its kernel `V(I_X)`. -/
theorem isGenericPoint_ker_support [IrreducibleSpace X] :
    IsGenericPoint (emb (genericPoint X)) (emb.ker.support : Set A) := by
  rw [isGenericPoint_def, ← Set.image_singleton, emb.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ, Scheme.Hom.support_ker,
    emb.isClosedEmbedding.isClosed_range.closure_eq]

/-- The generic point of an irreducible scheme is one of its generic points (Mathlib's
`genericPoints`, the set over which the codimension hypothesis is stated). -/
theorem genericPoint_mem_genericPoints [IrreducibleSpace X] : genericPoint X ∈ genericPoints X := by
  rw [genericPoints_eq_singleton]
  exact Set.mem_singleton _

variable {k : Type u} [Field k] [CharZero k]

/-- The absorption for the ambient triple `TA = (A, I_X, E)` of an integral closed subscheme
`X ↪ A` of codimension `≥ 2` at its generic point, with clause (2) of [Kol07, Theorem 35] as the
hypothesis (`Π^* I_X` is the ideal of a simple normal crossing divisor, hence invertible): some
centre of `BP TA` contains the strict transform of `X`. The boundary plays no role, the argument
being local at `η_X`. -/
theorem exists_centerContains_BP_of_isInvertible (TA : Triple k) (emb : X ⟶ TA.X.left)
    [IsClosedImmersion emb] [IsIntegral X] (hI : emb.ker = TA.I)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η)))
    (hinv : (TA.I.comap (Hironaka.Sequence.BP TA).composite).IsInvertible) :
    ∃ n, CenterContains (Hironaka.Sequence.BP TA) TA.I n := by
  have : IsLocallyNoetherian TA.X.left :=
    (TA.X.left ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  rw [← hI] at hinv ⊢
  have : IsIntegral emb.ker.subscheme := isIntegral_image emb
  exact exists_centerContains_of_isInvertible_comap_composite (Hironaka.Sequence.BP TA) emb.ker
    (isGenericPoint_ker_support emb) (hcodim _ genericPoint_mem_genericPoints) hinv

end Embedded

end Hironaka.Resolution
