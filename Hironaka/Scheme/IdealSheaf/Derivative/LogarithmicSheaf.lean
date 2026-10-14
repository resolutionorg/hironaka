/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicLocalization
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicQuotient
import Hironaka.Scheme.IdealSheaf.Derivative.Properties
import Hironaka.Scheme.IdealSheaf.Derivative.StalkCoords
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.EtaleCoordinates
import Hironaka.Scheme.Smooth.SubschemeStalk
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The logarithmic derivative ideal sheaf: gluing, stalks, restriction, filtration

[Kol07, 87] for the sheaf `D(−log S)(I)` of
`Hironaka/Scheme/IdealSheaf/Derivative/Logarithmic.lean`, on a scheme `f : X ⟶ Spec k`.

* **Gluing** (`ideal_logDerivative`): for `f` locally of finite type,
  `(D(−log S)(I))(U) = D(−log S(U))(I(U))` on every affine open `U`. As for `derivative` of
  `Hironaka/Scheme/IdealSheaf/Derivative/Sheaf.lean`, the family `U ↦ D(−log S(U))(I(U))` is
  compatible with restriction to basic opens (`Γ(D(s)) = Γ(U)_s`, `S(D(s)) = S(U)_s`, `I(D(s)) =
  I(U)_s`, and `D(−log S(U)_s)(I(U)_s) = D(−log S(U))(I(U))_s` by `Ideal.logDerivative_map` of
  `Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicLocalization.lean`, which needs `Ω_{Γ(U)/k}`
  finitely presented and `S(U)` finitely generated: `Γ(U)` is a finitely generated `k`-algebra,
  hence Noetherian), so it is itself an ideal sheaf, the largest one below it.
* **Stalks** (`stalkIdeal_logDerivative`, `stalkIdeal_logDerivativeIter`):
  `(D(−log S)(I))_x = D(−log S_x)(I_x)`, the logarithmic derivations of the stalk being the
  `k`-derivations of `𝒪_{X,x}` preserving `S_x`; the same compatibility for the localization
  `𝒪_{X,x} = Γ(U)_𝔭`.
* **Restriction** ([Kol07, (87.1)]; `logDerivativeIter_comap_subschemeι`):
  `(D^r(−log S)(I))|_S = D^r(I|_S)` as ideal sheaves on `V(S)`, for `X` smooth over `k`. Stalkwise:
  the stalk of `K.comap ι` at `z ∈ V(S)` is `ι^♯(K_{ι z})` (`stalkIdeal_comap`,
  `Hironaka/Scheme/IdealSheaf/StalkIdeal.lean`), the stalk map `𝒪_{X,ι z} → 𝒪_{V(S),z}` is
  surjective with kernel `S_{ι z}` (`ker_stalkMap_subschemeι`,
  `Hironaka/Scheme/Smooth/SubschemeStalk.lean`), `𝒪_{X,ι z}` is formally smooth over `k`
  (`formallySmooth_stalk`, `Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean`), and the
  ring-level `Ideal.logDerivativeIter_map_of_surjective` of
  `Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicQuotient.lean` applies. Only the smoothness of
  `X` is used: the identity holds for every closed subscheme `S`, while Kollár states it for `S`
  smooth.
* **Filtration** ([Kol07, (87.2)]; `logDerivativeIter_derivativeIter_le`,
  `logDerivativeIter_le_derivativeIter`): `D^s(−log S)(I) ⊆ D^{s−1}(−log S)(D(I)) ⊆ ⋯ ⊆ D^s(I)`,
  from `D(−log S)(K) ⊆ D(K)` and the monotonicity of the iterates.

Used for Theorem 88 and Corollary 89 on schemes
(`Hironaka/Scheme/BlowUpSequence/Theorem88Basic.lean`,
`Hironaka/Resolution/Algebraic/Kol07/Theorem88BlowUp.lean`,
`Hironaka/Resolution/Algebraic/Kol07/Theorem88Sequence.lean`,
`Hironaka/Resolution/Algebraic/Kol07/Corollary89.lean`,
`Hironaka/Scheme/BlowUpSequence/TransformLogDerivative.lean`) and on manifolds
(`Hironaka/Manifold/IdealSheaf/LogDerivRestrict.lean`).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (S I : X.IdealSheafData)

/-! ### The filtration, for any `k`-scheme -/

theorem logDerivativeIter_mono (r : ℕ) {I I' : X.IdealSheafData} (h : I ≤ I') :
    logDerivativeIter f S r I ≤ logDerivativeIter f S r I' := by
  induction r with
  | zero => exact h
  | succ r ih =>
    rw [logDerivativeIter_succ, logDerivativeIter_succ]
    exact logDerivative_mono f S ih

theorem logDerivativeIter_succ' (r : ℕ) :
    logDerivativeIter f S (r + 1) I = logDerivativeIter f S r (logDerivative f S I) :=
  Function.iterate_succ_apply _ _ _

/-- [Kol07, (87.2)]: `D^s(−log S)(I) ⊆ D^s(I)`. -/
theorem logDerivativeIter_le_derivativeIter (s : ℕ) :
    logDerivativeIter f S s I ≤ derivativeIter f s I := by
  induction s with
  | zero => rw [logDerivativeIter_zero, derivativeIter_zero]
  | succ s ih =>
    rw [logDerivativeIter_succ, derivativeIter_succ]
    exact (logDerivative_le_derivative f S _).trans (derivative_mono f ih)

/-- [Kol07, (87.2)], one step of the filtration
`D^s(−log S)(I) ⊆ D^{s−1}(−log S)(D(I)) ⊆ ⋯ ⊆ D^s(I)`. -/
theorem logDerivativeIter_derivativeIter_le {s j : ℕ} (hj : j < s) :
    logDerivativeIter f S (s - j) (derivativeIter f j I) ≤
      logDerivativeIter f S (s - (j + 1)) (derivativeIter f (j + 1) I) := by
  obtain ⟨t, ht⟩ : ∃ t, s - j = t + 1 := ⟨s - (j + 1), by omega⟩
  rw [ht, show s - (j + 1) = t by omega, logDerivativeIter_succ', derivativeIter_succ]
  exact logDerivativeIter_mono f S t (logDerivative_le_derivative f S _)

/-! ### The gluing and the stalks, for `f` locally of finite type -/

section FiniteType

variable [LocallyOfFiniteType f]

include f in
/-- For `f` locally of finite type, `Γ(X, U)` is Noetherian on every affine `U`, so every ideal of
sections is finitely generated. -/
theorem ideal_fg (U : X.affineOpens) : (S.ideal U).FG := by
  let _ := f.sectionsAlgebra U.1
  have : Algebra.FiniteType k Γ(X, U.1) := f.finiteType_sectionsAlgebra U.2
  have : IsNoetherianRing Γ(X, U.1) := Algebra.FiniteType.isNoetherianRing k Γ(X, U.1)
  exact IsNoetherian.noetherian _

/-- The family `U ↦ D(−log S(U))(I(U))` is compatible with restriction to basic opens (Mathlib's
`isLocalization_basicOpen`, `map_ideal_basicOpen`, and `Ideal.logDerivative_map`). -/
theorem map_logDerivative_ideal_basicOpen (U : X.affineOpens) (s : Γ(X, U)) :
    (letI := f.sectionsAlgebra U.1; Ideal.logDerivative k (S.ideal U) (I.ideal U)).map
        (X.presheaf.map (homOfLE <| X.basicOpen_le s).op).hom =
      letI := f.sectionsAlgebra (X.affineBasicOpen s).1
      Ideal.logDerivative k (S.ideal (X.affineBasicOpen s)) (I.ideal (X.affineBasicOpen s)) := by
  let _ := f.sectionsAlgebra U.1
  let _ := f.sectionsAlgebra (X.basicOpen s)
  have hloc : IsLocalization.Away s Γ(X, X.basicOpen s) := U.2.isLocalization_basicOpen s
  have hST : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen s) := by
    have h := isScalarTower_sectionsAlgebra_restrict f (X.basicOpen_le s)
    exact h
  have hFP := finitePresentation_kaehlerDifferential_sections f U
  rw [← S.map_ideal_basicOpen U s, ← I.map_ideal_basicOpen U s]
  exact (@Ideal.logDerivative_map k _ _ _ _ _ _ _ _ hST (Submonoid.powers s) hloc hFP _
    (ideal_fg f S U) (I.ideal U)).symm

/-- The gluing ([Kol07, 87] for the sheaf): for `f` locally of finite type,
`(D(−log S)(I))(U) = D(−log S(U))(I(U))` on every affine open. -/
theorem ideal_logDerivative (U : X.affineOpens) :
    (logDerivative f S I).ideal U =
      letI := f.sectionsAlgebra U.1; Ideal.logDerivative k (S.ideal U) (I.ideal U) := by
  refine le_antisymm (ideal_logDerivative_le f S I U) ?_
  let J : X.IdealSheafData :=
    { ideal := fun U => letI := f.sectionsAlgebra U.1; Ideal.logDerivative k (S.ideal U) (I.ideal U)
      map_ideal_basicOpen := fun U s => map_logDerivative_ideal_basicOpen f S I U s }
  have hJ : J ≤ logDerivative f S I := le_ofIdeals_iff.mpr le_rfl
  exact hJ U

/-- The stalk of `D(−log S)(I)` at `x` is the logarithmic derivative of the stalk `I_x` for the
`k`-derivations of `𝒪_{X,x}` preserving `S_x`. -/
theorem stalkIdeal_logDerivative (x : X) :
    (logDerivative f S I).stalkIdeal x =
      letI := f.stalkAlgebra x
      Ideal.logDerivative k (S.stalkIdeal x) (I.stalkIdeal x) := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  let _ := f.sectionsAlgebra U.1
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have hloc := U.2.isLocalization_stalk ⟨x, hxU⟩
  have hST := f.isScalarTower_sectionsAlgebra_stalk U.1 hxU
  have hFP := finitePresentation_kaehlerDifferential_sections f U
  rw [stalkIdeal_eq_map_germ _ U hxU, stalkIdeal_eq_map_germ S U hxU,
    stalkIdeal_eq_map_germ I U hxU, ideal_logDerivative f S I U]
  exact (@Ideal.logDerivative_map k _ _ _ _ _ _ _ _ hST _ hloc hFP _ (ideal_fg f S U)
    (I.ideal U)).symm

/-- `(D^r(−log S)(I))_x = D^r(−log S_x)(I_x)`. -/
theorem stalkIdeal_logDerivativeIter (r : ℕ) (x : X) :
    (logDerivativeIter f S r I).stalkIdeal x =
      letI := f.stalkAlgebra x
      Ideal.logDerivativeIter k (S.stalkIdeal x) r (I.stalkIdeal x) := by
  let _ := f.stalkAlgebra x
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [logDerivativeIter_succ, stalkIdeal_logDerivative, ih, Ideal.logDerivativeIter_succ]

end FiniteType

/-! ### Restriction to `S` ([Kol07, (87.1)]) -/

section Restriction

variable (n : ℕ) [SmoothOfRelativeDimension n f]

include n

/-- [Kol07, (87.1)]: `(D^r(−log S)(I))|_S = D^r(I|_S)` as ideal sheaves on `V(S)`, the
restriction being the inverse image along the closed immersion `ι : V(S) ⟶ X`.
Stalkwise at `z ∈ V(S)`: the stalk map `ι^♯ : 𝒪_{X,ι z} → 𝒪_{V(S),z}` is surjective with kernel
`S_{ι z}`, and `ι^♯(D^r(−log S_{ι z})(I_{ι z})) = D^r(ι^♯ I_{ι z})` because `𝒪_{X,ι z}` is formally
smooth over `k`. Only the smoothness of `X` is used: the identity holds for every closed subscheme
`S` (Kollár states it for `S` smooth). -/
theorem logDerivativeIter_comap_subschemeι (r : ℕ) :
    (logDerivativeIter f S r I).comap S.subschemeι =
      (I.comap S.subschemeι).derivativeIter (S.subschemeι ≫ f) r := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  refine AlgebraicGeometry.Scheme.IdealSheafData.ext_stalkIdeal fun z => ?_
  let _ := f.stalkAlgebra (S.subschemeι z)
  let _ := (S.subschemeι ≫ f).stalkAlgebra z
  have hfs : Algebra.FormallySmooth k (X.presheaf.stalk (S.subschemeι z)) :=
    formallySmooth_stalk f n _
  have hψ : Function.Surjective (S.subschemeι.stalkMap z).hom := S.subschemeι.stalkMap_surjective z
  have hker : RingHom.ker (S.subschemeι.stalkMap z).hom = S.stalkIdeal (S.subschemeι z) :=
    ker_stalkMap_subschemeι S z
  rw [stalkIdeal_comap, stalkIdeal_derivativeIter, stalkIdeal_comap, stalkIdeal_logDerivativeIter,
    ← hker]
  exact Ideal.logDerivativeIter_map_of_surjective' (S.subschemeι.stalkMap z).hom
    (stalkMap_subschemeι_algebraMap S f z) hψ r _

end Restriction

end AlgebraicGeometry.Scheme.IdealSheafData
