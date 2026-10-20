/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Model
import Hironaka.AnalyticSpace.Manifold.FullyFaithful
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The shear isomorphism of Kollár's Lemma 39, and the equivalence of two embeddings

Kollár's Lemma 39 [Kol07, Lemma 39]: for two closed embeddings `i₁ : Y ↪ 𝕜ⁿ`, `i₂ : Y ↪ 𝕜ᵐ` of
one piece, the paddings `(i₁, 0)` and `(0, i₂)` into `𝕜ⁿ⁺ᵐ` are equivalent under a (nonlinear)
automorphism. The proof extends `i₂` to `j₂ : 𝕜ⁿ → 𝕜ᵐ` and `i₁` to `j₁ : 𝕜ᵐ → 𝕜ⁿ` and uses the
two shears `Φ₂ (x, y) = (x, y + j₂ x)` and `Φ₁ (x, y) = (x + j₁ y, y)`, each carrying one padding
onto the image of `(i₁, i₂)` [Kol07, Lemma 39, proof]; analytically the extensions exist only
locally, so the composite `Φ₁⁻¹ ∘ Φ₂` carries the paddings into each other near any point, with
the local lifts `j₂`, `j₁` of `PieceLemma39Model.lean`. This module provides:

* the bookkeeping of partial analytic isomorphisms — membership in the source and target of a
  composite, the restriction of a partial analytic isomorphism to an analytic isomorphism from
  its source onto its target (`partialDiffeomorphToDiffeomorph`);
* the coordinates of the paddings: `pieceCoord (padExt σ w) = extend σ (pieceCoord w) 0`;
* **the shear isomorphism** `Ψₐ = chart₂⁻¹ ∘ (Φ₂.trans Φ₁.symm) ∘ chart₁` between the two padded
  ambients, its source and target, and the point condition `Ψₐ (i₁(y), 0) = (0, i₂(y))`
  ;
* **the ideal identity** at the embedded points (the kernel argument: both stalk ideals are the
  kernels of the padded stalk maps `ε ∘ s^*`, which `Ψₐ^*` interchanges by the coordinate
  identities of the lifts) and off them (`⊤ = ⊤`, the embedded points of the two paddings
  corresponding under `Ψₐ`);
* the theorem `embeddings_equivalent_under_automorphism`, the analytic form of Lemma 39.

Włodarczyk's counterpart is the commutation of the resolution of a marked ideal with closed
embeddings of the ambient manifold [Wlo09, §7.1]. The proofs are routine.
-/

@[expose] public section

open TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Manifold ContDiff Topology

universe u

noncomputable section

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### Partial analytic isomorphisms: composites, sources, targets, restriction -/

section PartialDiffeo

variable {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E'' P]

theorem partialDiffeomorph_trans_apply (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') M N ω)
    (Ψ : PartialDiffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E'') N P ω) (z : M) : (Φ.trans Ψ) z = Ψ (Φ z) := rfl

theorem partialDiffeomorph_trans_symm_apply (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') M N ω)
    (Ψ : PartialDiffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E'') N P ω) (w : P) :
    (Φ.trans Ψ).symm w = Φ.symm (Ψ.symm w) := rfl

theorem mem_partialDiffeomorph_trans_source (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') M N ω)
    (Ψ : PartialDiffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E'') N P ω) (z : M) :
    z ∈ (Φ.trans Ψ).source ↔ z ∈ Φ.source ∧ Φ z ∈ Ψ.source := by
  change z ∈ (Φ.toOpenPartialHomeomorph.trans Ψ.toOpenPartialHomeomorph).source ↔ _
  rw [OpenPartialHomeomorph.trans_source]
  rfl

theorem mem_partialDiffeomorph_trans_target (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') M N ω)
    (Ψ : PartialDiffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E'') N P ω) (w : P) :
    w ∈ (Φ.trans Ψ).target ↔ w ∈ Ψ.target ∧ Ψ.symm w ∈ Φ.target := by
  change w ∈ (Φ.toOpenPartialHomeomorph.trans Ψ.toOpenPartialHomeomorph).target ↔ _
  rw [OpenPartialHomeomorph.trans_target]
  rfl

theorem mem_partialDiffeomorph_symm_source (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') M N ω)
    (w : N) : w ∈ Φ.symm.source ↔ w ∈ Φ.target := Iff.rfl

theorem mem_partialDiffeomorph_symm_target (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') M N ω)
    (z : M) : z ∈ Φ.symm.target ↔ z ∈ Φ.source := Iff.rfl

end PartialDiffeo

section Restrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M N : AnalyticManifold.{u} 𝕜 E}

/-- A partial analytic isomorphism `Ψ : M ⇀ N` between analytic manifolds, as an analytic
isomorphism from its source onto its target (the restrictions `M|source`, `N|target`). -/
def partialDiffeomorphToDiffeomorph (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (M.restrict ⟨Ψ.source, Ψ.open_source⟩)
      (N.restrict ⟨Ψ.target, Ψ.open_target⟩) ω where
  toFun z := ⟨Ψ z.1, Ψ.toPartialEquiv.map_source z.2⟩
  invFun w := ⟨Ψ.symm w.1, Ψ.toPartialEquiv.map_target w.2⟩
  left_inv z := Subtype.ext (Ψ.toPartialEquiv.left_inv z.2)
  right_inv w := Subtype.ext (Ψ.toPartialEquiv.right_inv w.2)
  contMDiff_toFun :=
    (AnalyticSpace.KLocallyRingedSpace.contMDiff_subtypeVal_comp_iff'
      (U := ⟨Ψ.target, Ψ.open_target⟩) _).mp
      (Ψ.contMDiffOn_toFun.comp_contMDiff contMDiff_subtype_val fun z => z.2)
  contMDiff_invFun :=
    (AnalyticSpace.KLocallyRingedSpace.contMDiff_subtypeVal_comp_iff'
      (U := ⟨Ψ.source, Ψ.open_source⟩) _).mp
      (Ψ.contMDiffOn_invFun.comp_contMDiff contMDiff_subtype_val fun w => w.2)

theorem partialDiffeomorphToDiffeomorph_apply_coe (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (z : M.restrict ⟨Ψ.source, Ψ.open_source⟩) :
    (partialDiffeomorphToDiffeomorph Ψ z).1 = Ψ z.1 := rfl

end Restrict

/-! ### The coordinates of the paddings -/

section Pad

variable {n n' : ℕ} (σ : Fin n ↪ Fin n') (G : Opens (Fin n → 𝕜))

/-- The zero extension `𝕜ⁿ → 𝕜ⁿ'` along `σ` on the model spaces. -/
def modelPadExt : (Fin n → 𝕜) → (Fin n' → 𝕜) := fun v => Function.extend σ v 0

theorem contDiff_modelPadExt : ContDiff 𝕜 ω (modelPadExt (𝕜 := 𝕜) σ) := contDiff_extend σ

theorem contDiffOn_modelPadExt_apply (i : Fin n') (O : Opens (Fin n → 𝕜)) :
    ContDiffOn 𝕜 ω (fun v : Fin n → 𝕜 => modelPadExt σ v i) (O : Set (Fin n → 𝕜)) :=
  ((contDiff_apply 𝕜 (fun _ => 𝕜) i).comp (contDiff_modelPadExt σ)).contDiffOn

theorem pieceCoord_padExt (w : pieceAmbient.{u} 𝕜 G) :
    pieceCoord (padOpens σ G) (padExt σ G w) = modelPadExt σ (pieceCoord G w) :=
  padExt_snd σ G w

end Pad

/-! ### Germs of functions of the model space: congruence, subtraction, coordinates -/

section ModelGermMore

variable {n : ℕ}

theorem modelGerm_congr {O O' : Opens (Fin n → 𝕜)} {f g : (Fin n → 𝕜) → 𝕜}
    (hf : ContDiffOn 𝕜 ω f O) (hg : ContDiffOn 𝕜 ω g O') {v : Fin n → 𝕜} (hv : v ∈ O)
    (hv' : v ∈ O') (h : ∀ᶠ w in 𝓝 v, f w = g w) : modelGerm f hf hv = modelGerm g hg hv' := by
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) v
  rw [stalkToGerm_modelGerm, stalkToGerm_modelGerm]
  exact Filter.Germ.coe_eq.mpr h

theorem modelGerm_sub {O : Opens (Fin n → 𝕜)} {f g : (Fin n → 𝕜) → 𝕜} (hf : ContDiffOn 𝕜 ω f O)
    (hg : ContDiffOn 𝕜 ω g O) {v : Fin n → 𝕜} (hv : v ∈ O) :
    modelGerm (fun w => f w - g w) (hf.sub hg) hv = modelGerm f hf hv - modelGerm g hg hv := by
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) v
  rw [map_sub, stalkToGerm_modelGerm, stalkToGerm_modelGerm, stalkToGerm_modelGerm]
  rfl

theorem modelGerm_zero {O : Opens (Fin n → 𝕜)} {f : (Fin n → 𝕜) → 𝕜} (hf : ContDiffOn 𝕜 ω f O)
    {v : Fin n → 𝕜} (hv : v ∈ O) (h : ∀ w, f w = 0) : modelGerm f hf hv = 0 := by
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) v
  rw [stalkToGerm_modelGerm, map_zero, ← Filter.Germ.coe_zero]
  exact Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall h)

theorem modelGerm_eq_modelCoordGerm {O : Opens (Fin n → 𝕜)} {f : (Fin n → 𝕜) → 𝕜}
    (hf : ContDiffOn 𝕜 ω f O) {v : Fin n → 𝕜} (hv : v ∈ O) (k : Fin n) (h : ∀ w, f w = w k) :
    modelGerm f hf hv = modelCoordGerm v k := by
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) v
  rw [stalkToGerm_modelGerm, stalkToGerm_modelCoordGerm]
  exact Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall h)

/-- The germ map of a partial analytic map carries the model germ of `f` to the model germ of
`f ∘ j`. -/
theorem germMapOn_modelGerm {m : ℕ} {j : (Fin n → 𝕜) → (Fin m → 𝕜)} {O : Opens (Fin n → 𝕜)}
    (hj : ContDiffOn 𝕜 ω j O) {v : Fin n → 𝕜} (hv : v ∈ O) {w : Fin m → 𝕜} (hjv : j v = w)
    {O' : Opens (Fin m → 𝕜)} {f : (Fin m → 𝕜) → 𝕜} (hf : ContDiffOn 𝕜 ω f O') (hw : w ∈ O')
    {O'' : Opens (Fin n → 𝕜)} (hfj : ContDiffOn 𝕜 ω (f ∘ j) O'') (hv'' : v ∈ O'') :
    germMapOn j (contMDiffOn_iff_contDiffOn.mpr hj) hv hjv (modelGerm f hf hw) =
      modelGerm (f ∘ j) hfj hv'' := by
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) v
  rw [stalkToGerm_germMapOn, stalkToGerm_modelGerm, stalkToGerm_modelGerm,
    Filter.Germ.coe_compTendsto]

/-- The stalk map along a partial analytic isomorphism, read at any point equal to the image, is
bijective (`germMapOn_partialDiffeomorph_bijective` with the target point transported). -/
theorem germMapOn_partialDiffeomorph_bijective' {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {M₁' : Type u} [TopologicalSpace M₁'] [ChartedSpace E M₁']
    {M₂' : Type u} [TopologicalSpace M₂'] [ChartedSpace E M₂']
    (g : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁' M₂' ω) {x : M₁'} (hx : x ∈ g.source) {c : M₂'}
    (hc : g x = c) :
    Function.Bijective (germMapOn (g : M₁' → M₂') (V := ⟨g.source, g.open_source⟩)
      g.contMDiffOn_toFun hx hc) := by
  subst hc
  exact germMapOn_partialDiffeomorph_bijective g hx

end ModelGermMore

/-! ### The shear automorphism of the model space ([Kol07, Lemma 39, proof]) -/

section ShearModel

variable {n m : ℕ} (O₁ : Opens (Fin n → 𝕜)) (j₂ : (Fin n → 𝕜) → (Fin m → 𝕜))
  (hj₂ : ContDiffOn 𝕜 ω j₂ O₁) (O₂ : Opens (Fin m → 𝕜)) (j₁ : (Fin m → 𝕜) → (Fin n → 𝕜))
  (hj₁ : ContDiffOn 𝕜 ω j₁ O₂)

/-- The shear `(x, y) ↦ (x + j(y), y)` of [Kol07, Lemma 39, proof] on a block pair. -/
theorem shearFst_append (a : Fin n → 𝕜) (b : Fin m → 𝕜) :
    shearFst O₂ j₁ hj₁ (Fin.append a b) = Fin.append (a + j₁ b) b := by
  rw [shearFst_apply, append_comp_natAdd, append_add_append, add_zero]

/-- **The composite `Φ₁⁻¹ ∘ Φ₂` of the two shears of [Kol07, Lemma 39, proof]** on the model space
`𝕜ⁿ⁺ᵐ`: the shear by `j₂` in the second block followed by the inverse shear by `j₁` in the
first. -/
def shearModel : PartialDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜)
    (Fin (n + m) → 𝕜) (Fin (n + m) → 𝕜) ω :=
  (shearSnd O₁ j₂ hj₂).trans (shearFst O₂ j₁ hj₁).symm

theorem shearModel_apply (z : Fin (n + m) → 𝕜) :
    shearModel O₁ j₂ hj₂ O₂ j₁ hj₁ z = (shearFst O₂ j₁ hj₁).symm (shearSnd O₁ j₂ hj₂ z) := rfl

theorem mem_shearModel_source (z : Fin (n + m) → 𝕜) :
    z ∈ (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).source ↔
      z ∘ Fin.castAdd m ∈ O₁ ∧ shearSnd O₁ j₂ hj₂ z ∘ Fin.natAdd n ∈ O₂ :=
  mem_partialDiffeomorph_trans_source (shearSnd O₁ j₂ hj₂) (shearFst O₂ j₁ hj₁).symm z

theorem mem_shearModel_target (w : Fin (n + m) → 𝕜) :
    w ∈ (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).target ↔
      w ∘ Fin.natAdd n ∈ O₂ ∧ shearFst O₂ j₁ hj₁ w ∘ Fin.castAdd m ∈ O₁ :=
  mem_partialDiffeomorph_trans_target (shearSnd O₁ j₂ hj₂) (shearFst O₂ j₁ hj₁).symm w

/-- `Φ₁⁻¹ (Φ₂ (x, 0)) = (x - j₁ (j₂ x), j₂ x)`. -/
theorem shearModel_append_zero (a : Fin n → 𝕜) :
    shearModel O₁ j₂ hj₂ O₂ j₁ hj₁ (Fin.append a 0) = Fin.append (a - j₁ (j₂ a)) (j₂ a) := by
  rw [shearModel_apply, shearSnd_append, zero_add, shearFst_symm_append]

theorem shearModel_append_zero_of_eq (a : Fin n → 𝕜) (ha : j₁ (j₂ a) = a) :
    shearModel O₁ j₂ hj₂ O₂ j₁ hj₁ (Fin.append a 0) = Fin.append 0 (j₂ a) := by
  rw [shearModel_append_zero, ha, sub_self]

theorem append_zero_mem_shearModel_source (a : Fin n → 𝕜) (ha : a ∈ O₁) (hb : j₂ a ∈ O₂) :
    Fin.append a 0 ∈ (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).source := by
  rw [mem_shearModel_source, append_comp_castAdd, shearSnd_append, zero_add, append_comp_natAdd]
  exact ⟨ha, hb⟩

theorem of_append_zero_mem_shearModel_source (a : Fin n → 𝕜)
    (h : Fin.append a 0 ∈ (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).source) : a ∈ O₁ ∧ j₂ a ∈ O₂ := by
  rw [mem_shearModel_source, append_comp_castAdd, shearSnd_append, zero_add,
    append_comp_natAdd] at h
  exact h

theorem of_zero_append_mem_shearModel_target (b : Fin m → 𝕜)
    (h : Fin.append 0 b ∈ (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).target) : b ∈ O₂ ∧ j₁ b ∈ O₁ := by
  rw [mem_shearModel_target, append_comp_natAdd, shearFst_append, zero_add,
    append_comp_castAdd] at h
  exact h

end ShearModel

/-! ### The shear isomorphism of the padded ambients -/

section ShearAmbient

variable {n m : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V) (x : X.restrictSet V)
  (O₁ : Opens (Fin n → 𝕜)) (j₂ : (Fin n → 𝕜) → (Fin m → 𝕜)) (hj₂ : ContDiffOn 𝕜 ω j₂ O₁)
  (O₂ : Opens (Fin m → 𝕜)) (j₁ : (Fin m → 𝕜) → (Fin n → 𝕜)) (hj₁ : ContDiffOn 𝕜 ω j₁ O₂)

/-- The left-padded ambient point in coordinates, `(i(y), 0)`. -/
theorem pieceCoord_padExt_castAdd (w : pieceAmbient.{u} 𝕜 E₁.G) :
    pieceCoord (padOpens (Fin.castAddEmb m) E₁.G) (padExt (Fin.castAddEmb m) E₁.G w) =
      Fin.append (pieceCoord E₁.G w) 0 :=
  (pieceCoord_padExt _ _ w).trans (extend_castAddEmb _)

/-- The right-padded ambient point in coordinates, `(0, i(y))`. -/
theorem pieceCoord_padExt_natAdd (w : pieceAmbient.{u} 𝕜 E₂.G) :
    pieceCoord (padOpens (Fin.natAddEmb n) E₂.G) (padExt (Fin.natAddEmb n) E₂.G w) =
      Fin.append 0 (pieceCoord E₂.G w) :=
  (pieceCoord_padExt _ _ w).trans (extend_natAddEmb _)

theorem ambientPoint_padLeft (y : X.restrictSet V) :
    (E₁.padLeft m).ambientPoint y = padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) :=
  E₁.ambientPoint_padAlong _ y

theorem ambientPoint_padRight (y : X.restrictSet V) :
    (E₂.padRight n).ambientPoint y = padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y) :=
  E₂.ambientPoint_padAlong _ y

/-- **The shear of [Kol07, Lemma 39, proof] on the padded ambients**:
`chart₂⁻¹ ∘ (Φ₁⁻¹ ∘ Φ₂) ∘ chart₁ : Sp(G₁ × 𝕜ᵐ) ⇀ Sp(𝕜ⁿ × G₂)`, the charts being taken at the
padded ambient points of `x`. -/
def shearAmbient : PartialDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜)
    (pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G))
    (pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)) ω :=
  (pieceAmbientChart (padOpens (Fin.castAddEmb m) E₁.G)
    (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint x))).trans
    ((shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).trans
      (pieceAmbientChart (padOpens (Fin.natAddEmb n) E₂.G)
        (padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint x))).symm)

theorem shearAmbient_apply (z : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)) :
    shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ z =
      (pieceAmbientChart (padOpens (Fin.natAddEmb n) E₂.G)
        (padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint x))).symm
        (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁ (pieceCoord (padOpens (Fin.castAddEmb m) E₁.G) z)) := by
  rw [shearAmbient, partialDiffeomorph_trans_apply, partialDiffeomorph_trans_apply,
    pieceAmbientChart_apply]

theorem mem_shearAmbient_source (z : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)) :
    z ∈ (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source ↔
      pieceCoord (padOpens (Fin.castAddEmb m) E₁.G) z ∈ (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).source ∧
        shearModel O₁ j₂ hj₂ O₂ j₁ hj₁ (pieceCoord (padOpens (Fin.castAddEmb m) E₁.G) z) ∈
          (pieceAmbientChart (padOpens (Fin.natAddEmb n) E₂.G)
            (padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint x))).target := by
  rw [shearAmbient, mem_partialDiffeomorph_trans_source, mem_partialDiffeomorph_trans_source,
    pieceAmbientChart_apply]
  exact ⟨fun h => h.2, fun h => ⟨mem_pieceAmbientChart_source _ _ _, h⟩⟩

theorem mem_shearAmbient_target (w : pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)) :
    w ∈ (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).target ↔
      pieceCoord (padOpens (Fin.natAddEmb n) E₂.G) w ∈ (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).target ∧
        (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).symm (pieceCoord (padOpens (Fin.natAddEmb n) E₂.G) w) ∈
          (pieceAmbientChart (padOpens (Fin.castAddEmb m) E₁.G)
            (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint x))).target := by
  rw [shearAmbient, mem_partialDiffeomorph_trans_target, mem_partialDiffeomorph_trans_target,
    partialDiffeomorph_trans_symm_apply]
  have e : (pieceAmbientChart (padOpens (Fin.natAddEmb n) E₂.G)
      (padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint x))).symm.symm w =
      pieceCoord (padOpens (Fin.natAddEmb n) E₂.G) w :=
    pieceAmbientChart_apply _ _ w
  rw [e]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨mem_pieceAmbientChart_source _ _ _, h.1⟩, h.2⟩⟩

/-- **The point condition**: the shear carries `(i₁(y), 0)` to `(0, i₂(y))` when the lifts take
`i₁(y)` to `i₂(y)` and back ([Kol07, Lemma 39, proof]). -/
theorem shearAmbient_padExt (y : X.restrictSet V) (h₂ : j₂ (E₁.modelPoint y) = E₂.modelPoint y)
    (h₁ : j₁ (E₂.modelPoint y) = E₁.modelPoint y) :
    shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y)) =
      padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y) := by
  rw [shearAmbient_apply, pieceCoord_padExt_castAdd,
    shearModel_append_zero_of_eq _ _ _ _ _ _ _ (by rw [h₂]; exact h₁), h₂,
    ← pieceCoord_padExt_natAdd, pieceAmbientChart_symm_pieceCoord]

theorem padExt_mem_shearAmbient_source (y : X.restrictSet V)
    (hy₁ : E₁.modelPoint y ∈ O₁) (hy₂ : E₂.modelPoint y ∈ O₂)
    (h₂ : j₂ (E₁.modelPoint y) = E₂.modelPoint y) (h₁ : j₁ (E₂.modelPoint y) = E₁.modelPoint y) :
    padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈
      (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source := by
  rw [mem_shearAmbient_source, pieceCoord_padExt_castAdd]
  refine ⟨append_zero_mem_shearModel_source _ _ _ _ _ _ _ hy₁ (h₂.symm ▸ hy₂), ?_⟩
  rw [shearModel_append_zero_of_eq _ _ _ _ _ _ _ (by rw [h₂]; exact h₁), h₂,
    ← pieceCoord_padExt_natAdd]
  exact pieceCoord_mem_pieceAmbientChart_target _ _ _

theorem modelPoint_mem_of_padExt_mem_source (y : X.restrictSet V)
    (h : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈
      (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source) :
    E₁.modelPoint y ∈ O₁ ∧ j₂ (E₁.modelPoint y) ∈ O₂ := by
  rw [mem_shearAmbient_source, pieceCoord_padExt_castAdd] at h
  exact of_append_zero_mem_shearModel_source _ _ _ _ _ _ _ h.1

theorem modelPoint_mem_of_padExt_mem_target (y : X.restrictSet V)
    (h : padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y) ∈
      (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).target) :
    E₂.modelPoint y ∈ O₂ ∧ j₁ (E₂.modelPoint y) ∈ O₁ := by
  rw [mem_shearAmbient_target, pieceCoord_padExt_natAdd] at h
  exact of_zero_append_mem_shearModel_target _ _ _ _ _ _ _ h.1

end ShearAmbient

/-! ### The padded stalk maps and the kernel argument -/

section PadStalk

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)
  {N : ℕ} (σ : Fin n ↪ Fin N) (y : X.restrictSet V)

/-- **The padded stalk map** `δ = ε ∘ s^* : 𝒪_{𝕜ⁿ' ⊇ G', s(i(y))} →+* 𝒪_{X|V, y}` of a piece
embedding along a coordinate padding: the stalk map of the piece after the restriction to the
slice. Its kernel is the stalk of the padded ideal (`stalkIdeal_padIdeal_padExt` with
`stalkIdeal_eq_ker_pieceStalkMap`). -/
def padStalkMap :
    (structureSheaf 𝕜 (Fin N → 𝕜) (pieceAmbient.{u} 𝕜 (padOpens σ E.G))).presheaf.stalk
        (padExt σ E.G (E.ambientPoint y)) →+*
      (X.restrictSet V).toLocallyRingedSpace.presheaf.stalk y :=
  (E.pieceStalkMap y).comp (germMap (padExt σ E.G) (contMDiff_padExt σ E.G) (E.ambientPoint y))

theorem stalkIdeal_padIdeal_eq_ker_padStalkMap :
    (padIdeal σ E.ideal).stalkIdeal (padExt σ E.G (E.ambientPoint y)) =
      RingHom.ker (padStalkMap E σ y) :=
  (stalkIdeal_padIdeal_padExt σ E.ideal (E.ambientPoint y)).trans
    ((congrArg (Ideal.comap (germMap (padExt σ E.G) (contMDiff_padExt σ E.G) (E.ambientPoint y)))
      (E.stalkIdeal_eq_ker_pieceStalkMap y)).trans (RingHom.comap_ker _ _))

instance isLocalHom_padStalkMap : IsLocalHom (padStalkMap E σ y) :=
  @RingHom.isLocalHom_comp _ _ _ _ _ _ (E.pieceStalkMap y)
    (germMap (padExt σ E.G) (contMDiff_padExt σ E.G) (E.ambientPoint y))
    (E.isLocalHom_pieceStalkMap y)
    (isLocalHom_germMapOn (padExt σ E.G) (contMDiff_padExt σ E.G).contMDiffOn (Opens.mem_top _)
      rfl)

theorem padStalkMap_const (c : 𝕜) :
    padStalkMap E σ y (const 𝕜 (Fin N → 𝕜) (pieceAmbient.{u} 𝕜 (padOpens σ E.G))
        (padExt σ E.G (E.ambientPoint y)) c) =
      AnalyticSpace.KLocallyRingedSpace.constAt
        (AnalyticSpace.toKLocallyRingedSpace (X.restrictSet V)) y c :=
  (congrArg (E.pieceStalkMap y) (germMapOn_const' (padExt σ E.G) _ (Opens.mem_top _) rfl c)).trans
    (E.pieceStalkMap_const y c)

/-- The padded stalk map on the coordinate germs of the padded ambient: the `i`-th coordinate of
the zero extension, pulled back through the piece. -/
theorem padStalkMap_coord (i : Fin N) :
    padStalkMap E σ y (coord (Fin N → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin N → 𝕜))
        (chartAt (Fin N → 𝕜) (padExt σ E.G (E.ambientPoint y)))
        (IsManifold.chart_mem_maximalAtlas _) (mem_chart_source _ _) i) =
      E.modelStalkMap y (modelGerm (fun v => modelPadExt σ v i)
        (contDiffOn_modelPadExt_apply σ i ⊤) (Opens.mem_top _)) := by
  refine (congrArg (E.pieceStalkMap y) ?_)
  rw [coord_pieceAmbient_eq]
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbient.{u} 𝕜 E.G) (E.ambientPoint y)
  simp only [stalkToGerm_germMap, stalkToGerm_modelCoordGerm, stalkToGerm_modelGerm,
    Filter.Germ.coe_compTendsto]
  rfl

end PadStalk

section Transport

variable {n m : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V) (x : X.restrictSet V)
  (O₁ : Opens (Fin n → 𝕜)) (j₂ : (Fin n → 𝕜) → (Fin m → 𝕜)) (hj₂ : ContDiffOn 𝕜 ω j₂ O₁)
  (O₂ : Opens (Fin m → 𝕜)) (j₁ : (Fin m → 𝕜) → (Fin n → 𝕜)) (hj₁ : ContDiffOn 𝕜 ω j₁ O₂)

/-- The open of `𝕜ⁿ` where the shear is defined on the left-padded model points. -/
def shearModelOpens : Opens (Fin n → 𝕜) :=
  ⟨modelPadExt (Fin.castAddEmb m) ⁻¹' (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).source,
    (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).open_source.preimage (contDiff_modelPadExt _).continuous⟩

theorem contDiffOn_shearModel_modelPadExt (i : Fin (n + m)) :
    ContDiffOn 𝕜 ω (fun v => shearModel O₁ j₂ hj₂ O₂ j₁ hj₁ (modelPadExt (Fin.castAddEmb m) v) i)
      (shearModelOpens O₁ j₂ hj₂ O₂ j₁ hj₁) :=
  (contDiff_apply 𝕜 (fun _ => 𝕜) i).comp_contDiffOn
    ((contMDiffOn_iff_contDiffOn.mp (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).contMDiffOn_toFun).comp
      (contDiff_modelPadExt _).contDiffOn fun _ hv => hv)

/-- The padded stalk map of `E₁` after the shear, on the coordinate germs of the right-padded
ambient: the `i`-th coordinate of `Ψ ∘ s₁`, pulled back through `E₁`. -/
theorem padStalkMap_shear_coord (y : X.restrictSet V)
    (hb : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈
      (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source)
    (hc : shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ (padExt (Fin.castAddEmb m) E₁.G
      (E₁.ambientPoint y)) = padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y))
    (hv : E₁.modelPoint y ∈ shearModelOpens O₁ j₂ hj₂ O₂ j₁ hj₁) (i : Fin (n + m)) :
    padStalkMap E₁ (Fin.castAddEmb m) y
        (germMapOn (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁)
          (V := ⟨(shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source,
            (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).open_source⟩)
          (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).contMDiffOn_toFun hb hc
          (coord (Fin (n + m) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜))
            (chartAt (Fin (n + m) → 𝕜) (padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y)))
            (IsManifold.chart_mem_maximalAtlas _) (mem_chart_source _ _) i)) =
      E₁.modelStalkMap y (modelGerm _ (contDiffOn_shearModel_modelPadExt O₁ j₂ hj₂ O₂ j₁ hj₁ i)
        hv) := by
  refine (congrArg (E₁.pieceStalkMap y) ?_)
  rw [coord_pieceAmbient_eq]
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbient.{u} 𝕜 E₁.G) (E₁.ambientPoint y)
  set Ψₐ := shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ with hΨₐ
  set q₂ := padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y) with hq₂
  set c := modelCoordGerm (pieceCoord (padOpens (Fin.natAddEmb n) E₂.G) q₂) i with hcdef
  set B := germMap (pieceCoord (padOpens (Fin.natAddEmb n) E₂.G)) (contMDiff_pieceCoord _) q₂ c
    with hB
  set A := germMapOn Ψₐ (V := ⟨Ψₐ.source, Ψₐ.open_source⟩) Ψₐ.contMDiffOn_toFun hb hc B with hA
  have L1 := stalkToGerm_germMap (padExt (Fin.castAddEmb m) E₁.G) (contMDiff_padExt _ _)
    (E₁.ambientPoint y) A
  have L2 := stalkToGerm_germMapOn Ψₐ (V := ⟨Ψₐ.source, Ψₐ.open_source⟩) Ψₐ.contMDiffOn_toFun
    hb hc B
  have L3 := stalkToGerm_germMap (pieceCoord (padOpens (Fin.natAddEmb n) E₂.G))
    (contMDiff_pieceCoord _) q₂ c
  have L4 := stalkToGerm_modelCoordGerm (pieceCoord (padOpens (Fin.natAddEmb n) E₂.G) q₂) i
  have R1 := stalkToGerm_germMap (pieceCoord E₁.G) (contMDiff_pieceCoord _) (E₁.ambientPoint y)
    (modelGerm _ (contDiffOn_shearModel_modelPadExt O₁ j₂ hj₂ O₂ j₁ hj₁ i) hv)
  have R2 := stalkToGerm_modelGerm _ (contDiffOn_shearModel_modelPadExt O₁ j₂ hj₂ O₂ j₁ hj₁ i) hv
  rw [L1, L2, L3, L4, R1, R2]
  simp only [Filter.Germ.coe_compTendsto]
  refine Filter.Germ.coe_eq.mpr ?_
  have hopen : IsOpen (padExt (Fin.castAddEmb m) E₁.G ⁻¹' Ψₐ.source) :=
    Ψₐ.open_source.preimage (contMDiff_padExt _ _).continuous
  filter_upwards [hopen.mem_nhds hb] with w hw
  have hw' := (mem_shearAmbient_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ _).mp hw
  change pieceCoord (padOpens (Fin.natAddEmb n) E₂.G) (Ψₐ (padExt (Fin.castAddEmb m) E₁.G w)) i =
    shearModel O₁ j₂ hj₂ O₂ j₁ hj₁ (modelPadExt (Fin.castAddEmb m) (pieceCoord E₁.G w)) i
  rw [hΨₐ, shearAmbient_apply, pieceCoord_pieceAmbientChart_symm _ _ hw'.2, pieceCoord_padExt]

/-- **The two padded stalk maps agree through the shear** (the first half of the kernel argument):
at an embedded point `y`, `δ₂ = δ₁ ∘ Ψ^*` — `ringHom_ext_of_coord'` on the constants and on the
coordinate germs of the right-padded ambient (`padStalkMap_shear_coord`, the two lifts' coordinate
identities `H₁`, `H₂`). -/
theorem padStalkMap_eq_comp_germMapOn_shear (y : X.restrictSet V) (hy₁ : E₁.modelPoint y ∈ O₁)
    (hy₂ : E₂.modelPoint y ∈ O₂) (h₂ : j₂ (E₁.modelPoint y) = E₂.modelPoint y)
    (H₂ : ∀ k, E₂.modelStalkMap y (modelCoordGerm (E₂.modelPoint y) k) =
      E₁.modelStalkMap y (modelGerm (fun v => j₂ v k) (contDiffOn_pi.mp hj₂ k) hy₁))
    (H₁ : ∀ k, E₁.modelStalkMap y (modelCoordGerm (E₁.modelPoint y) k) =
      E₂.modelStalkMap y (modelGerm (fun v => j₁ v k) (contDiffOn_pi.mp hj₁ k) hy₂))
    (hb : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈
      (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source)
    (hc : shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ (padExt (Fin.castAddEmb m) E₁.G
      (E₁.ambientPoint y)) = padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y)) :
    padStalkMap E₂ (Fin.natAddEmb n) y =
      (padStalkMap E₁ (Fin.castAddEmb m) y).comp
        (germMapOn (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁)
          (V := ⟨(shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source,
            (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).open_source⟩)
          (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).contMDiffOn_toFun hb hc) := by
  set Ψₐ := shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ with hΨₐ
  set θ := germMapOn Ψₐ (V := ⟨Ψₐ.source, Ψₐ.open_source⟩) Ψₐ.contMDiffOn_toFun hb hc with hθ
  have hθloc : IsLocalHom θ := isLocalHom_germMapOn Ψₐ Ψₐ.contMDiffOn_toFun hb hc
  -- the open where `j₂` lands in `O₂`
  let O₁₂ : Opens (Fin n → 𝕜) :=
    ⟨O₁ ∩ j₂ ⁻¹' O₂, hj₂.continuousOn.isOpen_inter_preimage O₁.2 O₂.2⟩
  have hy₁₂ : E₁.modelPoint y ∈ O₁₂ := ⟨hy₁, by
    change j₂ (E₁.modelPoint y) ∈ O₂
    rw [h₂]
    exact hy₂⟩
  have hv : E₁.modelPoint y ∈ shearModelOpens O₁ j₂ hj₂ O₂ j₁ hj₁ := by
    change modelPadExt (Fin.castAddEmb m) (pieceCoord E₁.G (E₁.ambientPoint y)) ∈
      (shearModel O₁ j₂ hj₂ O₂ j₁ hj₁).source
    rw [← pieceCoord_padExt]
    exact ((mem_shearAmbient_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ _).mp hb).1
  -- the two padded stalk maps agree through the shear
  refine @AnalyticSpace.KLocallyRingedSpace.ringHom_ext_of_coord' 𝕜 _ _ _ _ _ _ _ _
    ((X.restrictSet V).toLocallyRingedSpace.presheaf.stalk y) _
    ((X.restrictSet V).toLocallyRingedSpace.isLocalRing y)
    (AnalyticSpace.isNoetherianRing_stalk (X.restrictSet V) y)
    (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜)) _
    (IsManifold.chart_mem_maximalAtlas (padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y))) _
    (mem_chart_source _ _) _ _ (isLocalHom_padStalkMap E₂ _ y)
    (@RingHom.isLocalHom_comp _ _ _ _ _ _ _ θ (isLocalHom_padStalkMap E₁ _ y) hθloc) ?_ ?_
  · intro c
    exact (padStalkMap_const E₂ _ y c).trans
      ((congrArg (padStalkMap E₁ (Fin.castAddEmb m) y)
        (germMapOn_const' Ψₐ Ψₐ.contMDiffOn_toFun hb hc c)).trans
        (padStalkMap_const E₁ _ y c)).symm
  · intro i
    change padStalkMap E₂ (Fin.natAddEmb n) y _ = padStalkMap E₁ (Fin.castAddEmb m) y (θ _)
    rw [padStalkMap_coord, padStalkMap_shear_coord E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hb hc hv i]
    induction i using Fin.addCases with
    | left k =>
      -- the first block: `0` on the right, `x_k - j₁ (j₂ x)_k` on the left
      rw [modelGerm_zero (contDiffOn_modelPadExt_apply (Fin.natAddEmb n) (Fin.castAdd m k) ⊤)
        (Opens.mem_top _) fun v => by
        simp only [modelPadExt, extend_natAddEmb, Fin.append_left, Pi.zero_apply]]
      rw [map_zero]
      have hk : ContDiffOn 𝕜 ω (fun v : Fin n → 𝕜 => v k) O₁₂ :=
        (contDiff_apply 𝕜 (fun _ => 𝕜) k).contDiffOn
      have hjj : ContDiffOn 𝕜 ω (fun v : Fin n → 𝕜 => j₁ (j₂ v) k) O₁₂ :=
        (contDiffOn_pi.mp hj₁ k).comp (hj₂.mono Set.inter_subset_left) fun _ hv => hv.2
      rw [modelGerm_congr (contDiffOn_shearModel_modelPadExt O₁ j₂ hj₂ O₂ j₁ hj₁ _) (hk.sub hjj)
        hv hy₁₂ (Filter.Eventually.of_forall fun v => by
          simp only [modelPadExt, extend_castAddEmb, shearModel_append_zero, Fin.append_left,
            Pi.sub_apply])]
      rw [modelGerm_sub hk hjj hy₁₂, map_sub, modelGerm_eq_modelCoordGerm hk hy₁₂ k fun _ => rfl]
      have e1 : modelGerm (fun v : Fin n → 𝕜 => j₁ (j₂ v) k) hjj hy₁₂ =
          germMapOn j₂ (contMDiffOn_iff_contDiffOn.mpr hj₂) hy₁ h₂
            (modelGerm (fun w => j₁ w k) (contDiffOn_pi.mp hj₁ k) hy₂) :=
        (germMapOn_modelGerm hj₂ hy₁ h₂ (contDiffOn_pi.mp hj₁ k) hy₂ hjj hy₁₂).symm
      rw [e1, ← E₁.modelStalkMap_eq_of_lift E₂ y hj₂ hy₁ h₂ H₂, ← H₁ k, sub_self]
    | right k =>
      -- the second block: `x_k` on the right, `(j₂ x)_k` on the left
      rw [modelGerm_eq_modelCoordGerm
        (contDiffOn_modelPadExt_apply (Fin.natAddEmb n) (Fin.natAdd n k) ⊤) (Opens.mem_top _) k
        fun v => by
        simp only [modelPadExt, extend_natAddEmb, Fin.append_right]]
      rw [H₂ k]
      exact congrArg (E₁.modelStalkMap y)
        (modelGerm_congr (contDiffOn_pi.mp hj₂ k)
          (contDiffOn_shearModel_modelPadExt O₁ j₂ hj₂ O₂ j₁ hj₁ _) hy₁ hv
          (Filter.Eventually.of_forall fun v => by
            simp only [modelPadExt, extend_castAddEmb, shearModel_append_zero,
              Fin.append_right]))

/-- **The kernel argument** (the ideals are compared through their restrictions to the piece,
never through zero sets): at an embedded point, the stalk of the left-padded ideal is the image
under the shear's stalk map of the stalk of the right-padded ideal — both are kernels of padded
stalk maps, which the shear interchanges by the coordinate identities of the two lifts. -/
theorem stalkIdeal_padIdeal_shear (y : X.restrictSet V) (hy₁ : E₁.modelPoint y ∈ O₁)
    (hy₂ : E₂.modelPoint y ∈ O₂) (h₂ : j₂ (E₁.modelPoint y) = E₂.modelPoint y)
    (H₂ : ∀ k, E₂.modelStalkMap y (modelCoordGerm (E₂.modelPoint y) k) =
      E₁.modelStalkMap y (modelGerm (fun v => j₂ v k) (contDiffOn_pi.mp hj₂ k) hy₁))
    (H₁ : ∀ k, E₁.modelStalkMap y (modelCoordGerm (E₁.modelPoint y) k) =
      E₂.modelStalkMap y (modelGerm (fun v => j₁ v k) (contDiffOn_pi.mp hj₁ k) hy₂))
    (hb : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈
      (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source)
    (hc : shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ (padExt (Fin.castAddEmb m) E₁.G
      (E₁.ambientPoint y)) = padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y)) :
    (padIdeal (Fin.castAddEmb m) E₁.ideal).stalkIdeal
        (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y)) =
      Ideal.map (germMapOn (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁)
          (V := ⟨(shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source,
            (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).open_source⟩)
          (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).contMDiffOn_toFun hb hc)
        ((padIdeal (Fin.natAddEmb n) E₂.ideal).stalkIdeal
          (padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y))) := by
  set Ψₐ := shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ with hΨₐ
  set θ := germMapOn Ψₐ (V := ⟨Ψₐ.source, Ψₐ.open_source⟩) Ψₐ.contMDiffOn_toFun hb hc with hθ
  have hsurj : Function.Surjective θ := (germMapOn_partialDiffeomorph_bijective' Ψₐ hb hc).2
  have hδ : padStalkMap E₂ (Fin.natAddEmb n) y = (padStalkMap E₁ (Fin.castAddEmb m) y).comp θ :=
    padStalkMap_eq_comp_germMapOn_shear E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hy₁ hy₂ h₂ H₂ H₁ hb hc
  rw [stalkIdeal_padIdeal_eq_ker_padStalkMap, stalkIdeal_padIdeal_eq_ker_padStalkMap, hδ]
  exact (Ideal.map_comap_of_surjective θ hsurj _).symm.trans
    (congrArg (Ideal.map θ) (RingHom.comap_ker _ θ))

end Transport

/-! ### Off the embedded points, and the ideal identity on the source -/

section Assembly

variable {n m : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}

/-- Off the embedded points the ideal of a piece embedding has the unit stalk: the embedded points
are the cosupport of the ideal, `emb` being an isomorphism onto the closed subspace. -/
theorem PieceEmbedding.stalkIdeal_eq_top_of_forall_ne {N : ℕ} (P : PieceEmbedding 𝕜 N X V)
    (z : pieceAmbient.{u} 𝕜 P.G) (h : ∀ y, P.ambientPoint y ≠ z) : P.ideal.stalkIdeal z = ⊤ := by
  by_contra hne
  have hE : IsIso P.emb := P.emb_isIso
  obtain ⟨p, hp⟩ : ∃ p : P.ideal.toAnalyticSpace,
      P.ideal.toAnalyticSpaceι p = z :=
    ⟨(⟨z, hne⟩ : P.ideal.support), rfl⟩
  refine h ((@inv (AnalyticSpace.{u} 𝕜) _ _ _ P.emb hE) p) ?_
  have e : P.emb ((@inv (AnalyticSpace.{u} 𝕜) _ _ _ P.emb hE) p) = p :=
    congrArg (fun g : @Quiver.Hom (AnalyticSpace.{u} 𝕜) _
        P.ideal.toAnalyticSpace P.ideal.toAnalyticSpace =>
      g p)
      (@IsIso.inv_hom_id (AnalyticSpace.{u} 𝕜) _ _ _ P.emb hE)
  exact (congrArg P.ideal.toAnalyticSpaceι e).trans
      hp

/-- The padded form: off the padded embedded points the padded ideal has the unit stalk. -/
theorem stalkIdeal_padIdeal_eq_top_of_forall_ne (E : PieceEmbedding 𝕜 n X V) {N : ℕ}
    (σ : Fin n ↪ Fin N) (z : pieceAmbient.{u} 𝕜 (padOpens σ E.G))
    (h : ∀ y, padExt σ E.G (E.ambientPoint y) ≠ z) : (padIdeal σ E.ideal).stalkIdeal z = ⊤ :=
  PieceEmbedding.stalkIdeal_eq_top_of_forall_ne (E.padAlong σ) z fun y hy =>
    h y ((E.ambientPoint_padAlong σ y).symm.trans hy)

variable (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V) (x : X.restrictSet V)
  (O₁ : Opens (Fin n → 𝕜)) (j₂ : (Fin n → 𝕜) → (Fin m → 𝕜)) (hj₂ : ContDiffOn 𝕜 ω j₂ O₁)
  (O₂ : Opens (Fin m → 𝕜)) (j₁ : (Fin m → 𝕜) → (Fin n → 𝕜)) (hj₁ : ContDiffOn 𝕜 ω j₁ O₂)
  (v₂ : ∀ y, E₁.modelPoint y ∈ O₁ → j₂ (E₁.modelPoint y) = E₂.modelPoint y)
  (v₁ : ∀ y, E₂.modelPoint y ∈ O₂ → j₁ (E₂.modelPoint y) = E₁.modelPoint y)

include v₁ v₂ in
/-- An embedded point of the right padding in the target of the shear is the image of the
corresponding embedded point of the left padding, which lies in the source. -/
theorem padExt_mem_source_of_padExt_mem_target (y : X.restrictSet V)
    (h : padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y) ∈
      (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).target) :
    padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈
        (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source ∧
      shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁
          (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y)) =
        padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y) := by
  obtain ⟨hy₂, hj⟩ := modelPoint_mem_of_padExt_mem_target E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y h
  have h₁ := v₁ y hy₂
  have hy₁ : E₁.modelPoint y ∈ O₁ := h₁ ▸ hj
  have h₂ := v₂ y hy₁
  exact ⟨padExt_mem_shearAmbient_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hy₁ hy₂ h₂ h₁,
    shearAmbient_padExt E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y h₂ h₁⟩

include v₁ v₂ in
/-- **The ideal identity on the source of the shear** ([Kol07, Lemma 39]): at every point of the
source, the stalk of the left-padded ideal is the image of the stalk of the right-padded ideal
under the stalk map of the shear — the kernel argument at the embedded points, `⊤ = ⊤` off them. -/
theorem stalkIdeal_shear
    (H₂ : ∀ (y : X.restrictSet V) (hy : E₁.modelPoint y ∈ O₁) (k : Fin m),
      E₂.modelStalkMap y (modelCoordGerm (E₂.modelPoint y) k) =
        E₁.modelStalkMap y (modelGerm (fun v => j₂ v k) (contDiffOn_pi.mp hj₂ k) hy))
    (H₁ : ∀ (y : X.restrictSet V) (hy : E₂.modelPoint y ∈ O₂) (k : Fin n),
      E₁.modelStalkMap y (modelCoordGerm (E₁.modelPoint y) k) =
        E₂.modelStalkMap y (modelGerm (fun v => j₁ v k) (contDiffOn_pi.mp hj₁ k) hy))
    (z : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G))
    (hz : z ∈ (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source) :
    (padIdeal (Fin.castAddEmb m) E₁.ideal).stalkIdeal z =
      Ideal.map (germMapOn (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁)
          (V := ⟨(shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source,
            (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).open_source⟩)
          (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).contMDiffOn_toFun hz rfl)
        ((padIdeal (Fin.natAddEmb n) E₂.ideal).stalkIdeal
          (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ z)) := by
  by_cases hr : ∃ y, padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) = z
  · obtain ⟨y, hy⟩ := hr
    subst hy
    obtain ⟨hy₁, hj⟩ := modelPoint_mem_of_padExt_mem_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hz
    have h₂ := v₂ y hy₁
    have hy₂ : E₂.modelPoint y ∈ O₂ := h₂ ▸ hj
    have h₁ := v₁ y hy₂
    have hc := shearAmbient_padExt E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y h₂ h₁
    rw [germMapOn_map_stalkIdeal_congr (V := ⟨(shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source,
      (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).open_source⟩)
      (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).contMDiffOn_toFun hz hc rfl hc
      (padIdeal (Fin.natAddEmb n) E₂.ideal)]
    exact stalkIdeal_padIdeal_shear E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hy₁ hy₂ h₂ (H₂ y hy₁)
      (H₁ y hy₂) hz hc
  · have hr' : ∀ y, padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ≠ z :=
      fun y hy => hr ⟨y, hy⟩
    rw [stalkIdeal_padIdeal_eq_top_of_forall_ne E₁ _ z hr',
      stalkIdeal_padIdeal_eq_top_of_forall_ne E₂ _ _ ?_, Ideal.map_top]
    intro y hy
    obtain ⟨hs, e⟩ := padExt_mem_source_of_padExt_mem_target E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ v₂ v₁ y
      (hy ▸ (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).toPartialEquiv.map_source hz)
    exact hr' y ((shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).toPartialEquiv.injOn hs hz (e.trans hy))

end Assembly

/-! ### The equivalence of two embeddings -/

section

variable {n m : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V) (x : X.restrictSet V)

/-- **The ideal identity on the restrictions for the explicit shear witnesses** (the fourth clause
of `exists_padded_equivalence_of_shear`, extracted): the left-padded ideal restricted to the
source equals the pullback along `g` of the right-padded ideal restricted to the target — pointwise
through the stalk maps of the inclusions (`stalkIdeal_pullback`, `germMapOn_germMapOn`). -/
theorem pullback_padIdeal_inclusion_eq_of_shear
    (Ψₐ : PartialDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜)
      (pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G))
      (pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)) ω)
    (g : Diffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜)
      ((pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)).restrict
        ⟨Ψₐ.source, Ψₐ.open_source⟩)
      ((pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)).restrict
        ⟨Ψₐ.target, Ψₐ.open_target⟩) ω)
    (hg : ∀ z, (g z).1 = Ψₐ z.1)
    (hideal : ∀ (z : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)) (hz : z ∈ Ψₐ.source),
      (padIdeal (Fin.castAddEmb m) E₁.ideal).stalkIdeal z =
        Ideal.map (germMapOn Ψₐ (V := ⟨Ψₐ.source, Ψₐ.open_source⟩) Ψₐ.contMDiffOn_toFun hz rfl)
          ((padIdeal (Fin.natAddEmb n) E₂.ideal).stalkIdeal (Ψₐ z))) :
    (padIdeal (Fin.castAddEmb m) E₁.ideal).pullback
        (AnalyticManifold.inclusion _ ⟨Ψₐ.source, Ψₐ.open_source⟩)
        (AnalyticManifold.inclusion _ ⟨Ψₐ.source, Ψₐ.open_source⟩).contMDiff =
      ((padIdeal (Fin.natAddEmb n) E₂.ideal).pullback
        (AnalyticManifold.inclusion _ ⟨Ψₐ.target, Ψₐ.open_target⟩)
        (AnalyticManifold.inclusion _
            ⟨Ψₐ.target, Ψₐ.open_target⟩).contMDiff).pullback
        g.toContMDiffMap g.toContMDiffMap.contMDiff := by
  refine IdealSheaf.ext fun z' => ?_
  simp only [IdealSheaf.stalkIdeal_pullback, Ideal.map_map]
  have hΨ' : ContMDiffOn 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω
      (Ψₐ ∘ (Subtype.val : ((pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)).restrict
        ⟨Ψₐ.source, Ψₐ.open_source⟩) → pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)))
      ⊤ :=
    (Ψₐ.contMDiffOn_toFun.comp_contMDiff contMDiff_subtype_val fun z => z.2).contMDiffOn
  have hcomp : (germMap g.toContMDiffMap g.toContMDiffMap.contMDiff z').comp
      (germMap (AnalyticManifold.inclusion _ ⟨Ψₐ.target, Ψₐ.open_target⟩)
        (AnalyticManifold.inclusion _ ⟨Ψₐ.target, Ψₐ.open_target⟩).contMDiff
        (g.toContMDiffMap z')) =
      (germMap (AnalyticManifold.inclusion _ ⟨Ψₐ.source, Ψₐ.open_source⟩)
        (AnalyticManifold.inclusion _ ⟨Ψₐ.source, Ψₐ.open_source⟩).contMDiff
            z').comp
        (germMapOn Ψₐ (V := ⟨Ψₐ.source, Ψₐ.open_source⟩) Ψₐ.contMDiffOn_toFun z'.2
          (hg z').symm) := by
    refine RingHom.ext fun s => ?_
    refine (germMapOn_germMapOn
      (AnalyticManifold.inclusion _
          ⟨Ψₐ.target, Ψₐ.open_target⟩).contMDiff.contMDiffOn
      g.toContMDiffMap.contMDiff.contMDiffOn (Opens.mem_top z') rfl (Opens.mem_top _) rfl
      ((AnalyticManifold.inclusion _
          ⟨Ψₐ.target, Ψₐ.open_target⟩).contMDiff.comp
        g.toContMDiffMap.contMDiff).contMDiffOn (Opens.mem_top z') rfl s).trans ?_
    refine (germMapOn_congr _ hΨ' (Opens.mem_top z') rfl (hg z').symm (fun w _ => hg w) s).trans ?_
    exact (germMapOn_germMapOn Ψₐ.contMDiffOn_toFun
      (contMDiff_subtype_val (U := (⟨Ψₐ.source, Ψₐ.open_source⟩ :
        Opens (pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G))))).contMDiffOn
      (Opens.mem_top z') rfl z'.2 (hg z').symm hΨ' (Opens.mem_top z') (hg z').symm s).symm
  rw [hcomp]
  exact (congrArg (Ideal.map _) ((hideal z'.1 z'.2).trans
    (germMapOn_map_stalkIdeal_congr (V := ⟨Ψₐ.source, Ψₐ.open_source⟩) Ψₐ.contMDiffOn_toFun z'.2
      (hg z').symm rfl (hg z').symm _))).trans (Ideal.map_map _ _)

/-- **The assembly** of the equivalence from a local analytic isomorphism `Ψ` of the padded
ambients that carries the left-padded ambient points to the right-padded ones and the right-padded
ideal to the left-padded one: `W₁ := Ψ.source`, `W₂ := Ψ.target`, `g := Ψ` restricted; the ideal
identity on the restrictions is the pointwise identity through the stalk maps of the
inclusions. -/
theorem exists_padded_equivalence_of_shear
    (Ψₐ : PartialDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜)
      (pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G))
      (pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)) ω)
    (g : Diffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜)
      ((pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)).restrict
        ⟨Ψₐ.source, Ψₐ.open_source⟩)
      ((pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)).restrict
        ⟨Ψₐ.target, Ψₐ.open_target⟩) ω)
    (hg : ∀ z, (g z).1 = Ψₐ z.1)
    (hx : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint x) ∈ Ψₐ.source)
    (hideal : ∀ (z : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)) (hz : z ∈ Ψₐ.source),
      (padIdeal (Fin.castAddEmb m) E₁.ideal).stalkIdeal z =
        Ideal.map (germMapOn Ψₐ (V := ⟨Ψₐ.source, Ψₐ.open_source⟩) Ψₐ.contMDiffOn_toFun hz rfl)
          ((padIdeal (Fin.natAddEmb n) E₂.ideal).stalkIdeal (Ψₐ z)))
    (hpt : ∀ (y : X.restrictSet V), padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈ Ψₐ.source →
      Ψₐ (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y)) =
        padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y)) :
    ∃ (W₁ : Opens (pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)))
      (W₂ : Opens (pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)))
      (g : AnalyticMap
        ((pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)).restrict W₁)
        ((pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)).restrict W₂)),
      padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint x) ∈ W₁ ∧
      IsLocalDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω g ∧
      Function.Bijective g ∧
      (padIdeal (Fin.castAddEmb m) E₁.ideal).pullback
          (AnalyticManifold.inclusion _ W₁)
          (AnalyticManifold.inclusion _ W₁).contMDiff =
        ((padIdeal (Fin.natAddEmb n) E₂.ideal).pullback
          (AnalyticManifold.inclusion _ W₂)
          (AnalyticManifold.inclusion _ W₂).contMDiff).pullback g g.contMDiff ∧
      ∀ (y : X.restrictSet V) (hy : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈ W₁),
        (g ⟨padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y), hy⟩).1 =
          padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y) := by
  refine ⟨⟨Ψₐ.source, Ψₐ.open_source⟩, ⟨Ψₐ.target, Ψₐ.open_target⟩, g.toContMDiffMap, hx,
    g.isLocalDiffeomorph, g.toEquiv.bijective, ?_, fun y hy => (hg _).trans (hpt y hy)⟩
  exact pullback_padIdeal_inclusion_eq_of_shear E₁ E₂ Ψₐ g hg hideal

/-- **The equivalence of two embeddings, in padded form** ([Kol07, Lemma 39]): the shear
`Ψ = chart₂⁻¹ ∘ Φ₁⁻¹ ∘ Φ₂ ∘ chart₁` built from the two local lifts, restricted from its source `W₁`
to its target `W₂`, carries the left-padded ambient points `s₁(i₁(y))` to the right-padded ones
`s₂(i₂(y))` and pulls the right-padded ideal back to the left-padded one — everything on the
padded ambients `Sp(padOpens σ G)` and with the padded ideals `padIdeal σ 𝓘` (the forms of the
padded embeddings `padLeft`/`padRight` up to unfolding). -/
theorem embeddings_equivalent_under_automorphism_pad :
    ∃ (W₁ : Opens (pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)))
      (W₂ : Opens (pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)))
      (g : AnalyticMap
        ((pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)).restrict W₁)
        ((pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)).restrict W₂)),
      padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint x) ∈ W₁ ∧
      IsLocalDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω g ∧
      Function.Bijective g ∧
      (padIdeal (Fin.castAddEmb m) E₁.ideal).pullback
          (AnalyticManifold.inclusion _ W₁)
          (AnalyticManifold.inclusion _ W₁).contMDiff =
        ((padIdeal (Fin.natAddEmb n) E₂.ideal).pullback
          (AnalyticManifold.inclusion _ W₂)
          (AnalyticManifold.inclusion _ W₂).contMDiff).pullback g g.contMDiff ∧
      ∀ (y : X.restrictSet V) (hy : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈ W₁),
        (g ⟨padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y), hy⟩).1 =
          padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y) := by
  obtain ⟨O₁, hx₁, j₂, hj₂, H₂⟩ := E₁.exists_modelLift E₂ x
  obtain ⟨O₂, hx₂, j₁, hj₁, H₁⟩ := E₂.exists_modelLift E₁ x
  have v₂ : ∀ y, E₁.modelPoint y ∈ O₁ → j₂ (E₁.modelPoint y) = E₂.modelPoint y := fun y hy =>
    funext fun k => (E₁.modelPoint_eq_of_coord_eq E₂ y _ hy k (H₂ y hy k)).symm
  have v₁ : ∀ y, E₂.modelPoint y ∈ O₂ → j₁ (E₂.modelPoint y) = E₁.modelPoint y := fun y hy =>
    funext fun k => (E₂.modelPoint_eq_of_coord_eq E₁ y _ hy k (H₁ y hy k)).symm
  refine exists_padded_equivalence_of_shear E₁ E₂ x (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁)
    (partialDiffeomorphToDiffeomorph _) (partialDiffeomorphToDiffeomorph_apply_coe _)
    (padExt_mem_shearAmbient_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ x hx₁ hx₂ (v₂ x hx₁) (v₁ x hx₂))
    (stalkIdeal_shear E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ v₂ v₁ H₂ H₁) fun y hy => ?_
  obtain ⟨hy₁, hj⟩ := modelPoint_mem_of_padExt_mem_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hy
  have h₂ := v₂ y hy₁
  exact shearAmbient_padExt E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y h₂ (v₁ y (h₂ ▸ hj))

/-- **Two embeddings of one piece are equivalent under a local automorphism of the padded
ambient** — the analytic form of [Kol07, Lemma 39] (compare [Wlo09, §7.1]), from the padded form
through the identifications `(E.padLeft m).ambientPoint y = s₁ (i(y))`,
`(E.padRight n).ambientPoint y = s₂ (i(y))` and the empty divisors. -/
theorem embeddings_equivalent_under_automorphism :
    ∃ (W₁ : Opens (pieceAmbient.{u} 𝕜 (E₁.padLeft m).G))
      (W₂ : Opens (pieceAmbient.{u} 𝕜 (E₂.padRight n).G))
      (g : AnalyticMap ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).restrict W₁)
        ((pieceAmbient.{u} 𝕜 (E₂.padRight n).G).restrict W₂)),
      (E₁.padLeft m).ambientPoint x ∈ W₁ ∧
      IsLocalDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω g ∧
      Function.Bijective g ∧
      ((E₁.padLeft m).ambientTriple.pullback (AnalyticManifold.inclusion _ W₁)
          (isLocalDiffeomorph_inclusion _ W₁)).IsPullbackOf
        ((E₂.padRight n).ambientTriple.pullback
            (AnalyticManifold.inclusion _ W₂)
          (isLocalDiffeomorph_inclusion _ W₂)) g ∧
      ∀ (y : X.restrictSet V) (hy : (E₁.padLeft m).ambientPoint y ∈ W₁),
        (g ⟨(E₁.padLeft m).ambientPoint y, hy⟩).1 = (E₂.padRight n).ambientPoint y := by
  obtain ⟨W₁, W₂, g, hx, hloc, hbij, hI, hpt⟩ :=
    embeddings_equivalent_under_automorphism_pad E₁ E₂ x
  refine ⟨W₁, W₂, g, ?_, hloc, hbij, ⟨hI, ?_⟩, ?_⟩
  · exact (congrArg (fun p : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G) => p ∈ W₁)
      (ambientPoint_padLeft E₁ x)).mpr hx
  · change (HypersurfaceFamily.empty _).comap _ = ((HypersurfaceFamily.empty _).comap _).comap _
    rw [HypersurfaceFamily.empty_comap, HypersurfaceFamily.empty_comap,
      HypersurfaceFamily.empty_comap]
  · intro y hy
    have hy' : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈ W₁ :=
      (congrArg (fun p : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G) => p ∈ W₁)
        (ambientPoint_padLeft E₁ y)).mp hy
    have e : (⟨(E₁.padLeft m).ambientPoint y, hy⟩ : W₁) =
        ⟨padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y), hy'⟩ :=
      Subtype.ext (ambientPoint_padLeft E₁ y)
    exact ((congrArg (fun q : W₁ => (g q).1) e).trans (hpt y hy')).trans
      (ambientPoint_padRight E₂ y).symm

end

end Hironaka.Manifold
