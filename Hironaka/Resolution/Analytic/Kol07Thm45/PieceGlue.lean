/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Over
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceIndependence
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Gluing the local resolutions of the pieces over a relatively compact open

Włodarczyk glues the canonical desingularizations of the germs of an open cover: for a cover of a
compact set `Z` by opens `V_i ⊂ W_i ⊂ U_i` with `V̄_i ⊂ W_i` and `W̄_i ⊂ U_i` compact, the
desingularization of the germ at `W̄_i` determines the desingularization `Ṽ_i → V_i`, the
embeddings `Y_{Z_i ∩ Z_j} → Y_{Z_i}` lift to embeddings of the desingularizations, and `Ṽ` is the
manifold obtained by gluing the `Ṽ_i` along the `Ṽ_i ∩ Ṽ_j`, with `des_V : Ṽ → V` bimeromorphic
and proper [Wlo09, §4, (3)⇒(4)]; the desingularization of a whole space is then assembled from
the restrictions `des_i⁻¹(U_i) → U_i` [Wlo09, §4.3]. Kollár glues the resolutions of the members
of an affine cover through the commutation with smooth surjections ([Kol07, Theorem 36, proof]
and [Kol07, Proposition 37]). For local embedding data `D : LocalEmbeddingData 𝕜 X U` and an
embedded desingularization functor `bed : BEDanFamStar 𝕜`:

* `PieceEmbedding.domOpens E W`: the base open of a piece embedding over an ambient open `W` —
  the points of the piece whose ambient point lies in `W` (Włodarczyk's `W_i`, read in `X`);
  `PieceEmbedding.toSpaceMap E bed W hW`: the local resolution's map to `X`
  (`localResolutionToPiece` followed by the open immersion of the piece), landing in `domOpens`;
  `LocalEmbeddingData.pieceDom D i W` and `LocalEmbeddingData.pieceToSpace D bed i W hW` are the
  two at the `i`-th piece;
* `LocalEmbeddingData.ResolutionGluing D bed`: the gluing datum — the chosen ambient opens `W_i`
  with compact closures containing the ambient points of `closure (inner i)`, and a `GlueOver` of
  the local resolutions `localResolution (D.embedding i) bed (W i) _` over `X` along the overlaps
  `pieceDom i ∩ pieceDom j` (the transitions are the unique isomorphisms between the local
  resolutions of two pieces restricted to the overlap, the cocycle identity follows from the same
  uniqueness, and the glued space is Hausdorff by the closed-graph criterion); its existence under
  `hbed : bed.IsEmbeddedDesing` is proved in `GluingProperties.lean`
  (`resolutionGluesOn_of_isEmbeddedDesing`, through `PieceGlueDatum.lean`), the proposition being
  `LocalEmbeddingData.ResolutionGluesOn D bed := Nonempty (ResolutionGluing D bed)` (the analytic
  counterpart of `Hironaka.Resolution.BRDescends`);
* `LocalEmbeddingData.resolutionOnFullPair D bed`: the glued space with its descended map to `X`
  when a gluing datum exists (chosen), the pair `⟨X, 𝟙 X⟩` otherwise (a fallback value, never
  taken under `hbed`, as the `nil X` of `Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`) — the sigma
  pair keeps the map's type uniform across the two branches;
  `resolutionOnFull`/`resolutionOnFullMap` its components (`des_V : Ṽ → V`, over the union of the
  `pieceDom`);
* `LocalEmbeddingData.resolutionOn D bed`, the glued space restricted over `U`, and
  `LocalEmbeddingData.resolutionOnMap D bed : resolutionOn D bed ⟶ X.restrictSet U` —
  Włodarczyk's `Ũ_i := des_i⁻¹(U_i) → U_i` [Wlo09, §4.3]; `resolutionOnToSpace` the same map into
  `X`. The unfolding lemmas `resolutionOnFullPair_eq_of_glues` / `_of_not_glues`,
  `resolutionOnFull_eq_of_glues` / `_of_not_glues` record the two branches.

The gluing locus is `pieceDom i ⊓ pieceDom j` — the parts of the two pieces OVER `W_i`, `W_j`
(`range_localResolutionToPiece_subset`) — the transcription of Włodarczyk's `V_i ⊂ W_i ⊂ U_i`,
matching the overlap `embPreimage W₁ ∩ embPreimage W₂` on which two local resolutions of one piece
are compared. `hbed` binds no definition: membership in the class is a hypothesis of the theorems,
never of a definition.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set
open AnalyticSpace KLocallyRingedSpace

universe u

namespace Hironaka.Manifold.PieceEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- **The base open of a piece embedding over the ambient open `W`**: the points of `X` in the
piece whose ambient point lies in `W` (`embPreimage` pushed into `X`): the open `W_i` of
Włodarczyk's cover `V_i ⊂ W_i ⊂ U_i` [Wlo09, §4, (3)⇒(4)]. -/
def domOpens (W : Opens (pieceAmbient.{u} 𝕜 E.G)) : Opens X :=
  ⟨Subtype.val '' E.embPreimage W,
    (openOf X V).isOpen.isOpenEmbedding_subtypeVal
      |>.isOpenMap _ (E.isOpen_embPreimage W)⟩

/-- Membership in the base open: the image in `X` of a point of the piece over `W`. -/
theorem mem_domOpens {W : Opens (pieceAmbient.{u} 𝕜 E.G)} {x : X} :
    x ∈ E.domOpens W ↔ ∃ y : X.restrictSet V, y ∈ E.embPreimage W ∧ Subtype.val y = x :=
  Iff.rfl

/-- The base open is monotone in the ambient open. -/
theorem domOpens_mono {Q W : Opens (pieceAmbient.{u} 𝕜 E.G)} (h : Q ≤ W) :
    E.domOpens Q ≤ E.domOpens W := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

/-- **The local resolution's map to `X`**: `Π` (`localResolutionToPiece`) followed by the open
immersion of the piece: Włodarczyk's desingularization `Ṽ_i → V_i ⊆ Y` [Wlo09, §4, (3)⇒(4)]. -/
def toSpaceMap (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) :
    (E.localResolution bed W hW).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace :=
  (E.localResolutionToPiece bed W hW :
      (E.localResolution bed W hW).toKLocallyRingedSpace ⟶ (X.restrictSet V).toKLocallyRingedSpace)
          ≫
    ofRestrict X.toKLocallyRingedSpace (openOf X V)

/-- The map to `X` lands in the base open (`range_localResolutionToPiece_subset`). -/
theorem range_toFun_toSpaceMap_subset (bed : BEDanFamStar.{u} 𝕜)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) :
    range (KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW)) ⊆ (E.domOpens W : Set X) := by
  rintro _ ⟨r, rfl⟩
  exact ⟨(E.localResolutionToPiece bed W hW) r,
    E.range_localResolutionToPiece_subset bed W hW ⟨r, rfl⟩, rfl⟩

end Hironaka.Manifold.PieceEmbedding

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)

/-- **The base open of the `i`-th piece over the ambient open `W`**: `domOpens` of the `i`-th
embedding (the open `W_i` of Włodarczyk's cover `V_i ⊂ W_i ⊂ U_i` [Wlo09, §4, (3)⇒(4)]). -/
abbrev pieceDom (i : D.ι) (W : Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G)) : Opens X :=
  (D.embedding i).domOpens W

/-- **The piece map to `X`**: `toSpaceMap` of the `i`-th embedding (Włodarczyk's
desingularization `Ṽ_i → V_i` of `V_i ⊂ U_i`, read into `Y` [Wlo09, §4, (3)⇒(4)]). -/
abbrev pieceToSpace (i : D.ι) (W : Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 (D.embedding i).G)))) :
    ((D.embedding i).localResolution bed W hW).toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace :=
  (D.embedding i).toSpaceMap bed W hW

/-- **A gluing datum for the local resolutions of the pieces of `D`** — the ambient opens
`W_i ⋐ G_i` over which the pieces are resolved, containing the ambient points of
`closure (inner i)` (Włodarczyk's `V̄_i ⊂ W_i`), and the gluing data over `X` (`GlueOver`) of the
local resolutions `localResolution (D.embedding i) bed (W i) _` along the overlaps
`pieceDom i ∩ pieceDom j`, with a Hausdorff glued space (the gluing of the `Ṽ_i` in
[Wlo09, §4, (3)⇒(4)]). -/
structure ResolutionGluing where
  /-- The relatively compact ambient opens over which the pieces are resolved. -/
  W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G)
  isCompact_closure_W : ∀ i, IsCompact (closure (W i : Set (pieceAmbient 𝕜 (D.embedding i).G)))
  /-- `V̄_i ⊂ W_i`: the inner opens lie over the chosen ambient opens [Wlo09, §4, (3)⇒(4)]. -/
  closure_inner_subset_pieceDom : ∀ i, closure (D.inner i) ⊆ D.pieceDom i (W i)
  /-- The gluing over `X` of the local resolutions along the overlaps of their base opens. -/
  glue : GlueOver X (fun i => (D.embedding i).localResolution bed (W i) (isCompact_closure_W i))
    (fun i => D.pieceToSpace bed i (W i) (isCompact_closure_W i)) (fun i => D.pieceDom i (W i))

/-- **A gluing datum exists** (the analytic counterpart of `Hironaka.Resolution.BRDescends`); its
proof under `hbed : bed.IsEmbeddedDesing` is `resolutionGluesOn_of_isEmbeddedDesing`
(`GluingProperties.lean`). -/
abbrev ResolutionGluesOn : Prop := Nonempty (D.ResolutionGluing bed)

open Classical in
/-- **The glued space with its descended map to `X`**, over the union of the base opens
(Włodarczyk's `Ṽ` with `des_V : Ṽ → V` [Wlo09, §4, (3)⇒(4)]) — the glued analytic space of a chosen
gluing datum when one exists, the pair `⟨X, 𝟙 X⟩` otherwise (a fallback value, never taken under
`hbed`, as the `nil X` of `Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`). -/
def resolutionOnFullPair :
    Σ R : AnalyticSpace.{u} 𝕜, (R ⟶ X) :=
  if h : D.ResolutionGluesOn bed then ⟨h.some.glue.gluedOver, h.some.glue.descMap⟩
  else ⟨X, 𝟙 X⟩

/-- The glued space over the union of the base opens (Włodarczyk's `Ṽ`). -/
def resolutionOnFull : AnalyticSpace.{u} 𝕜 := (D.resolutionOnFullPair bed).1

/-- The descended map `des_V : Ṽ → V ⊆ X` into `X`. -/
def resolutionOnFullMap : D.resolutionOnFull bed ⟶ X :=
  (D.resolutionOnFullPair bed).2

/-- **The resolution over `U`, `resolutionOn D bed`** — the glued space of the local resolutions of
the pieces of `D`, restricted over `U` (Włodarczyk's `Ũ_i := des_i⁻¹(U_i)` [Wlo09, §4.3]). -/
def resolutionOn : AnalyticSpace.{u} 𝕜 :=
  (D.resolutionOnFull bed).restrictSet (D.resolutionOnFullMap bed ⁻¹' U)

/-- **The resolution map over `U`, `Π_U = resolutionOnMap D bed : resolutionOn D bed → X|U`**
(Włodarczyk's restriction `Ũ_i := des_i⁻¹(U_i) → U_i` [Wlo09, §4.3]). -/
def resolutionOnMap : D.resolutionOn bed ⟶ X.restrictSet U :=
  (D.resolutionOnFullMap bed).restrictSet U

/-- The resolution map read into `X`: `Π_U` followed by the open immersion `X|U → X` (the map of
one member of the exhaustion by relatively compact opens from which the resolution of the whole
space is glued). -/
def resolutionOnToSpace : D.resolutionOn bed ⟶ X :=
  (D.resolutionOnMap bed :
      (D.resolutionOn bed).toKLocallyRingedSpace ⟶ (X.restrictSet U).toKLocallyRingedSpace) ≫
    ofRestrict X.toKLocallyRingedSpace (openOf X U)

/-! ### Unfolding lemmas -/

open Classical in
/-- With a gluing datum, the pair is the chosen datum's glued space and map. -/
theorem resolutionOnFullPair_eq_of_glues (h : D.ResolutionGluesOn bed) :
    D.resolutionOnFullPair bed = ⟨h.some.glue.gluedOver, h.some.glue.descMap⟩ := by
  unfold resolutionOnFullPair
  rw [dite_eq_left h]

open Classical in
/-- Without a gluing datum, the pair is `⟨X, 𝟙 X⟩` (a branch never taken under `hbed`). -/
theorem resolutionOnFullPair_eq_of_not_glues (h : ¬ D.ResolutionGluesOn bed) :
    D.resolutionOnFullPair bed = ⟨X, 𝟙 X⟩ := by
  unfold resolutionOnFullPair
  rw [dite_eq_right h]

/-- With a gluing datum, `resolutionOnFull` is the chosen datum's glued space. -/
theorem resolutionOnFull_eq_of_glues (h : D.ResolutionGluesOn bed) :
    D.resolutionOnFull bed = h.some.glue.gluedOver :=
  congrArg Sigma.fst (D.resolutionOnFullPair_eq_of_glues bed h)

/-- Without a gluing datum, `resolutionOnFull` is `X`. -/
theorem resolutionOnFull_eq_of_not_glues (h : ¬ D.ResolutionGluesOn bed) :
    D.resolutionOnFull bed = X :=
  congrArg Sigma.fst (D.resolutionOnFullPair_eq_of_not_glues bed h)

/-- Without a gluing datum, the descended map is (heterogeneously) the identity. -/
theorem resolutionOnFullMap_heq_of_not_glues (h : ¬ D.ResolutionGluesOn bed) :
    HEq (D.resolutionOnFullMap bed) (𝟙 X) :=
  (Sigma.ext_iff.mp (D.resolutionOnFullPair_eq_of_not_glues bed h)).2

end Hironaka.Manifold.LocalEmbeddingData

end
