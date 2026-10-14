/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.FamilyExt
public import Hironaka.Resolution.Analytic.Wlo09.FamilyLift
public import Hironaka.Resolution.Analytic.Wlo09.FamilyPushforward
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Resolution.Analytic.ModelTransport.Principalization
public import Hironaka.Resolution.Analytic.ModelTransport.Pushforward
public import Hironaka.Resolution.Analytic.OrderReduction.Stage.Concrete
public import Hironaka.Resolution.Analytic.Principalization.Assembly
import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.LimitGluing
import Hironaka.Resolution.Analytic.Functor.PullbackUpToEmpty
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1ExistsComap
import Hironaka.Resolution.Analytic.OrderReduction.Modified.BmoSeqOnOne
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Hironaka.Resolution.Analytic.Principalization.ClauseThree
import Hironaka.Resolution.Analytic.Principalization.IsoOff
import Hironaka.Resolution.Analytic.Principalization.MonomialSeq
import Hironaka.Resolution.Analytic.Principalization.NormalCrossingsOfMonomial
import Hironaka.Resolution.Analytic.Wlo09.HironakaClauses
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Włodarczyk's functorial locally finite principalization

Włodarczyk's locally finite principalization of an ideal sheaf on an analytic manifold over
`𝕜 = ℝ` or `ℂ` together with its commutation with local analytic isomorphisms and with closed
embeddings [Wlo09, Theorem 2.0.3], the analytic counterpart of Kollár's functorial principalization
[Kol07, Theorem 35] for an empty boundary: the main theorem
`AnalyticManifold.exists_functorial_principalization` at the end of this file.

On the standard model `𝕜ⁿ` the value at an ideal sheaf `I` with nonzero stalks is Kollár's order
reduction of the marked ideal `(M, I, ∅, 1)` [Kol07, 72], the marked family `concreteBMOanFam` of
the concrete tower at the mark `1`, glued along the exhaustion of `M` (`principalizationExt`):

* `isLocallyFinitelyPrincipalizedBy_principalizationExt`: the clauses of
  `IdealSheaf.IsLocallyFinitelyPrincipalizedBy`. Over every compact the value is a smooth blow-up
  sequence of order `≥ 1` for `(I, ∅)` whose marked transform has order `< 1` at the end
  (`BMOanFam.isOfOrderGe`, `BMOanFam.ord_lt`): the centres have normal crossings with the
  exceptional divisors, which are simple normal crossings families
  (`isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt`), the total transform of `I` is
  Kollár's monomial in the final exceptional divisor (`exists_boundaryMonomial_of_isOfOrderGe_one`,
  [Kol07, 72]), and the centres lie over the support of `I` (`CentersOver.of_isOfOrderGe`);
  properness, the divisor clause on `M̃` and the isomorphism off the support are those of the
  gluing;
* `isPullbackUpToEmptyAlong_principalizationExt`: for a local analytic isomorphism `g : N → M`
  the triple `(N, g^*I, ∅)` carries the pull-back data of `(M, I, ∅)`, so the values of the marked
  family correspond (`BMOanFam.commutesWithLocalIsos`, [Kol07, Theorem 107 (2)]) and the
  succession over a compact of `N` is the pull-back up to empty blow-ups of the succession over
  every compact of `M` whose neighbourhood contains its image
  (`CompatibleFamily.isPullbackUpToEmptyAlong_seqOn`);
* `isPushforwardUpToEmptyAlong_principalizationExt`: for a closed embedding `τ : N → M` with
  image a closed submanifold `S` of codimension `s` and `I ⊇ I_S`, the value at `(M, I, ∅)` is
  over every relatively compact open the push-forward of the value at `(S, I|_S, ∅)` in dimension
  `n − s` (`concreteBMOanFam_commutesWithClosedEmbeddings`, Kollár's Claim 71.2 from
  [Kol07, Theorem 107 (3)] and [Kol07, Theorem 103 (3)]), so the succession over a compact of `M`
  is the push-forward along `τ` of the succession over every compact of `N` whose neighbourhood
  maps into its neighbourhood, up to blow-ups whose centres lie away from the image
  (`isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily`,
  `Hironaka/Resolution/Analytic/Wlo09/FamilyPushforward.lean`).

On an arbitrary model `E` the assignment `principalizationAssignment 𝕜 E` reads the value on the
re-modelled manifold back along `E ≃ 𝕜ⁿ` (`ExtensionCompatibleFamily.transportBack`), with the
clauses (`isLocallyFinitelyPrincipalizedBy_transportBack`), the pull-back relation along the
re-modelled local isomorphism (`IsPullbackUpToEmptyAlong.transportAlong`,
`Hironaka/Resolution/Analytic/ModelTransport/Principalization.lean`) and the push-forward relation
along the re-modelled closed embedding (`IsPushforwardUpToEmptyAlong.transportAlong`,
`Hironaka/Resolution/Analytic/ModelTransport/Pushforward.lean`; the embedding identifies `N` with
the bundled submanifold `τ(N)` by `IsClosedAnalyticEmbedding.toDiffeomorph`, which fixes the
dimension of `N`, `dim_eq_of_diffeomorph`).

The global lift of a local analytic isomorphism `g : N → M` to `g̃ : Ñ → M̃`
(`liftsLocalAnalyticIsomorphisms_principalizationAssignment`) is glued from the per-compact
relation and the compact closures of the neighbourhoods
(`liftsLocalAnalyticIsomorphisms_of_commutes`,
`Hironaka/Resolution/Analytic/Wlo09/FamilyLift.lean`).
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u v

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### The principalization on the standard model -/

section Model

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- The triple `(M, I, ∅)` of an ideal sheaf with nonzero stalks and the empty boundary family, the
input of the marked order reduction for Włodarczyk's principalization of `I`. -/
def emptyBoundaryTriple {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (I : IdealSheaf M)
    (hI : I.IsNonzeroEverywhere) :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M :=
  ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩

/-- The triple `(M, I, ∅)` lies in the marked class at the mark `1`: the mark is positive and no
boundary member is nonempty. -/
theorem bmoClass_emptyBoundaryTriple {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (I : IdealSheaf M)
    (hI : I.IsNonzeroEverywhere) : AnalyticTriple.BMOClass 1 (emptyBoundaryTriple I hI) :=
  ⟨le_rfl, @Subtype.finite _ (inferInstanceAs (Finite PEmpty)) _⟩

/-- **The principalization of `I` on the standard model over the relatively compact opens**:
Kollár's order reduction of the marked ideal `(M, I, ∅, 1)` [Kol07, 72], the value of the marked
family `concreteBMOanFam` of the concrete tower at the mark `1`. -/
def bmoPrincipalizationFam (M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)) (I : IdealSheaf M)
    (hI : I.IsNonzeroEverywhere) : CompatibleFamily (emptyBoundaryTriple I hI) :=
  (concreteBMOanFam.{u} 𝕜 n).functor.fam _ (bmoClass_emptyBoundaryTriple I hI)

/-- **The principalization of `I` on the standard model**: the order reduction of `(M, I, ∅, 1)`
glued along the exhaustion of `M` (`CompatibleFamily.toExtensionCompatibleFamily`). -/
def principalizationExt (M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)) (I : IdealSheaf M)
    (hI : I.IsNonzeroEverywhere) : ExtensionCompatibleFamily M :=
  (bmoPrincipalizationFam M I hI).toExtensionCompatibleFamily

variable (M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)) (I : IdealSheaf M) (hI : I.IsNonzeroEverywhere)

/-- The boundary ideal sheaf of `(M, I, ∅)` restricted to an open is the unit ideal. -/
theorem restrictTriple_emptyBoundaryTriple_F_idealSheaf (U : Opens M) :
    (restrictTriple (emptyBoundaryTriple I hI) U).F.idealSheaf (𝕜 := 𝕜) (E := Fin n → 𝕜) = ⊤ := by
  rw [restrictTriple_F_idealSheaf]
  change IdealSheaf.restrict (HypersurfaceFamily.empty M).idealSheaf U = ⊤
  rw [HypersurfaceFamily.idealSheaf_empty (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))]
  exact IdealSheaf.pullback_top _ _

/-- **The principalization on the standard model is a locally finite principalization of `I`**
(`IdealSheaf.IsLocallyFinitelyPrincipalizedBy`, [Wlo09, Theorem 2.0.3 (1)–(3)]): properness, the
isomorphism off the support and the divisor clause on `M̃` are those of the glued family; the
neighbourhoods are pieces of the exhaustion; over every compact the value is a smooth blow-up
sequence of order `≥ 1` for `(I, ∅)` whose marked transform has order `< 1` at the end
(`BMOanFam.isOfOrderGe`, `BMOanFam.ord_lt`), so its exceptional divisors are simple normal
crossings families having simple normal crossings with the centres
(`isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt`,
`hasSncWith_totalTransformSeqFrom_center_of_forall_lt`), the total transform of `I` is Kollár's
monomial in the final exceptional divisor (`exists_boundaryMonomial_of_isOfOrderGe_one`,
[Kol07, 72]), and the centres lie over the support of `I` (`CentersOver.of_isOfOrderGe`). -/
theorem isLocallyFinitelyPrincipalizedBy_principalizationExt :
    I.IsLocallyFinitelyPrincipalizedBy (principalizationExt M I hI) := by
  set T := emptyBoundaryTriple I hI with hT
  set C := bmoPrincipalizationFam M I hI with hC
  have hF : ∀ U : Opens M, (restrictTriple T U).F.idealSheaf (𝕜 := 𝕜) (E := Fin n → 𝕜) = ⊤ :=
    restrictTriple_emptyBoundaryTriple_F_idealSheaf M I hI
  -- the per-open data of the marked family at the mark `1`
  have hge : ∀ (U : Opens M) (hU : IsCompact (closure (U : Set M))),
      (C.seqOn U hU).toSuccession.IsOfOrderGe (restrictTriple T U).I 1
        (restrictTriple T U).F.idealSheaf :=
    fun U hU => (concreteBMOanFam.{u} 𝕜 n).isOfOrderGe T _ U hU
  have hlt : ∀ (U : Opens M) (hU : IsCompact (closure (U : Set M)))
      (x : (C.seqOn U hU).toSuccession.stage (Fin.last _)),
      ((C.seqOn U hU).toSuccession.markedTransformSeq (restrictTriple T U).I 1 (Fin.last _)).ord x <
        ((1 : ℕ) : ℕ∞) :=
    fun U hU x => (concreteBMOanFam.{u} 𝕜 n).ord_lt T _ U hU x
  have hsnc : ∀ (U : Opens M) (hU : IsCompact (closure (U : Set M)))
      (i : Fin ((C.seqOn U hU).toSuccession.length + 1)),
      ((C.seqOn U hU).toSuccession.totalTransformSeqFrom (restrictTriple T U).F i).IsSnc
          (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) ∧
        (C.seqOn U hU).toSuccession.boundarySeq ⊤ i =
          ((C.seqOn U hU).toSuccession.totalTransformSeqFrom (restrictTriple T U).F i).idealSheaf :=
    fun U hU i => by
      have h := FiniteSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
        (S := (C.seqOn U hU).toSuccession) (restrictTriple T U).isSnc i
        (fun i' _ => (hge U hU i').1)
      rwa [hF U] at h
  have hmon := fun (U : Opens M) (hU : IsCompact (closure (U : Set M))) x =>
    FiniteSuccession.exists_boundaryMonomial_of_isOfOrderGe_one (C.seqOn U hU).toSuccession
      (restrictTriple T U).isSnc (hge U hU) (hlt U hU) x
  have hemb := fun (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
    (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂) =>
    C.isAnalyticOpenEmbedding_endResultEmbedding hU₁ hU₂ h
  have hcomp := fun (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
    (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂) p =>
    C.composite_endResultEmbedding hU₁ hU₂ h p
  refine ⟨C.isProperMap_toExtensionCompatibleFamily_map,
    fun K => isCompact_closure_relCompactOpen (exhaustion M) _,
    fun K i => FiniteSuccession.center_isNonsingular _ i, fun K => ⟨fun i => ?_, ?_⟩, fun K => ?_,
    ?_, ?_⟩
  · -- (2): the boundary at the stage of a centre has simple normal crossings with it
    exact ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), _, _, (hsnc _ _ i.castSucc).1,
      (hsnc _ _ i.castSucc).2.symm,
      FiniteSuccession.hasSncWith_totalTransformSeqFrom_center_of_forall_lt
        (restrictTriple T _).isSnc i (fun i' _ => (hge _ _ i').1)⟩
  · -- (2): the last boundary has simple normal crossings
    exact ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), _, (hsnc _ _ (Fin.last _)).1,
      (hsnc _ _ (Fin.last _)).2.symm⟩
  · -- (3): Kollár's monomial in the final exceptional divisor
    refine ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), _, (hsnc _ _ (Fin.last _)).1,
      (hsnc _ _ (Fin.last _)).2.symm, fun x => ?_⟩
    obtain ⟨s, α, hs, heq⟩ := hmon _ _ x
    refine ⟨s, α, hs, ?_⟩
    rw [IdealSheaf.stalkIdeal_top, Ideal.top_mul]
    exact heq
  · -- (3) on `M̃`: the total transform is a normal-crossings divisor
    exact CompatibleFamily.isNormalCrossingsDivisor_comap_limitBlowDown C (exhaustion M) hemb hcomp
      I fun m => isNormalCrossingsDivisor_of_forall_monomial _ (hsnc _ _ (Fin.last _)).1 _
        (hmon _ _)
  · -- the isomorphism off the support of `I`
    refine CompatibleFamily.isAnalyticIsoOver_limitBlowDown C (exhaustion M) hemb hcomp I.support
      fun m => ?_
    have h := FiniteSuccession.isAnalyticIsoOver_stageMap
      (FiniteSuccession.CentersOver.of_isOfOrderGe _ (hge (relCompactOpen (exhaustion M) m)
        (isCompact_closure_relCompactOpen (exhaustion M) m)) le_rfl) (Fin.last _)
    have e : (restrictTriple T (relCompactOpen (exhaustion M) m)).I.support =
        Subtype.val ⁻¹' I.support :=
      IdealSheaf.support_pullback _ _ I
    rw [e] at h
    exact h

/-- **The principalization on the standard model commutes with local analytic isomorphisms**,
over every pair of compacts ([Wlo09, Theorem 3.5.1 (2)]): for a local analytic isomorphism
`g : N → M` and `J = g^* I`, the succession over `U_{K'}` is the pull-back along `g` of the
succession over `U_K` up to empty blow-ups whenever `g(U_{K'}) ⊆ U_K`. The triple `(N, J, ∅)`
carries the pull-back data of `(M, I, ∅)`, so the marked family commutes with `g`
(`BMOanFam.commutesWithLocalIsos`), and `CompatibleFamily.isPullbackUpToEmptyAlong_seqOn` reads
the pull-back predicate. -/
theorem isPullbackUpToEmptyAlong_principalizationExt {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)
    (J : IdealSheaf N) (hJ : J.IsNonzeroEverywhere) (hIJ : J = I.pullback g g.contMDiff)
    (K' : Compacts N) (K : Compacts M)
    (hK : ⇑g '' ((principalizationExt N J hJ).nhd K' : Set N) ⊆
      (principalizationExt M I hI).nhd K) :
    ((principalizationExt N J hJ).seq K').IsPullbackUpToEmptyAlong
      ((principalizationExt M I hI).seq K) g := by
  have hpb : (emptyBoundaryTriple J hJ).IsPullbackOf (emptyBoundaryTriple I hI) g :=
    ⟨hIJ, (HypersurfaceFamily.empty_comap ⇑g).symm⟩
  exact CompatibleFamily.isPullbackUpToEmptyAlong_seqOn (bmoPrincipalizationFam M I hI)
    (bmoPrincipalizationFam N J hJ) g hg _ (isCompact_closure_relCompactOpen (exhaustion N) _)
    ((concreteBMOanFam.{u} 𝕜 n).commutesWithLocalIsos _ _ g hg hpb _ _ _ _) _
    (isCompact_closure_relCompactOpen (exhaustion M) _) hK

/-- **The principalization on the standard model commutes with closed embeddings**, over every
pair of compacts ([Kol07, 34.3]): for a closed embedding `τ : N → M` identified by `e` with the
bundled closed submanifold `S = τ(N)` of codimension `s`, `I ⊇ I_S` and `J = τ^*I`, the succession
over `U_K` is the push-forward along `τ` of the succession over `U_{K'}`, up to blow-ups whose
centres lie away from `τ(U_{K'})`, whenever `τ(U_{K'}) ⊆ U_K`. The marked family of the concrete
tower commutes with closed embeddings of empty divisor over the relatively compact opens
(`concreteBMOanFam_commutesWithClosedEmbeddings`, Kollár's Claim 71.2), and
`isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily` reads the push-forward predicate for
the glued families. -/
theorem isPushforwardUpToEmptyAlong_principalizationExt {s : ℕ}
    {N : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    (τ : C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (e : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω)
    (he : ∀ x, (e x : Set.range τ).1 = τ x)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (J : IdealSheaf N) (hJ : J.IsNonzeroEverywhere) (hJI : J = I.pullback τ τ.contMDiff)
    (K' : Compacts N) (K : Compacts M)
    (hK : ⇑τ '' ((principalizationExt N J hJ).nhd K' : Set N) ⊆
      (principalizationExt M I hI).nhd K) :
    ((principalizationExt M I hI).seq K).IsPushforwardUpToEmptyAlong
      ((principalizationExt N J hJ).seq K') τ :=
  isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily
    (concreteBMOanFam_commutesWithClosedEmbeddings 𝕜 n s)
    (fun _ _ => ⟨le_rfl, @Subtype.finite _ (inferInstanceAs (Finite PEmpty)) _⟩)
    (concreteBMOanFam.{u} 𝕜 (n - s)).commutesWithLocalIsos τ hS e he I hI hle J hJ hJI
    (bmoClass_emptyBoundaryTriple I hI) (bmoClass_emptyBoundaryTriple J hJ) K' K hK

/-- `isPushforwardUpToEmptyAlong_principalizationExt` for a nonempty `N` modelled on any `𝕜^m`:
the identification `e` of `N` with the bundled submanifold of codimension `s` forces `m = n − s`
(`dim_eq_of_diffeomorph`). -/
theorem isPushforwardUpToEmptyAlong_principalizationExt_of_diffeomorph {m s : ℕ}
    {N : AnalyticManifold.{u} 𝕜 (Fin m → 𝕜)} [Nonempty N]
    (τ : C^ω⟮𝓘(𝕜, Fin m → 𝕜), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (e : Diffeomorph 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω)
    (he : ∀ x, (e x : Set.range τ).1 = τ x)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (J : IdealSheaf N) (hJ : J.IsNonzeroEverywhere) (hJI : J = I.pullback τ τ.contMDiff)
    (K' : Compacts N) (K : Compacts M)
    (hK : ⇑τ '' ((principalizationExt N J hJ).nhd K' : Set N) ⊆
      (principalizationExt M I hI).nhd K) :
    ((principalizationExt M I hI).seq K).IsPushforwardUpToEmptyAlong
      ((principalizationExt N J hJ).seq K') τ := by
  obtain ⟨x₀⟩ := ‹Nonempty N›
  obtain rfl : m = n - s := dim_eq_of_diffeomorph e x₀
  exact isPushforwardUpToEmptyAlong_principalizationExt M I hI τ hS e he hle J hJ hJI K' K hK

/-- `isPushforwardUpToEmptyAlong_principalizationExt` for an empty `N` modelled on any space: both
successions are empty (`isPushforwardUpToEmptyAlong_seqOn_of_isEmpty`). -/
theorem isPushforwardUpToEmptyAlong_principalizationExt_of_isEmpty {s : ℕ} {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    {N : AnalyticManifold.{u} 𝕜 E'} [IsEmpty N]
    (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (F : ExtensionCompatibleFamily N) (hF : ∀ K' : Compacts N, (F.seq K').NoEmptyCenters)
    (K' : Compacts N) (K : Compacts M) :
    ((principalizationExt M I hI).seq K).IsPushforwardUpToEmptyAlong (F.seq K') τ :=
  isPushforwardUpToEmptyAlong_seqOn_of_isEmpty
    (concreteBMOanFam_commutesWithClosedEmbeddings 𝕜 n s)
    (fun _ _ => ⟨le_rfl, @Subtype.finite _ (inferInstanceAs (Finite PEmpty)) _⟩)
    τ hS I hI hle (bmoClass_emptyBoundaryTriple I hI) (F.seq K') (hF K') _ _

end Model

/-! ### The assignment on an arbitrary model -/

section Assignment

variable (𝕜 : Type) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The identification of `E` with its standard model `𝕜ⁿ`, `n = dim E`. -/
abbrev modelEquiv : E ≃L[𝕜] (Fin (Module.finrank 𝕜 E) → 𝕜) :=
  ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun 𝕜).symm

variable {E}

/-- **Włodarczyk's principalization as an assignment on the pairs** `(M, I)`: the principalization
of the re-modelled ideal sheaf on the re-modelled manifold (standard model `𝕜ⁿ`, `n = dim E`,
`principalizationExt`), read back on the manifold (`transportBack`). -/
def principalizationAssignment : CompatibleFamilyAssignment (IdealSheafPair.{u, v} 𝕜) :=
  fun T =>
    (principalizationExt (T.M.transport (modelEquiv 𝕜 T.E)) (T.I.transport (modelEquiv 𝕜 T.E))
      ((IdealSheaf.isNonzeroEverywhere_pullbackDiffeomorph_iff _ _).mpr
        T.isNonzeroEverywhere)).transportBack (modelEquiv 𝕜 T.E)

variable {𝕜}

/-- **Every value of the assignment is a locally finite principalization**: the principalization
on the standard model (`isLocallyFinitelyPrincipalizedBy_principalizationExt`) carried back
(`isLocallyFinitelyPrincipalizedBy_transportBack`). -/
theorem isLocallyFinitelyPrincipalizedBy_principalizationAssignment (T : IdealSheafPair.{u, v} 𝕜) :
    T.I.IsLocallyFinitelyPrincipalizedBy (principalizationAssignment 𝕜 T) :=
  ExtensionCompatibleFamily.isLocallyFinitelyPrincipalizedBy_transportBack _ _ T.I
    (isLocallyFinitelyPrincipalizedBy_principalizationExt _ _ _)

/-- **The successions of the assignment pull back along local analytic isomorphisms**, over every
pair of compacts: on the standard model the re-modelled map is a local analytic isomorphism along
which the re-modelled ideal sheaves pull back (`isLocalDiffeomorph_transport`,
`IdealSheaf.transport_pullback`), where the principalization commutes with it
(`isPullbackUpToEmptyAlong_principalizationExt`); the pull-back predicate carries back to `E`
(`IsPullbackUpToEmptyAlong.transportAlong`). -/
theorem isPullbackUpToEmptyAlong_principalizationAssignment (T : IdealSheafPair.{u, v} 𝕜)
    {N : AnalyticManifold.{u} 𝕜 T.E} (g : AnalyticMap N T.M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g) (K' : Compacts N) (K : Compacts T.M)
    (hK : ⇑g '' ((principalizationAssignment 𝕜 (T.pullback g hg)).nhd K' : Set N) ⊆
      (principalizationAssignment 𝕜 T).nhd K) :
    ((principalizationAssignment 𝕜 (T.pullback g hg)).seq K').IsPullbackUpToEmptyAlong
      ((principalizationAssignment 𝕜 T).seq K) g := by
  dsimp only [principalizationAssignment] at hK ⊢
  exact FiniteSuccession.IsPullbackUpToEmptyAlong.transportAlong (modelEquiv 𝕜 T.E) g
    (AnalyticMap.transport (modelEquiv 𝕜 T.E) g) (fun _ => rfl)
    (isPullbackUpToEmptyAlong_principalizationExt _ _ _ (AnalyticMap.transport (modelEquiv 𝕜 T.E) g)
      (AnalyticMap.isLocalDiffeomorph_transport (modelEquiv 𝕜 T.E) hg) _ _
      (IdealSheaf.transport_pullback (modelEquiv 𝕜 T.E) g T.I) K' K hK)

/-- **The assignment commutes with local analytic isomorphisms**, over every pair of compacts and
as the lift of the isomorphism: the pull-back relation
(`isPullbackUpToEmptyAlong_principalizationAssignment`) and the compact closures of the
neighbourhoods (`isCompact_closure_nhd`) glue the lift
(`IdealSheafPair.commutesWithLocalAnalyticIsomorphisms_of_isPullbackUpToEmptyAlong`). -/
theorem commutesWithLocalAnalyticIsomorphisms_principalizationAssignment :
    IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms (principalizationAssignment.{u, v} 𝕜) :=
  IdealSheafPair.commutesWithLocalAnalyticIsomorphisms_of_isPullbackUpToEmptyAlong _
    isPullbackUpToEmptyAlong_principalizationAssignment
    fun T K =>
      (isLocallyFinitelyPrincipalizedBy_principalizationAssignment T).isCompact_closure_nhd K

end Assignment

/-! ### The commutation with closed embeddings across the model spaces -/

section ClosedEmbeddings

variable {𝕜 : Type} [RCLike 𝕜]

/-- **The assignment commutes with closed embeddings**
(`IdealSheafPair.CommutesWithClosedEmbeddings`, [Kol07, 34.3] over the compact sets): for a closed
embedding of analytic manifolds `τ : N → M` along which `I` is the push-forward of `J`, the
re-modelled map `transportBetween` is a closed embedding of the re-modelled manifolds with image a
closed submanifold of the same codimension, along which the re-modelled ideal sheaves pull back
and the containment of the ideal sheaf of the image carries over
(`Hironaka/Resolution/Analytic/Wlo09/ClosedEmbedding.lean`). For a nonempty `N` the embedding
identifies the re-modelled `N` with the bundled submanifold
(`IsClosedAnalyticEmbedding.toDiffeomorph`), and the push-forward relation holds on the standard
models (`isPushforwardUpToEmptyAlong_principalizationExt_of_diffeomorph`); for an empty `N` both
successions are empty (`isPushforwardUpToEmptyAlong_principalizationExt_of_isEmpty`). The
relation carries back to `E` and `E'` (`IsPushforwardUpToEmptyAlong.transportAlong`). -/
theorem commutesWithClosedEmbeddings_principalizationAssignment :
    IdealSheafPair.CommutesWithClosedEmbeddings (principalizationAssignment.{u, v} 𝕜) := by
  intro T T' τ hτ K' K hK
  obtain ⟨n, s, ψ, hS, hle⟩ := hτ.exists_isClosedSubmanifold_stalkIdeal_le
  have hemb := hτ.isClosedAnalyticEmbedding
  have hJI := hτ.pullback_eq
  -- the data on the standard models
  have hI' : (T.I.transport (modelEquiv 𝕜 T.E)).IsNonzeroEverywhere :=
    (IdealSheaf.isNonzeroEverywhere_pullbackDiffeomorph_iff _ _).mpr T.isNonzeroEverywhere
  have hJ' : (T'.I.transport (modelEquiv 𝕜 T'.E)).IsNonzeroEverywhere :=
    (IdealSheaf.isNonzeroEverywhere_pullbackDiffeomorph_iff _ _).mpr T'.isNonzeroEverywhere
  have hST : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (Module.finrank 𝕜 T.E) → 𝕜))
      (Set.range (transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) τ)) s :=
    (AnalyticManifold.IsClosedSubmanifold.range_transportBetween (modelEquiv 𝕜 T.E)
      (modelEquiv 𝕜 T'.E) hS).congr_chart _
  have hleT := stalkIdeal_idealSheaf_range_transportBetween_le (modelEquiv 𝕜 T.E)
    (modelEquiv 𝕜 T'.E) hS hST T.I hle
  have hJIT : T'.I.transport (modelEquiv 𝕜 T'.E) =
      (T.I.transport (modelEquiv 𝕜 T.E)).pullback
        (transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) τ)
        (transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) τ).contMDiff := by
    rw [hJI]
    exact IdealSheaf.transport_pullback_transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) T.I
  dsimp only [principalizationAssignment] at hK ⊢
  refine FiniteSuccession.IsPushforwardUpToEmptyAlong.transportAlong (modelEquiv 𝕜 T.E)
    (modelEquiv 𝕜 T'.E) τ (transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) τ)
    (fun _ => rfl) ?_
  rcases isEmpty_or_nonempty T'.M with hN | hN
  · -- an empty `N`: both successions are empty
    have : IsEmpty (T'.M.transport (modelEquiv 𝕜 T'.E)) := hN
    exact isPushforwardUpToEmptyAlong_principalizationExt_of_isEmpty _ _ hI' _ hST hleT _
      (fun K' => (bmoPrincipalizationFam _ _ hJ').noEmptyCenters _ _) K' K
  · -- a nonempty `N`: identified with the bundled submanifold of the image
    have : Nonempty (T'.M.transport (modelEquiv 𝕜 T'.E)) := hN
    have hτT := hemb.transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) hS
    exact isPushforwardUpToEmptyAlong_principalizationExt_of_diffeomorph _ _ hI' _ hST
      (hτT.toDiffeomorph hST) (hτT.coe_toDiffeomorph_apply hST) hleT _ hJ' hJIT K' K hK

end ClosedEmbeddings

end Hironaka.Manifold

end

end

public section

universe u v

section Principalization

open TopologicalSpace

namespace AnalyticManifold

/-- **Włodarczyk's functorial locally finite principalization** [Wlo09, Theorem 2.0.3], over
`𝕜 = ℝ` or `𝕜 = ℂ`, the analytic counterpart of Kollár's functorial principalization
[Kol07, Theorem 35] for an empty boundary. There is a compatible family assignment `P` on the
pairs `(M, I)` of an analytic manifold `M` over `𝕜`, modelled on a finite-dimensional space, and an
ideal sheaf `I` on `M` with nonzero stalks (`CompatibleFamilyAssignment (IdealSheafPair 𝕜)`) —
to each pair an analytic map `prin_I : M̃ → M` which over an open neighbourhood `U_K` of every
compact `K ⊆ M` splits, compatibly across compacts, into a finite succession of blow-ups
`U_K = U_0 ← U_1 ← ⋯ ← U_r` with smooth centres `C_i ⊆ U_i` and composite `σ_K : U_r → U_K` —
such that
* every value `P(M, I)` is a locally finite principalization of `I`
  (`IdealSheaf.IsLocallyFinitelyPrincipalizedBy`): with exceptional divisors `E_i` (the boundaries
  started at the empty boundary `⊤`), `prin_I` is proper and every `U_K` has compact closure;
  (1) every centre `C_i` is smooth; (2) every `E_i` has simple normal crossings with `C_i`, and
  `E_r` has simple normal crossings (`FiniteSuccession.HasSncBoundaries`); (3) the total transform
  `σ_K^*(I|_{U_K})` is, near every point, the ideal of an effective combination of the components of
  `E_r` through it (`IdealSheaf.IsMulBoundaryMonomial`, with the unit ideal `⊤` as its first
  factor), and the total transform `prin_I^*(I)` on `M̃` is a normal-crossings divisor
  (`IdealSheaf.IsNormalCrossingsDivisor`); and `prin_I` is an isomorphism over the complement of
  the support of `I` (`AnalyticMap.IsIsoOver`);
* `P` commutes with local analytic isomorphisms
  (`IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms`): for a local analytic isomorphism
  `g : N → M` of manifolds modelled on one space and the pair `(N, g^*I)`
  (`IdealSheafPair.pullback`), over every pair of compacts `K' ⊆ N`, `K ⊆ M` with
  `g(U_{K'}) ⊆ U_K` the succession of `P(N, g^*I)` over `U_{K'}` is the pull-back along `g` of the
  succession of `P(M, I)` over `U_K`, up to blow-ups with empty centre
  (`FiniteSuccession.IsPullbackUpToEmptyAlong`; [Wlo09, Theorem 3.5.1 (2)]); and there is a unique
  continuous map `g̃ : Ñ → M̃` over `g` between the spaces of `P(N, g^*I)` and `P(M, I)`, which is
  analytic, a local analytic isomorphism, and maps every fibre of `prin_{g^*I}` bijectively onto
  the fibre of `prin_I` over the image point, so that `Ñ` is the fibre product `N ×_M M̃`;
* `P` commutes with closed embeddings (`IdealSheafPair.CommutesWithClosedEmbeddings`): for pairs
  `(M, I)` and `(N, J)` and a closed embedding of analytic manifolds `τ : N → M`
  (an analytic embedding with closed image) along which `I` is the push-forward of `J` — the ideal
  of the closed submanifold `τ(N)` lies in `I`, and `J = τ^*I` (`IdealSheaf.IsPushforwardAlong`) —
  and compacts `K' ⊆ N`, `K ⊆ M` with `τ(U_{K'}) ⊆ U_K`, the succession of `P(M, I)` over `U_K` is
  the push-forward along `τ` of the succession of `P(N, J)` over `U_{K'}`, up to blow-ups whose
  centres lie outside the part over `τ(U_{K'})` (`FiniteSuccession.IsPushforwardUpToEmptyAlong`;
  [Kol07, 34.3]).

Włodarczyk's (4), that the factorization over a larger compact restricts to the factorization over
a smaller one, is the compatibility of the family: the succession over `K ⊆ K'`, restricted to
`U_K`, is an extension of the succession over `K`, the same blow-ups with isomorphisms interspersed
(`ExtensionCompatibleFamily.isExtensionOf_restrict`; [Wlo09, Definition 3.2.6]). Centres of
codimension one are admitted, as in [Wlo09, Remark (1) after Theorem 2.0.3]: the blow-up of such a
centre is an isomorphism, and the centre becomes a component of the exceptional divisor.

Relation to the source.
* **Translation.** `P` is Włodarczyk's principalization as a rule on all pairs $(M, I)$, the
  morphism $\mathrm{prin}$ of his last sentence: for the pair `T = (M, I)`, `P T` is the compatible
  family of $\mathrm{prin}_I \colon \tilde M \to M$, and
  `T.I.IsLocallyFinitelyPrincipalizedBy (P T)` is his "there exists a locally finite
  principalization of $I$", with clauses (1)–(3).
* **Correction.** The hypothesis that $I$ has nonzero stalks (the field `isNonzeroEverywhere` of
  the pair) is tacit in the source: otherwise the total transform $\sigma^{r*}(I)$ could not be the
  ideal of a divisor. Kollár states it explicitly, for an ideal sheaf "not zero on any irreducible
  component" [Kol07, Theorem 35]. The ideal sheaves with a zero stalk are not inputs, so nothing is
  asserted of them.
* **Interpretation.** In Włodarczyk's clause (3), the total transform $\sigma^{r*}(I)$ "is the ideal
  of a simple normal crossing divisor $\tilde E_U$ which is a locally finite combination of the
  irreducible components of the divisor $E_{U_r}$": the exponents of $\tilde E_U$ are read at each
  point, $\tilde E_U$ near a point being a combination of the components of $E_{U_r}$ through it.
* **Interpretation.** Włodarczyk's sheaf of ideals $\tilde I$ on $\tilde M$, which none of his
  clauses mentions, is read as the total transform $\mathrm{prin}_I^*(I)$; it is asserted to be a
  normal-crossings divisor (`IdealSheaf.IsNormalCrossingsDivisor`), the form of clause (3) that is
  local on $\tilde M$.
* **Translation.** "Embeddings of ambient varieties" in the last sentence is read as Kollár's
  commutation with closed embeddings [Kol07, Theorem 35 (5)], in the form of [Kol07, 34.3] for an
  empty boundary: $B(X, I_X) = j_* B(Y, I_Y)$ for a closed embedding $j$ of smooth varieties with
  $\mathcal{O}_X / I_X = j_*(\mathcal{O}_Y / I_Y)$, here `I.IsPushforwardAlong J τ` with the
  closed embedding `τ` (an analytic embedding with closed image), whose image is a closed
  submanifold: the ideal of the image (`vanishingStalk`) lies in `I`, and `J = τ^*I`. This is
  Włodarczyk's $I = \tau_*(J) \cdot \mathcal{O}_M$ [Wlo09, Remark (3) after Theorem 2.0.3], whose
  canonical resolution has the centres $\tau(C_i)$ of that of $J$ [Wlo09, Theorem 3.5.1 (3)]. The
  proof follows Kollár's derivation from his Claim 71.2 [Kol07, 72], the commutation of the marked
  order reduction with closed embeddings, through [Kol07, Theorem 107 (3)] and
  [Kol07, Theorem 103 (3)] at the mark `1`, the value of `P`.
* **Restatement.** The commutation with closed embeddings is stated over every pair of compact
  sets, as the push-forward of a succession up to blow-ups whose centres lie outside the part over
  $\tau(U_{K'})$ (`FiniteSuccession.IsPushforwardUpToEmptyAlong`): the succession of `P(M, I)` over
  $U_K$ also blows up centres over $U_K \setminus \tau(U_{K'})$, which the succession over $U_{K'}$
  does not see. The strict transforms of $\tau(N)$ are not formed: the relation is stated through
  embeddings of the stages, over $\tau$, with closed images containing every centre point over
  $\tau(U_{K'})$ and along which the centres pull back.
* **Restatement.** The commutation with local analytic isomorphisms is stated in two forms: over
  every pair of compact sets, as the relation between two successions of
  [Wlo09, Theorem 3.5.1 (2)], and globally, as the lift of $g \colon N \to M$ to a local analytic
  isomorphism $\tilde g \colon \tilde N \to \tilde M$ over $g$ identifying $\tilde N$ with the fibre
  product $N \times_M \tilde M$, the "natural lifting" of [Wlo09, Theorem 2.0.1 (3)]; the fibre
  product is stated pointwise, as the bijection of $\tilde g$ between the fibres over corresponding
  points.
* **Interpretation.** The exact equality for a surjective local analytic isomorphism
  [Wlo09, Theorem 3.5.1 (1)] has no counterpart per pair of compact sets: for $g$ the identity and
  compacts $K' \subsetneq K$ with a centre of the succession over $U_K$ lying over
  $U_K \setminus U_{K'}$, the succession induced over $U_{K'}$ has an empty centre which the
  succession over $U_{K'}$ omits. Its global content is read as: for surjective $g$ the lift
  $\tilde g$ is a surjective local analytic isomorphism identifying $\tilde N$ with
  $N \times_M \tilde M$.
* **Interpretation.** Włodarczyk's analytic manifold is read as pure-dimensional: the local analytic
  isomorphisms relate manifolds modelled on one space, and a closed embedding relates manifolds
  modelled on two, so the pairs carry their model space and `P` is one assignment over all
  finite-dimensional model spaces over $\mathbb{K}$.
* **Strengthening.** Every neighbourhood $U_K$ has compact closure, which the source does not ask.
  It makes the commutations apply, for a local analytic isomorphism or a closed embedding
  $g \colon N \to M$, to every compact set $K'$ of $N$: the closure $K$ of $g(U_{K'})$ is compact,
  and $g(U_{K'}) \subseteq K \subseteq U_K$.
* **Strengthening.** The clause that $\mathrm{prin}_I$ is an isomorphism over the complement of the
  support of $I$ is not in [Wlo09, Theorem 2.0.3]; it is [Wlo09, Lemma 4.0.3] and, for an empty
  boundary, [Kol07, Theorem 35 (3)].
* **Strengthening.** Each centre has a single codimension, and empty centres are admitted (their
  blow-ups are isomorphisms).
* **Gap.** Compared with Kollár's functorial principalization [Kol07, Theorem 35]
  (`AlgebraicGeometry.exists_functorial_principalization`): the inputs are pairs $(M, I)$, Kollár's
  triples with an empty boundary; the values are compatible families over the compact sets rather
  than single blow-up sequences, as Kollár's passage to analytic spaces provides them [Kol07, 44];
  the commutation with smooth morphisms [Kol07, 34.1] is asserted, in Włodarczyk's form, for local
  analytic isomorphisms only, the smooth morphisms of relative dimension zero; and the commutation
  with change of fields [Kol07, 34.2] has no counterpart.

Source statement: [Wlo09, Theorem 2.0.3, p. 35]

Source statement: [Kol07, Theorem 35] (analytic manifolds, empty boundary; item 44) -/
theorem exists_functorial_principalization (𝕜 : Type) [RCLike 𝕜] :
    ∃ P : CompatibleFamilyAssignment (IdealSheafPair.{u, v} 𝕜),
      -- (1)–(3)
      (∀ T : IdealSheafPair.{u, v} 𝕜, T.I.IsLocallyFinitelyPrincipalizedBy (P T)) ∧
      -- last sentence, 3.5.1 (2) and 2.0.1 (3)
      IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms P ∧
      -- last sentence, 34.3 with `E = ∅`
      IdealSheafPair.CommutesWithClosedEmbeddings P :=
  ⟨Hironaka.Manifold.principalizationAssignment 𝕜,
    Hironaka.Manifold.isLocallyFinitelyPrincipalizedBy_principalizationAssignment,
    Hironaka.Manifold.commutesWithLocalAnalyticIsomorphisms_principalizationAssignment,
    Hironaka.Manifold.commutesWithClosedEmbeddings_principalizationAssignment⟩

end AnalyticManifold

end Principalization
