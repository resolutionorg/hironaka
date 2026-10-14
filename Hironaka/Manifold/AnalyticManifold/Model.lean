/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.AnalyticManifold.Defs

/-!
# The model space as an analytic manifold

`AnalyticManifold.of 𝕜 E` bundles the model space `E` itself as an analytic manifold. No statement
of a main theorem uses it, and `scripts/check_defs.lean` admits in a module named `Defs` only what
some statement needs, so it is declared here, beside `Defs`, for the proofs that use it (the
monomialization of `Hironaka/Resolution/Standard/Analytic.lean`).
-/

@[expose] public section

namespace AnalyticManifold

/-- The model space `E` itself as an analytic manifold (Mathlib's `chartedSpaceSelf` and
`instIsManifoldModelSpace`, Hausdorff and second countable by hypothesis), as `ModuleCat.of`
bundles a module. An `abbrev`, so that `↥(AnalyticManifold.of 𝕜 E) = E` reduces and an open
`W ⊆ E` is `Opens E`. A type `M` carrying Mathlib's unbundled instances of an analytic manifold
modelled on `E` (charted space, analytic manifold, Hausdorff, second countable) is bundled by the
anonymous constructor, `⟨M⟩ : AnalyticManifold 𝕜 E`; the analytic main theorems apply to it. -/
abbrev of (𝕜 : Type) [RCLike 𝕜] (E : Type) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SecondCountableTopology E] : AnalyticManifold.{0} 𝕜 E :=
  ⟨E⟩

end AnalyticManifold

end
