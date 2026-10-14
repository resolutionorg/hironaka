/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import VersoBlueprint

/-!
# The bibliography of the blueprint

The entries of `references.bib`, the bibliography of the library, registered for the `{cite}`
role of the chapters and the citations of the docstring annotation items. The library
`BlueprintReferences` of `lakefile.toml` holds this module alone and needs the file, so that a
change to it rebuilds the registry and the chapters.
-/

blueprint_bibliography_file "../../references.bib"
