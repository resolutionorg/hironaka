# The blueprint

A Verso Blueprint document over the library, written for a mathematician checking that each main
theorem's Lean statement says what its source says. It has five parts, declared in
`Blueprint.lean`, each chapter a file under `Blueprint/` and a page of the site (the introduction
is one page): *Introduction* (resolution of singularities and principalization, the theorems, how
to read a node, where to start); *Schemes* and *Analytic geometry*, the chapters on the objects
and operations in terms of which the statements are made, each notion explained once, where it is
defined (normal crossings with the singularity vocabulary, the blow-up with its universal property
and the resolution of the cusp, successions of blow-ups with their transforms, the operations on
them and blow-up sequence functors; manifolds, finite successions and compatible families,
analytic spaces); *Main theorems*, with a chapter on two statements in Mathlib's language,
then the chapters on algebraic schemes and on analytic manifolds and spaces, one
section per theorem (the theorems named in
`../comparator.json`, each stated at the end of the module that proves it) holding the properties
the theorem asserts and the inputs particular to it, then the theorem with an explanation of the
statement and its source and a sketch of its proof (a property asserted by several theorems is
stated at the first of them in its chapter); and the *Appendix*: a one-page dictionary from the
classical notions of scheme theory to their Mathlib or library names and nodes, the conventions
and the sources. Every declaration on which a main theorem's statement depends is embedded at a
node, linked by name to the library (signature, docstring, and the body of every plain
definition). It is reference-only: it describes the declarations as they are, and does not cover
the proofs beyond the sketches.

## Building

From this directory, after the library itself has been built (`lake exe cache get && lake build`
in the repository root):

```bash
lake update                        # once; shares the parent's dependency checkouts via packagesDir
lake exe vbp build                 # add --serve to preview at http://localhost:8000
lake exe vbp build --hide-review   # the same site, with the annotation boxes but no review badges
```

The site is written to `_out/site/html-multi/`. `VERSO_BLUEPRINT_HIDE_REVIEW=1` in the environment
has the same effect as `--hide-review`.

The one figure, the embedded resolution of the cusp in the chapter on the blow-up, is the SVG file
`static/cusp-sequence.svg`, which `Main.lean` copies to the root of the site with the rest of
`static/` (the pages refer to it as `static/cusp-sequence.svg`). It is drawn by the script in
`figures/` (plain Python, no dependencies), which rewrites the file:

```bash
python3 figures/cusp_sequence.py
```

The coverage of the statement vocabulary is checked from the library's package directory (the
parent of `blueprint/`, where `lakefile.toml` and `comparator.json` are) by

```bash
lake lean scripts/check_blueprint.lean
```

which compares the declarations named in the `(lean := ...)` fields of the nodes with the main
theorems it presents (those of `../comparator.json` that the script's docstring does not exclude)
and with the library declarations their statements depend on (the walk of
`scripts/check_defs.lean`, without the declarations Lean generates as internal, constructors and
recursors), and fails if one is missing or if a node names a declaration that is neither. The
introduction has no nodes of its own; it links to the nodes of the other chapters.

The VersoBlueprint dependency is the Timaeus fork of verso-blueprint
([timaeus-research/verso-blueprint](https://github.com/timaeus-research/verso-blueprint)), which
renders the annotation boxes from docstrings, reads the review ledger, links declaration names and
cites the BibTeX bibliography. `lakefile.toml` requires
it by git URL, pinned to a commit of the fork's branch `timaeus/v4.34.0` (the commit in `lakefile.toml`), and
`lake-manifest.json` locks that commit, so `lake update` fetches it like any other dependency.
Its patches to Verso are not needed by this document and are not applied.

## Declaration names

In the embedded declarations every constant presented at a node links to that node (a definition
node if there is one, else the first node naming it), and every other constant of Mathlib or Lean
core to Mathlib's API documentation. In the prose, a declaration is named with the role
`{decl}`Name``, the name written as in the chapter's `open` scope (or by its last components when
that is unambiguous): it renders as code linking to the node presenting the declaration, or to the
API documentation for a Mathlib name. `{decl Full.name}`text`` resolves `Full.name` and displays
`text`. Inside a node, a name first matches that node's own declarations. `lake exe vbp build`
fails on a `{decl}` whose name no node presents and the documentation does not cover, so the prose
cannot keep naming a declaration the blueprint no longer presents. Expressions (`h : Y ⟶ X`,
`D.blowUp`), namespaces and library names without a node stay plain code.

## Annotations

How a statement relates to its source is written once, in the docstring of the declaration: a
section headed by the line `Relation to the source.`, followed by Markdown bullets, each beginning
with a bold label. The labels are the fork's editorial kinds, chosen by three questions in order:

- Does the source's item have a formal counterpart? If not: `**Unformalised.**` (a statement or
  proof is missing) or `**Out of scope.**` (none is owed, by decision).
- Is the source's claim true as printed? If false: `**Correction.**` (the hypothesis it needs is
  added, and the corrected version stated). If underspecified: `**Interpretation.**` (the library
  fixes one reading).
- For a true claim, how do the statements compare? `**Restatement.**` (logically equivalent),
  `**Strengthening.**` (the formal statement implies the source's) or `**Gap.**` (weaker or
  incomparable).

`**Translation.**` is a dictionary entry (this Lean expression is the source's such-and-such),
whatever the answers, and `**Formalisation note.**` the fallback for a remark that is none of
these. A *Gap* or *Unformalised* item marks its node "Owes work". An item may continue on indented
lines and may use inline code and inline LaTeX `$...$`. The docstrings of
the main theorems carry such a section (the library copy and the challenge copy are identical), as
do the definitions where the source's notion and the library's part ways.

The fork renders the items of every declaration embedded at a node as annotation boxes after the
node's text, with the math typeset; there are no hand-written annotation directives in this
document. The items of the theorems are compiled into the `note`s of `alignment.statements`
in `../formalization.yaml` by `../scripts/sync_formalization.lean`. The introduction
(`Blueprint/Introduction.lean`) explains the kinds to the reader, and so does the label of each
box: hovering, focusing or tapping it shows its kind's one-sentence explanation. The sentences,
which follow the introduction, are in `annotation-labels.js` and the popover's style in
`annotation-labels.css`; `Main.lean` inlines both in every page.

Review status is not written in the docstrings. It is recorded in `reviews.json` (this
directory), a JSON array of entries

```json
{"decl": "<full name>", "kind": "Translation", "hash": "<16 hex digits>", "reviewer": "<name>", "date": "YYYY-MM-DD"}
```

which the fork reads, when it generates the site, from the directory the site is generated in
(this one; no option is needed). An item is *reviewed* when an entry with its declaration, kind
and hash exists. It is *changed since review* when it is the edited version of a reviewed item:
its hash has no entry, and the ledger names a hash, for its declaration and kind, that none of
the current items has (with several such items, they are matched to these stale hashes in
docstring order; the fork's `TIMAEUS.md` gives the exact rule). Otherwise it is *unreviewed*; a
new item next to reviewed ones stays unreviewed. A missing ledger means that every item is
unreviewed, and a malformed one fails the build. When an item is reviewed again, its entry is
replaced, not added to. The hash is the 64-bit FNV-1a hash of the UTF-8 bytes of the
item's text after its label, with every run of whitespace collapsed to one space and the ends
trimmed, so rewrapping an item keeps its review and any other edit withdraws it; the definition is
in the docstring of `../scripts/sync_formalization.lean` and in the fork's `TIMAEUS.md`. From the
package directory,

```bash
LIST_REVIEW_ITEMS=1 lake lean scripts/sync_formalization.lean
```

prints an entry for every item, ready to paste into `reviews.json` once `reviewer` and `date` are
filled in. Editing the ledger needs no rebuild of the chapters, only a new `lake exe vbp build`.

Source citations use the keys of the bibliography `../references.bib`, which `Blueprint/References.lean`
registers with the fork's `blueprint_bibliography_file` (the library `BlueprintReferences` of
`lakefile.toml` needs the file, so that a change to it rebuilds the chapters): `{cite Kol07}[Definition 29]`
renders as `[Kol07, Definition 29]`, linked to the entry in the Blueprint Bibliography, the part
that `{blueprint_bibliography}` adds at the end of `Blueprint.lean`, listing the entries that the
chapters and the annotation boxes cite with the places they are cited from. The citations
`[Kol07, Definition 29]` of the docstring annotation items link the same way. A citation whose
link is a name rather than the bracketed tag, `{citeAs Ati70}[Atiyah's Resolution Theorem]` in a
chapter and `[Atiyah's Resolution Theorem][Ati70]` in a docstring (the form doc-gen4 reads too),
is for the few places where a named result or author stands right before its source; the
bracketed form is the default. The text shown is the
entry's tag, generated from its authors and year as doc-gen4 does, which is the key for every entry
but `Sta`, shown as `[TSPA]`. `python3 ../scripts/check_references.py` checks that every key the
chapters cite is in the file and every entry is cited somewhere.
