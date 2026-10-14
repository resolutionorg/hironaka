#!/usr/bin/env python3
"""Compare the `sources` of a `formalization.yaml` with `references.bib`.

Each source other than an `original-proof` has the `title` of an entry of the bibliography (braces
dropped), and the `authors` of that entry (names as first names and last name). The other generated
parts of the file, `status.main_results` and `alignment.statements`, are written and checked by
`scripts/sync_formalization.lean`, which reads the `Source statement:` paragraphs of the docstrings.

Usage, from the directory of `lakefile.toml`:
  uv run --with pyyaml python3 scripts/check_formalization_yaml.py formalization.yaml
Exits with status 1 on a discrepancy, 2 on a usage error or without PyYAML.
"""

import sys

from check_references import BIB, BibError, read_bib


def plain(value):
    """A field value as text: braces dropped, `--` an en dash, white space collapsed."""
    text = value.replace("{", "").replace("}", "").replace("---", "—").replace("--", "–")
    return " ".join(text.split())


def split_top(value, sep):
    """`value` split at the occurrences of `sep` outside braces."""
    parts, depth, start, i = [], 0, 0, 0
    while i < len(value):
        if value[i] in "{}":
            depth += 1 if value[i] == "{" else -1
        elif depth == 0 and value.startswith(sep, i):
            parts.append(value[start:i])
            start = i = i + len(sep)
            continue
        i += 1
    return parts + [value[start:]]


def authors(entry):
    """The authors of an entry as (first names, last name); a name in braces is a last name."""
    names = []
    for name in split_top(entry.fields.get("author", ""), " and "):
        parts = split_top(name.strip(), ",")
        if len(parts) > 1:
            names.append((plain(",".join(parts[1:])), plain(parts[0])))
        else:
            words = split_top(name.strip(), " ")
            names.append((plain(" ".join(words[:-1])), plain(words[-1])))
    return names


def check_sources(doc, entries):
    """The discrepancies between the `sources` of `formalization.yaml` and the bibliography."""
    by_title = {plain(e.fields.get("title", "")): e for e in entries}
    bad = []
    for source in doc.get("sources") or []:
        title = source.get("title", "")
        if source.get("type") == "original-proof":
            continue
        entry = by_title.get(title)
        if entry is None:
            bad.append(f"source {title!r}: no entry of {BIB} has this title")
            continue
        names = [" ".join(filter(None, name)) for name in authors(entry)]
        if source.get("authors") != names:
            bad.append(f"source {title!r}: the authors of `{entry.key}` in {BIB} are {names!r}")
    return bad


def main(argv):
    if len(argv) != 1 or argv[0].startswith("-"):
        print(__doc__)
        return 2
    try:
        import yaml
    except ImportError:
        print("check_formalization_yaml: needs PyYAML; run it with "
              "`uv run --with pyyaml python3 scripts/check_formalization_yaml.py …`")
        return 2
    with open(argv[0], encoding="utf-8") as h:
        doc = yaml.safe_load(h)
    try:
        entries = read_bib()
    except BibError as e:
        print(f"check_formalization_yaml: {e}")
        return 1
    bad = check_sources(doc, entries)
    for b in bad:
        print(f"check_formalization_yaml: {b}")
    if bad:
        print(f"check_formalization_yaml: {len(bad)} discrepancy(ies)")
        return 1
    print(f"check_formalization_yaml: ok ({len(doc.get('sources') or [])} sources)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
