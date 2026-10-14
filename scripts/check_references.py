#!/usr/bin/env python3
r"""The bibliography `references.bib`: its check.

`references.bib`, at the root of the package, is the one list of the sources. Its BibTeX keys are
the keys by which everything cites them: docstrings and comments (`[Hir64, Main Theorem I]`,
among them the `Source statement:` paragraphs that `scripts/sync_formalization.lean` reads), the
blueprint (`{cite Hir64}[Main Theorem I]`, whose registry `Blueprint.References` reads the file
too) and the Markdown files. The check:

* the file is written in the part of BibTeX that every reader of it accepts (`read_bib`, the same
  as `parseBib` in `scripts/sync_formalization.lean`): no key twice, every entry with an author
  and a title, no backslash (accented letters are Unicode characters, not TeX macros);
* a source is listed exactly when the tree cites it. Every key of the file is cited by some `.lean`
  or `.md` file of the package, as `[KEY]` or `[KEY, …]`, or as `{cite KEY}` in the blueprint.
  Conversely, every citation of a key shaped like the keys of the file, capitals and letters
  followed by a two-digit year (`Hir64`, `BM97`, `Wlo05`), is of a key of the file; citations are
  looked for in the comments and docstrings of the `.lean` files, in the whole text of the
  blueprint's chapters and in the Markdown files. (A citation of an unknown key without a year,
  such as `[Sta]`, is not found; `scripts/sync_formalization.lean` rejects an unknown key in a
  `Source statement:` paragraph, and the blueprint rejects one in `{cite}` when it is built.)

Build directories (`.lake`, `_out`, `_site`) are not searched. Usage, from anywhere in the
repository:
  python3 scripts/check_references.py           # prints every discrepancy; status 1 if there is one
`scripts/check_formalization_yaml.py` and `scripts/build_docs.py` read the file with `read_bib`.
"""

import os
import re
import sys
from dataclasses import dataclass, field

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIB = "references.bib"
BLUEPRINT = "blueprint"
SKIP_DIRS = {".git", ".lake", "_out", "_site"}

# A letter of a key: an ASCII letter, or a Latin letter with a diacritic (Latin-1 Supplement and
# Latin Extended-A and -B, without the signs × and ÷), as `isRefKeyChar` in
# `scripts/sync_formalization.lean`.
LETTER = "A-Za-z\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u024f"
KEY = f"[{LETTER}][{LETTER}0-9]*"
# A citation of a key: `[KEY]`, `[KEY, …]`, `{cite KEY}`, `{cite "KEY"}`.
CITATION = re.compile(rf"(?:\[|\{{cite\s+\"?)({KEY})(?=\]|,|\s|\"|\}})")
# A citation in prose of a key shaped like the keys of the file: capitals and letters, then a year.
YEAR_KEY = re.compile(rf"(?:\[|\{{cite\s+\"?)([A-Z][{LETTER}]*[0-9]{{2}})(?=\]|,|\"|\}})")


class BibError(Exception):
    """A malformed bibliography."""


@dataclass
class Entry:
    """An entry of the bibliography: type and field names in lower case, values as written."""
    type: str
    key: str
    line: int
    fields: dict = field(default_factory=dict)


def read_bib(text=None):
    """The entries of `references.bib` (or of the BibTeX text `text`), in order.

    The grammar is that of `parseBib` in `scripts/sync_formalization.lean`: an entry is
    `@type{key, name = {value}, …}`, where the key is a letter followed by letters and digits
    (`KEY`), a field name is made of ASCII letters, digits, `_` and `-`, and a value is text in
    braces (braces inside balanced) or a number; text between entries is a comment, so it must not
    contain `@`. Raises `BibError`, naming the line, on anything else.
    """
    if text is None:
        text = read(BIB)
    entries, i, n = [], 0, len(text)

    def fail(msg, at):
        raise BibError(f"{BIB}, line {text.count(chr(10), 0, at) + 1}: {msg}")

    def skip_ws(j):
        while j < n and text[j].isspace():
            j += 1
        return j

    while True:
        i = text.find("@", i)
        if i < 0:
            return entries
        start = i
        m = re.compile(r"@([A-Za-z]+)\s*\{\s*").match(text, i)
        if not m:
            fail("expected an entry `@type{key, …}`", i)
        k = re.compile(KEY).match(text, m.end())
        if not k:
            fail("expected a key: a letter followed by letters and digits", m.end())
        i = skip_ws(k.end())
        if i >= n or text[i] != ",":
            fail(f"expected `,` after the key `{k.group()}`", i)
        entry = Entry(m.group(1).lower(), k.group(), text.count("\n", 0, start) + 1)
        i += 1
        while True:
            i = skip_ws(i)
            if i < n and text[i] == "}":
                i += 1
                break
            name = re.compile(r"[A-Za-z0-9_-]+").match(text, i)
            if not name:
                fail("expected a field name or `}`", i)
            i = skip_ws(name.end())
            if i >= n or text[i] != "=":
                fail("expected `=` after the field name", i)
            i = skip_ws(i + 1)
            if i < n and text[i] == "{":
                depth, j = 0, i + 1
                while j < n and (text[j] != "}" or depth):
                    depth += {"{": 1, "}": -1}.get(text[j], 0)
                    j += 1
                if j >= n:
                    fail("unexpected end of file", j)
                value, i = text[i + 1:j], j + 1
            elif i < n and text[i].isdigit():
                value = re.compile(r"[0-9]+").match(text, i).group()
                i += len(value)
            else:
                fail("expected a value in braces or a number", i)
            if name.group().lower() in entry.fields:
                fail(f"the field `{name.group().lower()}` occurs twice", i)
            entry.fields[name.group().lower()] = value
            i = skip_ws(i)
            if i < n and text[i] == ",":
                i += 1
            elif i < n and text[i] == "}":
                i += 1
                break
            else:
                fail("expected `,` or `}` after a field", i)
        entries.append(entry)


def read(path):
    with open(os.path.join(ROOT, path), encoding="utf-8") as h:
        return h.read()


def lean_comments(text):
    """The comments and docstrings of a Lean file (string and character literals skipped)."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(text[i:j])
            i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(text[i:j])
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
        elif text[i] == "'" and i + 2 < n and text[i + 2] == "'":
            i += 3
        else:
            i += 1
    return "\n".join(out)


def package_texts():
    """(path, text, prose) for every `.lean` and `.md` file of the package, where `prose` is the
    part searched for citations of unknown keys: the comments of a Lean file outside the
    blueprint, all of any other file."""
    for top, dirs, files in os.walk(ROOT):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
        for name in sorted(files):
            if not name.endswith((".lean", ".md")):
                continue
            path = os.path.relpath(os.path.join(top, name), ROOT)
            text = read(path)
            in_blueprint = path.startswith(BLUEPRINT + os.sep)
            prose = text if name.endswith(".md") or in_blueprint else lean_comments(text)
            yield path, text, prose


def main(argv):
    if argv:
        print(__doc__)
        return 2
    bad = []
    try:
        entries = read_bib()
    except BibError as e:
        print(f"check_references: {e}")
        return 1
    keys = [e.key for e in entries]
    for k in sorted({k for k in keys if keys.count(k) > 1}):
        bad.append(f"the key `{k}` occurs more than once in {BIB}")
    for e in entries:
        for f in ("author", "title"):
            if f not in e.fields:
                bad.append(f"{BIB}, line {e.line}: `{e.key}` has no {f}")
        for f, v in e.fields.items():
            if "\\" in v:
                bad.append(f"{BIB}, line {e.line}: the {f} of `{e.key}` contains a backslash")
            if f in ("url", "doi", "eprint") and (not v or any(c.isspace() for c in v)):
                bad.append(f"{BIB}, line {e.line}: the {f} of `{e.key}` is empty or has spaces")

    cited, cited_by_blueprint, unknown = set(), set(), {}
    for path, text, prose in package_texts():
        found = set(CITATION.findall(text)) & set(keys)
        cited |= found
        if path.startswith(BLUEPRINT + os.sep):
            cited_by_blueprint |= found
        for k in YEAR_KEY.findall(prose):
            if k not in keys:
                unknown.setdefault(k, path)
    for k in keys:
        if k not in cited:
            bad.append(f"`{k}` is in {BIB} but no file of the package cites it")
    for k, path in sorted(unknown.items()):
        bad.append(f"{path} cites `{k}`, which is not in {BIB}")

    for b in bad:
        print(f"check_references: {b}")
    if bad:
        print(f"check_references: {len(bad)} discrepancy(ies)")
        return 1
    print(f"check_references: ok ({len(keys)} references, "
          f"{len(cited_by_blueprint)} cited by the blueprint)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
