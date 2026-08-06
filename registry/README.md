# The statement registry

`bridgeland2007.json` is the only hand-authored contract artifact in this repo,
and the only place a citation key is minted. Everything else is measured.

Validate it with the contract package:

```sh
mfc registry validate registry/bridgeland2007.json --frontier-kind-labels mathlib-gap
```

## Rules that are easy to break by typing

- **The registry id is minted once and never changes.** `a520a8d4f877`, from
  `mfc registry init`. It is the middle segment of every key and it is not
  derived from the notebook slug — slugs live in a machine-local sqlite database
  with no global registry, so two adopters both choosing the same one would
  collide silently.
- **A key contains zero corpus-derived bytes.** No `chunk_id`, no
  `corpus_version`, no notebook slug. `chunk_id` rotates on any re-parse, there
  is no alias table, and `merge_insert` has no delete arm — so an id we minted
  from corpus bytes is an id we break. `R-06` refuses a key shaped like one.
- **Edit a `quote` and you must recompute its `quote_sha256`.** `R-02` is the
  only rule that compares a digest to the text it summarizes rather than to
  another digest, and it will catch this.
- **`relation_claimed: exact` is not available while an entry has an open
  frontier item.** That is `E-05`, and it is the reason `lem-8.2` cannot be
  cited `exact` today.

## Why JSON and not YAML

GitHub #34 specifies `bridgeland2007.yaml`. It is JSON, deliberately:

- The quotes are verbatim LaTeX — `$\operatorname{\mathcal{D}}$`, `\phi^{-}`,
  `{\tilde{\operatorname{GL^{+}}}}`. YAML has several ways to quote a string
  containing backslashes and they do not all round-trip to the same bytes. A
  re-serialization that changed one byte would break `quote_sha256` and the
  failure would look like corpus drift rather than like a formatting change.
- `mfc validate` reads YAML only when PyYAML is installed, and reports its
  absence as a missing capability. JSON has no such edge.

`load_artifact` accepts both, so this is reversible if the ergonomics ever
matter more than the byte-stability.

## Provenance of the current entries

Seven statements lifted verbatim from the `bridgeland-stability` arXMCP corpus
and one obligation that has no printed statement. Each quote was verified three
ways at mint time: the registry text is byte-identical to the corpus body, the
declared `quote_sha256` recomputes from it, and the corpus `chunk_id` itself
still recomputes as `sha256(NFC(body_text))[:16]` (every chunk of this paper has
`preamble_ref = NULL`, so the id reduces to that).

**`mint_resolution` is `null` on every entry, with a reason.** No resolver has
been run — `tools/statement_resolve.py` (#43) does not exist. And the corpus
records `arxiv_version = ''` for every row (#44), so even a hash match would be
a match against a probable-but-unconfirmed v3. The version the formalization
targeted is confirmed v3 by the owner; the version that was *ingested* is not
confirmed by anything. Those are two facts and only one is known.
