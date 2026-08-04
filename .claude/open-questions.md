# Open questions — decisions blocking contract v1

Five. Each has a `gate:owner` issue. Each names what changes either way, so the
answer is a choice and not an essay.

Ranked by how much they block.

---

## Q1 — Which arXiv version of `math/0212237` was §8 formalized against?

**Blocks:** the registry schema's `source.version` is `required` when
`scheme == arxiv`, so no entry can be minted until this is known.
**Effort to answer:** 5 minutes, by opening `arxiv.org/abs/math/0212237`.

**Nothing on this machine knows.** The live `bridgeland-stability` notebook
records `arxiv_version = ''` — and the red team found this is not specific to
this paper: it is `''` for **every row in both live notebooks** (8/8 sampled in
each). The corpus **structurally cannot represent a version**.

This must be **confirmed by reading the abstract page, not inferred**. Every
downstream artifact pins it, and the unversioned form silently resolves to
arXiv's latest — so after the author posts a v3 and the operator re-ingests, the
resolver would match against v3 bytes and write `status: current` for an entry
declaring v2.

**Consequence either way:** the answer goes into `formalization.yaml`
`source.id` and into every registry entry. It also forces an arXMCP-side
change — an `arxiv_version` backfill in ingest — which is a **third** arXMCP CLI
change, not the two the architecture budgeted.

---

## Q2 — Third repo (`math-formal-contract`), or `arXMCP/contract/`? — **ANSWERED**

**Answered 2026-08-04 (UTC): `arXMCP/contract/`.** Full reasoning and the
correction of the earlier recommendation are in
[`decisions/ADR-0007`](decisions/ADR-0007-contract-package-location.md).

Short version: the recorded verdict was read in full rather than in summary,
and it dissolves the case for overriding it. There is only one `mfc`
implementation, so a fixture corpus cannot referee "two implementations"
wherever it lives; the drift problem already has a precedented fix in this
ecosystem (`personal-website` vendors pinned bridge contracts with a
checksum-drift test); and the verdict explicitly rejected "create it now" as to
*timing*, on reasoning that holds exactly at N=1 adopter.

**The larger finding:** a versioned bridge-contract system already exists
(§5 of the same document) — a common envelope, an artifact-type registry that
already contains `verdict-record` with *"statement hash, toolchain/env
versions"*, per-type MAJOR.MINOR versioning, and a `GET /bridge/contracts`
handshake. Our artifacts join it. Its rule 7 — *"no shared Python package
imported by both repos"* — also kills `mfc`-as-shared-dependency.

**Reverses when** the ecosystem's own trigger 3 fires ("bridge contracts gain
consumers outside the two repos"), which is the same event as the M3
generalization gate. Sequencing is therefore settled, not judged.

---

## Q3 — Shared Lake dependency for `@[cites]`, or vendored? — **ANSWERED**

**Answered 2026-08-04 (UTC): shared dependency**, recorded as a **named
exception** in `CLAUDE.md` §1 rather than taken silently. Full record in
[`decisions/ADR-0008`](decisions/ADR-0008-cites-is-a-shared-lake-dependency.md).

Vendoring turned out not to be an option rather than a worse option: `@[cites]`
is a `SimplePersistentEnvExtension`, and duplicate attribute registration is an
import-time error, so two vendored topic repos could never coexist in one Lean
environment.

The exception is **bounded and lapses**: it rests on the package being a leaf
with zero transitive dependencies (core Lean only, no Mathlib, no anchor). If
that stops being true, the dependency comes out — it is not grandfathered.

**One consequence worth knowing:** the package does **not** live in
`arXMCP/contract/`, despite ADR-0007 putting the schemas there. A
`[[require]]` on arXMCP would falsify the sentence written into that repo's
`CLAUDE.md` §4.10 the same day — *"Sibling, never a subdirectory, never a
dependency."* So the Lean package gets its own minimal Lean-only repo, and a
topic repo pins two things that move on different clocks. That is deliberate,
not an oversight; see ADR-0008 for why it does not relitigate ADR-0007.

---

## Q4 — What is the registry's size ceiling, and is there a `sketch` lane?

**Blocks:** nothing immediately. **But the red team names this the single
biggest risk to the whole plan.**

The arithmetic: minting an entry is 20–40 min; a faithfulness review is ~2 h.
Ten entries ≈ 5–8 owner-days. The notebook has **146 papers / 15,280 chunks**.
One entry per paper ≈ 36–73 owner-days ≈ 2–4 months full-time for one person.
At ten entries the served surface has a **~0.07% hit rate**, and an LLM that
queries it three times, gets nothing, and stops querying is behaving rationally.

> the plan's most likely six-month state is not a broken contract but an
> immaculate, green, **empty** one: CI passing, digests matching, `caveats[]`
> correctly generated, ten entries, and nothing reading it.

`faithfulness: agent_drafted` was **deliberately rejected** (ADR-0005) — it would
let an LLM verdict occupy the one human axis. That rejection is right, but
rejecting it without a substitute makes volume unreachable by any route.

**The options:**

1. **10 curated entries, permanently.** Honest, and the served resource carries a
   dated coverage census so nobody mistakes it for corpus-wide.
2. **Add a `kind: sketch` lane** — agent-drafted, satisfies **zero** axes,
   excluded from `required_axes` filtering, mandatory caveat. Volume without
   letting an LLM occupy a human axis.
3. **A second reviewer**, which changes the arithmetic but not the shape.

Recommendation: **1 + 2 together.** The census is required by arXMCP `CLAUDE.md`
§4.9 anyway ("novelty claims are dated censuses"), so it is policy-compliant
rather than new.

---

## Q5 — `quote_mode`: `verbatim` or `digest_only` by default?

**Blocks:** the registry schema (M2). Lowest stakes of the five.

Registry entries inline verbatim statement text. Bridgeland 2007 is arXiv
perpetual-non-exclusive, so this is fine **here**. A future adopter's source may
not be.

`digest_only` weakens offline verification — the topic repo can no longer
recompute its own hash from the inline quote — and degrades resolution to
`printed_number`, which is exactly the field most likely to be **absent** on
textbook and PDF-OCR sources (`_extract_printed_number` lives only in the
ar5iv/LaTeXML chunker; coverage is 36 of 66 chunks even on the flagship paper).

Recommendation: **`quote_mode` required from v1**, so the two grounding
strengths are always distinguishable in the served record, with `verbatim` the
default for arXiv sources.
