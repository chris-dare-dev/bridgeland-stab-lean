# ADR-0007 — Where the contract package lives

- **Status:** accepted — **Option B, `arXMCP/contract/`**
- **Date raised:** 2026-08-04 (UTC) · **Decided:** 2026-08-04 (UTC)
- **Deciders:** Chris Dare (delegated), on the reading below
- **Supersedes:** the Option A recommendation this ADR carried when first
  written. That recommendation was **wrong**, and the correction is the point
  of this record — see "Why the first recommendation was wrong".

## Decision

The contract's schemas, fixtures, and CLI live in **`arXMCP/contract/`**, and
topic repos **vendor pinned copies** with a checksum-drift test.

The third repo (`math-research-orchestrator`) is **not** created now. It is
created when the ecosystem's own recorded trigger fires — see "When this
reverses", which is a real dated condition, not an aspiration.

## Why the first recommendation was wrong

The first draft of this ADR recommended a third repo, on the ground that a
conformance fixture corpus cannot referee two implementations from inside one
of them. It cited the recorded verdict as *"NOT NOW — create on trigger"* and
argued for overriding it.

Reading the verdict in full — `_pipeline/stage-1-discovery/synthesis/target-architecture.md`
**§4.2** (note: `_pipeline/` is at the *Source Code* root, **not** inside
arXMCP; the audit's path was wrong) — dissolves the argument three ways:

1. **The referee argument is thin here, because there is only one
   implementation.** The Bowtie / JSON-Schema-Test-Suite model works because
   ~20 independent implementations run the corpus. `mfc` was designed to run on
   both sides, which the red team already flagged (gap 16) as removing the
   check the corpus exists to provide. A corpus cannot referee one
   implementation from anywhere. The fix is gap 16's — hand-computed expected
   digests checked into the fixtures — and it works regardless of location.
2. **The drift problem already has a working, precedented solution in this
   ecosystem.** §4.1: `personal-website` vendors pinned copies of the bridge
   contracts under `.claude/references/bridge/<major>/` **with a checksum-drift
   test**, mirroring the `EXPECTED_TOOL_SCHEMA_SHA256` idiom. That is the
   practical failure — producer silently changes the contract — and it is
   solved without a third repo.
3. **The verdict already considered and rejected this exact argument, as to
   timing.** Verbatim: *"starting it as an arXMCP `.claude/` pipeline with
   envelope-wrapped outputs costs nothing to move later (prompts + scripts
   relocate cheaply), whereas standing up the repo first pays the
   third-constitution tax before any code exists."* With N=1 adopter that
   reasoning holds exactly.

The override was argued from the audit's one-line summary of §4.2. The full
section is a four-trigger decision procedure with a documented losing option,
not a preference. **Do not override a recorded verdict from a summary of it.**

## The larger finding: there is already a bridge contract, and this must join it

§5 of the same document specifies a versioned bridge-contract system that this
design independently re-derived. Composing with it is not optional politeness;
duplicating it would be the failure mode this whole track exists to prevent.

- **§5.1 — "Written-artifact contracts over live coupling … The bridge never
  crosses the network."** This is ADR-0001's cold seam, already adopted
  ecosystem-wide. ADR-0001 is *conformance*, not innovation.
- **§5.2 — a common envelope** every bridge artifact carries:
  `bridge.{artifact, version, producer, produced_at, substrate{server,
  corpus_version, notebook{slug,uri}, filter_echo, retrieval_mode,
  tool_schema_sha256}}` + `payload`. **Our artifacts must use this envelope**,
  not a parallel one.
- **§5.3 — an artifact-type registry that already contains our artifacts.**
  `verdict-record` is *"lean_verify wrapper / panel agents → domain-tagged
  verdict, per-domain vocabulary, **statement hash, toolchain/env versions**"*
  — substantially the attestation bundle. `notebook-ref` already carries the
  `corpus_version` pin. Register new types there; do not mint a private
  namespace.
- **§5.4 rule 7 — "no shared Python package imported by both repos."** This
  **kills `mfc`-as-shared-dependency** as designed. Each side validates with
  its own machinery against vendored schemas.
- **§5.4 rule 4 — registry + handshake:** `GET /bridge/contracts` → type→version
  map + schema SHA-256s, with vendored pins compared in a preflight that halts
  on mismatch. That is where a topic repo checks it is pinned to a live
  contract version.
- **§5.4 rule 6 — verdict vocabularies do not unify.** SP2 measured exactly
  `["VERIFIED"]` overlap across pipelines. Our seven axes are the
  *formalization-domain* vocabulary, not a global enum — which is also
  ADR-0005 restated.

## Consequences

**Good.** No third constitution, no third `.claude/` world, no new pin for a
solo operator. The contract inherits an existing versioning discipline,
handshake endpoint, and vendoring precedent rather than inventing three.
ADR-0001 through ADR-0006 are unaffected — every one of them is about *what*
the contract says, and none about where the schemas are committed.

**Costs, accepted.**

- **Adopter #2 needs commit rights on arXMCP, or a fork, to add fixtures about
  their own topic.** This is the real price. It is also precisely the condition
  that fires the third-repo trigger, so it is self-limiting rather than
  permanent.
- **The fixture corpus lives inside one of the implementations it referees.**
  Compensating rule, adopted: the corpus is **append-only and PR-gated**, and
  arXMCP CI may not modify a fixture in the same commit as a behaviour change.
  Plus gap 16's hand-computed digests, which pin canonicalization by data.
- **`mfc` is no longer a shared package.** It ships as an arXMCP-side CLI. The
  topic repo's half is its Lean emitter plus schema validation against vendored
  copies — no cross-repo Python import.

**Unaffected.** The `@[cites]` attribute and the Lean emitter library are a
*Lean* dependency, not a Python one, so §5.4 rule 7 does not reach them. Where
that Lake package lives is a separate question — see `open-questions.md` Q3,
still open.

## When this reverses

§4.2 names four triggers. **Trigger 3 — "bridge contracts gain consumers
outside the two repos" — is the one that governs here**, and it fires when a
*second topic repo* adopts the contract.

That is the same event as the M3 generalization gate (GitHub #56). So the
sequencing is settled rather than judged: build in `arXMCP/contract/` now; when
adopter #2 is real, the trigger has fired and contracts move to
`math-research-orchestrator`, which §4.2 says *"on creation takes contracts
custody (both repos then vendor)"* — the vendoring pattern is already what we
are doing, so the move is a path change, not a redesign.

Note `bridgeland-stab-lean` is arguably already a consumer outside "the two
repos" (arXMCP + personal-website), so trigger 3 is defensibly already met. It
is not being called met, on the same timing logic the verdict used: one
consumer does not need a registry to be shared.
