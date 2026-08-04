# ADR-0007 — Where the contract package lives

- **Status:** **OPEN — needs an owner decision (Chris Dare)**
- **Date raised:** 2026-08-04
- **Blocks:** every epic in milestone M1. Nothing downstream can start until this
  is settled, because it decides where the schemas and fixtures are committed.
- **Tracked as:** `gate:owner` issue in the M1 milestone.

## Context

The contract needs a home for: seven JSON Schemas, the language-neutral
adversarial fixture corpus, the `mfc` CLI, a zero-dependency Lake package
(`@[cites]` attribute + emitter library), and the copier template.

The recommended architecture says a **third repo, `math-formal-contract`**.
**This contradicts a recorded verdict.** `arXMCP/_pipeline/stage-1-discovery/synthesis/target-architecture.md:113-126`
says **"NOT NOW — create on trigger"**, rejecting a third repo on the grounds it
*"would be nearly empty (a handful of schemas)"*, and assigns contract custody to
`math-research-orchestrator` on that repo's creation.

## The two options

### A. Third repo, `math-formal-contract` (the architecture's recommendation)

**For.** The conformance corpus **must** live outside both implementations, or
neither side can be prevented from drifting the tests toward its own behaviour —
this is the Bowtie / JSON-Schema-Test-Suite model, and it is the only reason
cross-repo contract tests work at all. With N topic repos the corpus cannot live
in any one of them. The Lake package must be a shared dependency rather than
vendored, because `@[cites]` is a `SimplePersistentEnvExtension` and **duplicate
attribute registration is an import-time error** — two vendored topic repos could
never coexist in one Lean environment.

**Against.** It overrides a recorded architecture verdict. It is a fourth thing
to pin, version, and keep alive. At N=1 adopter it really is nearly empty.

### B. `arXMCP/contract/`, vendored by topic repos

**For.** No new repo. Defensible under Pact, where the *consumer* writes the
contract. Zero override of the recorded verdict.

**Against.** Adopter #2 needs commit rights on the shared server repo or must
fork it, in order to add fixtures about their own topic. And the fixture corpus
then lives inside one of the two implementations it is supposed to referee.

## What is identical either way

The seven schemas, the fixture corpus contents, `mfc`'s command surface, the
emitter's behaviour, and every other ADR here. Only the import path, the pin
count, and who can push change.

## Recommendation

**Option A**, on the narrow ground that the fixture corpus cannot referee two
implementations from inside one of them — which is a correctness argument, not a
tidiness one. The "nearly empty" objection is answered by what it actually
contains: 7 schemas + ~15 adversarial fixtures + a CLI + a Lake package +
a copier template is not a handful of schemas.

If Option B is chosen, add a compensating rule: the fixture corpus is
append-only and PR-gated, and arXMCP's own CI is forbidden from modifying a
fixture in the same commit as a behaviour change.

## Related open question

ADR-0007 does not settle whether the Lake package is a **shared `[[require]]`**
or **vendored**. That is a separate call against this repo's `CLAUDE.md` §1
("a second pin is a second thing to drift"). The recommendation is the shared
dependency, on the grounds that it is a leaf package with **zero** transitive
dependencies — core Lean only, no Mathlib — making it the least drift-prone pin
in the tree. But §1 is the standing rule and this is an exception to it, so it
is the owner's call. See `open-questions.md` Q3.
