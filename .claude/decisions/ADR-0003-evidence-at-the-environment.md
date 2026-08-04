# ADR-0003 — Elaboration and axiom evidence is produced only where the environment lives

- **Status:** accepted
- **Date:** 2026-08-04
- **Deciders:** Chris Dare
- **Evidence:** `.claude/notes/2026-08-04-arxmcp-lean-integration-audit.md` §2

## Context

arXMCP has a `lean_verify` tool. It is not a stub — 1459 lines over a 483-line
REPL harness, the largest handler in that repo. The tempting design is to let it
produce the contract's elaboration and axiom evidence. The audit found four
reasons that would be unsound, and one of them is a demonstrated exploit.

**1. Wrong environment.** Its REPL is Lean v4.31.0; this repo pins v4.29.0. No
`lean-toolchain`, lakefile, or repl commit is pinned anywhere in arXMCP, and no
result carries library identity — a grep for `mathlib_rev|toolchain|lean_version`
over `server/` returns 4 hits, all comments and error strings.

**2. Demonstrated fail-open.** The declaration-name extractor
(`_DECL_SITE_RE` / `_DECL_NAME_RE`, `server/handlers/lean_verify.py:445-456`)
matches neither sites nor names for the legal single-line forms:

```lean
set_option maxHeartbeats 400000 in theorem sneaky : False := bad
open Classical in theorem sneaky : False := bad
```

The verifying agent **executed the regexes** and reproduced `(['good'], True)`:
`complete` stays `True`, `sneaky` is never `#print axioms`-ed, and the record
emits `outcome: "clean"`.

**3. `status: "ok"` is not a trust verdict**, by arXMCP's own admission —
`.claude/roadmap-briefs/R3-verification-contract.md:4-12`: *"the current surface
can be made to say `ok` to an `axiom`-backed proof."* The rename to
`elaborated_no_errors` is queued and not shipped.

**4. Source-parsing is the wrong mechanism.** Any regex over Lean source is a
race against Lean's grammar, which the grammar wins.

## Decision

**All elaboration and axiom evidence is produced by this repo, in this repo's
pinned environment, by sweeping the kernel's own data structures.**

`lake exe mfc-emit` walks `Environment.constants` and calls
`Lean.collectAxioms`. **It never parses source.** The `set_option … in` evasion
above is therefore not merely caught but structurally impossible on the
producing side — there is no text for it to hide in.

**arXMCP is forbidden by construction from producing this evidence.** Every axis
record carries an `env_digest`. Any axis whose `env_digest` differs from the
record's environment renders **`not_applicable`** — never `pass`, never `fail`.
That converts the v4.31-vs-v4.29 skew from a silent soundness hole into a value
in the type system. `lean_verify` output is admissible only under a reserved
predicate type that satisfies **zero** axes.

`env_digest = sha256(canonical_json({lean_toolchain, lean_githash, resolved
leanOptions, sorted [(name, rev)]}))` — hashing `rev`, never `inputRev` (nine
packages in the manifest carry `inputRev: "main"`), and including
`[leanOptions] autoImplicit = false` because it is elaboration-affecting.

## Consequences

**The shared axiom allowlist becomes the contract's one pre-existing
touchpoint.** `AXIOM_ALLOWLIST = frozenset({"propext", "Quot.sound",
"Classical.choice"})` at `lean_verify.py:397-399` is **byte-identical** to what
`formalization.yaml:82-90` claims for every audited declaration in this repo.
That agreement is now load-bearing and should be pinned by a fixture on both
sides rather than left as a coincidence.

**Two emitter defects must be fixed before the reproducibility gate can pass.**
The ground-phase probe found `collectAxioms` output is **unsorted** —
`["propext","Quot.sound","Classical.choice"]` on one declaration and
`["Quot.sound","propext","Classical.choice"]` on the next. Sort every emitted
array. And emission must be **module-scoped** to the topic's `lean_lib`, not
name-prefix-scoped, or a declaration outside the prefix escapes the sweep.

**`lake env lean scripts/Audit.lean` is not a gate and cannot become one.** It
exits 0 even when `#print axioms` prints `[sorryAx]`, its output is unstructured
prose that wraps unpredictably (2 of 42 entries wrapped over three lines), and
`scripts/` is covered by no `lean_lib` so `lake build` never builds it. The
emitter replaces it; the script's own header already admits it can rot.

**arXMCP still needs its `lean_verify` repaired** — not because the contract
depends on it, but because it is on the same wire an agent reads. Today an agent
can get `outcome: "clean"` on a sorry-backed proof from the tool sitting next to
the honest record. Tracked as a cross-repo epic.
