# CLAUDE.md — context for agents working in BridgelandStabLean

Read `README.md` first for the mathematical framing. This file is the working
rules.

## 1. The pins are load-bearing

- `lean-toolchain` is `leanprover/lean4:v4.29.0`.
- `lakefile.toml` pins `BridgelandStability` to commit `9e48f23a382…` — an
  **exact commit, never a branch**.
- Mathlib (`8a178386ffc0…`) arrives **transitively** through the anchor.
  Do not add a direct Mathlib `require`. A second pin is a second thing to
  drift, and the point of this repo is a citable, reproducible environment.

Bumping any pin is a deliberate act with a `formalization.yaml` update in the
same commit. Never bump one to make a build error go away.

### Named exceptions to the one-pin rule

Exactly one, and it is listed here so a second one cannot be added quietly.

**`MathFormalContract`** — the `@[cites]` attribute and the evidence emitter,
a `[[require]]` at an exact commit. Decided in
[`ADR-0008`](.claude/decisions/ADR-0008-cites-is-a-shared-lake-dependency.md).

Vendoring it is not an option rather than a worse option: `@[cites]` is a
`SimplePersistentEnvExtension`, and **duplicate attribute registration is an
import-time error**, so two vendored topic repos could never coexist in one
Lean environment.

The exception is bounded by the property that justifies it — **the package is a
leaf with zero transitive dependencies**, core Lean only, no Mathlib and no
anchor. It cannot drag anything else in and cannot disagree with the anchor
about a Mathlib revision. **If that ever stops being true, the exception
lapses** and the dependency comes out; it is not grandfathered.

Everything else in §1 applies to it unchanged: exact commit, never a branch,
bumped deliberately with a `formalization.yaml` update in the same commit.

Do **not** add a `[[require]]` on arXMCP to get this package. That repo's
`CLAUDE.md` §4.10 states the relationship is *"Sibling, never a subdirectory,
never a dependency"*, and a Lake require would make that false.

## 2. No `sorry`. Absent beats sorry-backed.

`fidelity.sorry_count` is `0` and should stay there.

When a result is not yet proved, **do not declare it with `sorry`** — leave it
undeclared and write the intent in a `TODO` comment. `GroupAction/NormalizedShift.lean`
demonstrates the pattern: the `Group` instance is described precisely and not
declared. A sorry-backed instance typechecks, gets imported, and silently
launders an unproved claim into everything downstream.

## 3. Never conflate the lattice model with geometry

`Lattice/NumericalK.lean` uses `Fin 2 → ℤ` as a stand-in for `K_num(Ku(X))`.

A lemma proved there is a theorem about **any rank-2 torsion-free lattice**.
It is not a theorem about a Kuznetsov component, a surface, or any geometric
object. The identification requires `D^b(Coh X)`, which Mathlib does not have.

Do not name a declaration in a way that implies otherwise. Do not write
doc-comments claiming a geometric consequence. If a statement needs the
identification, it belongs in the assumption frontier, not in a proof.

## 4. The geometric lane is closed

Do not start work requiring coherent sheaves on a scheme, `D^b(Coh X)`, Serre
duality, Chern characters, HRR, numerical Grothendieck groups of varieties,
semiorthogonal decompositions, or Fourier–Mukai transforms. None exist in
Mathlib at the pinned commit. Building them is a multi-year Mathlib program,
not a task in this repo.

If a proposed target needs any of them, say so and stop rather than
axiomatizing the gap.

## 5. Order of work in lane 1 (§8)

1. ~~`Group` instance on `NormalizedShift`.~~ **Done** (2026-08-03) — via
   `toOrderIso_injective` + the `@[ext]` lemma `ext'`. Note `ext'`, not `ext`:
   Lean auto-generates `NormalizedShift.ext` for the structure, so the
   pointwise lemma needs a distinct name.
2. ~~Pair with `T ∈ GL⁺(2, ℝ)` under the shared-map-on-`S¹` condition.~~
   **Done** (2026-08-03) — `GLTilde`. The `Group` instance must be
   `noncomputable`: `GLPos` membership is a `0 < det` condition and `ℝ`'s
   `LinearOrder` is noncomputable. Invert via group multiplication
   (`inv_mul_cancel` on `GLPos`), never via `Matrix.inv` — the nonsingular
   inverse then never has to appear.
3. The action on stability conditions. **Read
   [`notes/anchor-api-map.md`](notes/anchor-api-map.md) first** — it maps every
   anchor type this step touches, straight from the pinned checkout, and
   stages it 3a / 3b / 3c.
   - **3a — action on `Slicing`. Done** (2026-08-03),
     `GroupAction/SlicingAction.lean`.
   - **3b — action on `PreStabilityCondition.WithClassMap`. Done**
     (2026-08-03), `GroupAction/PreStabilityAction.lean` + `actC` in
     `ComplexBridge.lean`.
   - **3c — action on `StabilityCondition.WithClassMap`. Done** (2026-08-03),
     `GroupAction/StabilityAction.lean`. **The §8 `G̃L⁺(2, ℝ)` action is
     complete.**

   Remaining on this track: the covering-space identification of `GLTilde`,
   and the autoequivalence (`Aut`) half of §8 — **groundwork landed**
   (`GroupAction/AutAction.lean`: `PostnikovTower.mapF`, `HNFiltration.mapF`,
   `Slicing.mapEquiv`), the action on `WithClassMap` not.

   Two packagings exist, both on **slicings only**:

   - `GroupAction/QuotAutAction.lean` — **the general one.** `AutQuot C` is
     triangulated auto-equivalences modulo natural isomorphism, a genuine
     `Group` with `MulAction (AutQuot C) (Slicing C)`. Excludes nothing.
     Prefer this. Note `AutQuot` is a plain `def`, so use `AutQuot.mk` — a
     bare `Quotient.mk` leaves `•` unable to find its instance.
   - `GroupAction/StrictAutAction.lean` — the cheap special case, a group
     mapping *strictly* into `C ⥤ C`. Its `map_one`/`map_mul` are equalities
     of functors, so each `F g` is an **isomorphism of categories** and Serre
     functors and spherical twists are out of its scope.

   **Do not write "the `Aut` action is formalized" for either.** Neither acts
   on stability conditions, so neither is §8's `Aut` action.

   Still needed for stability conditions: `K₀` functoriality, a class-map
   compatibility datum, and invariance of strict finite length under an
   *equivalence* of interval categories (a different problem from 3c — phase
   windows do not move here, so
   `interval_thinFiniteLength_of_inclusion_strict` does not apply).
   [`notes/anchor-api-map.md`](notes/anchor-api-map.md) §7.

   Facts worth having up front:

   - A non-`module` file imports the anchor fine — no migration needed.
   - The anchor is **not** covered by `lake exe cache get`; it is built now,
     keep it that way.
   - Inside a `MulAction` instance's own elaboration `•` is opaque, so `simp`
     needs a `show` to see through it.
   - The anchor's `ext` lemmas live in `StabilityCondition/Basic.lean`, not
     `Defs.lean`. The auto-generated structure `ext` is useless — it demands
     equality of the `compat'` proofs.
   - On `ℂ`, `smul_smul` will not match `m • r • z` (different instance
     paths). Convert out with `Complex.real_smul`, then `push_cast; ring`.
   - **`Deformation/` is not only deformation theory.** It carries general
     interval-category infrastructure that `IntervalCategory/` does not — the
     whole `interval_*_of_inclusion_strict` family lives in
     `Deformation/IntervalSelection.lean`. Searching only `IntervalCategory/`
     and `QuasiAbelian/` once produced a false "the anchor lacks this" finding.
     **Search the whole anchor before concluding something is missing.**

Three claims to keep off the page.

- **"The §8 action is formalized"** — half of it is. The `G̃L⁺(2, ℝ)` half is
  complete on stability conditions (steps 1–3c). The autoequivalence half is
  landed on **slicings only**; the action on `WithClassMap` is not declared.
  Say which half.
- **"`GLTilde` is a formalized universal cover"** — no. Only the group law and
  nonemptiness are proved. Surjectivity of the projection, the `ℤ` fibre, and
  simple connectedness are all untouched.
- **"`AutQuot` is `Aut(D)`"** — not proved. Its setoid asks for the functors
  *and* the inverses to be naturally isomorphic; adjoint uniqueness would make
  the second redundant, but that is not imported here, so the relation is a
  priori finer and `AutQuot` a priori larger. Everything proved about
  `AutQuot` holds; that it *equals* `Aut(D)` does not.

Related: do not cite `StrictAut` as the `Aut` action either. Its `F g` are
isomorphisms of categories, not equivalences, so Serre functors and spherical
twists are outside it. `QuotAutAction` supersedes it for slicings.

Step 3 is the first declaration here that touches the anchor's API. **Read
`BridgelandStability/Slicing/` and `BridgelandStability/StabilityCondition/`
end to end before attempting it.** Guessing at that API and iterating against
compile errors wastes a full Mathlib rebuild per guess.

## 6. `formalization.yaml` is a claim, not decoration

Its schema mirrors the anchor's key-for-key so one parser reads both. Keep it
that way; do not rename keys.

Every field is a claim someone may cite. `human_review: none` stays `none`
until a human actually reviews. `builds_clean` is `pending` until a clean
build is observed, and carries the date when it is. Fields that cannot be
filled honestly say `none` or `pending` — never a flattering guess.

## 7. Build

```bash
lake exe cache get && lake build
```

`lake exe cache get` pulls prebuilt Mathlib oleans. Skipping it means
compiling Mathlib from source — hours, not minutes.

## 8. Relationship to arXMCP

Sibling repo, never a subdirectory. Never a `require`, never a submodule.
Nothing here imports anything from it, and nothing here runs while it does.

arXMCP is a local-first, loopback-only, **read-only** retrieval server over a
LanceDB corpus of parsed arXiv papers, organized into per-topic notebooks. The
`bridgeland-stability` notebook is the corpus behind this repo's sources.

### Three things this section used to assert that are false

Kept, because the corrections are the useful part.

- **Its R5 track does not pin released formalizations or serve trust records.**
  R5 is a brief with no `plans/` entry; `get_formal_targets` / `formal_targets`
  return zero hits in `server/`; and `find -iname "*formaliz*"` across arXMCP
  returns zero files. There is no parser.
- **arXMCP's `CLAUDE.md` §4.8 does not forbid hosting formalization work.** Its
  three rules are: the server never runs agents; writes enter only via offline
  ingest CLIs or operator-gated `/ui/` actions; the orchestrator loop lives in
  a separate repo. The prohibition on hosting formalization is in
  `.claude/roadmap-briefs/R5-formal-target-registry.md` — an unroadmapped
  brief, topic-scoped to geometry. Cite the brief, not §4.8.
- **`formalization.yaml` is not "the entire interface."** It has no reader, on
  either side.

### The rules that do bind

1. arXMCP is a read-only data plane. Nothing here may ask it to write, to run
   an agent, or to hold formalization source.
2. **An arXMCP Lean verdict is not evidence about this environment.** Its REPL
   runs v4.31.0 from a directory outside that repo; we pin v4.29.0. Its axiom
   audit fails open on `set_option … in theorem` and on `open … in theorem`.
   Do not quote a `lean_verify` result here as if it were a build result.
3. **No bare "verified."** arXMCP's §4.9 forbids any single token collapsing
   distinct trust questions, and no axis may be inferred from another. That
   binds anything this repo publishes for it to serve — see §2, which is the
   same rule pointed the other way.

### The contract that replaces the prose

Designed 2026-08-03; **not yet built.** A cold seam of versioned files
exchanged at git tags, with statement identity minted *here* and containing
zero corpus-derived bytes. Read [`.claude/decisions/`](.claude/decisions/) in
numeric order before touching anything that crosses the boundary — the ADRs
are short and they are the whole design. Work is tracked in
[`.claude/roadmap/contract-v1.yaml`](.claude/roadmap/contract-v1.yaml) and on
the GitHub issue tracker.

Until it ships the boundary is **unilateral**: arXMCP contains zero documents
mentioning this repo. Do not write text here that assumes otherwise, and do
not describe the contract in the present tense.
