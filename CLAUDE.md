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
   - **3c — action on `StabilityCondition.WithClassMap`.** Next, and the
     hardest. Needs local finiteness preserved, which needs uniform
     continuity of `f⁻¹`. Schedule alone.

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

Two claims to keep off the page. Do not describe the current state as "the §8
action is formalized" — there is no action on a stability condition until
step 3. And do not call `GLTilde` a formalized universal cover: only the
group law and nonemptiness are proved. Surjectivity of the projection, the
`ℤ` fibre, and simple connectedness are all untouched.

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

Sibling repo, never a subdirectory. arXMCP is a read-only retrieval data
plane whose R5 track pins *released* formalizations and serves their trust
records; it does not host formalization work, and its CLAUDE.md §4.8
data-plane boundary forbids it. `formalization.yaml` is the entire interface.
