# Anchor API map — what step 3 has to talk to

Produced by reading the pinned checkout at
`.lake/packages/BridgelandStability/` (commit `9e48f23`) directly. Every
signature below is copied from source, not recalled. Line references are to
that checkout.

Step 3 is "the `G̃L⁺(2, ℝ)` action on stability conditions". This file exists
because that step is the first one that imports the anchor, and guessing at
its API costs a full rebuild per guess.

---

## 1. The three types

All live in namespace `CategoryTheory.Triangulated`.

### `Slicing C` — `Slicing/Defs.lean:82`

```lean
structure Slicing where
  P : ℝ → ObjectProperty C
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)
```

**`Slicing.ext` already exists** (`Slicing/Defs.lean:99`). Do not write another
one. Note its elaborated signature takes `C` **explicitly**:

```lean
Slicing.ext : ∀ (C : Type u_2) [...] {s t : Slicing C}, s.P = t.P → s = t
```

so it is `Slicing.ext C hP`, not `Slicing.ext hP`.

### `PreStabilityCondition.WithClassMap C v` — `StabilityCondition/Defs.lean:60`

```lean
structure WithClassMap (v : K₀ C →+ Λ) where
  slicing : Slicing C
  Z : Λ →+ ℂ
  compat' : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)
```

### `StabilityCondition.WithClassMap C v` — `StabilityCondition/Defs.lean:126`

```lean
structure WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  locallyFinite : slicing.IsLocallyFinite C
```

### Typeclass context to copy verbatim

```lean
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]
```

**Verified against elaborated signatures, not the source `variable` lines** —
the file-level `variable` block is misleading here:

| Type | needs `[IsTriangulated C]`? |
|---|---|
| `Slicing C` | no |
| `HNFiltration` | no |
| `PreStabilityCondition.WithClassMap` | **no** |
| `StabilityCondition.WithClassMap` | **yes** |

`StabilityCondition/Defs.lean` declares `[IsTriangulated C]` at file scope, but
many declarations carry `omit [IsTriangulated C]`, and
`PreStabilityCondition.WithClassMap` is one that does not need it. So 3a and 3b
can be stated without it; only 3c requires it.

---

## 2. The action, and why the conventions line up

For `x = (T, f) : GLTilde` acting on `σ = (P, Z)`:

- **slicing:** `P' φ := P (f⁻¹ φ)`
- **charge:** `Z' := T ∘ Z`

`f⁻¹` (not `f`) is what makes this a *left* action: `f⁻¹ ∘ h⁻¹ = (h ∘ f)⁻¹`,
and `h * f` in `NormalizedShift` is `h` after `f`. Verified by hand; make it a
test.

### Compatibility is consistent — worked through

Assume `P' φ E`, i.e. `P (f⁻¹ φ) E`. Old `compat'` at phase `f⁻¹ φ` gives
`Z (v[E]) = m · exp(iπ f⁻¹φ)` with `m > 0`. Then

```
Z' (v[E]) = T (m · exp(iπ f⁻¹φ)) = m · T(exp(iπ f⁻¹φ))       (ℝ-linearity, m real)
          = m · r · exp(iπ · f(f⁻¹φ))                        (GLTilde compat)
          = (m·r) · exp(iπφ),      m·r > 0                    ✓
```

The middle step is exactly `Compatible`. So step 2 was the right shape.

### Axiom-by-axiom cost for the new slicing

| Axiom | What it needs | Cost |
|---|---|---|
| `closedUnderIso` | reindexing only | free |
| `zero_mem` | reindexing only | free |
| `shift_iff` | `f⁻¹ (φ + 1) = f⁻¹ φ + 1` | **`NormalizedShift.symm_map_add_one`** |
| `hom_vanishing` | `φ₂ < φ₁ → f⁻¹φ₂ < f⁻¹φ₁` | free from `≃o` |
| `hn_exists` | transport `HNFiltration` | small, see below |

**`shift_iff` is why step 1 exists.** `symm_map_add_one` was proved before
there was any consumer for it; this is the consumer. That is the single
load-bearing link between the `+1`-equivariance condition and Bridgeland's
shift axiom.

### Transporting an `HNFiltration` — `Slicing/Defs.lean:66`

```lean
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C)
    extends PostnikovTower C E where
  φ : Fin n → ℝ
  hφ : StrictAnti φ
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j)
```

`PostnikovTower` (`PostnikovTower/Defs.lean:63`) carries **no phase data** —
chain, triangles, base/top isos only. So transport keeps the tower untouched
and replaces `φ` with `f ∘ φ`. `StrictAnti` survives because `f` is strictly
monotone. `semistable` is then definitional: `P' (f (φ j)) = P (f⁻¹ (f (φ j)))
= P (φ j)`.

---

## 3. The impedance mismatch — read this before writing code

**`Z : Λ →+ ℂ` maps into `ℂ`. `GLTilde.mat` acts on `Fin 2 → ℝ`.**

These do not compose. This is the one real architectural finding of the read.

The bridge exists in Mathlib and the coordinate conventions already agree:

- `Complex.basisOneI : Basis (Fin 2) ℝ ℂ` — `LinearAlgebra/Complex/Module.lean:133`
- `Complex.coe_basisOneI_repr (z : ℂ) : ⇑(basisOneI.repr z) = ![z.re, z.im]` — `:145`, and it is `rfl`
- `Complex.exp_mul_I : exp (x * I) = cos x + sin x * I` — `Analysis/Complex/Trigonometric.lean:519`

So coordinate `0` is the real part, coordinate `1` the imaginary part, and

```
basisOneI.repr (Complex.exp (↑(π * φ) * I)) = ![cos (π*φ), sin (π*φ)] = rayVec φ
```

### RESOLVED — this risk is retired

This was the largest identified risk in the step, so it was closed
immediately rather than left as a note.
`BridgelandStabLean/GroupAction/ComplexBridge.lean` now carries:

- `cplxCoord : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ)` — `Complex.basisOneI.equivFun`
- `cplxCoord_exp : cplxCoord (exp (↑(π * φ) * I)) = rayVec φ` — **proved**
- `compat_exp` — `Compatible` restated on the anchor's `exp (i π ·)` rays,
  which is the form step 3b consumes

So option **A** below is taken, and option B is not needed.

Two traps found while proving it, both costly to rediscover:

- **Do not use `simp`.** It normalises `↑(π * φ)` into `↑π * ↑φ`, after which
  `Complex.exp_ofReal_mul_I_re` no longer matches. Use `rw` throughout.
- **`Basis.equivFun_apply` does not resolve** from our import set, despite
  existing at `LinearAlgebra/Basis/Defs.lean:245`. It is `rfl`, so go through
  `Complex.basisOneI.repr` with a `show` instead.

`Analysis/Complex/Isometry.lean:149-162` remains the worked template if the
full matrix-↔-`ℂ`-linear-map translation is ever needed, determinants included
(`LinearMap.toMatrix basisOneI basisOneI`, `LinearMap.det_toMatrix`).

### The two options, for the record

- **A — keep matrices, bridge at the boundary.** Taken. Keeps
  `Matrix.GLPos`'s free group structure; `Fin 2 → ℝ` never has to appear
  downstream of `ComplexBridge`.
- **B — refactor `GLTilde` onto `ℂ ≃ₗ[ℝ] ℂ`.** Not needed. It would have
  discarded `Matrix.GLPos` and re-done step 2's closure proofs, and
  "GL⁺(2, ℝ)" is literally matrices in Bridgeland's presentation.

---

## 4. The hard part: local finiteness

`Slicing.IsLocallyFinite` — `IntervalCategory/FiniteLength.lean:268`

```lean
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  intervalFinite : ∃ η : ℝ, ∃ hη : 0 < η, ∃ hη' : η < 1 / 2, ∀ t : ℝ, ...
    ∀ (E : s.IntervalCat C a b), IsStrictArtinianObject E ∧ IsStrictNoetherianObject E
```
with `a := t - η`, `b := t + η`.

**A single uniform `η` is quantified over all `t`.** A general normalized shift
distorts intervals, so `(t-η, t+η)` does not map to a window of any fixed
width. Preserving this is not bookkeeping.

It is still true, and the argument is: `f⁻¹` is continuous and satisfies
`f⁻¹(x+1) = f⁻¹(x)+1`, so its increment function is periodic, hence `f⁻¹` is
**uniformly** continuous on all of `ℝ` by compactness of `[0,1]`. Pick `η'`
with `|x - y| < 2η' → |f⁻¹x - f⁻¹y| < 2η`, and shrink below `1/2`.

That is a genuine real-analysis lemma with no existing consumer in this repo.
Budget it separately; do not discover it mid-step.

---

## 5. Recommended staging

Do not attempt step 3 as one milestone.

1. ~~**3a — action on `Slicing`.**~~ **Done** (2026-08-03) —
   `GroupAction/SlicingAction.lean`. `MulAction NormalizedShift (Slicing C)`
   with `one_smul` and `mul_smul` proved, and `MulAction GLTilde (Slicing C)`
   through `MulAction.compHom GLTilde.toShiftHom`. The §2 table held exactly:
   only `shift_iff` and `hn_exists` had content.

   One gotcha: inside the `MulAction` instance's own elaboration `•` stays
   opaque, so `relabel_P` cannot match and `simp` reports "no progress". Add
   `show (relabel C … ).P φ = …` before the `simp` in `one_smul`/`mul_smul`.
2. **3b — action on `PreStabilityCondition.WithClassMap`.** Needs the §3
   bridge and the `compat'` computation. Medium.
3. **3c — action on `StabilityCondition.WithClassMap`.** Needs §4's uniform
   continuity lemma. Hardest; schedule alone.

Prove the `MulAction` laws (`one_smul`, `mul_smul`) at each stage rather than
at the end — 3a's are cheap and will catch a wrong `f` vs `f⁻¹` convention
immediately, which is the failure mode most likely to survive typechecking.

---

## 6. Open risks

- ~~**Module system.**~~ **RESOLVED.** The anchor uses Lean's new module
  system (`module`, `public import`, `@[expose] public section`) and this
  repo's files do not. That is fine: a non-`module` file importing
  `BridgelandStability.StabilityCondition.Defs` sees every declaration listed
  above, with full signatures and no errors, and our own declarations coexist
  in the same file. No `module` migration is needed. (Probed
  2026-08-03 once the anchor oleans existed — the earlier attempt failed only
  because nothing had ever built them.)
- **Build cost.** The anchor is 74 files / ~35.7k LOC and is **not** covered
  by `lake exe cache get`, which is Mathlib-only. It also is not built by
  `lake build` unless something imports it — as of step 2 nothing did, so the
  first `lake build BridgelandStability` was a cold ~35k-LOC compile. It is
  built now. Avoid touching anything it depends on, and expect the first
  step-3 edit that imports it to be slower than the step-1/2 loop.
- **Universe variables.** The anchor uses `universe v u u'` with `Λ : Type u'`.
  Our files have not needed explicit universes yet.
- **`autoImplicit false`.** Our `lakefile.toml` sets it (and
  `relaxedAutoImplicit`); the anchor does not. Copied snippets may need
  explicit binders.
