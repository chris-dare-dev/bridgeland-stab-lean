# BridgelandStabLean

Extensions to [`mattrobball/BridgelandStability`](https://github.com/mattrobball/BridgelandStability),
pinned at commit [`9e48f23`](https://github.com/mattrobball/BridgelandStability/tree/9e48f23a382ba117b63076a33e0e775389fef1ba).

The anchor formalizes Bridgeland 2007 §2–7 — Theorem 1.2 and Corollary 1.3, in
general surjective-class-map form. This repo works on what sits just outside
it.

## Why these two lanes and not others

The anchor's directory tree is worth reading before starting anything here:

```
Deformation/  EulerForm/  ForMathlib/  GrothendieckGroup/  HeartEquivalence/
IntervalCategory/  NumericalStability/  PostnikovTower/  QuasiAbelian/
Slicing/  StabilityCondition/  StabilityFunction/  TStructure/
```

There is no geometry directory, and `ForMathlib/` contains only `Analysis/`
and `CategoryTheory/{ObjectProperty, Shift}` — **zero** algebraic geometry.
That is not an oversight. The whole formalization is abstract: an arbitrary
triangulated category `D` with a surjective class map `v : K₀(D) →+ Λ`. A
variety never appears.

Mathlib today has schemes, `Spec`, structure sheaves, sheaves of modules,
ideal sheaves, and derived categories of abelian categories. It does **not**
have coherent sheaves as a workable abelian category `Coh(X)`, `D^b(Coh X)`
for a smooth projective variety, Serre duality, Chern characters or HRR for
surfaces, numerical Grothendieck groups of varieties, semiorthogonal
decompositions, or Fourier–Mukai transforms.

So a paper like "Bridgeland stability on K3 surfaces" is not a hard
formalization target — it is a *blocked* one, behind a multi-year Mathlib
program. The papers that are reachable are the ones that never leave the
abstract layer. Both lanes below were chosen on that criterion alone.

### Lane 1 — `GroupAction/` (the §8 gap)

Bridgeland §8 is the `G̃L⁺(2, ℝ)` action on `Stab(D)` and the autoequivalence
action. It is outside the anchor's stated scope, it is purely categorical, and
Serre-invariance arguments consume exactly it. Highest value in this repo.

Current state: the phase-relabelling half (`NormalizedShift` — order
isomorphisms of `ℝ` commuting with `φ ↦ φ + 1`) is defined and **proved to be
a group under composition**, with no dependency on the anchor's API.

`GLTilde` then pairs it with `T ∈ GL⁺(2, ℝ)` under Bridgeland's
same-map-on-the-circle condition — the circle being `ℝ/2ℤ` embedded by
`φ ↦ (cos πφ, sin πφ)`, with the `π` (not `2π`) making `φ ↦ φ + 1` the
antipodal map, i.e. the shift functor `[1]`. That pair type is **proved to be
a group**, with both projections group homs.

`SlicingAction` then makes this act: `NormalizedShift` — and hence `GLTilde`,
through `toShiftHom` — acts on the anchor's `Slicing C` by relabelling phases,
`(f • s).P φ = s.P (f⁻¹ φ)`, with the `MulAction` laws proved.

`PreStabilityAction` puts both factors to work at once:

```
(x • σ).slicing = x.shift • σ.slicing      -- phases relabelled
(x • σ).Z       = actC x.mat ∘ σ.Z         -- charge transformed
```

The anchor's `compat'` axiom is what forces the two to agree, and `Compatible`
is exactly what discharges it: a semistable object's charge ray moves from
phase `f⁻¹ φ` to phase `φ`, with the positive scalar `m` becoming `m * r`.
That is why step 2 defined `Compatible` the way it did.

Two things that are deliberately *not* proved. `GLTilde` is not shown to be
the universal cover — the projection is not shown surjective, the fibre is
not shown to be `ℤ`, simple connectedness is untouched. And nothing yet acts
on a full *stability condition*, which additionally carries local finiteness;
preserving that needs uniform continuity of `f⁻¹` and is step 3c. See
[`notes/anchor-api-map.md`](notes/anchor-api-map.md).

### Lane 2 — `Lattice/` (closable today)

Rank-2 torsion-free arithmetic: `2 • x = 0 → x = 0`, injectivity of scaling,
rank-component non-vanishing. Small, closed, no substrate required. These
exist to exercise the whole path — build, axiom audit, review record — on
statements too simple to hide a mistake in.

### Not a lane

Anything requiring `Coh(X)`. See above.

## What this repo is not

`Lattice/NumericalK.lean` models `K_num(Ku(X))` as `Fin 2 → ℤ`. Every lemma
there is a theorem about a **rank-2 torsion-free lattice**, not about a
Kuznetsov component. The identification is geometry, is not expressible in
Mathlib today, and is tracked as an unrealized assumption. It is never
discharged here.

Typechecking is not fidelity. TheoremGraph's statement-only experiment had
22/24 outputs typecheck while 5/24 were semantically faithful. Nothing in this
repo has had human faithfulness review; see `formalization.yaml`.

## Build

```bash
lake exe cache get && lake build
```

Toolchain is pinned to `leanprover/lean4:v4.29.0`. Mathlib
(`8a17838…`) arrives transitively through the anchor and is deliberately
**not** pinned separately — a second pin is a second thing to drift.

## Relationship to arXMCP

This repo is a deliberate sibling of, never a subdirectory of,
[arXMCP](https://github.com/chris-dare-dev/arXMCP). arXMCP is a read-only
retrieval data plane; its R5 track pins *released* formalizations and serves
their trust records. It does not host formalization work. `formalization.yaml`
is the interface between the two, and its schema mirrors the anchor's so one
parser reads both.
