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

`StabilityAction` reaches full stability conditions, which additionally carry
local finiteness. That is the one step with real analysis in it:
`Slicing.IsLocallyFinite` quantifies **one** window radius over **all**
centres, while a phase relabelling distorts windows. `ShiftAnalysis` proves a
normalized shift is *uniformly* continuous — not automatic for a continuous
bijection of `ℝ`, and exactly the quantifier shape needed — `relabel_intervalProp`
shows interval subcategories are reindexed on the nose, and the anchor's own
`interval_thinFiniteLength_of_inclusion_strict` finishes it.

**So the `G̃L⁺(2, ℝ)` action of Bridgeland §8 is complete on stability
conditions.**

`AutAction` starts §8's *other* half. `G̃L⁺(2, ℝ)` moves phases and fixes
objects; an autoequivalence does the opposite. The anchor has **no** functor
transport at all, so `PostnikovTower.mapF`, `HNFiltration.mapF` and
`Slicing.mapEquiv` are built from scratch — the last giving
`(Φ • s).P φ X = s.P φ (Φ⁻¹ X)`.

`StrictAutAction` then supplies group packaging. `C ≌ C` has no `Group`
instance — composition is associative only up to natural isomorphism — but
**functor composition in Lean is strictly associative**, so `C ⥤ C` is an
honest monoid under `⋙`. A group mapping *strictly* into it therefore gets a
real `MulAction G (Slicing C)`, with `(g • s).P φ X = s.P φ (g⁻¹ X)`.

That restriction is real: `map_one`/`map_mul` are equalities of functors, so
each `F g` is an *isomorphism of categories*, and Serre functors and spherical
twists fall outside it.

`QuotAutAction` therefore does the general construction, and it is the one to
prefer. `AutQuot C` — triangulated auto-equivalences modulo natural
isomorphism — is a genuine `Group` acting on slicings, and **excludes
nothing**.

The whole content is one lemma. If `Φ⁻¹ ≅ Ψ⁻¹` then `Φ⁻¹ X ≅ Ψ⁻¹ X` for every
`X`, so `s.P φ (Φ⁻¹ X)` and `s.P φ (Ψ⁻¹ X)` are equivalent propositions —
because a slicing's `P` is closed under isomorphism — and `propext` upgrades
that to *equality*. So `closedUnderIso`, which reads like bookkeeping among the
`Slicing` axioms, is exactly what makes the quotient well defined. The group
laws split the same way: associativity and the unit laws are `Iso.refl`, and
only `inv_mul_cancel` needs a real natural isomorphism — precisely the one
place strictness fails.

`AutStabilityAction` then carries it to *stability conditions*. All three
prerequisites landed: `K₀` functoriality (`K0Functor`), the class-lattice datum
(`actStabAut`'s `lam`), and invariance of strict finite length under an
equivalence (`mapEquiv_isLocallyFinite`, on the general
`isStrictArtinian_of_faithful_strict`).

Local finiteness survives with the **same `η`** — an autoequivalence moves
objects, not phases, so the interval endpoints do not move and no
uniform-continuity argument is needed. `compat'` likewise costs nothing: the
witness `m` is unchanged, where `G̃L⁺(2, ℝ)` replaced it by `m * r`.

`AutPairAction` closes it as a group action. The acting object is a *pair*
`(Φ, lam)`, which `AutQuot` cannot group because it carries only the `Φ`s, so
`AutPair v` bundles both and `AutPairQuot v` — the quotient by natural
isomorphism of `Φ`, with `lam` fixed on the nose — is a `Group` acting on
`StabilityCondition.WithClassMap C v`.

Two things that fall out of demanding a group rather than a map. `lam` has to
be an `AddEquiv`: a group needs `lam⁻¹` and nothing produces one, since `v` is
arbitrary — so `actStabAut`, which takes a bare `→+`, remains strictly the more
general statement. And `lam` must **not** be quotiented, because two `lam`s
over one `Φ` give different `σ.Z ∘ lam` whenever `v` is not surjective.

**`AutPairQuot v` is not `Aut(D)`**, and is further from it than `AutQuot` is.
Its elements are pairs, and the forgetful map to `AutQuot C` is neither
injective nor surjective in general — both failures are about `v`.

`GLTildeFibre` proves one of the three covering-space facts: the **fibre is
`ℤ`**. Everything lying over the identity matrix is a deck transformation
`φ ↦ φ + 2n`, and `kerEquiv` packages that as `Multiplicative ℤ ≃* ker`. The
factor of two is Bridgeland's phase convention showing through — `rayVec φ` is
the ray at angle `πφ`, so `φ ↦ φ + 1` is the antipodal map and only an even
shift returns every ray to itself.

`GLTildeSurj` proves the second: **the projection is surjective**. Every `T`
of positive determinant carries a compatible phase relabelling, so `toMatHom`
is onto.

The construction avoids covering-space machinery entirely by writing the lift
down. A real-linear map of `ℂ` is `z ↦ a z + b z̄`, and its determinant is
`‖a‖² − ‖b‖²` — so `det T > 0` says exactly `‖b‖ < ‖a‖`. Then

```
T(e^{iπφ}) = e^{iπφ} · a · (1 + (b/a) e^{-2iπφ})
```

and the last factor has real part at least `1 − ‖b/a‖ > 0`. It never leaves the
right half-plane, so its `arg` is continuous with no branch cut to work around,
and `lift φ = φ + arg a/π + arg(W φ)/π` is the relabelling.

Monotonicity comes from the 2×2 cross product rather than a derivative:
`(M *ᵥ v) × (M *ᵥ w) = det M · (v × w)` and
`rayVec φ × rayVec ψ = sin(π(ψ−φ))`, so `det T > 0` forces
`sin(π(lift ψ − lift φ)) > 0`; the `arg` bound then traps the difference in
`(−1, 2)`, where that has the unique solution set `(0,1)`. Positivity of `det`
is used twice, differently — once for the half-plane, once for the sign.

Together these give an exact sequence `1 → ℤ → G̃L⁺(2,ℝ) → GL⁺(2,ℝ) → 1`
(`exact_deckHom_toMatHom`).

`lift` is canonical rather than chosen, so it is a genuine **section**:
`existsUnique_deck_mul_sect` says every element factors uniquely as
`deck n * sect x.mat`, which trivialises the `ℤ`-bundle globally with an
explicit trivialisation. Note `sect` is *not* a group homomorphism — the
extension is non-split, which is precisely what makes it interesting.

**Simple connectedness remains open, and is not reachable at the pinned
Mathlib.** Checked rather than assumed: `SimplyConnectedSpace`'s only instances
there are `ofContractible` and `Unit`, and no fundamental group of any space is
computed anywhere in that revision — so `π₁(S¹) ≅ ℤ` is unavailable and the
covering-space route is closed. The remaining route is contractibility (true —
`G̃L⁺(2,ℝ) ≅ ℝ⁴`), which needs a polar decomposition of `2 × 2` real matrices
that Mathlib does not have at this pin. Independently, nothing here puts a
topology on `GLTilde`, so the statement is not currently expressible.

So `GLTilde` is still **not** shown to be the universal cover, and the gap is
now a change of category rather than a missing lemma — a central extension by
`ℤ` is a statement about groups, being the universal cover is a statement about
spaces. Nothing anywhere defines a topology on the space of stability
conditions either, so no statement here is about `Stab(D)` as a manifold.

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
