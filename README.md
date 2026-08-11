# BridgelandStabLean

Extensions to [`mattrobball/BridgelandStability`](https://github.com/mattrobball/BridgelandStability),
pinned at commit [`9e48f23`](https://github.com/mattrobball/BridgelandStability/tree/9e48f23a382ba117b63076a33e0e775389fef1ba).

The anchor formalizes Bridgeland 2007 §2–7 — Theorem 1.2 and Corollary 1.3, in
general surjective-class-map form. This repo works on what sits just outside
it.

## Why these seven lanes and not others

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
abstract layer. Every lane below was chosen on that criterion alone.

**Lane 3 does not change that.** `Mukai/` formalizes the *lattice* that a K3's
Mukai lattice is an instance of, which is arithmetic and needs no substrate.
The identification with `H⁰ ⊕ NS(X) ⊕ H⁴` still needs `D^b(Coh X)`, Chern
characters and HRR, and is still blocked. Adding the lattice does not move that
wall an inch; it just means the arithmetic is already there when someone else
moves it.

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

The quotient relation itself is now the standard one: natural isomorphism of
the **forward** functors. `TriEquiv.inverseIsoOfFunctorIso` derives the inverse
natural isomorphism from uniqueness of right adjoints, so neither `AutQuot`
nor `AutPairQuot` carries the earlier, artificially finer two-component
relation.

`CombinedAction` proves that the two §8 actions commute and packages the
direct-product action

```
MulAction (GLTilde × AutPairQuot v)
  (StabilityCondition.WithClassMap C v).
```

The topological action layer is also present. `TopologicalAction` proves that
each compatible autoequivalence class acts by a homeomorphism.
`GLTildeContinuousAction` obtains the analogous result for each fixed lifted
matrix from uniform phase control and a condition-number estimate on `actC`.
`GLTildeJointContinuousAction` strengthens this to genuine joint continuity.
Near the identity, integer equivariance makes `x.shift φ - φ` uniformly
small on all phases after checking the compact interval `[0,1]`, while
`actCCLM x.mat - id` is small in operator norm. Translation by a fixed group
element gives the result at every pair. Autoequivalence classes carry their
standard discrete topology, so `GLTilde`, `AutPairQuot v`, and their direct
product all have `ContinuousSMul` on the stability space.

The next three symmetry milestones are also complete. `ComponentAction`
functorially transports connected-component labels, restricts each symmetry
to a homeomorphism between component subtypes, and lets the stabilizer of a
component act on that component. `PeriodMapEquivariance` packages the induced
additive equivalences of the charge space and proves equivariance of both the
global central-charge map and the anchor's componentwise local-model chart.
Finally, `EffectiveAction` constructs the categorical double shift as a
triangulated autoequivalence and checks the convention-sensitive identity

```
[2] acts as deck (-1), so (deck 1, [2]) acts trivially.
```

The effective combined symmetry group is the direct-product symmetry group
quotiented by its full action kernel; its induced action is faithful by
construction. The explicit deck/double-shift pair is proved to lie in that
kernel. No claim is made that this one pair generates the entire kernel in an
arbitrary category.

The full-metric chain is now implemented as well. `StabilityMass` defines the
finite charge-norm sum for one HN filtration and an initially choice-free mass
envelope over all HN filtrations. `HNMassUniqueness` constructs head--tail
triangles by octahedral induction and uses the slicing-induced t-structure to
prove that every HN filtration has the same mass. Consequently
`stabilityMass` equals every finite HN mass sum, is never `⊤`, and vanishes
exactly on zero objects; its `toReal` is the literal sum of factor-charge
norms. `StabilityDistance` combines the two intrinsic phase
discrepancies with the ordinary logarithmic mass discrepancy; the resulting
`ℝ≥0∞`-valued distance is reflexive, symmetric, satisfies the triangle
inequality, and dominates the anchor's `slicingDist`. `AutFullIsometry` proves
that compatible autoequivalence representatives and `AutPairQuot v` preserve
all three coordinates exactly. `StabilityDistanceSeparation` reconstructs the
slicing and the observable charge `Z.comp v` from distance zero. It proves
literal identity of stability conditions when `v` is surjective, including
unconditionally for ordinary stability conditions over `K₀ C`.

`StabilityDistanceTopology` now proves the analytic estimates and both local
cofinality directions needed to identify full-distance balls with the Section
6 neighborhoods.  It packages the comparison conditionally on the one
remaining categorical input, HN-mass subadditivity across distinguished
triangles.  The compatible `PseudoEMetricSpace`/`EMetricSpace` constructors use
Mathlib's `ofEDistOfTopology`; regression theorems check that their topology is
definitionally the pre-existing Section 6 topology, and no competing global
instance is installed.  Proposition 8.1 is therefore still `no_claim` until
the explicit mass-triangle proposition is proved.  Independently,
`AutPairQuot v` carries compatible class-lattice data and is not identified
with bare `Aut(D)`.

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
explicit set-level trivialisation. No group-homomorphism property is claimed
for `sect`, so this is not asserted to be a semidirect-product decomposition.

`GLTildeTopology` now proves **simple connectedness**. Rotating a matrix's
first column backwards through the lifted phase `f(0)` leaves a unique matrix
`!![r,b;0,d]` with `r,d > 0`. This gives global coordinates
`ℝ × (0,∞) × ℝ × (0,∞)`, a homeomorphism with a contractible space, and
hence `ContractibleSpace GLTilde` and `SimplyConnectedSpace GLTilde`. The
matrix projection is also continuous.

`GLTildeCover` completes the covering-space theorem. It gives
`GL⁺(2,ℝ)` global coordinates `S¹ × (0,∞) × ℝ × (0,∞)` and identifies
the matrix projection, in the source and target coordinates, with
`(θ ↦ exp(πθ)) × id`. Mathlib's standard exponential cover and stability
of covering maps under products and homeomorphisms then yield
`GLTilde.isCoveringMap_toMat`. Together with the instance above,
`GLTilde.universalCoverData` packages the covering-map, surjectivity, and
simply-connected source properties. The deck group `ℤ` remains recorded by
`exact_deckHom_toMatHom`.

`GLTildeTopologicalGroup` proves the compatibility between the group and this
topology. The key joint evaluation map `(x,φ) ↦ x.shift φ` is continuous: in
global coordinates the potentially branch-sensitive `arg(cA)` term cancels,
leaving arguments only of points in the open right half-plane. Multiplication
then follows from joint phase evaluation and continuous matrix multiplication;
inversion uses the explicit inverse positive-diagonal upper-triangular
coordinates. The resulting instance is `IsTopologicalGroup GLTilde`.

Together with `GLTildeContinuousAction`, every fixed element of this
topological group acts on the Bridgeland stability space by a homeomorphism.

### Lane 2 — `Lattice/` (closable today)

Rank-2 torsion-free arithmetic: `2 • x = 0 → x = 0`, injectivity of scaling,
rank-component non-vanishing. Small, closed, no substrate required. These
exist to exercise the whole path — build, axiom audit, review record — on
statements too simple to hide a mistake in.

### Lane 3 — `Mukai/` (lattice arithmetic for the wall literature)

The extension `ℤ ⊕ N ⊕ ℤ` of an additive group `N` carrying a symmetric
`ℤ`-bilinear form `b`, with

```
⟪(r, c, s), (r', c', s')⟫ = b c c' - r·s' - r'·s.
```

`Mukai/Lattice.lean` proves bilinearity, symmetry, the quadratic refinement
`⟪v,v⟫ = b c c - 2rs`, that the extension of an even lattice is even, the
disjointness of the spherical (`⟪v,v⟫ = -2`) and isotropic (`⟪v,v⟫ = 0`)
conditions, and that the two outer summands span a hyperbolic plane — two
isotropic generators pairing to `-1`.

`Mukai/RankTwo.lean` is the rank-two subpair arithmetic the wall literature is
organised around. Its two loads:

* **`gram_lincomb`** — the Gram determinant transforms by the *square* of the
  change-of-basis determinant, for an arbitrary integer `2 × 2` matrix rather
  than only unimodular ones. This is what makes "hyperbolic" a property of the
  sublattice and not of a chosen basis.
* **`selfPairing_orthWitness_neg`** — the explicit integral class
  `⟪v,w⟫ • v - ⟪v,v⟫ • w` is orthogonal to `v` and has strictly negative
  square whenever `⟪v,v⟫ > 0` and the pair is hyperbolic. That is the
  signature-`(1,1)` witness in integral form: no real coefficients, no
  diagonalisation, no appeal to Sylvester's law.

Three names in this lane are suggestive and each is weaker than it sounds.
`expectedDim v = ⟪v,v⟫ + 2` is a **definition**, not Mukai's dimension theorem.
`IsSpherical` is the numerical condition `⟪v,v⟫ = -2`, not a claim that any
object has that class. `IsHyperbolicPair` is negative Gram determinant, not a
claim that a wall exists — the correspondence with actual walls is
Bayer–Macrì Theorem 5.7, which is geometry and is **not** formalized here.

### Lane 4 — `Tilting/` (a gap in Mathlib, not in the anchor)

Torsion pairs on an abelian category: two isomorphism-closed classes `(T, F)`
with no nonzero map `T → F`, such that every object sits in a short exact
sequence `0 → tX → X → fX → 0` with `tX ∈ T`, `fX ∈ F`.

**Mathlib does not have this at the pin.** Every `Torsion` file there is about
torsion in algebra — `Algebra/Group/Torsion.lean`, `GroupTheory/Torsion.lean`,
`RingTheory/Flat/TorsionFree.lean`. There is no torsion pair, torsion theory,
or torsion class for abelian categories, so this is built from scratch. It
imports only Mathlib: no anchor, no triangulated category, no geometry.

Proved: each class is exactly the orthogonal of the other (`tors_iff`,
`free_iff`); `F` is closed under subobjects and `T` under quotients; both are
closed under extensions; and a torsion subobject factors through any
decomposition, so the torsion end is maximal. The two degenerate torsion pairs
are **constructed**, not assumed — a structure with no inhabitant would make
every theorem about it vacuously true.

`HeartTorsionPair.lean` then carries the same notion on the heart of a
t-structure, phrased inside `C`, and builds the tilted aisles.

**The aisles are not defined the usual way, and the deviation is forced.**
Textbook HRS writes `D^{≤0}_† = {X ∈ D^{≤0} : H⁰(X) ∈ T}`. Mathlib has no
bundled `Hⁿ` functor into the heart at the pin: `TStructure/` supplies
`truncLE`, `truncGE`, and truncation triangles. The project now constructs
that functor and proves its homologicality, but the original aisle
construction remains phrased by **Hom-orthogonality**:

```
H⁰(X) ∈ T   ⟺   Hom(X, F) = 0 for every torsion-free F
```

The two agree wherever the usual one can be stated, but they are not literally
the same definition, and a reader comparing to a textbook should know it. As
of #94 the agreement is itself a theorem on both sides, with the truncations
in the role of `H⁰`: `tiltLE_iff_tors_truncGE` and `tiltGE_iff_free_truncLE`,
via the dual factorisation pair and `free_of_orthogonal`.

`HeartCohomology.lean` now adds the complementary object-level bridge without
changing that construction: `originalHeartCohFunctor` depends only on a
t-structure, so it applies to both the original and tilted hearts. For every
tilted-heart object it identifies the canonical torsion-free `H⁻¹` and torsion
`H⁰` factors and proves
`0 → H⁻¹(E)[1] → E → H⁰(E) → 0` short exact in the tilted heart, with the two
maps exposed as a kernel and a cokernel. It does not claim the six-term
original-cohomology sequence by itself; the next two modules supply that
result.

`HeartCohomologyHomological.lean` closes the general category-theoretic gap:
`originalHeartCohFunctor_isHomological` proves that degree-zero cohomology of
any t-structure sends distinguished triangles to exact short complexes in
the heart. The proof uses only truncation triangles, octahedra, and the
abelian heart; it requires no stability function or HN data.

`GroupAction/H0ExactnessBridge.lean` is the focused current-main adapter for
issue #89. It identifies the anchor's `HeartStabilityData.H0Functor`
definitionally with `originalHeartCohFunctor`, transports homologicality
without installing a new global instance, and exposes the exact-middle-term
and monic-cokernel conclusions intended for the current-main mass-triangle
rewrite of stale PR #103. The conclusion is `ShortComplex.Exact`, not
`ShortExact`; no mass inequality is proved in this module. This replaces the
duplicated homologicality proof in stale draft PR #100 rather than porting that
draft wholesale.

`HeartCohomologySequence.lean` constructs the six terms and connecting map,
identifies them with the canonical
`H⁻¹(P), H⁻¹(E), H⁻¹(Q), H⁰(P), H⁰(E), H⁰(Q)` objects, and converts any short
exact sequence in the tilted heart to the required ambient distinguished
triangle. Exactness at all four interior terms, monicity at the left
endpoint, and epicity at the right are now unconditional.

**Every `TStructure` field is proved, and `tilt` assembles them** into a
genuine `Triangulated.TStructure`:

| field | theorem |
|---|---|
| `le_isClosedUnderIsomorphisms` / `ge_…` | `tiltLEAt_isClosedUnderIsomorphisms` / `…` |
| `le_shift` / `ge_shift` | `tiltLEAt_shift` / `tiltGEAt_shift` — one `shiftFunctorAdd'` each |
| `le_zero_le` / `ge_one_le` | `tiltLEAt_zero_le` / `tiltGEAt_one_le` — pure degree counts |
| `zero'` | `tiltAt_zero'` |
| `exists_triangle_zero_one` | `exists_tilt_triangle` — two octahedra |

`tilt` carries `[IsTriangulated C]` explicitly, and it earns it three times: the
octahedral axiom is what makes `τ^{≥0}` preserve `D^{≤0}` (so the truncation
lands in the heart), and it supplies both octahedra in the last field.

The last field is where the choice of *which* octahedron matters.
`Octahedron'` works with **fibres**, so on `B → H → F₀` its three fibres are
`τ^{≤-1}A`, `X`, `T₀` — giving `τ^{≤-1}A → X → T₀` with no desuspension.
`Octahedron` works with **cones**, so on `X → B → A` its three cones are `F₀`,
`Y`, `τ^{≥1}A`. Both outputs are exactly what the two recognition lemmas
consume.

**Nothing is declared with `sorry`.**

**The tilted heart is identified** (#106): `tilt_heart_iff` says `X` lies in
`tilt.heart` exactly when it is an extension of a torsion object by a shifted
torsion-free one — the textbook `A† = ⟨F⟦1⟧, T⟩`, in the single-step form
that is exact for a torsion pair, so no extension-closure operator appears.

**What is still not here.** `tilt` is a t-structure on a triangulated
category. Nothing in the lane connects it to a stability condition — that is
a further theorem, and the weak-stability program (#81) is where it would
land.

### Lane 5 — `Support/` (the Kontsevich–Soibelman reformulation)

The support property — `‖v‖ ≤ C ‖Z v‖` uniformly over a distinguished set `S` —
is equivalent to the existence of a form `Q` that is nonnegative on `S` and
negative definite on `ker Z`.

The compactness direction cuts the unit sphere by `Q ≥ 0`, observes that `Z`
cannot vanish there (a kernel vector would have `Q < 0`), and takes the
reciprocal of the minimum of `‖Z ·‖` on the resulting compact slice. The
converse is explicit: `Q v = C²‖Z v‖² - ‖v‖²`.

**Two boundaries, and the second is the sharp one.**

`S` is an **arbitrary subset**. It is not identified with the classes of
`σ`-semistable objects — nothing in the lane mentions a triangulated category,
a slicing, or the anchor. That identification is what would make these
statements about Bridgeland stability, and it is not made.

The equivalence is stated for `IsHomogTwo` (continuous, `Q(a•v) = a²Q(v)`),
which is **strictly weaker** than being a quadratic form — `Q(x,y) = |xy|` on
`ℝ²` satisfies it and is not one. That cuts both ways, asymmetrically:

* form ⟹ support property has a *weaker hypothesis*, so it is **stronger** than
  the literature's version;
* support property ⟹ form has a *weaker conclusion*, so it is **weaker**. It
  produces a continuous degree-two homogeneous function, not a bundled
  `QuadraticForm ℝ V`.

So do not cite `hasSupportProperty_iff` as "the support property is equivalent
to the existence of a quadratic form". Closing that gap means restricting to an
inner product space and building an actual `QuadraticMap`; it is not done.

**The support property is open in the charge** (PR #78), in three forms of
increasing packaging and *decreasing* hypotheses — all three are stated with
`FiniteDimensional` omitted, and none uses compactness:

* `hasSupportProperty_of_norm_sub_le` — the quantitative estimate. A charge
  `ε`-close to `Z` (pointwise, `‖Z'v - Zv‖ ≤ ε‖v‖`) with `Cε < 1` has the
  property with constant `C / (1 - Cε)`, which degrades to `+∞` exactly as
  `Cε → 1`: a barely-true estimate tolerates a barely-nonzero perturbation.
* `HasSupportProperty.exists_tolerance` — openness with **no topology on the
  space of charges**: a positive tolerance exists around any charge with the
  property, stated for plain linear maps.
* `isOpen_hasSupportProperty` — the `IsOpen` form, for `S` fixed and charges
  `V →L[ℝ] W` under the operator norm. The mathematical content is entirely in
  the previous lemma; the only added step is `le_opNorm`.

`S` stays an arbitrary subset throughout, so none of this asserts anything
about semistable objects — the boundary above applies unchanged.

### Lane 6 — `FiniteLength/` (the lattice half of Bridgeland's `ℍ̄ⁿ`)

Bridgeland's worked example: for an abelian category of finite length with `n`
simples, a stability function is a choice of `Z(Sᵢ)` in the semi-closed upper
half plane, one per simple — so that component of the manifold is `ℍ̄ⁿ`.

What is proved is the lattice half over the model `Fin n → ℤ`:

* the two cone-closure facts the anchor lacks — closure under multiplication by
  a positive real, and closure under a **nonempty** finite sum;
* `existsUnique_charge` — a choice of value per basis vector determines a
  unique additive charge, and every additive charge arises that way;
* `mem_cone_natCombination` — a nonzero `ℕ`-combination of cone values stays in
  the cone, hence is nonzero.

The cone `upperHalfPlaneUnion` and its closure under addition are the anchor's.
This is the first of these lanes to import the anchor at all, and the two new
cone lemmas are kept in this repo's namespace rather than injected as
`CategoryTheory.upperHalfPlaneUnion_*` — CLAUDE.md §1 already tracks 21
dot-notation extensions on anchor types as bump-collision candidates, and
nothing needs these two by dot notation.

**`Fin n → ℤ` is not `K₀(A)`, and the missing bridge has a name.** Identifying
them is Jordan–Hölder — that `K₀(A)` is free abelian on the classes of the
simples — and it exists in **neither Mathlib nor the anchor**.
`Mathlib/Order/JordanHolder.lean` is about modular lattices and is not
connected to `K₀` of a category; the anchor's `GrothendieckGroup/` builds `K₀`
as a quotient and never says that quotient is free on the simples.

So the stability-manifold conclusion is **not** drawn. Do not cite
`existsUnique_charge` as "Stab of a finite-length heart is `ℍⁿ`".

### Lane 7 — `Wall/` (numerical walls in the `(s, t)` half plane)

For a class `v = (r, c, d)` — a triple of reals, standing for
`(ch₀, ch₁·H, ch₂)` — the twisted charge at `(s, t)` is

```
Re Z = -d + s·c - (s²/2)·r + (t²/2)·r,      Im Z = t·(c - s·r).
```

The whole lane rests on one identity, `wallExpr_eq`: the cross product of two
charges collapses to

```
t · ( minC + s·minB + ((s² + t²)/2)·minA )
```

where `minA, minB, minC` are the three `2 × 2` minors of the matrix with rows
`v` and `w`. So for `t ≠ 0` the wall is `minA(s²+t²) + 2·minB·s + 2·minC = 0` —
**a circle centred on the `s`-axis, or a vertical line.** Centre and radius are
given in cleared form, so no division appears. Each minor is alternating, so a
wall depends only on `w` modulo `v`.

**No Bogomolov–Gieseker inequality is assumed, and none is axiomatised.** This
lane was scoped expecting to need one — a numerical-surface structure carrying
the Hodge index and the discriminant bound as stated hypotheses. It turned out
none is required: `wallExpr_eq` is a polynomial identity, and the circle and
line forms need only `t ≠ 0` and a nonvanishing minor, both hypotheses of the
individual theorems. CLAUDE.md §4's "say so and stop rather than axiomatise the
gap" was never engaged, because the gap was not on the path.

**There is no surface.** `NumClass` is a triple of reals, not `ch(E)`.

**The nesting theorem is proved, and its charge hypothesis is proved
necessary.** `wall_eq_of_meet`: two walls for the *same* `v` with nonzero
minor vectors, meeting at one point where `v`'s own charge does not vanish,
agree at every point of the half plane — contrapositively, distinct walls for
a fixed `v` are disjoint away from the degenerate locus. That is the statement
the "nested semicircles" picture rests on. The hypothesis is load-bearing:
`wall_eq_of_meet_needs_charge` exhibits `v = (2,0,1)`, whose charge vanishes
at `(0,1)`; *every* wall of `v` passes through that point, and two explicit
walls meet there and differ at `(0,2)`. Cite the theorem with its hypotheses —
and still with no surface behind it (above).

### Lane 8 — `WeakStability/` (the §14 definitions)

Definitions 14.1–14.3 of `1902.08184v4` on the abstract layer, opened for the
weak-stability epic (#81). A **weak** prestability condition is the anchor's
datum with the compatibility ray *closed* at integer phases — the charge of a
nonzero semistable object may vanish there — and open elsewhere; on a heart,
values land in `ℍ ⊔ ℝ_{≤0}` instead of `ℍ ⊔ ℝ_{<0}`. The zero-charge
subcategory `A⁰` is closed under subobjects, quotients and extensions, by
`K₀` additivity and half-plane arithmetic.

**Ordinary stability embeds by theorems, not prose**: `ofPre` keeps the
slicing and charge definitionally (`ofPre_slicing`, `ofPre_Z`), and `toWeak`
weakens strict stability functions.

**Weak stability restricts to the slicing heart**: `weakStabilityFunctionOnHeart`
composes the lattice charge with the class map, including the closed
phase-`1` boundary. Charge and zero-charge compatibility are definitional,
and `weakStabilityFunctionOnHeart_isSemistable_iff` identifies nonzero
slicing-heart objects that are slicing-semistable with the triangle-based
weak slope-semistability predicate. The converse is proved by splitting a
non-semistable HN filtration at a midpoint phase and obtaining a strict slope
contradiction.

**Weak Harder--Narasimhan filtrations on the heart**:
`WeakAbelianHNFiltration` packages a strict finite subobject chain in the
abelian full heart whose weak-semistable quotients have strictly decreasing
`WithTop ℝ` slopes. The phase--slope comparison treats phase `1` as the
`+infinity` boundary, including zero charge, and
`weakStabilityFunctionOnHeart_hasHN` converts slicing HN towers into these
abelian filtrations while removing zero factors.

**The torsion pair at a phase cutoff** (#109): `slicingTorsionPair` — display
(14.1) in phase language, `(P((β,1]), P((0,β]))` as a `HeartTorsionPair` on
the slicing heart, unconditional on the slicing axioms: the HN cut is the
decomposition and the slicing's phase-ordered vanishing is the orthogonality.
The reviewed tilt applies, and `slicingTilt_heart_iff` identifies the tilted
heart with extensions of `P((β,1])` by `P((0,β])⟦1⟧` — the `A^{♯β}` of the
paper, up to the exact slope-cutoff translation. The normalized
slope--phase ray identity is formalized in `WeakStability/ChargeRay.lean`, but
the source-facing display (14.1) equivalence has not been packaged and
reviewed; the coverage map therefore remains `mapped`, not a claim.

**Noetherian torsion subcategories** (#108): Definition 14.6, with Remark
14.7's chain condition *as* the definition — the full heart is abelian, but
an arbitrary object property `B` has no bundled noetherian abelian-subcategory
structure at the pin, and every §14 use runs on chain termination. A torsion pair's
free class is proved to be `B^⊥` (`free_iff_rightOrthogonal`, the payoff of
#94's `free_of_orthogonal`), and the zero subcategory is the nonvacuity
witness. **Lemmas 14.8 and 14.11 are deliberately undeclared** — statable,
but their proofs need heart kernel/image machinery, the weak-HN layer, and a
`ℚ[i]`-discreteness decision; the gaps are named in the module. Absent beats
sorry-backed.

**The tilting property** (#110): `TiltingProperty` packages Definition
14.12 in the same phase-language model. Its zero-charge class is explicitly
the torsion class of a `NoetherianTorsionSubcategory`; for every heart object
with `phiPlus < 1`, `HasTiltingEnvelope` supplies the heart triangle
`F -> Ftilde -> F0` with `F0` of zero charge and every map
`A0 -> Ftilde⟦1⟧` zero. The `phiPlus < 1` premise is the phase form of
`muPlus < +infinity`; the exact source-facing cutoff comparison remains an
explicit review gap. `WeakStability/TiltSemistable.lean` now proves both
directions of Lemma 14.17's **phase-language** semistable-object
classification, using the canonical original-cohomology sequence, and proves
the positive-imaginary/stable Hom-vanishing refinement by factoring through
tilted-heart images. The exact slope-language source statement stays under
the existing `mapped` hypothesis. **Proposition 14.16 remains deliberately
undeclared.** Its support-property transport is now proved in
`WeakStability/Support.lean`; `WeakStability/TiltNoetherian.lean` constructs
the zero-charge torsion pair and its noetherian chain data from either the
relative chain condition, phase-compatible envelopes, or the raw Definition
14.12 envelope clause. In the raw route, Ext-vanishing transfers zero-charge
subobject chains to the original zero-charge quotient; chain termination and
the maximal-subobject construction then produce the shifted phase-compatible
decomposition without claiming that the raw middle term is phase-free.
`WeakStability/TiltHarderNarasimhan.lean` performs boundary-phase saturation
without assuming the last shifted factor is already right-orthogonal, then
iterates the cohomological reduction through the original `H⁻¹` and `H⁰` HN
filtrations. `WeakStability/TiltAssembly.lean` combines that HN theorem with
the noetherian and support constructions to package all three heart-level
obligations directly from `TiltingProperty`, with no external envelope, rank,
or quotient-induction premise. The heart-level constructive seams are now
closed. The exact Proposition 14.16 source statement remains undeclared
because the exact slope-cutoff translation has not been reviewed against the
pinned source. The reverse infrastructure is in
`WeakStability/HeartEquivalenceReverse.lean`: the strictly increasing
normalization `WithTop ℝ → (0,1]`, the integer-normalized ambient phase
predicates and their shift law, and the conversion of weak abelian HN chains
to ambient Postnikov towers. `WeakStability/ChargeRay.lean` proves the analytic
identity `μ = -cot(πφ)` in the form needed here: every weak upper-half-plane
charge lies on the ray of `weakPhaseOfSlope μ`, including the zero-radius
integer boundary, and the identity is preserved by arbitrary integer shifts.
`WeakStability/TiltPreStability.lean` connects those results to
`PhaseTiltHeartObligations` and packages an actual `WeakPreStabilityCondition`
without an external compatibility premise.
`WeakStability/HeartHomVanishing.lean`
proves the previously separate Hom-vanishing premise unconditionally: a
weak-slope see-saw and the heart kernel/image factorization give same-heart
vanishing, while integer shifts and t-structure orthogonality give the full
ambient statement. `WeakStability/AmbientHarderNarasimhan.lean` proves the
remaining categorical premise: pure cohomology towers are shifted from the
heart and concatenated along bounded truncation triangles, with amplitude
`[b,a]` giving the strict phase interval `(-a,1-b]`; it also proves that the
HRS tilt of a bounded t-structure stays bounded. Thus the analytic ray
and categorical reverse phase-language assembly is closed. The remaining
boundary is source-faithfulness review of the exact slope-language statement,
not a missing Lean construction.
The canonical two-term original/tilted-heart kernel--cokernel bridge is in
`Tilting/HeartCohomology.lean`; `Tilting/HeartCohomologySequence.lean`
constructs and proves the arbitrary-short-exact six-term sequence
unconditionally, using `Tilting/HeartCohomologyHomological.lean`.
The exact blockers are recorded in `WeakStability/TiltingProperty.lean`.

**Two boundaries.** The heart is carried inside `C` and subobject data is a
heart triangle, as in the Tilting lane; the available abelian full-heart
instance converts these triangles to short exact sequences when needed. And
the paper's `K(A)` is the ambient `K₀ C` here, positivity
quantified over heart objects; `K(A) ≅ K(D)` is neither available at the pin
nor assumed. The section-14 coverage coordinate stays `mapped`: its
phase-language correspondence is a recorded hypothesis, not a reviewed or
formalized source claim, and promotion remains owner-gated under #111.

### Not a lane

Anything requiring `Coh(X)`. See above. In particular the Bayer–Macrì wall
*classification* — assigning a type (totally semistable, divisorial, flopping,
fake) to a rank-two datum — needs moduli of stable objects and is out of scope.
Lane 3 supplies the numerical substrate that classification is phrased over,
and stops there.

## What this repo is not

`Lattice/NumericalK.lean` models `K_num(Ku(X))` as `Fin 2 → ℤ`. Every lemma
there is a theorem about a **rank-2 torsion-free lattice**, not about a
Kuznetsov component. The identification is geometry, is not expressible in
Mathlib today, and is tracked as an unrealized assumption. It is never
discharged here.

`Mukai/` is the same divergence one level up, and the suggestive naming makes
it easier to misread. `MukaiLattice N` is the abstract extension `ℤ × N × ℤ`
of **any** additive group with **any** symmetric `ℤ`-bilinear form. It is not
the Mukai lattice of a K3 surface. Every theorem in the lane is true of an
arbitrary symmetric bilinear `ℤ`-lattice and would remain true if no K3
surface existed. The lane also carries **no `@[cites]` records and no registry
entries** — the pinned source is Bridgeland 2007, which this lane is not
about, and minting keys against a document outside the pinned corpus would
require quotes that cannot be verified here. Uncited is the honest state.

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
retrieval data plane over a LanceDB corpus of parsed arXiv papers; the
`bridgeland-stability` notebook is the corpus behind this repo's sources.

**Three things this section used to assert that are false.** They were
corrected in `CLAUDE.md` §8 and not here, so the README kept saying them until
2026-08-06. Kept, because the corrections are the useful part.

- **arXMCP's R5 track does not pin released formalizations or serve trust
  records.** R5 is a brief with no `plans/` entry; `get_formal_targets` /
  `formal_targets` return zero hits in `server/`; and `find -iname "*formaliz*"`
  across arXMCP returns zero files. There is no parser.
- **"It does not host formalization work" is true, but not for the reason
  implied.** The prohibition is in an unroadmapped, geometry-scoped brief
  (`.claude/roadmap-briefs/R5-formal-target-registry.md`), not in arXMCP's
  `CLAUDE.md` §4.8. Cite the brief.
- **`formalization.yaml` is not "the interface between the two".** It has no
  reader, on either side. The interface is designed
  (`.claude/decisions/ADR-0001`…`ADR-0009`) and **not yet built**; until it
  ships, the boundary is unilateral — arXMCP contains zero documents mentioning
  this repo.

Its schema does mirror the anchor's, which is worth keeping, but "key-for-key
so one parser reads both" overstates it: no such parser exists, and the mirror
is a convention this repo maintains by hand.
