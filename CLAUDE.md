# Working in BridgelandStabLean

Read [README.md](README.md) for the mathematical scope and repository map. GitHub milestones
and issues are the source of truth for planned work.

## Reproducible dependencies

`lean-toolchain` and every revision in `lakefile.toml` are exact pins. The foundational
stability library supplies the shared definitions and the transitive Mathlib revision; do not
add a second direct Mathlib dependency. A pin change is a deliberate compatibility migration
and must update `formalization.yaml` in the same commit.

Before changing a pin, check local declarations under `ForMathlib/` and dot-notation extensions
on dependency-owned types for upstream collisions. Delete a local compatibility declaration
only after the replacement is present at the new pin and the complete build succeeds.

## Repository taxonomy

Place code beneath the narrowest stable mathematical owner:

- `Lattice/{Arithmetic,Numerical,Mukai}` for lattice theory.
- `StabilityCondition/Phase` for phase relabelling and analysis.
- `StabilityCondition/Symmetry/{GLTilde,Autoequivalence,Combined}` for actions.
- `StabilityCondition/Metric/{Mass,Distance,Isometry}` for metric geometry.
- `StabilityCondition/{Support,Walls}` for support properties and numerical walls.
- `StabilityCondition/Weak/{Basic,Heart,HarderNarasimhan,Support,Tilting}` for weak stability.

If a subject has multiple independent concepts, create a descriptive intermediate directory
instead of another long flat filename. Export every new leaf from its nearest same-named
umbrella module; keep the root imports at subsystem granularity.

## Proof integrity

There is no `sorry` in this library and there must never be one. Unfinished work belongs in a
module docstring and a tracker issue, not in a placeholder theorem, axiom, or instance.

Keep abstract lattice results distinct from geometric realizations. A theorem about an
abstract numerical or Mukai lattice is not automatically a theorem about a variety or derived
category; any realization hypotheses must remain explicit.

## Validation

Run before pushing:

```bash
lake build
lake env lean scripts/Audit.lean
```

`BridgelandStabLean/ForMathlib/` holds results **Mathlib does not have at the
pin**. Every file in it is a shadow of something that may land upstream, so a
pin bump is the moment each one can become a duplicate.

Before bumping, for each file in `ForMathlib/`: check whether the upstream
version now exists, and if it does, **delete the local file in the same
commit** rather than keeping both. Two copies of `Matrix.polarFactor` in one
environment is an ambiguous name at best and a silent divergence at worst — and
the divergence is not hypothetical, see below.

Do **not** "sync" a local file from its upstream counterpart. They are written
against different Mathlib generations and the differences are real, not
cosmetic. Delete and use upstream, or keep the local one and don't bump.

Current contents:

| file | upstream | status |
|---|---|---|
| `PolarDecomposition.lean` | [mathlib4#42449](https://github.com/leanprover-community/mathlib4/pull/42449) | **closed, not merged** — keep. A maintainer is upstreaming a *more general* version (not matrix-specific); delete this file only once that lands **and is in the pin**. Do not pre-emptively delete on the strength of the promise — see below. |

**Do not treat "a maintainer has code for this" as a delivery date.** #42449 is
the *second* matrix polar decomposition closed this way. The first,
[mathlib4#33642](https://github.com/leanprover-community/mathlib4/pull/33642),
was closed by a different maintainer in January 2026 with the same reasoning
and the same offer — *"I have code for this somewhere"* — and as of August 2026
nothing general had landed; #42449's reviewer then said the same thing again,
adding *"I haven't had time to clean it up and upstream it yet."* Two people,
seven months apart, both holding unupstreamed work. That is not bad faith, it
is what volunteer capacity looks like, and the checklist above must not stall
waiting for it. The deletion condition is a `lake build` against the new pin
resolving `Matrix.polarFactor` (or its general replacement) from Mathlib — a
command, not a citation.

### Bumping the anchor pin: check the injected names first

`ForMathlib/` is not the only place a pin bump can create a duplicate. This repo
declares **31 dot-notation extensions on types it does not own**, all of them
anchor types, and none is covered by the table above:

| owner type | injected here |
|---|---|
| `HNFiltration` | `exists_headTail`, `mapF`, `mass`, `mass_appendFactor`, `mass_dropFirst`, `mass_eq_mass`, `mass_eq_zero_of_isZero`, `mass_ofIso`, `mass_pos`, `mass_prefix_last`, `relabelPhasePredicate`, `shiftWeakAmbient`, `shiftWeakAmbient_phase` |
| `HeartStabilityData` | `H0FunctorIsoOriginalHeartCohFunctor`, `H0Functor_isHomological_unconditional`, `H0primeFunctor_isHomological_unconditional`, `heartSourceH0Complex`, `heartSourceH0Complex_exact`, `heartSourceH0Complex_exact_iff_mono_cokernelDesc`, `mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional` |
| `K₀` | `mapF`, `mapF_comp`, `mapF_congr`, `mapF_id`, `mapF_of`, `mapF_shift_neg_two` |
| `Slicing` | `mapEquiv`, `mapEquiv_P`, `phiMinus_congr`, `phiPlus_congr` |
| `PostnikovTower` | `mapF` |

Regenerate the list with:

```bash
grep -rhoE "^(private )?(noncomputable )?(scoped )?(theorem|lemma|def|instance|abbrev) (Slicing|HNFiltration|HeartStabilityData|PostnikovTower|K₀)\.[A-Za-z_'0-9]+" \
  BridgelandStabLean/ | sed -E 's/^.*(theorem|lemma|def|instance|abbrev) //' | sort -u
```

Add new public declarations to the audit. Review `git status` before staging and keep planning
or session-continuity documents named `ROADMAP.md` and `HANDOFF.md` outside Git.

The dependency API notes are maintained at
[`notes/dependencies/BridgelandStabilityAPI.md`](notes/dependencies/BridgelandStabilityAPI.md).
