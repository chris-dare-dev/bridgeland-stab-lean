# BridgelandStabLean

BridgelandStabLean is a Lean 4 library for the structure and geometry of Bridgeland stability
conditions. It develops phase analysis, symmetry actions, Harder–Narasimhan mass, the stability
metric, support properties, numerical walls, weak stability, tilting, and lattice models as
one standalone mathematical package.

## What is formalized

- The lifted positive general linear group, its topology and covering structure.
- Actions on slicings, pre-stability conditions, and stability conditions.
- Transport by triangulated autoequivalences, quotienting by natural isomorphism.
- Combined symmetry actions, component transport, period-map equivariance, and effective
  quotients.
- Harder–Narasimhan mass, uniqueness, positivity, and subadditivity along distinguished
  triangles.
- The full stability distance, separation, topology comparison, and symmetry isometries.
- Weak stability conditions on hearts, Harder–Narasimhan properties, support properties, and
  torsion-pair tilting.
- Arithmetic, numerical, and Mukai-style lattice constructions.

The library contains no `sorry` declarations. Open work and theorem-level dependencies are
tracked in GitHub issues and milestones.

## Repository map

The tree follows the mathematical ownership of each result. Same-named umbrella modules make
every level independently importable.

```text
BridgelandStabLean/
├── ForMathlib/
│   └── LinearAlgebra/Matrix/
├── Lattice/
│   ├── Arithmetic/
│   ├── Numerical/
│   └── Mukai/
└── StabilityCondition/
    ├── Phase/
    ├── Metric/
    │   ├── Distance/
    │   ├── Isometry/
    │   └── Mass/Subadditivity/
    ├── Symmetry/
    │   ├── GLTilde/{Action,Covering,Topology}/
    │   ├── Autoequivalence/{Foundations,Slicing,Stability}/
    │   └── Combined/
    ├── Support/
    ├── Walls/Numerical/
    └── Weak/
        ├── Basic/
        ├── Foundations/
        ├── Heart/
        ├── HarderNarasimhan/
        ├── Support/
        └── Tilting/{Cohomology,TorsionPair}/
```

This taxonomy leaves stable growth points for new metric estimates, wall structures, support
conditions, autoequivalence constructions, and weak-stability tilts without returning to flat
filenames.

## Building

The repository pins its Lean toolchain and all Lake dependencies.

```bash
lake build
lake env lean scripts/Audit.lean
```

## Using BridgelandStabLean

Import the complete library with:

```lean
import BridgelandStabLean
```

Or import a narrower umbrella such as
`BridgelandStabLean.StabilityCondition.Metric.Mass.Subadditivity`.

To use the library alongside Mathlib in another Lake package, add it as a dependency and keep
the consuming package on the Lean/Mathlib revisions recorded by this repository's
`lean-toolchain` and `lake-manifest.json`.

## Contributing

New leaves belong beneath the smallest durable mathematical subsystem and should be exported
from its nearest umbrella module. GitHub issues and milestones are the source of truth for
planned paths, prerequisites, and acceptance criteria.

## License

MIT. See [LICENSE](LICENSE).
