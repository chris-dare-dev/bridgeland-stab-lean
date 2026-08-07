/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.ForMathlib.PolarDecomposition
import BridgelandStabLean.Lattice.Basic
import BridgelandStabLean.Lattice.NumericalK
import BridgelandStabLean.Mukai.Lattice
import BridgelandStabLean.Mukai.RankTwo
import BridgelandStabLean.Tilting.TorsionPair
import BridgelandStabLean.GroupAction.NormalizedShift
import BridgelandStabLean.GroupAction.GLTilde
import BridgelandStabLean.GroupAction.GLTildeFibre
import BridgelandStabLean.GroupAction.GLTildeSurj
import BridgelandStabLean.GroupAction.GLTildeTopology
import BridgelandStabLean.GroupAction.GLTildeCover
import BridgelandStabLean.GroupAction.GLTildeTopologicalGroup
import BridgelandStabLean.GroupAction.ShiftAnalysis
import BridgelandStabLean.GroupAction.ComplexBridge
import BridgelandStabLean.GroupAction.SlicingAction
import BridgelandStabLean.GroupAction.PreStabilityAction
import BridgelandStabLean.GroupAction.StabilityAction
import BridgelandStabLean.GroupAction.AutAction
import BridgelandStabLean.GroupAction.StrictAutAction
import BridgelandStabLean.GroupAction.QuotAutAction
import BridgelandStabLean.GroupAction.K0Functor
import BridgelandStabLean.GroupAction.StrictFiniteLength
import BridgelandStabLean.GroupAction.AutStabilityAction
import BridgelandStabLean.GroupAction.AutPairAction
import BridgelandStabLean.GroupAction.AutIsometry
import BridgelandStabLean.GroupAction.StabilityMass
import BridgelandStabLean.GroupAction.HNMassUniqueness
import BridgelandStabLean.GroupAction.StabilityDistance
import BridgelandStabLean.GroupAction.StabilityDistanceSeparation
import BridgelandStabLean.GroupAction.StabilityDistanceTopology
import BridgelandStabLean.GroupAction.AutFullIsometry
import BridgelandStabLean.GroupAction.CombinedAction
import BridgelandStabLean.GroupAction.TopologicalAction
import BridgelandStabLean.GroupAction.GLTildeContinuousAction
import BridgelandStabLean.GroupAction.GLTildeJointContinuousAction
import BridgelandStabLean.GroupAction.ComponentAction
import BridgelandStabLean.GroupAction.PeriodMapEquivariance
import BridgelandStabLean.GroupAction.EffectiveAction

/-!
# BridgelandStabLean

Extensions to `mattrobball/BridgelandStability`, pinned at commit `9e48f23`.

Two lanes, both chosen because they need **no** algebraic-geometry substrate:

* `ForMathlib/` — results Mathlib lacks at the pin, written to be upstreamed.
* `Lattice/` — rank-2 torsion-free arithmetic (closed proofs, today).
* `Mukai/` — the Mukai extension `ℤ ⊕ N ⊕ ℤ` of a symmetric bilinear lattice,
  and rank-two subpair arithmetic. Pure lattice theory: no surface, no K3, no
  `D^b(Coh X)`. See that directory's module docstrings for the frontier.
* `Tilting/` — torsion pairs in an abelian category, which Mathlib lacks at
  the pin. Abelian-category theory only; the HRS tilt itself is not here.
* `GroupAction/` — the §8 `G̃L⁺(2, ℝ)` action the anchor does not cover.

See `README.md` for why the geometric lane is deliberately absent, and
`formalization.yaml` for the trust record.
-/
