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
import BridgelandStabLean.Tilting.HeartTorsionPair
import BridgelandStabLean.Support.SupportProperty
import BridgelandStabLean.FiniteLength.SimpleCharge
import BridgelandStabLean.Wall.Numerical
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
import BridgelandStabLean.GroupAction.StabilityMassTriangle

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
* `Support/` — the Kontsevich–Soibelman equivalence between the support
  property and a quadratic form negative definite on `ker Z`. Linear algebra
  and one compactness argument; the distinguished set is arbitrary and is not
  identified with the semistable classes.
* `FiniteLength/` — charges on `Fin n → ℤ`, the lattice half of Bridgeland's
  `ℍ̄ⁿ` example. The identification with `K₀(A)` is Jordan–Hölder, which
  neither Mathlib nor the anchor has, and is never discharged.
* `Wall/` — numerical walls in the `(s, t)` half plane. The wall equation is
  an identity on triples of reals: no surface, no Chern character, and no
  Bogomolov–Gieseker inequality assumed or axiomatised.
* `GroupAction/` — the §8 `G̃L⁺(2, ℝ)` action the anchor does not cover.

See `README.md` for why the geometric lane is deliberately absent, and
`formalization.yaml` for the trust record.
-/
