/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.ForMathlib.PolarDecomposition
import BridgelandStabLean.Lattice.Basic
import BridgelandStabLean.Lattice.NumericalK
import BridgelandStabLean.GroupAction.NormalizedShift
import BridgelandStabLean.GroupAction.GLTilde
import BridgelandStabLean.GroupAction.GLTildeFibre
import BridgelandStabLean.GroupAction.GLTildeSurj
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

/-!
# BridgelandStabLean

Extensions to `mattrobball/BridgelandStability`, pinned at commit `9e48f23`.

Two lanes, both chosen because they need **no** algebraic-geometry substrate:

* `ForMathlib/` — results Mathlib lacks at the pin, written to be upstreamed.
* `Lattice/` — rank-2 torsion-free arithmetic (closed proofs, today).
* `GroupAction/` — the §8 `G̃L⁺(2, ℝ)` action the anchor does not cover.

See `README.md` for why the geometric lane is deliberately absent, and
`formalization.yaml` for the trust record.
-/
