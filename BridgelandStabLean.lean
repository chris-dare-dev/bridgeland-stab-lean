/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license.
-/
import BridgelandStabLean.Lattice.Basic
import BridgelandStabLean.Lattice.NumericalK
import BridgelandStabLean.GroupAction.NormalizedShift
import BridgelandStabLean.GroupAction.GLTilde
import BridgelandStabLean.GroupAction.ShiftAnalysis
import BridgelandStabLean.GroupAction.ComplexBridge
import BridgelandStabLean.GroupAction.SlicingAction
import BridgelandStabLean.GroupAction.PreStabilityAction
import BridgelandStabLean.GroupAction.StabilityAction
import BridgelandStabLean.GroupAction.AutAction

/-!
# BridgelandStabLean

Extensions to `mattrobball/BridgelandStability`, pinned at commit `9e48f23`.

Two lanes, both chosen because they need **no** algebraic-geometry substrate:

* `Lattice/` — rank-2 torsion-free arithmetic (closed proofs, today).
* `GroupAction/` — the §8 `G̃L⁺(2, ℝ)` action the anchor does not cover.

See `README.md` for why the geometric lane is deliberately absent, and
`formalization.yaml` for the trust record.
-/
