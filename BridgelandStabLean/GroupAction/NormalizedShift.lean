/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

/-!
# Normalized shifts — the slicing half of `G̃L⁺(2, ℝ)`

Lane-1 groundwork for the §8 gap.

`BridgelandStability` (the anchor) covers Bridgeland 2007 §2-7. §8 — the
`G̃L⁺(2, ℝ)` action on `Stab(D)` and the autoequivalence action — is outside
its stated scope, and Serre-invariance arguments consume exactly that action.

The universal cover `G̃L⁺(2, ℝ)` is standardly presented as pairs `(T, f)`
with `T ∈ GL⁺(2, ℝ)` and `f : ℝ ≃o ℝ` satisfying `f (φ + 1) = f φ + 1`,
subject to `T` and `f` inducing the same map on `S¹`. This file builds the
`f` half, which is entirely self-contained: it needs neither the anchor's API
nor any geometry.

The `f` component is what acts on a slicing (it relabels phases); the `T`
component acts on the central charge. Splitting them lets the phase-relabelling
half be developed and checked independently of the anchor's `Slicing` API.

## Status

No `sorry` here. The group structure is deliberately *not* yet declared —
see the TODO below. Statements land before instances; an instance asserted
ahead of its proof is exactly the debt this project exists to avoid.
-/

namespace BridgelandStabLean.GroupAction

/-- An order-isomorphism of `ℝ` commuting with `φ ↦ φ + 1`.

The phase-relabelling half of an element of `G̃L⁺(2, ℝ)`. The `φ + 1`
equivariance is what makes it descend to the circle `ℝ / 2ℤ`, and it is why
the shift functor `[1]` interacts with the action the way §8 needs. -/
structure NormalizedShift where
  /-- The underlying increasing bijection of `ℝ`. -/
  toOrderIso : ℝ ≃o ℝ
  /-- Equivariance for the unit shift. -/
  map_add_one : ∀ φ : ℝ, toOrderIso (φ + 1) = toOrderIso φ + 1

namespace NormalizedShift

variable (f g : NormalizedShift)

/-- The inverse of a normalized shift is again `+1`-equivariant. -/
theorem symm_map_add_one (ψ : ℝ) :
    f.toOrderIso.symm (ψ + 1) = f.toOrderIso.symm ψ + 1 := by
  apply f.toOrderIso.injective
  rw [OrderIso.apply_symm_apply, f.map_add_one, OrderIso.apply_symm_apply]

/-- The identity relabelling. -/
protected def id : NormalizedShift where
  toOrderIso := OrderIso.refl ℝ
  map_add_one _ := rfl

/-- Composition of normalized shifts. -/
protected def comp : NormalizedShift where
  toOrderIso := g.toOrderIso.trans f.toOrderIso
  map_add_one φ := by
    simp only [OrderIso.trans_apply, g.map_add_one, f.map_add_one]

/-- The inverse relabelling. -/
protected def symm : NormalizedShift where
  toOrderIso := f.toOrderIso.symm
  map_add_one := f.symm_map_add_one

/-
TODO (lane-1, step 1): promote `id`/`comp`/`symm` to a `Group` instance.
Needs a `DFunLike`-style `ext` lemma for `NormalizedShift` first.

TODO (lane-1, step 2): pair with `T ∈ GL⁺(2, ℝ)` under the "same map on `S¹`"
compatibility to obtain `G̃L⁺(2, ℝ)` proper.

TODO (lane-1, step 3): the action on the anchor's `Slicing`. This is the first
declaration in this repo that touches `BridgelandStability`'s API, and it
should not be attempted before reading `BridgelandStability/Slicing/` and
`BridgelandStability/StabilityCondition/` end to end.
-/

end NormalizedShift

end BridgelandStabLean.GroupAction
