/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license.
-/
import BridgelandStabLean.GroupAction.GLTilde
import BridgelandStability.Slicing.Defs

/-!
# The action on slicings

Lane-1 step 3a. **The first file here that imports the anchor.**

A normalized shift `f` acts on a slicing by relabelling phases:

```
(f • s).P φ = s.P (f⁻¹ φ)
```

`f⁻¹` rather than `f` is what makes this a *left* action, and `mul_smul`
below is the test that pins it down — with `f` in place of `f⁻¹` the
definition still typechecks and `mul_smul` fails.

Only the `NormalizedShift` factor is involved: the matrix factor of
`G̃L⁺(2, ℝ)` acts on the central charge, not on the slicing. So the action is
defined for `NormalizedShift` and `GLTilde` inherits it through
`GLTilde.toShiftHom`.

## Why the axioms survive

See `notes/anchor-api-map.md` §2 for the full table. The one with content is
`shift_iff`, which needs `f⁻¹ (φ + 1) = f⁻¹ φ + 1` — i.e. exactly
`NormalizedShift.symm_map_add_one` from step 1, here reached through the
group structure as `f⁻¹.map_add_one`. That lemma was proved before it had a
consumer; this is the consumer.

`hn_exists` reuses the Postnikov tower untouched — `PostnikovTower` carries no
phase data, all of it lives in `HNFiltration`'s extra fields — and relabels
the factor phases by `f`.
-/

namespace BridgelandStabLean.GroupAction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

noncomputable section

universe v u

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Relabel a slicing's phases by `f`: the objects semistable of phase `φ` in
`relabel f s` are those semistable of phase `f⁻¹ φ` in `s`. -/
def relabel (f : NormalizedShift) (s : Slicing C) : Slicing C where
  P φ := s.P (f⁻¹.toOrderIso φ)
  closedUnderIso _ := s.closedUnderIso _
  zero_mem _ := s.zero_mem _
  shift_iff φ X := by
    rw [f⁻¹.map_add_one]
    exact s.shift_iff _ X
  hom_vanishing _ _ A B h hA hB g :=
    s.hom_vanishing _ _ A B (f⁻¹.toOrderIso.lt_iff_lt.mpr h) hA hB g
  hn_exists E := by
    obtain ⟨F⟩ := s.hn_exists E
    refine ⟨{ toPostnikovTower := F.toPostnikovTower
              φ := fun j => f.toOrderIso (F.φ j)
              hφ := fun _ _ hab => f.toOrderIso.lt_iff_lt.mpr (F.hφ hab)
              semistable := fun j => ?_ }⟩
    show s.P (f⁻¹.toOrderIso (f.toOrderIso (F.φ j))) _
    rw [NormalizedShift.inv_apply, OrderIso.symm_apply_apply]
    exact F.semistable j

@[simp]
theorem relabel_P (f : NormalizedShift) (s : Slicing C) (φ : ℝ) :
    (relabel C f s).P φ = s.P (f⁻¹.toOrderIso φ) := rfl

/-- Normalized shifts act on slicings by phase relabelling. -/
-- The `show`s are load-bearing: while the instance is still being elaborated
-- `•` stays opaque, so `relabel_P` has nothing to match against and `simp`
-- reports no progress.
instance slicingMulAction : MulAction NormalizedShift (Slicing C) where
  smul := relabel C
  one_smul s := Slicing.ext C (by
    funext φ
    show (relabel C 1 s).P φ = s.P φ
    simp)
  mul_smul f g s := Slicing.ext C (by
    funext φ
    show (relabel C (f * g) s).P φ = (relabel C f (relabel C g s)).P φ
    simp [mul_inv_rev])

@[simp]
theorem smul_slicing_P (f : NormalizedShift) (s : Slicing C) (φ : ℝ) :
    (f • s).P φ = s.P (f⁻¹.toOrderIso φ) := rfl

/-- `G̃L⁺(2, ℝ)` acts on slicings through its phase-relabelling factor.

The matrix factor is not involved — it acts on the central charge, which is
step 3b. -/
instance gltildeSlicingMulAction : MulAction GLTilde (Slicing C) :=
  MulAction.compHom _ GLTilde.toShiftHom

@[simp]
theorem gltilde_smul_slicing_P (x : GLTilde) (s : Slicing C) (φ : ℝ) :
    (x • s).P φ = s.P (x.shift⁻¹.toOrderIso φ) := rfl

end

end BridgelandStabLean.GroupAction
