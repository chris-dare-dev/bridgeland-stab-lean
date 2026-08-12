/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Phase.Order.Equivariance

/-!
# The abstract Bayer property

The geometric literature writes the Bayer property for tensoring by a line
bundle and shifting by an integer.  At the abstract slicing layer, the tensor
operation is simply a chosen autoequivalence action, while the shift is a
phase translation.  Keeping those two inputs explicit avoids importing a
scheme or pretending that `AutQuot C` is literally tensor by a line bundle.

## Quantifier order

`HasBayerProperty s q l` fixes one slicing `s`, one quotient
autoequivalence `q`, and one integer `l`, and asserts the single comparison

`s ≼ (q • s).phaseShift l`.

There is no existential quantifier over the twist or the integer.  This is the
quantifier order of arXiv:2607.28411v1, Definition 3.16; the geometric
instantiation `q = - ⊗ L` remains outside this repository.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u

namespace BridgelandStabLean.GroupAction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The abstract Bayer property for a slicing, a chosen autoequivalence, and
an integer phase shift. -/
def HasBayerProperty (s : Slicing C) (q : AutQuot C) (l : ℤ) : Prop :=
  s.PrecedesWeak C ((q • s).phaseShift C (l : ℝ))

/-- Explicit name for the slicing-level abstraction. -/
abbrev SlicingBayerProperty (s : Slicing C) (q : AutQuot C) (l : ℤ) : Prop :=
  HasBayerProperty s q l

/-- Unfold the abstract Bayer property to its defining slicing comparison. -/
theorem hasBayerProperty_iff (s : Slicing C) (q : AutQuot C) (l : ℤ) :
    HasBayerProperty s q l ↔
      s.PrecedesWeak C ((q • s).phaseShift C (l : ℝ)) := Iff.rfl

/-- The identity autoequivalence with zero phase shift satisfies the Bayer
property by reflexivity of the weak slicing order. -/
theorem hasBayerProperty_one_zero (s : Slicing C) :
    HasBayerProperty s (1 : AutQuot C) 0 := by
  unfold HasBayerProperty
  have hzero : s.phaseShift C 0 = s := by
    refine Slicing.ext C ?_
    funext phi E
    change s.P (phi + 0) E = s.P phi E
    rw [add_zero]
  simpa only [Int.cast_zero, one_smul, hzero] using s.precedesWeak_refl C

/-- Bayer's property is invariant under simultaneous autoequivalence
transport, with the twist conjugated by the transporting element. -/
theorem hasBayerProperty_smul_iff (r q : AutQuot C) (s : Slicing C)
    (l : ℤ) :
    HasBayerProperty (r • s) (r * q * r⁻¹) l ↔ HasBayerProperty s q l := by
  change (r • s).PrecedesWeak C
      ((((r * q * r⁻¹) • (r • s))).phaseShift C (l : ℝ)) ↔
    s.PrecedesWeak C ((q • s).phaseShift C (l : ℝ))
  have hact : (r * q * r⁻¹) • (r • s) = r • (q • s) := by
    simp only [mul_smul, inv_smul_smul]
  rw [hact]
  have hshift : (r • (q • s)).phaseShift C (l : ℝ) =
      r • ((q • s).phaseShift C (l : ℝ)) := by
    induction r using Quotient.inductionOn with
    | _ Phi =>
      refine Slicing.ext C ?_
      funext phi E
      rfl
  rw [hshift]
  exact AutQuot.precedesWeak_smul_iff r s ((q • s).phaseShift C (l : ℝ))

universe u'

variable [IsTriangulated C]
variable {Lambda : Type u'} [AddCommGroup Lambda] {v : K₀ C →+ Lambda}

/-- The paper-facing Bayer property for a class-map stability condition and a
chosen compatible autoequivalence.  The lattice component of `q` moves the
charge; its underlying autoequivalence moves the slicing. -/
def BayerProperty (sigma : StabilityCondition.WithClassMap C v)
    (q : AutPairQuot v) (l : ℤ) : Prop :=
  sigma.slicing.PrecedesWeak C ((q • sigma).slicing.phaseShift C (l : ℝ))

/-- Express the paper-facing Bayer property through the reusable
slicing-level predicate and the forgetful homomorphism to `AutQuot`. -/
theorem bayerProperty_iff (sigma : StabilityCondition.WithClassMap C v)
    (q : AutPairQuot v) (l : ℤ) :
    BayerProperty sigma q l ↔
      HasBayerProperty sigma.slicing (AutPairQuot.toAutQuot q) l := by
  rw [BayerProperty, HasBayerProperty, AutPairQuot.smul_slicing]

/-- The identity compatible autoequivalence with zero phase shift satisfies
the paper-facing Bayer property. -/
theorem bayerProperty_one_zero (sigma : StabilityCondition.WithClassMap C v) :
    BayerProperty sigma (1 : AutPairQuot v) 0 := by
  rw [bayerProperty_iff]
  simpa using hasBayerProperty_one_zero sigma.slicing

end BridgelandStabLean.GroupAction
