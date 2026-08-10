/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.WeakStability.HeartEquivalenceReverse
import BridgelandStabLean.WeakStability.TiltAssembly

/-!
# Reverse weak heart--slicing assembly for the phase tilt

This module connects the heart-level output of `TiltAssembly` to the reverse
weak heart--slicing foundations.  It isolates the exact remaining boundary
between the completed heart-level part of Proposition 14.16 and an ambient
weak prestability condition:

* Hom vanishing for the integer-normalized weak phase predicates;
* extension of the heart HN towers through shifts and finite t-cohomological
  extensions to every ambient object;
* the analytic ray identity relating the normalized slope phase to the
  rotated central charge.

The first constructor below records all three without hiding them.  The
second packages them into `WeakPreStabilityCondition`; no §14 coverage status
is promoted by this infrastructure.
-/

namespace BridgelandStabLean.WeakStability

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {v : K₀ C →+ V}

namespace WeakPreStabilityCondition

/-- The lattice-level central charge of the phase tilt. -/
noncomputable def phaseTiltLatticeCharge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) : V →+ ℂ :=
  (phaseTiltRotation beta).comp sigma.Z

omit [IsTriangulated C] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp]
theorem phaseTiltLatticeCharge_apply
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) (x : V) :
    sigma.phaseTiltLatticeCharge beta x =
      sigma.Z x * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

/-- The ambient reverse-direction data left after the heart-level HN,
noetherian, and support obligations have been assembled. -/
structure PhaseTiltPreStabilityObligations
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ) where
  /-- The already assembled heart-level conclusions. -/
  heart : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin
  /-- Hom vanishing and global HN existence for the induced weak phases. -/
  reverse : WeakStabilityFunction.ReverseSlicingObligations
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)
  /-- The normalized weak phase lies on the ray of the rotated charge. -/
  compat : ∀ (phi : ℝ) (E : C),
    WeakStabilityFunction.ambientPhasePredicate
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) phi E →
    ¬IsZero E → ∃ m : ℝ, 0 ≤ m ∧
      ((∀ n : ℤ, phi ≠ (n : ℝ)) → 0 < m) ∧
      sigma.phaseTiltLatticeCharge beta (v (K₀.of C E)) =
        (m : ℂ) * Complex.exp ((Real.pi * phi : ℂ) * Complex.I)

omit [FiniteDimensional ℝ V] in
/-- The heart-level HN field of the phase-tilt assembly gives ambient HN
towers for all objects already lying in the tilted heart. -/
theorem PhaseTiltHeartObligations.ambientHN_exists_of_mem_tiltedHeart
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ)
    (H : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin)
    (E : C)
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E) :
    Nonempty (HNFiltration C
      (WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)) E) :=
  WeakStabilityFunction.ambientHN_exists_of_mem_heart
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) H.hasHN E hE

/-- Package the completed heart-level phase-tilt assembly and the three
ambient reverse obligations into the weak prestability condition sought in
Proposition 14.16. -/
noncomputable def PhaseTiltPreStabilityObligations.toWeakPreStabilityCondition
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (O : sigma.PhaseTiltPreStabilityObligations
      beta hbeta0 hbeta1 Zlin) : WeakPreStabilityCondition v :=
  O.reverse.toWeakPreStabilityCondition
    (sigma.phaseTiltLatticeCharge beta) O.compat

omit [FiniteDimensional ℝ V] in
@[simp]
theorem PhaseTiltPreStabilityObligations.toWeakPreStabilityCondition_Z
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (O : sigma.PhaseTiltPreStabilityObligations beta hbeta0 hbeta1 Zlin) :
    O.toWeakPreStabilityCondition.Z = sigma.phaseTiltLatticeCharge beta := rfl

omit [FiniteDimensional ℝ V] in
@[simp]
theorem PhaseTiltPreStabilityObligations.toWeakPreStabilityCondition_P
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (O : sigma.PhaseTiltPreStabilityObligations beta hbeta0 hbeta1 Zlin) :
    O.toWeakPreStabilityCondition.slicing.P =
      WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) := rfl

end WeakPreStabilityCondition

end

end BridgelandStabLean.WeakStability
