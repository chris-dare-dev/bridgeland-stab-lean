/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.WeakStability.AmbientHarderNarasimhan
import BridgelandStabLean.WeakStability.TiltAssembly

/-!
# Reverse weak heart--slicing assembly for the phase tilt

This module connects the heart-level output of `TiltAssembly` to the reverse
weak heart--slicing foundations.  It isolates the exact remaining boundary
between the completed heart-level part of Proposition 14.16 and an ambient
weak prestability condition:

* the analytic ray identity relating the normalized slope phase to the
  rotated central charge.

Hom vanishing is discharged by `HeartHomVanishing`, and ambient HN existence
by `AmbientHarderNarasimhan`: boundedness of the tilted t-structure and the
heart HN property extend the towers through the finite t-cohomological
filtration.  The first constructor below therefore records only the remaining
analytic compatibility obligation.  No §14 coverage status is promoted by
this infrastructure.
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

/-- The reverse-direction data left after the heart-level HN, noetherian,
support, Hom-vanishing, and ambient HN obligations have been assembled. -/
structure PhaseTiltPreStabilityObligations
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ) where
  /-- The already assembled heart-level conclusions. -/
  heart : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin
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

omit [FiniteDimensional ℝ V] in
/-- The heart HN field of the phase-tilt assembly extends canonically to an
ambient HN filtration for every object.  Boundedness of the original slicing
t-structure is preserved by the HRS tilt, and
`WeakStabilityFunction.ambientHN_exists_of_bounded` performs the finite
t-cohomological assembly. -/
theorem PhaseTiltHeartObligations.ambientHN
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ)
    (H : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin)
    (E : C) :
    Nonempty (HNFiltration C
      (WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)) E) :=
  WeakStabilityFunction.ambientHN_exists_of_bounded
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)
    (heartTorsionPair_tilt_isBounded
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le)
      (sigma.slicing.toTStructure_bounded C))
    H.hasHN E

/-- Package the completed categorical phase-tilt assembly and the remaining
analytic ray compatibility into the weak prestability condition sought in
Proposition 14.16. -/
noncomputable def PhaseTiltPreStabilityObligations.toWeakPreStabilityCondition
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (O : sigma.PhaseTiltPreStabilityObligations
      beta hbeta0 hbeta1 Zlin) : WeakPreStabilityCondition v :=
  (WeakStabilityFunction.reverseSlicingObligationsOfHN
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)
    (fun E ↦ O.heart.ambientHN sigma beta hbeta0 hbeta1 Zlin E)).toWeakPreStabilityCondition
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
