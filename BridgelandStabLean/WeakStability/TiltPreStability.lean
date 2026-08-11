/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.WeakStability.AmbientHarderNarasimhan
import BridgelandStabLean.WeakStability.ChargeRay
import BridgelandStabLean.WeakStability.TiltAssembly

/-!
# Reverse weak heart--slicing assembly for the phase tilt

This module connects the heart-level output of `TiltAssembly` to the reverse
weak heart--slicing foundations.  The analytic ray identity is supplied by
`ChargeRay`: normalized weak slopes give the required heart charge rays, and
integer shifts give the ambient compatibility axiom.

Hom vanishing is discharged by `HeartHomVanishing`, and ambient HN existence
by `AmbientHarderNarasimhan`: boundedness of the tilted t-structure and the
heart HN property extend the towers through the finite t-cohomological
filtration.  Consequently the phase-language weak upper tilt is now packaged
without an external reverse-equivalence premise.  No §14 coverage status is
promoted by this infrastructure; the exact slope-language source statement
still requires a source-faithfulness review.
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

/-- The heart-level data used by the reverse phase-tilt constructor.  Charge
ray compatibility is now a theorem of every weak stability function rather
than an external field. -/
structure PhaseTiltPreStabilityObligations
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ) where
  /-- The assembled heart-level conclusions. -/
  heart : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The normalized ambient weak phase lies on the ray of the rotated lattice
charge.  This is the analytic compatibility field that was previously left
as an input to `PhaseTiltPreStabilityObligations`. -/
theorem phaseTilt_ambientPhasePredicate_charge_ray
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    ∀ (phi : ℝ) (E : C),
    WeakStabilityFunction.ambientPhasePredicate
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) phi E →
    ¬IsZero E → ∃ m : ℝ, 0 ≤ m ∧
      ((∀ n : ℤ, phi ≠ (n : ℝ)) → 0 < m) ∧
      sigma.phaseTiltLatticeCharge beta (v (K₀.of C E)) =
        (m : ℂ) * Complex.exp ((Real.pi * phi : ℂ) * Complex.I) := by
  intro phi E hP hE0
  simpa only [phaseTiltLatticeCharge_apply,
    phaseTiltWeakStabilityFunction_charge] using
    WeakStabilityFunction.ambientPhasePredicate_charge_ray
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) phi E hP hE0

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

/-- Package the completed heart-level phase-tilt assembly as an ambient weak
prestability condition.  Both ambient HN existence and charge-ray
compatibility are derived rather than supplied as premises. -/
noncomputable def PhaseTiltHeartObligations.toWeakPreStabilityCondition
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (H : sigma.PhaseTiltHeartObligations
      beta hbeta0 hbeta1 Zlin) : WeakPreStabilityCondition v :=
  (WeakStabilityFunction.reverseSlicingObligationsOfHN
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)
    (fun E ↦ H.ambientHN sigma beta hbeta0 hbeta1 Zlin E)).toWeakPreStabilityCondition
    (sigma.phaseTiltLatticeCharge beta)
    (sigma.phaseTilt_ambientPhasePredicate_charge_ray beta hbeta0 hbeta1)

omit [FiniteDimensional ℝ V] in
@[simp]
theorem PhaseTiltHeartObligations.toWeakPreStabilityCondition_Z
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (H : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin) :
    H.toWeakPreStabilityCondition.Z = sigma.phaseTiltLatticeCharge beta := rfl

omit [FiniteDimensional ℝ V] in
@[simp]
theorem PhaseTiltHeartObligations.toWeakPreStabilityCondition_P
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (H : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin) :
    H.toWeakPreStabilityCondition.slicing.P =
      WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) := rfl

/-- Backwards-compatible obligation wrapper for the direct heart-level
constructor.  Its sole field is the heart assembly; analytic compatibility is
the theorem `phaseTilt_ambientPhasePredicate_charge_ray`. -/
noncomputable def PhaseTiltPreStabilityObligations.toWeakPreStabilityCondition
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (O : sigma.PhaseTiltPreStabilityObligations
      beta hbeta0 hbeta1 Zlin) : WeakPreStabilityCondition v :=
  O.heart.toWeakPreStabilityCondition

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

/-- The phase-language weak upper tilt constructed directly from Definition
14.12's tilting property, the original support property, and the linear
realization of the charge.  This declaration deliberately makes no claim that
the exact slope-language statement of Proposition 14.16 has been reviewed. -/
noncomputable def phaseTiltWeakPreStabilityConditionOfTiltingProperty
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin) :
    WeakPreStabilityCondition v :=
  (sigma.phaseTiltHeartObligationsOfTiltingProperty
    beta hbeta0 hbeta1 htilt Zlin hcompat hsupport).toWeakPreStabilityCondition

omit [FiniteDimensional ℝ V] in
@[simp]
theorem phaseTiltWeakPreStabilityConditionOfTiltingProperty_Z
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin) :
    (sigma.phaseTiltWeakPreStabilityConditionOfTiltingProperty beta hbeta0 hbeta1
      htilt Zlin hcompat hsupport).Z = sigma.phaseTiltLatticeCharge beta := rfl

omit [FiniteDimensional ℝ V] in
@[simp]
theorem phaseTiltWeakPreStabilityConditionOfTiltingProperty_P
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin) :
    (sigma.phaseTiltWeakPreStabilityConditionOfTiltingProperty beta hbeta0 hbeta1
      htilt Zlin hcompat hsupport).slicing.P =
      WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1) := rfl

end WeakPreStabilityCondition

end

end BridgelandStabLean.WeakStability
