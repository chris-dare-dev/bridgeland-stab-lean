/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.WeakStability.HarderNarasimhan
import BridgelandStabLean.WeakStability.Support
import BridgelandStabLean.WeakStability.TiltHarderNarasimhan

/-!
# Heart-level assembly for the weak upper tilt

This file gathers the three heart-level obligations in Proposition 14.16:

* the weak Harder--Narasimhan property;
* the noetherian zero-charge torsion subcategory;
* transport of the support property.

The generic HN recursion is discharged by
`hasHNProperty_of_quotientInduction`; the noetherian structure is discharged
by `phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty`; and support is
transported unconditionally by `phaseTilt_hasSupportProperty`.

The first constructor keeps the relative zero-charge chain condition and
rank-decreasing quotient induction visible.  The second discharges the chain
condition from phase-compatible envelopes. `TiltHarderNarasimhan` supplies
the cohomological last-factor reduction underlying the quotient induction;
boundary saturation and iteration over both original cohomology filtrations
remain separate.
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

/-- The heart-level conclusions needed for the weak upper tilt.  This does
not assert the reverse weak heart--slicing equivalence, so it deliberately
does not package a new `WeakPreStabilityCondition`. -/
structure PhaseTiltHeartObligations
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ) where
  /-- Harder--Narasimhan filtrations for the rotated weak function. -/
  hasHN :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).HasHNProperty
  /-- The tilted zero-charge class, with its torsion-pair and chain data. -/
  zeroChargeNoetherian : NoetherianTorsionSubcategory
    (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
  /-- Its torsion class is exactly the new zero-charge class. -/
  zeroCharge_tors : zeroChargeNoetherian.pair.tors =
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge
  /-- Support for numerical classes of tilted weak-semistable objects. -/
  support :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).HasSupportProperty
      v (phaseTiltLinearCharge beta Zlin)

/-- Assemble all heart-level obligations for Proposition 14.16 from its two
remaining constructive seams. -/
noncomputable def phaseTiltHeartObligations
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin)
    (hacc : ∀ (E : C),
      ((slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt).heart E →
      ∀ c : SubobjectChain
        (slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).zeroCharge E,
        c.Terminates)
    (rank :
      ((slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt).heart.FullSubcategory
        → ℕ)
    (hquot : WeakStabilityFunction.HasHNQuotientInduction
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1) rank) :
    sigma.PhaseTiltHeartObligations beta hbeta0.le hbeta1 Zlin := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1
  let Nsharp :=
    sigma.phaseTiltNoetherianTorsionSubcategoryOfChainCondition
      beta hbeta0.le hbeta1 htilt hacc
  exact
    { hasHN := W.hasHNProperty_of_quotientInduction rank hquot
      zeroChargeNoetherian := Nsharp
      zeroCharge_tors := rfl
      support := sigma.phaseTilt_hasSupportProperty
        beta hbeta0 hbeta1 Zlin hcompat hsupport }

/-- Assemble the heart-level obligations with the relative zero-charge chain
condition discharged by phase-compatible envelopes.  Compared with
`phaseTiltHeartObligations`, this constructor removes the order-theoretic
`hacc` input: the envelope reduction, reduced-chain termination, and pullback
of the maximal zero-charge subobject are performed in `TiltNoetherian`.

The quotient-induction input remains visible until the last-factor reduction
in `TiltHarderNarasimhan` is iterated over both original cohomology HN
filtrations. -/
noncomputable def phaseTiltHeartObligationsOfPhaseEnvelopes
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin)
    (henv : ∀ (F : C), phaseFree sigma.slicing beta F →
      sigma.HasPhaseTiltingEnvelope beta F)
    (rank :
      ((slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt).heart.FullSubcategory
        → ℕ)
    (hquot : WeakStabilityFunction.HasHNQuotientInduction
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1) rank) :
    sigma.PhaseTiltHeartObligations beta hbeta0.le hbeta1 Zlin := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1
  let Nsharp :=
    sigma.phaseTiltNoetherianTorsionSubcategoryOfPhaseEnvelopes
      beta hbeta0.le hbeta1 htilt henv
  exact
    { hasHN := W.hasHNProperty_of_quotientInduction rank hquot
      zeroChargeNoetherian := Nsharp
      zeroCharge_tors := rfl
      support := sigma.phaseTilt_hasSupportProperty
        beta hbeta0 hbeta1 Zlin hcompat hsupport }

end WeakPreStabilityCondition

end


end BridgelandStabLean.WeakStability
