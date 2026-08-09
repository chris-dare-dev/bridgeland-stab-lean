/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.WeakStability.Noetherian
import BridgelandStabLean.WeakStability.SlopeTorsionPair

/-!
# The tilting property (Definition 14.12)

The tilting property from Definition 14.12 of arXiv:1902.08184v4, on the
reviewed abstract layer.  A weak prestability condition already carries its
Harder--Narasimhan slicing, so the paper's condition `muPlus F < +infinity`
is phrased here as `phiPlus F < 1`: for an object of the slicing heart these
say that the largest HN factor is off the real-axis boundary.  This is the
same phase-language convention as `SlopeTorsionPair.lean`.  The numerical
identity `mu = -cot (pi * phi)` is not formalized, so this declaration is a
candidate for Definition 14.12 under the coverage map's existing `mapped`
hypothesis, not a reviewed source claim.

The short exact sequence `F -> Ftilde -> F0` in part (2) is a distinguished
triangle whose three vertices lie in the heart, following the convention of
`Basic.lean` and `Noetherian.lean`.  The condition
`Hom(A0, Ftilde[1]) = 0` is stated literally as vanishing of every such map.

## What is deliberately not declared

**Proposition 14.16 and Lemma 14.17 are left undeclared.**  Their paper proof
uses the weak-HN heart equivalence of Lemma 14.4, kernels, images and
cohomology objects in both hearts, and the support-property transport of
Remark 14.9.  The current weak layer has a slicing and a heart-level weak
stability function, but no theorem identifying their semistable objects or
HN filtrations, no weak support-property package, and the pinned Mathlib has
no abelian-category instance on a t-structure heart.  In particular, the
classification in Lemma 14.17 cannot be proved from the present
`WeakStabilityFunction.IsSemistable`, and the HN-modification argument and
maximal-subobject step of Proposition 14.16 cannot be expressed honestly.
Declaring either result would therefore require new axioms or hypotheses not
present in the paper.
-/

namespace BridgelandStabLean.WeakStability

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

variable {Lambda : Type*} [AddCommGroup Lambda]

variable (t : TStructure C)

/-- An object property is a noetherian torsion subcategory when it is the
torsion class of a `NoetherianTorsionSubcategory`.  This exposes the class
parameter suppressed by the data-carrying structure of Definition 14.6. -/
def IsNoetherianTorsionSubcategory (B : ObjectProperty C) : Prop :=
  ∃ N : NoetherianTorsionSubcategory t, N.pair.tors = B

namespace WeakPreStabilityCondition

variable {v : K₀ C →+ Lambda}
variable (sigma : WeakPreStabilityCondition v)

/-- The zero-charge subcategory of the slicing heart, for the ambient charge
`sigma.Z ∘ v`.  This is the `A0` occurring in Definition 14.12. -/
def zeroCharge : ObjectProperty C := fun E =>
  sigma.slicing.toTStructure.heart E ∧ sigma.Z (v (K₀.of C E)) = 0

/-- The phase-language form of `muPlus F < +infinity` for a nonzero object of
the slicing heart: its largest HN phase is strictly below the boundary phase
`1`. -/
def HasFiniteMaxSlope (F : C) : Prop :=
  ∃ hF : ¬IsZero F, sigma.slicing.phiPlus C F hF < 1

/-- The envelope required by Definition 14.12(2): a heart short exact
sequence `F -> Ftilde -> F0` with zero-charge quotient and
`Hom(A0, Ftilde[1]) = 0`. -/
def HasTiltingEnvelope (F : C) : Prop :=
  ∃ (Ftilde F0 : C) (_ : sigma.slicing.toTStructure.heart Ftilde)
    (_ : sigma.zeroCharge F0) (i : F ⟶ Ftilde) (p : Ftilde ⟶ F0)
    (d : F0 ⟶ F⟦(1 : ℤ)⟧),
      Triangle.mk i p d ∈ distTriang C ∧
        ∀ A0 : C, sigma.zeroCharge A0 →
          ∀ f : A0 ⟶ Ftilde⟦(1 : ℤ)⟧, f = 0

/-- **The tilting property, Definition 14.12 (phase-language form).**

1. The zero-charge subcategory is noetherian torsion.
2. Every heart object whose largest HN phase is below `1` has a tilting
   envelope.

The support property of a weak stability condition is not used by this
definition, so it is stated on the underlying weak prestability condition. -/
structure TiltingProperty : Prop where
  /-- Definition 14.12(1). -/
  zeroCharge_noetherian :
    IsNoetherianTorsionSubcategory sigma.slicing.toTStructure sigma.zeroCharge
  /-- Definition 14.12(2), with finite maximum slope in phase language. -/
  exists_envelope : ∀ F : C, sigma.slicing.toTStructure.heart F →
    sigma.HasFiniteMaxSlope F → sigma.HasTiltingEnvelope F

end WeakPreStabilityCondition

end BridgelandStabLean.WeakStability
