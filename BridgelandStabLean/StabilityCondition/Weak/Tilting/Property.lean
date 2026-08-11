/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Weak.Heart.Noetherian
import BridgelandStabLean.StabilityCondition.Weak.Tilting.TorsionPair.Slope

/-!
# The tilting property (Definition 14.12)

The tilting property from Definition 14.12 of arXiv:1902.08184v4, on the
reviewed abstract layer.  A weak prestability condition already carries its
Harder--Narasimhan slicing, so the paper's condition `muPlus F < +infinity`
is phrased here as `phiPlus F < 1`: for an object of the slicing heart these
say that the largest HN factor is off the real-axis boundary.  This is the
same phase-language convention as `SlopeTorsionPair.lean`.  The normalized
slope--phase ray identity is formalized downstream in
`StabilityCondition/Weak/Basic/ChargeRay.lean`; the exact Definition 14.12 source comparison
has not yet received the review needed to move the coverage map beyond its
existing `mapped` hypothesis.

The short exact sequence `F -> Ftilde -> F0` in part (2) is a distinguished
triangle whose three vertices lie in the heart, following the convention of
`Basic.lean` and `Noetherian.lean`.  The condition
`Hom(A0, Ftilde[1]) = 0` is stated literally as vanishing of every such map.

## What remains deliberately undeclared

**Proposition 14.16 is left undeclared.**  Its paper proof uses the weak-HN
heart equivalence of Lemma 14.4 and the support-property transport of
Remark 14.9.  `StabilityCondition/Weak/Heart/Equivalence.lean` constructs the
heart-level weak stability function and identifies its semistable nonzero
heart objects with slicing semistability;
`StabilityCondition/Weak/HarderNarasimhan/Heart.lean` now packages the abelian weak HN
filtration and proves its existence for that induced function.
`StabilityCondition/Weak/Tilting/Cohomology/Basic.lean` supplies the common
cohomology functor, the canonical `H⁻¹[1] → E → H⁰` short exact sequence, and
its kernel/cokernel witnesses.  `StabilityCondition/Weak/Tilting/Cohomology/Sequence.lean`
constructs the arbitrary-short-exact six-term sequence, identifies all six
canonical factors, and proves exactness plus the two endpoint properties
unconditionally.  The underlying general theorem is supplied by
`StabilityCondition/Weak/Tilting/Cohomology/Homological.lean`, which proves degree-zero
cohomology homological for every t-structure without stability or HN data.
`StabilityCondition/Weak/Tilting/Semistable.lean` constructs the rotated weak function,
identifies its zero-charge subcategory, and proves both directions of the
phase-language classification in Lemma 14.17.  It also defines weak stability
and proves the lemma's positive-imaginary/stable `moreover` clause via images
in the tilted heart. `StabilityCondition/Weak/Tilting/Noetherian.lean` constructs the
maximal-subobject and noetherian-torsion assembly from the relative chain
condition. It now discharges that condition directly from the raw Definition
14.12 envelope: Ext-vanishing transfers a zero-charge subobject chain to the
original zero-charge quotient, and maximal subobjects provide the
phase-compatible shifted decomposition without asserting that the raw middle
term is phase-free.
`StabilityCondition/Weak/Tilting/HarderNarasimhan.lean` performs boundary-phase saturation
without a last-factor right-orthogonality premise and iterates the resulting
reduction over the original `H⁻¹` and `H⁰` HN filtrations.
`StabilityCondition/Weak/Tilting/Assembly.lean` packages the resulting HN theorem with the
noetherian and support obligations directly from `TiltingProperty`, without
an external envelope, rank, or quotient-induction input.
`StabilityCondition/Weak/Support/Basic.lean` transports the support property unconditionally.
The heart-level constructive obligations are therefore assembled; the exact
slope-language source statement remains under the registry's existing
`mapped` hypothesis until the exact slope-cutoff reparameterisation is
reviewed. `StabilityCondition/Weak/Basic/ChargeRay.lean` now proves the normalized
slope--phase charge-ray identity, and `StabilityCondition/Weak/Tilting/PreStability.lean`
packages the reverse construction as a new `WeakPreStabilityCondition`.
Proposition 14.16 nevertheless remains undeclared until the exact source
statement receives the required faithfulness review and owner signoff.
-/

namespace BridgelandStabLean.WeakStability

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

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

/-- A tilting envelope whose middle term is explicitly in the phase-cut
torsion-free class.  Rotating its defining triangle gives the short exact
sequence in the tilted heart used in the proof of Proposition 14.16.

The paper obtains this membership implicitly when it passes from Definition
14.12(2) to `0 → F⁰ → F[1] → F̃[1] → 0`.  It is named here so that
the heart-membership conversion is an independently checkable boundary; it is
not added to `TiltingProperty` as an extra axiom. -/
def HasPhaseTiltingEnvelope (beta : ℝ) (F : C) : Prop :=
  ∃ (Ftilde F0 : C) (_ : phaseFree sigma.slicing beta Ftilde)
    (_ : sigma.zeroCharge F0) (i : F ⟶ Ftilde) (p : Ftilde ⟶ F0)
    (d : F0 ⟶ F⟦(1 : ℤ)⟧),
      Triangle.mk i p d ∈ distTriang C ∧
        ∀ A0 : C, sigma.zeroCharge A0 →
          ∀ f : A0 ⟶ Ftilde⟦(1 : ℤ)⟧, f = 0

/-- Forgetting the phase-cut membership recovers a Definition 14.12
envelope. -/
theorem HasPhaseTiltingEnvelope.hasTiltingEnvelope
    (sigma : WeakPreStabilityCondition v) {beta : ℝ} {F : C}
    (hbeta1 : beta ≤ 1) (h : sigma.HasPhaseTiltingEnvelope beta F) :
    sigma.HasTiltingEnvelope F := by
  obtain ⟨Ftilde, F0, hFtilde, hF0, i, p, d, hd, hhom⟩ := h
  exact ⟨Ftilde, F0,
    mem_heart_of_bounds sigma.slicing hFtilde.1
      (sigma.slicing.leProp_mono C hbeta1 Ftilde hFtilde.2),
    hF0, i, p, d, hd, hhom⟩

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

/-- Definition 14.12(2) supplies a raw tilting envelope for every object in a
phase-cut torsion-free class.  The zero object is handled by the contractible
triangle; for a nonzero object, the `leProp beta` bound makes its largest
phase strictly smaller than `1`.

This deliberately returns `HasTiltingEnvelope`, not
`HasPhaseTiltingEnvelope`: the raw envelope's middle term need not remain in
`P((0, beta])`.  Its Ext-vanishing is instead used to prove termination of
zero-charge subobject chains after tilting. -/
theorem TiltingProperty.hasTiltingEnvelope_of_phaseFree
    (sigma : WeakPreStabilityCondition v) (h : sigma.TiltingProperty)
    (beta : ℝ) (hbeta1 : beta < 1) (F : C)
    (hF : phaseFree sigma.slicing beta F) : sigma.HasTiltingEnvelope F := by
  have hFheart : sigma.slicing.toTStructure.heart F :=
    mem_heart_of_bounds sigma.slicing hF.1
      (sigma.slicing.leProp_mono C hbeta1.le F hF.2)
  by_cases hFzero : IsZero F
  · refine ⟨F, 0, hFheart, ?_, 𝟙 F, 0, 0,
      contractible_distinguished F, ?_⟩
    · refine ⟨mem_heart_of_bounds sigma.slicing
        (sigma.slicing.gtProp_zero C 0) (sigma.slicing.leProp_zero C 1), ?_⟩
      rw [K₀.of_zero, map_zero, map_zero]
    · intro A0 hA0 f
      exact ((shiftFunctor C (1 : ℤ)).map_isZero hFzero).eq_of_tgt f 0
  · exact h.exists_envelope F hFheart
      ⟨hFzero,
        (sigma.slicing.phiPlus_le_of_leProp C hFzero hF.2).trans_lt hbeta1⟩

end WeakPreStabilityCondition

end BridgelandStabLean.WeakStability
