/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Tilting.HeartCohomologySequence
import BridgelandStabLean.WeakStability.HarderNarasimhan
import BridgelandStabLean.WeakStability.TiltingProperty

/-!
# Semistable objects after tilting a weak stability condition

This file develops the constructive direction of the phase-language
counterpart of Lemma 14.17 of arXiv:1902.08184v4.  The slope cutoff in the
paper is represented by a phase cutoff `beta` in `[0, 1)`, as in
`SlopeTorsionPair.lean`.  The numerical reparameterisation between the two
cutoffs is deliberately not asserted.

The first construction is the weak stability function on the HRS-tilted
heart.  Its charge is the original charge rotated clockwise through
`pi * beta`.  Every object of the tilted heart has all old slicing phases in
`(beta, beta + 1]`; decomposing it into its old HN factors therefore proves
the weak upper-half-plane condition directly, including zero-charge factors.

The two source-shaped classes are then defined and proved semistable.  The
reverse implication, which must extract a unique charged factor from the old
HN filtration of an arbitrary tilted-semistable object, is deliberately not
asserted here.
-/

namespace BridgelandStabLean.WeakStability

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex
open BridgelandStabLean.Tilting
open scoped BigOperators ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

variable {Lambda : Type*} [AddCommGroup Lambda]
variable {v : K₀ C →+ Lambda}

namespace WeakPreStabilityCondition

/-- Clockwise rotation through `pi * beta`, as an additive endomorphism of
the complex plane. -/
noncomputable def phaseTiltRotation (beta : ℝ) : ℂ →+ ℂ where
  toFun z := z * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)
  map_zero' := by simp
  map_add' z w := by rw [add_mul]

@[simp]
theorem phaseTiltRotation_apply (beta : ℝ) (z : ℂ) :
    phaseTiltRotation beta z =
      z * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

/-- The central charge rotated clockwise through the phase cutoff. -/
noncomputable def phaseTiltCharge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) : K₀ C →+ ℂ :=
  (phaseTiltRotation beta).comp (sigma.Z.comp v)

omit [IsTriangulated C] in
@[simp]
theorem phaseTiltCharge_apply
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) (E : C) :
    sigma.phaseTiltCharge beta (K₀.of C E) =
      sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

private def WeakUpperClosed (z : ℂ) : Prop :=
  0 ≤ z.im ∧ (z.im = 0 → z.re ≤ 0)

private theorem weakUpperClosed_zero : WeakUpperClosed 0 := by
  constructor <;> simp

private theorem weakUpperClosed_add {z w : ℂ}
    (hz : WeakUpperClosed z) (hw : WeakUpperClosed w) :
    WeakUpperClosed (z + w) := by
  constructor
  · simpa using add_nonneg hz.1 hw.1
  · intro him
    have hz_nonneg := hz.1
    have hw_nonneg := hw.1
    have hz0 : z.im = 0 := by
      simp only [Complex.add_im] at him
      linarith
    have hw0 : w.im = 0 := by
      simp only [Complex.add_im] at him
      linarith
    simp only [Complex.add_re]
    exact add_nonpos (hz.2 hz0) (hw.2 hw0)

private theorem weakUpperClosed_sum {I : Type*} [Fintype I] (f : I → ℂ)
    (hf : ∀ i, WeakUpperClosed (f i)) :
    WeakUpperClosed (∑ i, f i) := by
  classical
  exact Finset.sum_induction f WeakUpperClosed
    (fun _ _ => weakUpperClosed_add) weakUpperClosed_zero
    (by intro i _; exact hf i)

private theorem weakUpperClosed_eq_zero_of_sum_eq_zero
    {I : Type*} [Fintype I] (f : I → ℂ)
    (hf : ∀ i, WeakUpperClosed (f i)) (hsum : ∑ i, f i = 0) (i : I) :
    f i = 0 := by
  classical
  have himsum : ∑ j, (f j).im = 0 := by
    have := congrArg Complex.im hsum
    simpa using this
  have him : (f i).im = 0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg fun j => (hf j).1).mp himsum) i
  have hre_nonpos : ∀ j, (f j).re ≤ 0 := fun j =>
    (hf j).2 (congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg fun k => (hf k).1).mp himsum) j)
  have hresum : ∑ j, -(f j).re = 0 := by
    have hre := congrArg Complex.re hsum
    have : ∑ j, (f j).re = 0 := by simpa using hre
    simpa using congrArg Neg.neg this
  have hre : -(f i).re = 0 :=
    congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg fun j => neg_nonneg.mpr (hre_nonpos j)).mp
        hresum) i
  apply Complex.ext <;> simp_all

private theorem rotatedRay_weakUpperClosed {beta phi m : ℝ}
    (hm : 0 ≤ m) (hphi : phi ∈ Set.Ioc beta (beta + 1)) :
    WeakUpperClosed
      ((m : ℂ) * Complex.exp (((Real.pi * phi : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((Real.pi : ℂ) * (beta : ℂ)) * Complex.I)) := by
  have hdelta_pos : 0 < phi - beta := by linarith [hphi.1]
  have hdelta_le : phi - beta ≤ 1 := by linarith [hphi.2]
  have hrewrite :
      (m : ℂ) * Complex.exp (((Real.pi * phi : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-((Real.pi : ℂ) * (beta : ℂ)) * Complex.I) =
        (m : ℂ) *
          Complex.exp (((Real.pi * (phi - beta) : ℝ) : ℂ) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hrewrite, Complex.exp_ofReal_mul_I]
  unfold WeakUpperClosed
  simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im,
    Complex.I_im, Complex.I_re, zero_mul, mul_zero, mul_one, add_zero,
    zero_add, Complex.mul_re, sub_zero]
  change
    0 ≤ m * Real.sin (Real.pi * (phi - beta)) ∧
      (m * Real.sin (Real.pi * (phi - beta)) = 0 →
        m * Real.cos (Real.pi * (phi - beta)) ≤ 0)
  constructor
  · exact mul_nonneg hm
      (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))
  · intro him
    rcases mul_eq_zero.mp him with hm0 | hsin0
    · simp [hm0]
    have hdelta : phi - beta = 1 := by
      by_contra hne
      have hdelta_lt : phi - beta < 1 := lt_of_le_of_ne hdelta_le hne
      have hsin_pos : 0 < Real.sin (Real.pi * (phi - beta)) :=
        Real.sin_pos_of_pos_of_lt_pi
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      exact (ne_of_gt hsin_pos) hsin0
    rw [hdelta]
    simpa using neg_nonpos.mpr hm

private def cross (z w : ℂ) : ℝ :=
  z.re * w.im - z.im * w.re

private theorem ray_cross_nonneg {psi theta m n : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hpsi : 0 < psi)
    (horder : psi ≤ theta) (htheta : theta ≤ 1) :
    0 ≤ cross
      ((m : ℂ) * Complex.exp (((Real.pi * psi : ℝ) : ℂ) * Complex.I))
      ((n : ℂ) * Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  unfold cross
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, mul_one, add_zero, zero_add]
  rw [show
      m * Real.cos (Real.pi * psi) * (n * Real.sin (Real.pi * theta)) -
          m * Real.sin (Real.pi * psi) * (n * Real.cos (Real.pi * theta)) =
        (m * n) * Real.sin (Real.pi * (theta - psi)) by
      rw [show Real.pi * (theta - psi) = Real.pi * theta - Real.pi * psi by ring,
        Real.sin_sub]
      ring]
  exact mul_nonneg (mul_nonneg hm hn)
    (Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))

omit [IsTriangulated C] in
private theorem rotatedCharge_weakUpperClosed_of_interval
    (sigma : WeakPreStabilityCondition v) {beta : ℝ} {E : C}
    (hgt : sigma.slicing.gtProp C beta E)
    (hle : sigma.slicing.leProp C (beta + 1) E) :
    WeakUpperClosed
      (sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)) := by
  classical
  by_cases hE : IsZero E
  · simpa [K₀.of_isZero C hE] using weakUpperClosed_zero
  obtain ⟨F, hn, hfirst, hlast⟩ :=
    HNFiltration.exists_both_nonzero C sigma.slicing hE
  let P := F.toPostnikovTower
  have hphase : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc beta (beta + 1) := by
    intro i
    constructor
    · calc
        beta < sigma.slicing.phiMinus C E hE :=
          sigma.slicing.phiMinus_gt_of_gtProp C hE hgt
        _ = F.φ ⟨F.n - 1, by lia⟩ := by
          rw [sigma.slicing.phiMinus_eq C E hE F hn hlast]
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = sigma.slicing.phiPlus C E hE := by
          rw [sigma.slicing.phiPlus_eq C E hE F hn hfirst]
        _ ≤ beta + 1 := sigma.slicing.phiPlus_le_of_leProp C hE hle
  have hsum :
      sigma.Z (v (K₀.of C E)) *
          Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) =
        ∑ i : Fin F.n,
          sigma.Z (v (K₀.of C (P.factor i))) *
            Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum, map_sum, Finset.sum_mul]
  rw [hsum]
  apply weakUpperClosed_sum
  intro i
  by_cases hi : IsZero (P.factor i)
  · simpa [K₀.of_isZero C hi] using weakUpperClosed_zero
  obtain ⟨m, hm, -, hmZ⟩ :=
    sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
  rw [hmZ]
  exact rotatedRay_weakUpperClosed hm (hphase i)

omit [IsTriangulated C] in
private theorem rotatedCharge_cross_ray_nonneg_of_bounds
    (sigma : WeakPreStabilityCondition v) {beta theta n : ℝ} {A : C}
    (hn : 0 ≤ n) (htheta : theta ≤ 1)
    (hgt : sigma.slicing.gtProp C beta A)
    (hle : sigma.slicing.leProp C (beta + theta) A) :
    0 ≤ cross
      (sigma.Z (v (K₀.of C A)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I))
      ((n : ℂ) *
        Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I)) := by
  classical
  by_cases hA : IsZero A
  · simp [K₀.of_isZero C hA, cross]
  obtain ⟨F, hFn, hfirst, hlast⟩ :=
    HNFiltration.exists_both_nonzero C sigma.slicing hA
  let P := F.toPostnikovTower
  let z : ℂ := (n : ℂ) *
    Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I)
  let f : Fin F.n → ℂ := fun i =>
    sigma.Z (v (K₀.of C (P.factor i))) *
      Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)
  have hphase : ∀ i : Fin F.n,
      0 < F.φ i - beta ∧ F.φ i - beta ≤ theta := by
    intro i
    constructor
    · calc
        0 < sigma.slicing.phiMinus C A hA - beta := by
          linarith [sigma.slicing.phiMinus_gt_of_gtProp C hA hgt]
        _ = F.φ ⟨F.n - 1, by lia⟩ - beta := by
          rw [sigma.slicing.phiMinus_eq C A hA F hFn hlast]
        _ ≤ F.φ i - beta := by
          have hi : i ≤ (⟨F.n - 1, by lia⟩ : Fin F.n) :=
            Fin.mk_le_mk.mpr (by lia)
          linarith [F.hφ.antitone hi]
    · calc
        F.φ i - beta ≤ F.φ ⟨0, hFn⟩ - beta := by
          have hi : (⟨0, hFn⟩ : Fin F.n) ≤ i :=
            Fin.mk_le_mk.mpr (Nat.zero_le _)
          linarith [F.hφ.antitone hi]
        _ = sigma.slicing.phiPlus C A hA - beta := by
          rw [sigma.slicing.phiPlus_eq C A hA F hFn hfirst]
        _ ≤ theta := by
          linarith [sigma.slicing.phiPlus_le_of_leProp C hA hle]
  have hsum :
      sigma.Z (v (K₀.of C A)) *
          Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) =
        ∑ i, f i := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum, map_sum, Finset.sum_mul]
  rw [hsum]
  change 0 ≤ cross (∑ i, f i) z
  rw [show cross (∑ i, f i) z = ∑ i, cross (f i) z by
    simp [cross, Finset.sum_mul, ← Finset.sum_sub_distrib]]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : IsZero (P.factor i)
  · simp [f, K₀.of_isZero C hi, cross]
  obtain ⟨m, hm, -, hmZ⟩ :=
    sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
  have hrot : f i =
      (m : ℂ) *
        Complex.exp (((Real.pi * (F.φ i - beta) : ℝ) : ℂ) * Complex.I) := by
    dsimp [f]
    rw [hmZ, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hrot]
  exact ray_cross_nonneg hm hn (hphase i).1 (hphase i).2 htheta

/-- A tilted-heart object has all old slicing phases in `(beta, beta + 1]`.
This is the sector form of the HRS heart description. -/
theorem phaseTiltHeart_interval
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E) :
    sigma.slicing.gtProp C beta E ∧
      sigma.slicing.leProp C (beta + 1) E := by
  obtain ⟨F, T, hF, hT, f, g, d, hdist⟩ :=
    (slicingTilt_heart_iff sigma.slicing hbeta0 hbeta1.le E).mp hE
  have hFgt : sigma.slicing.gtProp C beta (F⟦(1 : ℤ)⟧) := by
    have hshift := sigma.slicing.gtProp_shift C 0 F 1 hF.1
    have hshift' : sigma.slicing.gtProp C 1 (F⟦(1 : ℤ)⟧) := by
      simpa using hshift
    exact sigma.slicing.gtProp_anti C hbeta1.le _ hshift'
  have hFle : sigma.slicing.leProp C (beta + 1) (F⟦(1 : ℤ)⟧) := by
    simpa only [Int.cast_one] using
      sigma.slicing.leProp_shift C beta F 1 hF.2
  have hTgt : sigma.slicing.gtProp C beta T := hT.1
  have hTle : sigma.slicing.leProp C (beta + 1) T :=
    sigma.slicing.leProp_mono C (by linarith) T hT.2
  exact ⟨sigma.slicing.gtProp_of_triangle C beta hFgt hTgt hdist,
    sigma.slicing.leProp_of_triangle C (beta + 1) hFle hTle hdist⟩

/-- The HRS tilt at the phase cut is exactly the heart of the phase-shifted
slicing.  This identifies both descriptions with the interval
`P((beta, beta + 1])`. -/
theorem phaseTiltHeart_iff_phaseShiftHeart
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) :
    ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E ↔
      ((sigma.slicing.phaseShift C beta).toTStructure).heart E := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  constructor
  · intro hE
    obtain ⟨hgt, hle⟩ := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hE
    rw [(sigma.slicing.phaseShift C beta).toTStructure_heart_iff]
    exact ⟨(sigma.slicing.phaseShift_gtProp_zero C beta E).mpr hgt,
      (sigma.slicing.phaseShift_leProp C beta 1 E).mpr (by simpa [add_comm] using hle)⟩
  · intro hE
    have hbounds :=
      (sigma.slicing.phaseShift C beta).toTStructure_heart_iff C E |>.mp hE
    have hgt : sigma.slicing.gtProp C beta E :=
      (sigma.slicing.phaseShift_gtProp_zero C beta E).mp hbounds.1
    have hle : sigma.slicing.leProp C (beta + 1) E :=
      (sigma.slicing.phaseShift_leProp C beta 1 E).mp hbounds.2 |>
        (by simpa [add_comm] using ·)
    by_cases hzero : IsZero E
    · exact ObjectProperty.prop_of_iso (P.tilt).heart hzero.isoZero.symm
        (P.tors_mem_tilt_heart P.tors_zero)
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      HNFiltration.exists_both_nonzero C sigma.slicing hzero
    have hphase : ∀ i : Fin F.n,
        beta < F.φ i ∧ F.φ i < beta + 2 := by
      intro i
      constructor
      · calc
          beta < sigma.slicing.phiMinus C E hzero :=
            sigma.slicing.phiMinus_gt_of_gtProp C hzero hgt
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            rw [sigma.slicing.phiMinus_eq C E hzero F hn hlast]
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C E hzero := by
            rw [sigma.slicing.phiPlus_eq C E hzero F hn hfirst]
          _ ≤ beta + 1 := sigma.slicing.phiPlus_le_of_leProp C hzero hle
          _ < beta + 2 := by linarith
    obtain ⟨X, Y, f, g, d, hdist, hXgt, hYle, -⟩ :=
      sigma.slicing.exists_split_at_cutoff C F hphase hn (t := 1)
    have hXle : sigma.slicing.leProp C (beta + 1) X := by
      have hYshift : sigma.slicing.leProp C (beta + 1) (Y⟦(-1 : ℤ)⟧) := by
        have hshift := sigma.slicing.leProp_shift C 1 Y (-1) hYle
        exact sigma.slicing.leProp_mono C (by push_cast; linarith) _ hshift
      exact sigma.slicing.leProp_of_triangle C (beta + 1) hYshift hle
        (inv_rot_of_distTriang _ hdist)
    have hYgt : sigma.slicing.gtProp C beta Y := by
      have hXshift : sigma.slicing.gtProp C beta (X⟦(1 : ℤ)⟧) := by
        have hshift := sigma.slicing.gtProp_shift C 1 X 1 hXgt
        exact sigma.slicing.gtProp_anti C (by push_cast; linarith) _ hshift
      exact sigma.slicing.gtProp_of_triangle C beta hgt hXshift
        (rot_of_distTriang _ hdist)
    have hfree : phaseFree sigma.slicing beta (X⟦(-1 : ℤ)⟧) := by
      constructor
      · have hshift := sigma.slicing.gtProp_shift C 1 X (-1) hXgt
        convert hshift using 1
        all_goals push_cast
        all_goals ring
      · have hshift := sigma.slicing.leProp_shift C (beta + 1) X (-1) hXle
        convert hshift using 1
        all_goals push_cast
        all_goals ring
    have htors : phaseTors sigma.slicing beta Y := ⟨hYgt, hYle⟩
    let e : (X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ X :=
      (shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by lia)).app X
    have hdist' :
        Triangle.mk (e.hom ≫ f) g (d ≫ e.inv⟦(1 : ℤ)⟧') ∈ distTriang C := by
      refine isomorphic_distinguished _ hdist _ ?_
      exact Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp [← Functor.map_comp])
    exact P.tilt_heart_of_triangle hfree htors hdist'

/-- The phase-language tilted weak stability function.  Its heart is the HRS
tilt at the cutoff `beta`, and its charge is the original charge rotated
clockwise through `pi * beta`. -/
noncomputable def phaseTiltWeakStabilityFunction
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    WeakStabilityFunction
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt where
  Z := sigma.phaseTiltCharge beta
  upper E hE _ := by
    obtain ⟨hgt, hle⟩ := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hE
    have hclosed :=
      rotatedCharge_weakUpperClosed_of_interval sigma hgt hle
    rcases lt_or_eq_of_le hclosed.1 with him | him
    · exact Or.inl him
    · exact Or.inr ⟨him.symm, hclosed.2 him.symm⟩

@[simp]
theorem phaseTiltWeakStabilityFunction_Z
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).Z =
      sigma.phaseTiltCharge beta := rfl

@[simp]
theorem phaseTiltWeakStabilityFunction_charge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E =
      sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

/-- A zero-charge object of the original slicing heart belongs to the
boundary slice `P(1)`. -/
theorem zeroCharge_mem_P_one
    (sigma : WeakPreStabilityCondition v) {E : C}
    (hEheart : sigma.slicing.toTStructure.heart E)
    (hZ : sigma.Z (v (K₀.of C E)) = 0) :
    sigma.slicing.P 1 E := by
  by_cases hzero : IsZero E
  · exact ObjectProperty.prop_of_iso (sigma.slicing.P 1) hzero.isoZero.symm
      (sigma.slicing.zero_mem 1)
  let W := sigma.weakStabilityFunctionOnHeart
  have hss : W.IsSemistable E := by
    refine ⟨hEheart, ?_⟩
    intro A B hA hB hA0 hB0 f g d hdist
    have hEzero : W.zeroCharge E := ⟨hEheart, hZ⟩
    have hAzero := W.zeroCharge_left hA hB hEzero hdist
    have hBzero := W.zeroCharge_right hA hB hEzero hdist
    rw [W.slope_of_im_nonpos (by simp [hAzero.2]),
      W.slope_of_im_nonpos (by simp [hBzero.2])]
  have hPplus := sigma.mem_P_phiPlus_of_weakStabilityFunctionOnHeart_isSemistable
    E hzero hss
  obtain ⟨m, hm, hm_strict, hmZ⟩ :=
    sigma.compat' (sigma.slicing.phiPlus C E hzero) E hPplus hzero
  have hm0c : (m : ℂ) = 0 := by
    rw [hZ, eq_comm, mul_eq_zero] at hmZ
    exact hmZ.resolve_right (Complex.exp_ne_zero _)
  have hm0 : m = 0 := by exact_mod_cast hm0c
  have hinter : ∃ n : ℤ, sigma.slicing.phiPlus C E hzero = (n : ℝ) := by
    by_contra h
    push Not at h
    have := hm_strict h
    linarith
  obtain ⟨n, hncast⟩ := hinter
  have hbounds := (sigma.slicing.toTStructure_heart_iff C E).mp hEheart
  have hpos : 0 < sigma.slicing.phiPlus C E hzero :=
    lt_of_lt_of_le (sigma.slicing.phiMinus_gt_of_gtProp C hzero hbounds.1)
      (sigma.slicing.phiMinus_le_phiPlus C E hzero)
  have hle : sigma.slicing.phiPlus C E hzero ≤ 1 :=
    sigma.slicing.phiPlus_le_of_leProp C hzero hbounds.2
  have hnpos : 0 < n := by exact_mod_cast (hncast ▸ hpos)
  have hnle : n ≤ 1 := by exact_mod_cast (hncast ▸ hle)
  have hn : n = 1 := by omega
  have hphi : sigma.slicing.phiPlus C E hzero = 1 := by simpa [hn] using hncast
  rw [← hphi]
  exact hPplus

/-- Rotation and HRS tilting do not change the zero-charge subcategory:
the zero-charge objects of the tilted heart are precisely the original-heart
objects of zero original charge. -/
theorem phaseTiltWeakStabilityFunction_zeroCharge_iff
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge E ↔
      sigma.zeroCharge E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  constructor
  · rintro ⟨hEtilt, hcharge⟩
    have hZ : sigma.Z (v (K₀.of C E)) = 0 := by
      have hmul : sigma.Z (v (K₀.of C E)) *
          Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) = 0 := by
        simpa [W] using hcharge
      exact (mul_eq_zero.mp hmul).resolve_right (Complex.exp_ne_zero _)
    by_cases hzero : IsZero E
    · exact ⟨ObjectProperty.prop_of_iso sigma.slicing.toTStructure.heart
          hzero.isoZero.symm
          (mem_heart_of_bounds sigma.slicing
            (sigma.slicing.gtProp_zero C 0) (sigma.slicing.leProp_zero C 1)),
        hZ⟩
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      HNFiltration.exists_both_nonzero C sigma.slicing hzero
    let P := F.toPostnikovTower
    let f : Fin F.n → ℂ := fun i =>
      sigma.Z (v (K₀.of C (P.factor i))) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)
    have hbounds := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hEtilt
    have hphase : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc beta (beta + 1) := by
      intro i
      constructor
      · calc
          beta < sigma.slicing.phiMinus C E hzero :=
            sigma.slicing.phiMinus_gt_of_gtProp C hzero hbounds.1
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            rw [sigma.slicing.phiMinus_eq C E hzero F hn hlast]
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C E hzero := by
            rw [sigma.slicing.phiPlus_eq C E hzero F hn hfirst]
          _ ≤ beta + 1 :=
            sigma.slicing.phiPlus_le_of_leProp C hzero hbounds.2
    have hsum : ∑ i, f i = 0 := by
      have hdecomp :
          sigma.Z (v (K₀.of C E)) *
              Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) =
            ∑ i, f i := by
        rw [K₀.of_postnikovTower_eq_sum C P, map_sum, map_sum, Finset.sum_mul]
      rw [hZ, zero_mul] at hdecomp
      exact hdecomp.symm
    have hfclosed : ∀ i, WeakUpperClosed (f i) := by
      intro i
      by_cases hi : IsZero (P.factor i)
      · simpa [f, K₀.of_isZero C hi] using weakUpperClosed_zero
      obtain ⟨m, hm, -, hmZ⟩ :=
        sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
      dsimp [f]
      rw [hmZ]
      exact rotatedRay_weakUpperClosed hm (hphase i)
    have hfactorZ : ∀ i, sigma.Z (v (K₀.of C (P.factor i))) = 0 := by
      intro i
      have hfi := weakUpperClosed_eq_zero_of_sum_eq_zero f hfclosed hsum i
      dsimp [f] at hfi
      exact (mul_eq_zero.mp hfi).resolve_right (Complex.exp_ne_zero _)
    have hphase_one_of_nonzero : ∀ i : Fin F.n, ¬IsZero (P.factor i) → F.φ i = 1 := by
      intro i hi
      obtain ⟨m, hm, hm_strict, hmZ⟩ :=
        sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
      have hm0 : m = 0 := by
        rw [hfactorZ i, eq_comm, mul_eq_zero] at hmZ
        exact_mod_cast hmZ.resolve_right (Complex.exp_ne_zero _)
      have hinter : ∃ n : ℤ, F.φ i = (n : ℝ) := by
        by_contra h
        push Not at h
        have := hm_strict h
        linarith
      obtain ⟨n, hncast⟩ := hinter
      have hnpos : 0 < n := by
        exact_mod_cast lt_of_le_of_lt hbeta0 (hncast ▸ (hphase i).1)
      have hnlt : n < 2 := by
        have hnlt_real : (n : ℝ) < 2 := by
          rw [← hncast]
          linarith [(hphase i).2]
        exact_mod_cast hnlt_real
      have : n = 1 := by omega
      simpa [this] using hncast
    have hfirst_phase : F.φ ⟨0, hn⟩ = 1 :=
      hphase_one_of_nonzero ⟨0, hn⟩ hfirst
    have hlast_phase : F.φ ⟨F.n - 1, by lia⟩ = 1 :=
      hphase_one_of_nonzero ⟨F.n - 1, by lia⟩ hlast
    have hP : sigma.slicing.P 1 E := by
      have heq : sigma.slicing.phiPlus C E hzero =
          sigma.slicing.phiMinus C E hzero := by
        rw [sigma.slicing.phiPlus_eq C E hzero F hn hfirst,
          sigma.slicing.phiMinus_eq C E hzero F hn hlast,
          hfirst_phase, hlast_phase]
      have hPplus := sigma.slicing.semistable_of_phiPlus_eq_phiMinus C hzero heq
      rw [sigma.slicing.phiPlus_eq C E hzero F hn hfirst, hfirst_phase] at hPplus
      exact hPplus
    exact ⟨mem_heart_of_bounds sigma.slicing
        (sigma.slicing.gtProp_of_semistable C 1 0 E hP (by norm_num))
        (sigma.slicing.leProp_of_semistable C 1 1 E hP le_rfl), hZ⟩
  · rintro ⟨hEheart, hZ⟩
    have hP := sigma.zeroCharge_mem_P_one hEheart hZ
    have hgt : sigma.slicing.gtProp C beta E :=
      sigma.slicing.gtProp_of_semistable C 1 beta E hP hbeta1
    have hle : sigma.slicing.leProp C (beta + 1) E :=
      sigma.slicing.leProp_of_semistable C 1 (beta + 1) E hP (by linarith)
    have hshiftHeart :
        ((sigma.slicing.phaseShift C beta).toTStructure).heart E := by
      rw [(sigma.slicing.phaseShift C beta).toTStructure_heart_iff]
      exact ⟨(sigma.slicing.phaseShift_gtProp_zero C beta E).mpr hgt,
        (sigma.slicing.phaseShift_leProp C beta 1 E).mpr (by simpa [add_comm] using hle)⟩
    exact ⟨(sigma.phaseTiltHeart_iff_phaseShiftHeart hbeta0 hbeta1 E).mpr hshiftHeart,
      by simp [hZ]⟩

/-- A ray criterion for semistability in the tilted heart.  The object has a
single nonzero-charge phase `theta`; the Hom condition excludes zero-charge
subobjects when that ray lies in the open upper half-plane. -/
theorem phaseTiltWeakStabilityFunction_isSemistable_of_ray
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    {E : C} (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    {theta m : ℝ} (htheta : theta ∈ Set.Ioc (0 : ℝ) 1) (hm : 0 < m)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E =
        (m : ℂ) *
          Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I))
    (hle : sigma.slicing.leProp C (beta + theta) E)
    (hHom : 0 <
        ((sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E).im →
      ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ E, f = 0) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  refine ⟨hEtilt, ?_⟩
  intro A B hAtilt hBtilt hA0 hB0 f g d hdist
  have hAint := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hAtilt
  have hBint := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hBtilt
  have hBshift : sigma.slicing.leProp C beta (B⟦(-1 : ℤ)⟧) := by
    have hshift := sigma.slicing.leProp_shift C (beta + 1) B (-1) hBint.2
    convert hshift using 1
    all_goals push_cast
    all_goals ring
  have hAle : sigma.slicing.leProp C (beta + theta) A :=
    sigma.slicing.leProp_of_triangle C (beta + theta)
      (sigma.slicing.leProp_mono C (by linarith [htheta.1]) _ hBshift) hle
      (inv_rot_of_distTriang _ hdist)
  have hsum : W.charge E = W.charge A + W.charge B :=
    W.charge_triangle' hdist
  by_cases htheta_one : theta = 1
  · have hEim : (W.charge E).im = 0 := by
      rw [hcharge, htheta_one, Complex.exp_ofReal_mul_I]
      simp
    have hAim_nonneg : 0 ≤ (W.charge A).im := by
      rcases W.upper A hAtilt hA0 with him | ⟨him, -⟩
      · exact him.le
      · exact him.ge
    have hBim_nonneg : 0 ≤ (W.charge B).im := by
      rcases W.upper B hBtilt hB0 with him | ⟨him, -⟩
      · exact him.le
      · exact him.ge
    have him_sum : (W.charge A).im + (W.charge B).im = 0 := by
      have := congrArg Complex.im hsum
      simpa [hEim] using this.symm
    have hAim : (W.charge A).im = 0 := by linarith
    have hBim : (W.charge B).im = 0 := by linarith
    rw [W.slope_of_im_nonpos (by rw [hAim]; exact lt_irrefl 0),
      W.slope_of_im_nonpos (by rw [hBim]; exact lt_irrefl 0)]
  · have htheta_lt : theta < 1 := lt_of_le_of_ne htheta.2 htheta_one
    have hEim : 0 < (W.charge E).im := by
      rw [hcharge, Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_im, zero_mul, mul_one, add_zero,
        zero_add]
      exact mul_pos hm (Real.sin_pos_of_pos_of_lt_pi
        (mul_pos Real.pi_pos htheta.1)
        (by nlinarith [mul_lt_mul_of_pos_left htheta_lt Real.pi_pos]))
    have hAcross : 0 ≤ cross (W.charge A) (W.charge E) := by
      have hcross := rotatedCharge_cross_ray_nonneg_of_bounds sigma hm.le htheta.2
        hAint.1 hAle
      rw [← hcharge] at hcross
      exact hcross
    have hAcharge : W.charge A ≠ 0 := by
      intro hAzero
      have hsigmaZero : sigma.zeroCharge A :=
        (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 A).mp
          ⟨hAtilt, hAzero⟩
      have hfzero : f = 0 := hHom hEim A hsigmaZero f
      let A' : P.tilt.heart.FullSubcategory := ⟨A, hAtilt⟩
      let E' : P.tilt.heart.FullSubcategory := ⟨E, hEtilt⟩
      let B' : P.tilt.heart.FullSubcategory := ⟨B, hBtilt⟩
      let f' : A' ⟶ E' := ObjectProperty.homMk f
      let g' : E' ⟶ B' := ObjectProperty.homMk g
      have hshort := TStructure.heartFullSubcategory_shortExact_of_distTriang
        (C := C) P.tilt (A := A') (B := E') (Q := B')
          (f := f') (g := g') (δ := d) hdist
      letI : Mono f' := hshort.mono_f
      have hfzero' : f' = 0 := by ext; exact hfzero
      have hAzero' : IsZero A' := IsZero.of_mono_eq_zero f' hfzero'
      exact hA0 ((P.tilt).heart.ι.map_isZero hAzero')
    have hAim : 0 < (W.charge A).im := by
      rcases W.upper A hAtilt hA0 with him | ⟨him, hre⟩
      · exact him
      · exfalso
        have hre0 : (W.charge A).re = 0 := by
          unfold cross at hAcross
          rw [him] at hAcross
          simp only [zero_mul, sub_zero] at hAcross
          nlinarith
        apply hAcharge
        exact Complex.ext hre0 him
    by_cases hBim : 0 < (W.charge B).im
    · have hcrossAB : 0 ≤ cross (W.charge A) (W.charge B) := by
        have heq : cross (W.charge A) (W.charge B) =
            cross (W.charge A) (W.charge E) := by
          rw [hsum]
          simp [cross]
          ring
        rw [heq]
        exact hAcross
      rw [W.slope_of_im_pos hAim, W.slope_of_im_pos hBim]
      exact_mod_cast (div_le_div_iff₀ hAim hBim).2 (by
        unfold cross at hcrossAB
        nlinarith)
    · rw [W.slope_of_im_nonpos hBim]
      exact le_top

/-! ## The two classes in Lemma 14.17 -/

/-- The first class in the phase-language form of Lemma 14.17: an original
heart semistable object with no maps from original zero-charge objects. -/
def IsPhaseTiltTypeOne
    (sigma : WeakPreStabilityCondition v) (E : C) : Prop :=
  sigma.weakStabilityFunctionOnHeart.IsSemistable E ∧
    ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ E, f = 0

/-- The second class in the phase-language form of Lemma 14.17: an extension
of a zero-charge object by the shift of a semistable torsion-free object.
The final implication is the positive-imaginary part of the lemma's
`moreover` clause; it is exactly what excludes zero-charge subobjects away
from the boundary ray. -/
def IsPhaseTiltTypeTwo
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) : Prop :=
  ∃ (U V : C), phaseFree sigma.slicing beta U ∧
    sigma.weakStabilityFunctionOnHeart.IsSemistable U ∧
    sigma.zeroCharge V ∧
    ∃ (f : U⟦(1 : ℤ)⟧ ⟶ E) (g : E ⟶ V)
      (d : V ⟶ U⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
      Triangle.mk f g d ∈ distTriang C ∧
        (0 <
            ((sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E).im →
          ∀ V0 : C, sigma.zeroCharge V0 → ∀ a : V0 ⟶ E, a = 0)

/-- Objects of the first class are semistable for the phase-tilted weak
stability function. -/
theorem isSemistable_of_isPhaseTiltTypeOne
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeOne E) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  have hEnz : ¬IsZero E := fun hzero =>
    hcharge ((W.charge_isZero hzero))
  have hheart := hE.1.1
  have hP :=
    (sigma.weakStabilityFunctionOnHeart_isSemistable_iff E hheart hEnz).mp hE.1
  let phi := sigma.slicing.phiPlus C E hEnz
  have hphi_eq := sigma.slicing.phiPlus_eq_phiMinus_of_semistable C hP hEnz
  have hinterval := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hEtilt
  have hphi_beta : beta < phi := by
    dsimp [phi]
    rw [← hphi_eq.2]
    exact sigma.slicing.phiMinus_gt_of_gtProp C hEnz hinterval.1
  have hphi_one : phi ≤ 1 := by
    exact sigma.slicing.phiPlus_le_of_leProp C hEnz
      ((sigma.slicing.toTStructure_heart_iff C E).mp hheart).2
  obtain ⟨m, hm, -, hmZ⟩ := sigma.compat' phi E hP hEnz
  have hZne : sigma.Z (v (K₀.of C E)) ≠ 0 := by
    intro hZ
    apply hcharge
    simp [hZ]
  have hmpos : 0 < m := by
    apply lt_of_le_of_ne hm
    intro hm0
    apply hZne
    rw [hmZ]
    simp [hm0]
  let theta := phi - beta
  have htheta : theta ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · dsimp [theta]; linarith
    · dsimp [theta]; linarith
  have hrot : W.charge E =
      (m : ℂ) *
        Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I) := by
    rw [show W.charge E = sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) from rfl, hmZ,
      mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [theta]
    push_cast
    ring
  have hle : sigma.slicing.leProp C (beta + theta) E := by
    have : sigma.slicing.leProp C phi E :=
      sigma.slicing.leProp_of_semistable C phi phi E hP le_rfl
    convert this using 1
    all_goals dsimp [theta]
    all_goals ring
  exact sigma.phaseTiltWeakStabilityFunction_isSemistable_of_ray beta hbeta0 hbeta1
    hEtilt htheta hmpos hrot hle (fun _ => hE.2)

/-- Objects of the second class are semistable for the phase-tilted weak
stability function. -/
theorem isSemistable_of_isPhaseTiltTypeTwo
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeTwo beta hbeta0 hbeta1 E) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  obtain ⟨U, V, hUfree, hUss, hVzero, f, g, d, hdist, hHom⟩ := hE
  have hVtiltZero : W.zeroCharge V :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 V).mpr
      hVzero
  have hsum : W.charge E = W.charge (U⟦(1 : ℤ)⟧) + W.charge V :=
    W.charge_triangle' hdist
  have hUshiftCharge : W.charge (U⟦(1 : ℤ)⟧) = W.charge E := by
    rw [hsum, hVtiltZero.2, add_zero]
  have hUne : ¬IsZero U := by
    intro hzero
    apply hcharge
    rw [← hUshiftCharge]
    exact W.charge_isZero ((shiftFunctor C (1 : ℤ)).map_isZero hzero)
  have hUheart := hUss.1
  have hUP :=
    (sigma.weakStabilityFunctionOnHeart_isSemistable_iff U hUheart hUne).mp hUss
  let phi := sigma.slicing.phiPlus C U hUne
  have hphi_eq := sigma.slicing.phiPlus_eq_phiMinus_of_semistable C hUP hUne
  have hphi_pos : 0 < phi := by
    dsimp [phi]
    rw [← hphi_eq.2]
    exact sigma.slicing.phiMinus_gt_of_gtProp C hUne hUfree.1
  have hphi_beta : phi ≤ beta := by
    exact sigma.slicing.phiPlus_le_of_leProp C hUne hUfree.2
  obtain ⟨m, hm, -, hmZ⟩ := sigma.compat' phi U hUP hUne
  have hZU_ne : sigma.Z (v (K₀.of C U)) ≠ 0 := by
    intro hZU
    apply hcharge
    rw [← hUshiftCharge]
    simp [W, WeakStabilityFunction.charge, K₀.of_shift_one, hZU]
  have hmpos : 0 < m := by
    apply lt_of_le_of_ne hm
    intro hm0
    apply hZU_ne
    rw [hmZ]
    simp [hm0]
  let theta := phi + 1 - beta
  have htheta : theta ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · dsimp [theta]; linarith
    · dsimp [theta]; linarith
  have hrot : W.charge E =
      (m : ℂ) *
        Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I) := by
    rw [← hUshiftCharge]
    change sigma.Z (v (K₀.of C (U⟦(1 : ℤ)⟧))) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) = _
    rw [K₀.of_shift_one, map_neg, map_neg, hmZ]
    rw [show -((m : ℂ) * Complex.exp (((Real.pi * phi : ℝ) : ℂ) * Complex.I)) =
        (m : ℂ) *
          Complex.exp (((Real.pi * (phi + 1) : ℝ) : ℂ) * Complex.I) by
      rw [show Real.pi * (phi + 1) = Real.pi * phi + Real.pi by ring,
        ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      ring]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [theta]
    push_cast
    ring
  have hUshiftLe : sigma.slicing.leProp C (phi + 1) (U⟦(1 : ℤ)⟧) := by
    simpa only [Int.cast_one] using
      sigma.slicing.leProp_shift C phi U 1
        (sigma.slicing.leProp_of_semistable C phi phi U hUP le_rfl)
  have hVP := sigma.zeroCharge_mem_P_one hVzero.1 hVzero.2
  have hVle : sigma.slicing.leProp C (phi + 1) V :=
    sigma.slicing.leProp_of_semistable C 1 (phi + 1) V hVP (by linarith)
  have hle : sigma.slicing.leProp C (beta + theta) E := by
    have := sigma.slicing.leProp_of_triangle C (phi + 1) hUshiftLe hVle hdist
    convert this using 1
    all_goals dsimp [theta]
    all_goals ring
  exact sigma.phaseTiltWeakStabilityFunction_isSemistable_of_ray beta hbeta0 hbeta1
    hEtilt htheta hmpos hrot hle hHom

/-- The constructive direction of the phase-language classification: either
class described in Lemma 14.17 gives a semistable object in the tilted
heart. -/
theorem isSemistable_of_phaseTiltClassification
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeOne E ∨
      sigma.IsPhaseTiltTypeTwo beta hbeta0 hbeta1 E) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  rcases hE with hE | hE
  · exact sigma.isSemistable_of_isPhaseTiltTypeOne beta hbeta0 hbeta1
      hEtilt hcharge hE
  · exact sigma.isSemistable_of_isPhaseTiltTypeTwo beta hbeta0 hbeta1
      hEtilt hcharge hE

end WeakPreStabilityCondition

end BridgelandStabLean.WeakStability
