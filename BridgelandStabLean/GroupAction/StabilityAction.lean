/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license.
-/
import BridgelandStabLean.GroupAction.PreStabilityAction
import BridgelandStabLean.GroupAction.ShiftAnalysis
import BridgelandStability.Deformation.IntervalSelection

/-!
# The action on stability conditions

Lane-1 step 3c, and the last one. `G̃L⁺(2, ℝ)` acts on
`StabilityCondition.WithClassMap C v`.

Everything except local finiteness came from 3b. What remained was that
`Slicing.IsLocallyFinite` survives phase relabelling, and that is genuinely
not bookkeeping: it quantifies **one** radius `η` over **all** centres `t`,
while a normalized shift distorts windows.

Three ingredients close it:

1. `NormalizedShift.exists_radius` (`ShiftAnalysis.lean`) — uniform continuity,
   giving one radius `η'` whose every window maps to width `< 2η`.
2. `relabel_intervalProp` (`SlicingAction.lean`) — interval subcategories are
   reindexed exactly, so the relabelled window at `(t-η', t+η')` *is* the
   original at `(f⁻¹(t-η'), f⁻¹(t+η'))`.
3. `interval_thinFiniteLength_of_inclusion_strict` — the anchor's own shrinking
   lemma, in `Deformation/IntervalSelection.lean`. It is stated for two
   *different* slicings related by `intervalProp ≤ intervalProp`, which is
   exactly the shape (2) produces.

Ingredient 3 is worth flagging: an earlier pass of this project recorded it as
missing from the anchor, because the search covered `IntervalCategory/` and
`QuasiAbelian/` but not `Deformation/`. It was there all along. The anchor's
`IsLocallyFinite` docstring remark that shrinking a witness is "harmless" is
backed by that lemma.
-/

namespace BridgelandStabLean.GroupAction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable (C : Type u) [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- **Local finiteness survives phase relabelling.**

The window radius changes — `η` becomes the `η'` supplied by uniform
continuity — but a single radius still works for every centre, which is what
`IsLocallyFinite` demands. -/
theorem relabel_isLocallyFinite (f : NormalizedShift) (s : Slicing C)
    (hs : s.IsLocallyFinite C) : (relabel C f s).IsLocallyFinite C := by
  obtain ⟨η, hη, hη2, hlf⟩ := hs.intervalFinite
  obtain ⟨η', hη'0, hη'M, hwidth⟩ :=
    NormalizedShift.exists_radius f⁻¹ (w := 2 * η) (M := 1 / 2) (by linarith) (by norm_num)
  refine ⟨⟨η', hη'0, hη'M, ?_⟩⟩
  intro t
  set A := f⁻¹.toOrderIso (t - η') with hA
  set B := f⁻¹.toOrderIso (t + η') with hB
  have hAB : B - A < 2 * η := hwidth t
  set u := (A + B) / 2 with hu
  have hlt : A < B := f⁻¹.toOrderIso.lt_iff_lt.mpr (by linarith)
  have ha2 : u - η ≤ A := by simp only [hu]; linarith
  have hb2 : B ≤ u + η := by simp only [hu]; linarith
  haveI : Fact (u - η < u + η) := ⟨by linarith⟩
  haveI : Fact ((u + η) - (u - η) ≤ 1) := ⟨by linarith⟩
  haveI : Fact (t - η' < t + η') := ⟨by linarith⟩
  haveI : Fact ((t + η') - (t - η') ≤ 1) := ⟨by linarith⟩
  have hle : (relabel C f s).intervalProp C (t - η') (t + η')
      ≤ s.intervalProp C (u - η) (u + η) := by
    intro E hE
    rw [relabel_intervalProp] at hE
    exact s.intervalProp_mono C ha2 hb2 hE
  exact fun E => interval_thinFiniteLength_of_inclusion_strict (C := C)
    (s₁ := relabel C f s) (s₂ := s) hle (hlf u) E

variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- `x = (T, f)` acting on a full stability condition. Slicing and charge come
from 3b; local finiteness is `relabel_isLocallyFinite`. -/
def actStab (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    StabilityCondition.WithClassMap C v where
  toWithClassMap := actPre C v x σ.toWithClassMap
  locallyFinite := relabel_isLocallyFinite C x.shift σ.slicing σ.locallyFinite

@[simp]
theorem actStab_slicing (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    (actStab C v x σ).slicing = x • σ.slicing := rfl

@[simp]
theorem actStab_Z (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) (a : Λ) :
    (actStab C v x σ).Z a = actC x.mat (σ.Z a) := rfl

/-- **The §8 action.** `G̃L⁺(2, ℝ)` acts on stability conditions. -/
instance stabMulAction : MulAction GLTilde (StabilityCondition.WithClassMap C v) where
  smul := actStab C v
  one_smul σ := by
    refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
    · show (actStab C v 1 σ).slicing = σ.slicing
      rw [actStab_slicing]
      exact one_smul _ _
    · ext a
      show (actStab C v 1 σ).Z a = σ.Z a
      rw [actStab_Z]
      simp
  mul_smul x y σ := by
    refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
    · show (actStab C v (x * y) σ).slicing = (actStab C v x (actStab C v y σ)).slicing
      rw [actStab_slicing, actStab_slicing, actStab_slicing]
      exact mul_smul _ _ _
    · ext a
      show (actStab C v (x * y) σ).Z a = (actStab C v x (actStab C v y σ)).Z a
      rw [actStab_Z, actStab_Z, actStab_Z, GLTilde.mul_mat, actC_mul]

@[simp]
theorem smul_stab_slicing (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

@[simp]
theorem smul_stab_Z (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

end

end BridgelandStabLean.GroupAction
