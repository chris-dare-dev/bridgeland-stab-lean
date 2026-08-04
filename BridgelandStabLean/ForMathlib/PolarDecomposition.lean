/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Polar decomposition of an invertible real matrix

`A = Q * P` with `Q` orthogonal and `P` positive definite.

**Mathlib has no polar decomposition for matrices at the pinned revision**
(`8a178386`) — a search for `polarDecomposition` across the whole library
returns nothing. This file supplies the case this repo needs, in the
`ForMathlib` pattern the anchor itself uses, and is written to be upstreamable
rather than to be convenient here.

## Why it costs almost nothing now

The classical proof needs a square root of the positive-definite matrix
`Aᴴ A`, and historically that meant the spectral theorem. It no longer does:
Mathlib's **continuous functional calculus** applies to real matrices once the
Loewner order is in scope (`open scoped MatrixOrder`), so `CFC.sqrt` is
available directly and `CFC.sqrt_mul_sqrt_self` is the only property needed.

That is the whole trick. `P := √(Aᴴ A)`, `Q := A P⁻¹`, and

```
Qᴴ Q = P⁻¹ Aᴴ A P⁻¹ = P⁻¹ (P P) P⁻¹ = 1.
```

## Scope

Existence, over `ℝ`. Uniqueness of the factorisation and the `RCLike`
generalisation are both reachable — uniqueness from uniqueness of the
nonnegative square root — but are not done here, and nothing below should be
read as claiming them.
-/

open scoped MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The positive-definite factor -/

/-- The positive-definite factor of the polar decomposition, `√(Aᴴ A)`. -/
noncomputable def polarFactor (A : Matrix n n ℝ) : Matrix n n ℝ := CFC.sqrt (Aᴴ * A)

theorem polarFactor_posSemidef (A : Matrix n n ℝ) : (polarFactor A).PosSemidef :=
  nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

/-- `√(Aᴴ A)` squares to `Aᴴ A`. This is the only property of the square root
the construction uses. -/
theorem polarFactor_mul_self (A : Matrix n n ℝ) :
    polarFactor A * polarFactor A = Aᴴ * A :=
  CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg

theorem polarFactor_isHermitian (A : Matrix n n ℝ) : (polarFactor A).IsHermitian :=
  (polarFactor_posSemidef A).isHermitian

section Invertible

variable {A : Matrix n n ℝ} (hA : IsUnit A.det)
include hA

theorem det_polarFactor_ne_zero : (polarFactor A).det ≠ 0 := by
  intro h
  have hsq : (polarFactor A).det * (polarFactor A).det = (Aᴴ * A).det := by
    rw [← det_mul, polarFactor_mul_self]
  rw [h, mul_zero, det_mul, det_conjTranspose] at hsq
  exact hA.ne_zero (by simpa [star_eq_zero] using mul_eq_zero.mp hsq.symm)

theorem isUnit_det_polarFactor : IsUnit (polarFactor A).det :=
  (isUnit_iff_ne_zero).mpr (det_polarFactor_ne_zero hA)

/-- With `A` invertible the factor is positive **definite**, not merely
semidefinite. -/
theorem polarFactor_posDef : (polarFactor A).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨polarFactor_isHermitian A, fun x hx => ?_⟩
  rcases lt_or_ge 0 (star x ⬝ᵥ polarFactor A *ᵥ x) with h | h
  · exact h
  · exfalso
    -- Semidefinite already gives `≥ 0`, so the only escape is `= 0`, and for a
    -- semidefinite matrix that forces `x` into the kernel — which is empty.
    have hnn := (polarFactor_posSemidef A).dotProduct_mulVec_nonneg x
    have hzero : star x ⬝ᵥ polarFactor A *ᵥ x = 0 := le_antisymm h hnn
    have hker : polarFactor A *ᵥ x = 0 :=
      ((polarFactor_posSemidef A).dotProduct_mulVec_zero_iff x).mp hzero
    refine hx ?_
    have hinv := isUnit_det_polarFactor hA
    have hx0 := congrArg (fun v => (polarFactor A)⁻¹ *ᵥ v) hker
    simpa [mulVec_mulVec, nonsing_inv_mul _ hinv] using hx0

/-! ## The orthogonal factor -/

/-- The orthogonal factor of the polar decomposition, `A · √(Aᴴ A)⁻¹`. -/
noncomputable def polarOrthogonal (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A * (polarFactor A)⁻¹

theorem polarOrthogonal_mul_polarFactor : polarOrthogonal A * polarFactor A = A := by
  rw [polarOrthogonal, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_polarFactor hA),
    Matrix.mul_one]

theorem polarOrthogonal_mem_orthogonalGroup :
    polarOrthogonal A ∈ Matrix.unitaryGroup n ℝ := by
  have hHerm : (polarFactor A)ᴴ = polarFactor A := polarFactor_isHermitian A
  have hinv : IsUnit (polarFactor A).det := isUnit_det_polarFactor hA
  have hinvHerm : ((polarFactor A)⁻¹)ᴴ = (polarFactor A)⁻¹ := by
    rw [conjTranspose_nonsing_inv, hHerm]
  rw [mem_unitaryGroup_iff']
  show (polarOrthogonal A)ᴴ * polarOrthogonal A = 1
  rw [polarOrthogonal, conjTranspose_mul, hinvHerm]
  calc (polarFactor A)⁻¹ * Aᴴ * (A * (polarFactor A)⁻¹)
      = (polarFactor A)⁻¹ * (Aᴴ * A) * (polarFactor A)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (polarFactor A)⁻¹ * (polarFactor A * polarFactor A) * (polarFactor A)⁻¹ := by
        rw [polarFactor_mul_self]
    _ = 1 := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hinv, Matrix.one_mul,
          mul_nonsing_inv _ hinv]

/-- **Polar decomposition.** Every invertible real matrix factors as an
orthogonal matrix times a positive-definite one. -/
theorem exists_polarDecomposition :
    ∃ Q ∈ Matrix.unitaryGroup n ℝ, ∃ P : Matrix n n ℝ, P.PosDef ∧ A = Q * P :=
  ⟨polarOrthogonal A, polarOrthogonal_mem_orthogonalGroup hA, polarFactor A,
    polarFactor_posDef hA, (polarOrthogonal_mul_polarFactor hA).symm⟩

end Invertible

end Matrix
