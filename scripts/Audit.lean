/-
Axiom + sorry audit over every declaration this project introduces.

Run: `lake env lean scripts/Audit.lean`

Not part of the library build (no `lean_lib` covers `scripts/`); it is a
manual gate whose output backs the `fidelity` block of `formalization.yaml`.
Re-run it before editing that block, and paste what it actually prints.

Reading the output: a declaration is clean iff its axiom list is a subset of
[propext, Classical.choice, Quot.sound]. Any other name -- above all
`sorryAx` -- is a failure, not a note.

Adding a declaration to the library means adding it here. This file is not
derived from the source tree, so it can silently fall behind; `#print axioms`
on a name that no longer exists is a hard error, but a name never added is
invisible.
-/
import BridgelandStabLean

open BridgelandStabLean

/-! ## Lattice lane -/

#print axioms Lattice.eq_zero_of_zsmul_eq_zero
#print axioms Lattice.eq_zero_of_two_zsmul_eq_zero
#print axioms Lattice.zsmul_injective
#print axioms Lattice.zsmul_left_cancel
#print axioms Lattice.finrank_numLattice
#print axioms Lattice.ne_zero_of_apply_ne_zero
#print axioms Lattice.eq_zero_of_two_zsmul_eq_zero_num

/-! ## GroupAction lane — NormalizedShift (step 1) -/

#print axioms GroupAction.NormalizedShift
#print axioms GroupAction.NormalizedShift.toOrderIso_injective
#print axioms GroupAction.NormalizedShift.ext'
#print axioms GroupAction.NormalizedShift.symm_map_add_one
#print axioms GroupAction.NormalizedShift.group
#print axioms GroupAction.NormalizedShift.mul_apply
#print axioms GroupAction.NormalizedShift.one_apply
#print axioms GroupAction.NormalizedShift.inv_apply

/-! ## GroupAction lane — GLTilde (step 2) -/

#print axioms GroupAction.rayVec
#print axioms GroupAction.rayVec_add_one
#print axioms GroupAction.rayVec_ne_zero
#print axioms GroupAction.OnRay
#print axioms GroupAction.OnRay.refl
#print axioms GroupAction.OnRay.trans
#print axioms GroupAction.toMat
#print axioms GroupAction.toMat_mul
#print axioms GroupAction.toMat_one
#print axioms GroupAction.Compatible
#print axioms GroupAction.compat_one
#print axioms GroupAction.compat_mul
#print axioms GroupAction.compat_inv
#print axioms GroupAction.GLTilde
#print axioms GroupAction.GLTilde.ext'
#print axioms GroupAction.GLTilde.group
#print axioms GroupAction.GLTilde.mul_mat
#print axioms GroupAction.GLTilde.mul_shift
#print axioms GroupAction.GLTilde.one_mat
#print axioms GroupAction.GLTilde.one_shift
#print axioms GroupAction.GLTilde.inv_mat
#print axioms GroupAction.GLTilde.inv_shift
#print axioms GroupAction.GLTilde.toMatHom
#print axioms GroupAction.GLTilde.toShiftHom

/-! ## GroupAction lane — ComplexBridge (step 3 groundwork) -/

#print axioms GroupAction.cplxCoord
#print axioms GroupAction.cplxCoord_exp
#print axioms GroupAction.compat_exp

/-! ## Group-law spot checks

`#print axioms` audits the proof term; these check the instance actually
computes the intended composition rather than some other group structure that
happens to typecheck. Both are `rfl`, so a wrong `mul` would fail here.
-/

section SpotChecks

open GroupAction

example (f g : NormalizedShift) (φ : ℝ) :
    (f * g).toOrderIso φ = f.toOrderIso (g.toOrderIso φ) := rfl

example (φ : ℝ) : (1 : NormalizedShift).toOrderIso φ = φ := rfl

example (f : NormalizedShift) (φ : ℝ) :
    (f⁻¹ * f).toOrderIso φ = φ := by simp

/-- `GLTilde` multiplication must compose the shift factors in the SAME order
as `NormalizedShift` does. An order flip here would typecheck and be wrong. -/
example (x y : GLTilde) (φ : ℝ) :
    (x * y).shift.toOrderIso φ = x.shift.toOrderIso (y.shift.toOrderIso φ) :=
  rfl

/-- The projections agree with the field accessors. -/
example (x : GLTilde) : GLTilde.toMatHom x = x.mat := rfl
example (x : GLTilde) : GLTilde.toShiftHom x = x.shift := rfl

/-- The identity really is a compatible pair, so `GLTilde` is inhabited and
the group is not vacuous. -/
example : (1 : GLTilde).mat = 1 ∧ (1 : GLTilde).shift = 1 := ⟨rfl, rfl⟩

/-- Phase `+1` is the antipodal ray — the shift functor `[1]`. -/
example (φ : ℝ) : rayVec (φ + 1) = -rayVec φ := rayVec_add_one φ

end SpotChecks
