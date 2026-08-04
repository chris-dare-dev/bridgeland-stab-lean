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

/-! ## GroupAction lane -/

#print axioms GroupAction.NormalizedShift
#print axioms GroupAction.NormalizedShift.toOrderIso_injective
#print axioms GroupAction.NormalizedShift.ext'
#print axioms GroupAction.NormalizedShift.symm_map_add_one
#print axioms GroupAction.NormalizedShift.group
#print axioms GroupAction.NormalizedShift.mul_apply
#print axioms GroupAction.NormalizedShift.one_apply
#print axioms GroupAction.NormalizedShift.inv_apply

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

end SpotChecks
