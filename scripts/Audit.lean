/-
Axiom + sorry audit over every declaration this project introduces.

Run: `lake env lean scripts/Audit.lean`

Not part of the library build (no `lean_lib` covers `scripts/`); it is a
manual gate whose output backs the `fidelity` block of `formalization.yaml`.
Re-run it before editing that block, and paste what it actually prints.
-/
import BridgelandStabLean

open BridgelandStabLean

-- Lattice lane
#print axioms Lattice.eq_zero_of_zsmul_eq_zero
#print axioms Lattice.eq_zero_of_two_zsmul_eq_zero
#print axioms Lattice.zsmul_injective
#print axioms Lattice.zsmul_left_cancel
#print axioms Lattice.finrank_numLattice
#print axioms Lattice.ne_zero_of_apply_ne_zero
#print axioms Lattice.eq_zero_of_two_zsmul_eq_zero_num

-- GroupAction lane
#print axioms GroupAction.NormalizedShift.symm_map_add_one
#print axioms GroupAction.NormalizedShift.id
#print axioms GroupAction.NormalizedShift.comp
#print axioms GroupAction.NormalizedShift.symm
