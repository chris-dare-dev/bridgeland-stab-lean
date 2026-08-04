/-
Axiom + sorry audit over every declaration this project introduces.

Run: `lake env lean scripts/Audit.lean` (to read the output), or `lake build`
(to check it still elaborates).

Part of the library build since 2026-08-04: `[[lean_lib]] name = "Audit"` with
`srcDir = "scripts"`, in `defaultTargets`. Its output backs the `fidelity`
block of `formalization.yaml`; re-run it before editing that block, and paste
what it actually prints.

Being in the build is not the same as being a gate. `#print axioms` prints
`[sorryAx]` and exits 0, so a sorry-backed declaration builds green here. What
the build now catches is this file falling behind the source tree in one
direction only -- see below.

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

/-! ## GroupAction lane — ShiftAnalysis (step 3c groundwork) -/

#print axioms GroupAction.NormalizedShift.map_add_nat
#print axioms GroupAction.NormalizedShift.map_sub_nat
#print axioms GroupAction.NormalizedShift.map_add_int
#print axioms GroupAction.NormalizedShift.uniformContinuous
#print axioms GroupAction.NormalizedShift.exists_radius

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
#print axioms GroupAction.actC
#print axioms GroupAction.actC_apply
#print axioms GroupAction.actC_one
#print axioms GroupAction.actC_mul
#print axioms GroupAction.actC_exp

/-! ## GroupAction lane — SlicingAction (step 3a) -/

#print axioms GroupAction.relabel
#print axioms GroupAction.relabel_P
#print axioms GroupAction.slicingMulAction
#print axioms GroupAction.smul_slicing_P
#print axioms GroupAction.gltildeSlicingMulAction
#print axioms GroupAction.gltilde_smul_slicing_P
#print axioms GroupAction.relabel_intervalProp_iff
#print axioms GroupAction.relabel_intervalProp

/-! ## GroupAction lane — PreStabilityAction (step 3b) -/

#print axioms GroupAction.actPre
#print axioms GroupAction.actPre_slicing
#print axioms GroupAction.actPre_Z
#print axioms GroupAction.preMulAction
#print axioms GroupAction.smul_pre_slicing
#print axioms GroupAction.smul_pre_Z

/-! ## GroupAction lane — StabilityAction (step 3c) -/

#print axioms GroupAction.relabel_isLocallyFinite
#print axioms GroupAction.actStab
#print axioms GroupAction.actStab_slicing
#print axioms GroupAction.actStab_Z
#print axioms GroupAction.stabMulAction
#print axioms GroupAction.smul_stab_slicing
#print axioms GroupAction.smul_stab_Z

/-! ## AutAction — transport along a triangulated auto-equivalence

These extend the anchor's own namespace, since they are API for its types. -/

#print axioms CategoryTheory.Triangulated.PostnikovTower.mapF
#print axioms CategoryTheory.Triangulated.HNFiltration.mapF
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv_P

/-! ## StrictAutAction — a strict subgroup of autoequivalences -/

#print axioms GroupAction.StrictAut
#print axioms GroupAction.StrictAut.comp_inv
#print axioms GroupAction.StrictAut.inv_comp
#print axioms GroupAction.StrictAut.obj_inv
#print axioms GroupAction.StrictAut.obj_self
#print axioms GroupAction.StrictAut.F_inv_one
#print axioms GroupAction.StrictAut.F_inv_mul
#print axioms GroupAction.StrictAut.equiv
#print axioms GroupAction.StrictAut.equiv_functor
#print axioms GroupAction.StrictAut.equiv_inverse
#print axioms GroupAction.StrictAut.actSlicing
#print axioms GroupAction.StrictAut.actSlicing_P
#print axioms GroupAction.StrictAut.mulActionSlicing

/-! ## QuotAutAction — Aut(D) as an honest group, by quotienting -/

#print axioms GroupAction.TriEquiv
#print axioms GroupAction.TriEquiv.id
#print axioms GroupAction.TriEquiv.comp
#print axioms GroupAction.TriEquiv.symm
#print axioms GroupAction.TriEquiv.act
#print axioms GroupAction.TriEquiv.act_P
#print axioms GroupAction.TriEquiv.act_id
#print axioms GroupAction.TriEquiv.act_comp
#print axioms GroupAction.TriEquiv.act_congr
#print axioms GroupAction.TriEquiv.setoid
#print axioms GroupAction.AutQuot
#print axioms GroupAction.AutQuot.group
#print axioms GroupAction.AutQuot.mulActionSlicing
#print axioms GroupAction.AutQuot.mk
#print axioms GroupAction.AutQuot.mk_smul_P

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

/-! ## Step-3a convention checks

The slicing action relabels by `f⁻¹`, not `f`. With `f` the definition still
typechecks and `mul_smul` fails, so the `MulAction` laws below are the real
guard; these `example`s pin the surface convention that goes with them.
-/

section SlicingChecks

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated GroupAction

-- Declared explicitly. `lake env lean` does not apply the package's
-- `[leanOptions]`, so under a bare `lean` invocation `u` and `v` were
-- auto-bound and this section elaborated by accident. Under the repo's actual
-- settings (`autoImplicit = false`) it did not compile at all -- which is
-- exactly the rot that covering this file with a `lean_lib` is meant to catch.
universe u v

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

example (f : NormalizedShift) (s : Slicing C) (φ : ℝ) :
    (f • s).P φ = s.P (f⁻¹.toOrderIso φ) := rfl

/-- `GLTilde` acts through its shift factor only — the matrix factor is not
consulted. -/
example (x : GLTilde) (s : Slicing C) (φ : ℝ) :
    (x • s).P φ = (x.shift • s).P φ := rfl

/-! Step 3b: both factors act, each on its own component. -/

variable {Λ : Type*} [AddCommGroup Λ] (v : K₀ C →+ Λ)

example (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

example (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

/-! Step 3c: the action reaches full stability conditions. -/

section StabChecks

variable [IsTriangulated C]

example (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

example (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

end StabChecks

end SlicingChecks
