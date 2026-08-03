/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Torsion-free lattice arithmetic

Lane-2 targets: the numerical/lattice bookkeeping steps that are provable
**today**, over plain torsion-free `ℤ`-modules, with no algebraic-geometry
substrate whatsoever.

These correspond to the §8.4-8.6 arithmetic steps that arXMCP's R5 brief
identifies as closable without the missing `D^b(Coh X)` layer
(`.claude/roadmap-briefs/R5-formal-target-registry.md`, "First entries").

`NoZeroSMulDivisors ℤ Λ` is exactly torsion-freeness for an additive group:
`n • x = 0 → n = 0 ∨ x = 0`.
-/

namespace BridgelandStabLean.Lattice

variable {Λ : Type*} [AddCommGroup Λ] [NoZeroSMulDivisors ℤ Λ]

/-- In a torsion-free abelian group, a nonzero integer multiple vanishes only
on zero. -/
theorem eq_zero_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {x : Λ} (h : n • x = 0) :
    x = 0 :=
  (smul_eq_zero.mp h).resolve_left hn

/-- `2 • x = 0 → x = 0`.

This is the article's §8 step "`2[E] = 0` in a torsion-free lattice, hence
`[E] = 0`" — the smallest genuinely load-bearing target in the registry. -/
theorem eq_zero_of_two_zsmul_eq_zero {x : Λ} (h : (2 : ℤ) • x = 0) : x = 0 :=
  eq_zero_of_zsmul_eq_zero (by norm_num) h

/-- Scaling by a nonzero integer is injective on a torsion-free group. -/
theorem zsmul_injective {n : ℤ} (hn : n ≠ 0) :
    Function.Injective fun x : Λ => n • x :=
  smul_right_injective Λ hn

/-- Cancellation: `n • x = n • y → x = y` for `n ≠ 0`. -/
theorem zsmul_left_cancel {n : ℤ} (hn : n ≠ 0) {x y : Λ} (h : n • x = n • y) :
    x = y :=
  zsmul_injective hn h

end BridgelandStabLean.Lattice
