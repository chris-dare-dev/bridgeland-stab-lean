/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Numerical walls in the `(s, t)` half plane

For a surface with polarisation `H`, tilt stability is parametrised by a point
`(s, t)` with `t > 0`, and the twisted charge of a numerical class
`v = (r, c, d)` — standing for `(ch₀, ch₁·H, ch₂)` — is

```
Re Z = -d + s·c - (s²/2)·r + (t²/2)·r,      Im Z = t·(c - s·r).
```

A **numerical wall** for a pair `(v, w)` is the locus where the two charges are
real-proportional. The theorem this file is built around is that the wall
equation collapses to

```
minA·(s² + t²) + 2·minB·s + 2·minC = 0
```

where `minA, minB, minC` are the three `2 × 2` minors of the matrix with rows
`v` and `w`. So **every numerical wall is a circle centred on the `s`-axis, or
a vertical line** — the statement the "walls are nested semicircles" picture
rests on.

## What this is a theorem about, and what it is not

Everything here is arithmetic on triples of real numbers. There is **no**
surface: no coherent sheaf, no Chern character, no polarisation, no
Bogomolov–Gieseker inequality. `NumClass` is a triple, not `ch(E)`, and the
identification is geometry that Mathlib cannot express at the pin — CLAUDE.md
§4 closes that lane, and nothing here reopens it.

In particular **no discriminant hypothesis is assumed anywhere below**, because
none is needed: the wall equation is an identity. Where the geometric theory
would invoke Bogomolov–Gieseker, these statements simply carry the numerical
hypothesis they actually use (`minA ≠ 0`, `t ≠ 0`) as an explicit hypothesis of
the theorem. Nothing is axiomatised.

## Main results

* `wallExpr_eq` — the collapse. Proved as an identity, with no side conditions.
* `wall_iff_circle` — the circle/line form, for `t ≠ 0`.
* `wall_circle_eq` — centre `(-minB/minA, 0)` and radius² `(minB² - 2·minA·minC)/minA²`.
* `minA_add_smul` and friends — a wall depends only on `w` modulo `v`.
* `charge_eq_zero_iff` — where the charge degenerates.
* `eq_of_two_walls` — two walls through a common point with non-proportional
  minor vectors pin down that point uniquely.
-/

namespace BridgelandStabLean.Wall

/-- A numerical class `(r, c, d)`.

A triple of reals. It is **not** `ch(E)` for a sheaf `E`; see the module
docstring. -/
abbrev NumClass : Type := ℝ × ℝ × ℝ

namespace NumClass

/-- The rank coordinate. -/
def rk (v : NumClass) : ℝ := v.1

/-- The degree coordinate, standing for `ch₁ · H`. -/
def deg (v : NumClass) : ℝ := v.2.1

/-- The second coordinate, standing for `ch₂`. -/
def ch2 (v : NumClass) : ℝ := v.2.2

end NumClass

open NumClass

/-! ### The twisted charge -/

/-- The real part of the twisted charge at `(s, t)`. -/
noncomputable def reZ (s t : ℝ) (v : NumClass) : ℝ :=
  -v.ch2 + s * v.deg - (s ^ 2 / 2) * v.rk + (t ^ 2 / 2) * v.rk

/-- The imaginary part of the twisted charge at `(s, t)`. -/
def imZ (s t : ℝ) (v : NumClass) : ℝ := t * (v.deg - s * v.rk)

/-! ### The three minors

`minA`, `minB`, `minC` are the `2 × 2` minors of `!![v.rk, v.deg, v.ch2;
w.rk, w.deg, w.ch2]`. Each is alternating and bilinear, which is what makes a
wall depend only on `w` modulo `v`. -/

/-- The rank–degree minor. -/
def minA (v w : NumClass) : ℝ := v.rk * w.deg - v.deg * w.rk

/-- The `ch₂`–rank minor. -/
def minB (v w : NumClass) : ℝ := v.ch2 * w.rk - v.rk * w.ch2

/-- The degree–`ch₂` minor. -/
def minC (v w : NumClass) : ℝ := v.deg * w.ch2 - v.ch2 * w.deg

/-- The wall expression: the cross product of the two charges, which vanishes
exactly when they are real-proportional. -/
noncomputable def wallExpr (s t : ℝ) (v w : NumClass) : ℝ :=
  reZ s t v * imZ s t w - imZ s t v * reZ s t w

/-! ### The collapse

The whole geometry of numerical walls follows from this one identity. -/

/-- **The wall expression collapses to a circle equation.**

An identity: no hypothesis on `s`, `t`, `v` or `w`. Everything quadratic in
`s` and `t` beyond `s² + t²` cancels. -/
theorem wallExpr_eq (s t : ℝ) (v w : NumClass) :
    wallExpr s t v w
      = t * (minC v w + s * minB v w + ((s ^ 2 + t ^ 2) / 2) * minA v w) := by
  simp only [wallExpr, reZ, imZ, minA, minB, minC, rk, deg, ch2]
  ring

/-- For `t ≠ 0` the wall is cut out by a circle equation in `(s, t)`. -/
theorem wall_iff_circle {s t : ℝ} (ht : t ≠ 0) (v w : NumClass) :
    wallExpr s t v w = 0 ↔
      minA v w * (s ^ 2 + t ^ 2) + 2 * minB v w * s + 2 * minC v w = 0 := by
  rw [wallExpr_eq, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h ht
    · linarith
  · intro h
    exact Or.inr (by linarith)

/-- **Centre and radius.** When the rank–degree minor is nonzero the wall is
the circle centred at `(-minB/minA, 0)` with radius squared
`(minB² - 2·minA·minC)/minA²`.

Stated in cleared form — both sides multiplied through by `minA²` — so that no
division appears and the equivalence is an honest polynomial identity plus one
use of `minA ≠ 0`. -/
theorem wall_circle_eq {s t : ℝ} (ht : t ≠ 0) {v w : NumClass}
    (hA : minA v w ≠ 0) :
    wallExpr s t v w = 0 ↔
      (minA v w * s + minB v w) ^ 2 + (minA v w * t) ^ 2
        = minB v w ^ 2 - 2 * minA v w * minC v w := by
  rw [wall_iff_circle ht]
  constructor
  · intro h
    linear_combination (minA v w) * h
  · intro h
    have key : minA v w *
        (minA v w * (s ^ 2 + t ^ 2) + 2 * minB v w * s + 2 * minC v w) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp key).resolve_left hA

/-- A vertical wall: when the rank–degree minor vanishes but the `ch₂`–rank one
does not, the wall is the line `s = -minC/minB`. -/
theorem wall_line_eq {s t : ℝ} (ht : t ≠ 0) {v w : NumClass}
    (hA : minA v w = 0) (hB : minB v w ≠ 0) :
    wallExpr s t v w = 0 ↔ s = -(minC v w) / minB v w := by
  rw [wall_iff_circle ht, hA]
  rw [eq_div_iff hB]
  constructor <;> intro h <;> linarith

/-! ### A wall sees only `w` modulo `v`

Each minor is alternating, so adding a multiple of `v` to `w` changes nothing.
This is why walls are indexed by classes modulo `v` rather than by classes. -/

/-- Scalar shift of `w` by `v`, componentwise. -/
def shift (k : ℝ) (v w : NumClass) : NumClass :=
  (w.rk + k * v.rk, w.deg + k * v.deg, w.ch2 + k * v.ch2)

@[simp]
theorem minA_shift (k : ℝ) (v w : NumClass) : minA v (shift k v w) = minA v w := by
  simp only [minA, shift, rk, deg]; ring

@[simp]
theorem minB_shift (k : ℝ) (v w : NumClass) : minB v (shift k v w) = minB v w := by
  simp only [minB, shift, rk, ch2]; ring

@[simp]
theorem minC_shift (k : ℝ) (v w : NumClass) : minC v (shift k v w) = minC v w := by
  simp only [minC, shift, deg, ch2]; ring

/-- The wall for `w` and for `w + k·v` is the same wall. -/
theorem wallExpr_shift (s t k : ℝ) (v w : NumClass) :
    wallExpr s t v (shift k v w) = wallExpr s t v w := by
  rw [wallExpr_eq, wallExpr_eq, minA_shift, minB_shift, minC_shift]

/-! ### Degeneracy of the charge -/

/-- The charge of `v` vanishes at `(s, t)`, `t ≠ 0`, exactly when `v` is the
rank-scaled point `r · (1, s, (s² + t²)/2)`. This is the one place a wall can
fail to be a genuine circle, and it is exactly the locus the geometric theory
excludes. -/
theorem charge_eq_zero_iff {s t : ℝ} (ht : t ≠ 0) (v : NumClass) :
    (reZ s t v = 0 ∧ imZ s t v = 0) ↔
      (v.deg = s * v.rk ∧ v.ch2 = ((s ^ 2 + t ^ 2) / 2) * v.rk) := by
  simp only [reZ, imZ, rk, deg, ch2]
  constructor
  · rintro ⟨hre, him⟩
    have hd : v.2.1 - s * v.1 = 0 := (mul_eq_zero.mp him).resolve_left ht
    refine ⟨by linarith, ?_⟩
    linear_combination (-1 : ℝ) * hre + s * hd
  · rintro ⟨hd, hc⟩
    constructor
    · rw [hd, hc]; ring
    · rw [hd]; ring

/-! ### Two walls through one point

If two walls meet at `(s, t)` and their minor vectors are **not** proportional
in the `(A, B)` slot, then that meeting point is forced. This is the algebraic
half of "walls for a fixed `v` are nested".

**The full nesting theorem is not proved here.** That statement — two distinct
walls for the *same* `v` never meet — needs the extra input that both minor
vectors are cross products against a common `v`, and a rank argument in `ℝ³`.
Neither is done; see the trust record. -/

/-- Two walls meeting at a common point determine `s` and `s² + t²`, provided
the `(A, B)` cross term is nonzero. -/
theorem eq_of_two_walls {s t : ℝ} (ht : t ≠ 0) {v w₁ w₂ : NumClass}
    (h₁ : wallExpr s t v w₁ = 0) (h₂ : wallExpr s t v w₂ = 0)
    (hD : minA v w₁ * minB v w₂ - minA v w₂ * minB v w₁ ≠ 0) :
    s = -(minA v w₁ * minC v w₂ - minA v w₂ * minC v w₁)
          / (minA v w₁ * minB v w₂ - minA v w₂ * minB v w₁) := by
  rw [wall_iff_circle ht] at h₁ h₂
  rw [eq_div_iff hD]
  linear_combination (-(minA v w₂) / 2) * h₁ + (minA v w₁ / 2) * h₂

end BridgelandStabLean.Wall
