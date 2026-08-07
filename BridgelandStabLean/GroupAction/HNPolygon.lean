/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStability.HeartEquivalence.Reverse
import Mathlib.Analysis.Convex.Hull

/-!
# Harder--Narasimhan polygon paths

This file supplies the algebraic path underlying the HN polygon of an object in
an abelian category with a stability function.  Its vertices are the charges of
the subobjects in an abelian HN filtration.  Consecutive edge vectors are
proved to be the charges of the semistable factors, so the polygonal path
length is exactly the usual sum of factor masses.

No convex-hull containment or extremality statement is built into the
definitions.  Those are separate mathematical theorems and must not be hidden
inside the path representation.
-/

open CategoryTheory CategoryTheory.Limits Complex
open scoped BigOperators

namespace CategoryTheory

noncomputable section

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The HN polygon of an object: the convex hull of the charges of all its
subobjects.  This is the paper's ambient polygon; a chosen HN filtration below
provides its distinguished decreasing-phase boundary path. -/
def StabilityFunction.hnPolygon (Z : StabilityFunction A) (E : A) : Set ℂ :=
  convexHull ℝ (Set.range fun S : Subobject E ↦ Z.Zobj (S : A))

/-- Every subobject charge is a point of the HN polygon. -/
theorem StabilityFunction.subobjectCharge_mem_hnPolygon
    (Z : StabilityFunction A) (E : A) (S : Subobject E) :
    Z.Zobj (S : A) ∈ Z.hnPolygon E :=
  subset_convexHull ℝ (Set.range fun T : Subobject E ↦ Z.Zobj (T : A))
    (Set.mem_range_self S)

namespace ComplexPolygonalPath

/-- The Euclidean length of a finite path in the complex plane.  A path with
`n` edges is represented by its `n + 1` vertices. -/
def length {n : ℕ} (z : Fin (n + 1) → ℂ) : ℝ :=
  ∑ i : Fin n, ‖z i.succ - z i.castSucc‖

/-- The straight chord between the endpoints of a finite complex path is no
longer than the path.  This is the metric primitive used when an HN polygonal
boundary is refined by inserting further vertices. -/
theorem norm_last_sub_zero_le_length {n : ℕ} (z : Fin (n + 1) → ℂ) :
    ‖z (Fin.last n) - z 0‖ ≤ length z := by
  induction n with
  | zero => simp [length]
  | succ n ih =>
      let z' : Fin (n + 1) → ℂ := fun i ↦ z i.castSucc
      have htriangle :
          ‖z (Fin.last (n + 1)) - z 0‖ ≤
            ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ +
              ‖z (Fin.last n).castSucc - z 0‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le
          (z (Fin.last (n + 1)) - z (Fin.last n).castSucc)
          (z (Fin.last n).castSucc - z 0)
      calc
        ‖z (Fin.last (n + 1)) - z 0‖
            ≤ ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ +
                ‖z (Fin.last n).castSucc - z 0‖ := htriangle
        _ ≤ ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ + length z' :=
          by
            simpa [z'] using add_le_add_left (ih z')
              ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖
        _ = length z := by
          unfold length
          rw [Fin.sum_univ_castSucc]
          simp [z', add_comm]

end ComplexPolygonalPath

namespace AbelianHNFiltration

variable {Z : StabilityFunction A} {E : A} (F : AbelianHNFiltration Z E)

/-- The object represented by the `i`-th successive quotient in an abelian HN
filtration. -/
abbrev factorObj (i : Fin F.n) : A :=
  cokernel (Subobject.ofLE (F.chain i.castSucc) (F.chain i.succ)
    (le_of_lt (F.chain_strictMono i.castSucc_lt_succ)))

/-- The charge vertices of the HN polygonal path. -/
def polygonVertex (j : Fin (F.n + 1)) : ℂ := Z.Zobj (F.chain j : A)

/-- The length of the distinguished, decreasing-phase boundary path of the HN
polygon. -/
def polygonLength : ℝ :=
  ComplexPolygonalPath.length F.polygonVertex

/-- The abelian HN mass: the sum of the norms of the factor charges. -/
def mass : ℝ := ∑ i : Fin F.n, ‖Z.Zobj (F.factorObj i)‖

/-- A consecutive HN polygon edge is the charge of the corresponding
semistable factor. -/
theorem polygonVertex_succ_sub (i : Fin F.n) :
    F.polygonVertex i.succ - F.polygonVertex i.castSucc =
      Z.Zobj (F.factorObj i) := by
  let f : (F.chain i.castSucc : A) ⟶ (F.chain i.succ : A) :=
    Subobject.ofLE (F.chain i.castSucc) (F.chain i.succ)
      (le_of_lt (F.chain_strictMono i.castSucc_lt_succ))
  haveI : Mono f := by dsimp [f]; infer_instance
  let S : ShortComplex A := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := StabilityFunction.shortExact_of_mono f
  have hadd := Z.additive S hS
  change Z.Zobj (F.chain i.succ : A) - Z.Zobj (F.chain i.castSucc : A) =
    Z.Zobj (cokernel f)
  change Z.Zobj (F.chain i.succ : A) =
    Z.Zobj (F.chain i.castSucc : A) + Z.Zobj (cokernel f) at hadd
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hadd)

/-- The length of the HN polygonal boundary is exactly its factor mass. -/
theorem polygonLength_eq_mass : F.polygonLength = F.mass := by
  unfold polygonLength ComplexPolygonalPath.length mass
  apply Finset.sum_congr rfl
  intro i _
  rw [F.polygonVertex_succ_sub i]

/-- The initial HN polygon vertex is the origin. -/
@[simp]
theorem polygonVertex_zero : F.polygonVertex 0 = 0 := by
  unfold polygonVertex
  have hbot : F.chain 0 = ⊥ := by
    simpa using F.chain_bot
  rw [hbot]
  exact Z.map_zero' _ ((StabilityFunction.subobject_isZero_iff_eq_bot _).2 rfl)

/-- The terminal HN polygon vertex is the charge of the filtered object. -/
@[simp]
theorem polygonVertex_last :
    F.polygonVertex ⟨F.n, Nat.lt_succ_self F.n⟩ = Z.Zobj E := by
  unfold polygonVertex
  rw [F.chain_top]
  exact Z.Zobj_eq_of_iso (asIso (⊤ : Subobject E).arrow)

/-- Every vertex of the distinguished HN path lies in the ambient HN
polygon. -/
theorem polygonVertex_mem_hnPolygon (j : Fin (F.n + 1)) :
    F.polygonVertex j ∈ Z.hnPolygon E :=
  Z.subobjectCharge_mem_hnPolygon E (F.chain j)

/-- The norm of the total charge is bounded by the HN polygon length. -/
theorem norm_charge_le_polygonLength : ‖Z.Zobj E‖ ≤ F.polygonLength := by
  have h := ComplexPolygonalPath.norm_last_sub_zero_le_length F.polygonVertex
  change ‖F.polygonVertex (Fin.last F.n) - F.polygonVertex 0‖ ≤
    F.polygonLength at h
  have hlast : F.polygonVertex (Fin.last F.n) = Z.Zobj E := by
    simp [Fin.last]
  have hzero : F.polygonVertex 0 = 0 := by
    exact F.polygonVertex_zero
  simpa [hlast, hzero] using h

/-- The norm of the total charge is bounded by the sum of the HN factor
masses. -/
theorem norm_charge_le_mass : ‖Z.Zobj E‖ ≤ F.mass := by
  rw [← F.polygonLength_eq_mass]
  exact F.norm_charge_le_polygonLength

end AbelianHNFiltration

end

end CategoryTheory
