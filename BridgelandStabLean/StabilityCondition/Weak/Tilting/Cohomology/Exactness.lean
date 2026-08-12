/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Homological
import BridgelandStabLean.TStructure.Exactness

/-!
# Exact sequences from heart cohomology

`originalHeartCohFunctor t n` is homological in every degree
(`originalHeartCohFunctor_isHomological`), so a distinguished triangle in `C`
maps to an exact short complex in the heart of `t` at every `n`.

## Main results

* `originalHeartCoh_exact_of_distTriang`: the degree-`n` short complex of a
  distinguished triangle is exact in the heart.
* `originalHeartCoh_isZero_of_isZero`: degree-`n` cohomology kills zero objects.
* `originalHeartCoh_map_isTExact`: a t-exact functor commutes with membership of
  the heart, so cohomology transports along it at the level of objects.

The associated connecting maps and five-term exact fragments are supplied in
`Cohomology.Sequence` via the shift-sequence API.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace BridgelandStabLean.Tilting

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (t : TStructure C)

-- `ShortComplex.Exact` in the heart needs the heart's abelian structure at statement
-- time, and `heartFullSubcategoryAbelian` is a `def`, not an instance. Scope it locally
-- rather than making it global: a global `Abelian` instance on every t-structure heart
-- is exactly the kind of thing that creates diamonds later.
attribute [local instance]
  BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian

/-- A distinguished triangle maps to an exact short complex under degree-`n`
heart cohomology. -/
theorem originalHeartCoh_exact_of_distTriang
    (n : ℤ) (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map (originalHeartCohFunctor t n)).Exact :=
  Functor.map_distinguished_exact (originalHeartCohFunctor t n) T hT

/-- Degree-`n` heart cohomology sends zero objects to zero objects. -/
theorem originalHeartCoh_isZero_of_isZero (n : ℤ) {X : C} (hX : IsZero X) :
    IsZero ((originalHeartCohFunctor t n).obj X) := by
  have : IsZero (((originalHeartCohFunctor t n).obj X).obj) := by
    simpa using (t.truncGELE n n ⋙ shiftFunctor C n).map_isZero hX
  exact BridgelandStabLean.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero this

section TExact

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F : C ⥤ D} {t' : TStructure D}

/-- A t-exact functor carries heart objects to heart objects, so it is defined on
the targets of `originalHeartCohFunctor`.

This is the object-level statement. The natural transformation
`F ∘ H⁰_t ⟶ H⁰_{t'} ∘ F` needs the truncation–shift API described in the module
docstring and is deliberately not asserted here. -/
theorem originalHeartCoh_map_isTExact [Functor.IsTExact F t t']
    (n : ℤ) (X : C) :
    t'.heart (F.obj ((originalHeartCohFunctor t n).obj X).obj) :=
  Functor.heart_map_of_isTExact _ ((originalHeartCohFunctor t n).obj X).property

end TExact

end BridgelandStabLean.Tilting
