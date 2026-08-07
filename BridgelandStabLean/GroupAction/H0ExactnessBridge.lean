/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStability.HeartEquivalence.EulerLift

/-!
# The exact H⁰ obstruction for heart-source triangles

For a distinguished triangle `A ⟶ X₂ ⟶ X₃ ⟶ A[1]` with `A` in the
heart, applying `H⁰` gives a short complex in the heart.  Exactness at
`H⁰(X₂)` is not the assertion that the first map is a kernel: the incoming
map from `H⁻¹(X₃)` may be nonzero.  The correct obstruction is instead the
monicity of the canonical map

`coker(A ⟶ H⁰(X₂)) ⟶ H⁰(X₃)`.

This file records that exact equivalence and connects it to Mathlib's
`Functor.IsHomological` interface.  It is deliberately a bridge, not an
assumption or a global instance.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- The `H⁰` short complex attached to a distinguished heart-source
triangle.  This abbreviation fixes the proof of the zero composite to the
canonical distinguished-triangle proof. -/
noncomputable abbrev HeartStabilityData.heartSourceH0Complex
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    ShortComplex h.t.heart.FullSubcategory :=
  h.heartSourceH0primeShortComplex (C := C) A f g
    (comp_distTriang_mor_zero₁₂ _ hT)

/-- Exactness of the heart-source `H⁰` complex is precisely monicity of its
canonical cokernel comparison into `H⁰(X₃)`. -/
theorem HeartStabilityData.heartSourceH0Complex_exact_iff_mono_cokernelDesc
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    (h.heartSourceH0Complex (C := C) A hT).Exact ↔
      Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
        (comp_distTriang_mor_zero₁₂ _ hT)) := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  exact (h.heartSourceH0Complex (C := C) A hT).exact_iff_mono_cokernel_desc

/-- A homological `H⁰'` functor supplies the correct heart-source exact
complex.  This theorem is useful both as a regression test for a future global
instance and as the forward half of the exactness bridge. -/
theorem HeartStabilityData.heartSourceH0Complex_exact_of_isHomological
    (h : HeartStabilityData C)
    [Functor.IsHomological (h.H0primeFunctor (C := C))]
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    (h.heartSourceH0Complex (C := C) A hT).Exact := by
  let hmap := Functor.map_distinguished_exact
    (F := h.H0primeFunctor (C := C)) (Triangle.mk f g δ) hT
  exact (ShortComplex.exact_iff_of_iso
    (h.heartSourceH0primeShortComplexIso (C := C) A hT)).2 hmap

/-- The same bridge stated using the anchor's primary `H⁰` functor.  The
homological structure is transported across the canonical natural
isomorphism `H⁰ ≅ H⁰'`; no global instance is installed. -/
theorem HeartStabilityData.heartSourceH0Complex_exact_of_H0Functor_isHomological
    (h : HeartStabilityData C)
    [Functor.IsHomological (h.H0Functor (C := C))]
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    (h.heartSourceH0Complex (C := C) A hT).Exact := by
  letI : Functor.IsHomological (h.H0primeFunctor (C := C)) :=
    Functor.IsHomological.of_iso (h.H0FunctorIsoH0primeFunctor (C := C))
  exact h.heartSourceH0Complex_exact_of_isHomological (C := C) A hT

/-- Consequently a homological `H⁰'` functor makes the canonical cokernel
comparison monic. -/
theorem HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc
    (h : HeartStabilityData C)
    [Functor.IsHomological (h.H0primeFunctor (C := C))]
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) :=
  (h.heartSourceH0Complex_exact_iff_mono_cokernelDesc (C := C) A hT).mp
    (h.heartSourceH0Complex_exact_of_isHomological (C := C) A hT)

/-- With homological `H⁰`, the exact obstruction is therefore discharged: the
canonical cokernel comparison is monic. -/
theorem HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc_of_H0Functor
    (h : HeartStabilityData C)
    [Functor.IsHomological (h.H0Functor (C := C))]
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) :=
  (h.heartSourceH0Complex_exact_iff_mono_cokernelDesc (C := C) A hT).mp
    (h.heartSourceH0Complex_exact_of_H0Functor_isHomological (C := C) A hT)

end

end CategoryTheory.Triangulated
