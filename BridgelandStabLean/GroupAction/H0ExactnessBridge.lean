/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Tilting.HeartCohomologyHomological
import BridgelandStability.HeartEquivalence.EulerLift
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The exact H⁰ bridge for heart-source triangles

The anchor constructs degree-zero heart cohomology from a bundled
`HeartStabilityData`, while the Tilting lane constructs the same functor from
an arbitrary t-structure and proves it homological.  The underlying functors
are definitionally equal: both lift

`t.truncGELE 0 0 ⋙ shiftFunctor C 0`

to the full heart subcategory.  This file records that identification and
transports the generic homologicality theorem to the anchor-facing API
intended for the current-main mass-triangle rewrite of stale PR #103.

For a distinguished triangle `A ⟶ X₂ ⟶ X₃ ⟶ A[1]` with `A` in the heart,
the induced degree-zero short complex is exact at its middle object.  This is
`ShortComplex.Exact`, not `ShortExact`: the first map need not be monic because
the preceding `H⁻¹(X₃)` term may be nonzero.  Equivalently, the canonical map

`coker(A ⟶ H⁰(X₂)) ⟶ H⁰(X₃)`

is monic.

The declarations below return homologicality values and install no new global
instance.  The generic instance remains in
`Tilting/HeartCohomologyHomological.lean`; this module is only a narrow adapter
to the anchor's `HeartStabilityData.H0Functor` and `H0primeFunctor` names.  It
proves no mass inequality and makes no source-faithfulness claim.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

open BridgelandStabLean.Tilting

/-- The anchor's degree-zero cohomology functor is definitionally the generic
t-structure-only cohomology functor from the Tilting lane.  The explicit
identity isomorphism pins that fact without installing another instance. -/
noncomputable def HeartStabilityData.H0FunctorIsoOriginalHeartCohFunctor
    (h : HeartStabilityData C) :
    h.H0Functor (C := C) ≅ originalHeartCohFunctor h.t 0 :=
  Iso.refl _

/-- Unconditional homologicality of the anchor-facing `H0Functor`, obtained by
transporting the generic t-structure theorem across the definitional
identification above.  “Unconditional” means that no prior homologicality
instance is an input; the theorem returns a value and installs no new global
instance. -/
theorem HeartStabilityData.H0Functor_isHomological_unconditional
    (h : HeartStabilityData C) :
    Functor.IsHomological (h.H0Functor (C := C)) := by
  letI : Functor.IsHomological (originalHeartCohFunctor h.t 0) :=
    originalHeartCohFunctor_isHomological h.t
  exact Functor.IsHomological.of_iso
    (h.H0FunctorIsoOriginalHeartCohFunctor (C := C)).symm

/-- The proof-friendly `H0primeFunctor` is homological as well, by the anchor's
canonical natural isomorphism `H⁰ ≅ H⁰'`.  This also returns a value rather
than adding a global instance. -/
theorem HeartStabilityData.H0primeFunctor_isHomological_unconditional
    (h : HeartStabilityData C) :
    Functor.IsHomological (h.H0primeFunctor (C := C)) := by
  letI : Functor.IsHomological (h.H0Functor (C := C)) :=
    h.H0Functor_isHomological_unconditional (C := C)
  exact Functor.IsHomological.of_iso
    (h.H0FunctorIsoH0primeFunctor (C := C))

/-- The degree-zero short complex attached to a distinguished heart-source
triangle, in the anchor's proof-friendly `H⁰'` normal form. -/
noncomputable abbrev HeartStabilityData.heartSourceH0Complex
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    ShortComplex h.t.heart.FullSubcategory :=
  h.heartSourceH0primeShortComplex (C := C) A f g
    (comp_distTriang_mor_zero₁₂ _ hT)

/-- Exactness of the heart-source degree-zero complex is equivalent to
monicity of the canonical map from its cokernel into `H⁰(X₃)`. -/
theorem HeartStabilityData.heartSourceH0Complex_exact_iff_mono_cokernelDesc
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    (h.heartSourceH0Complex (C := C) A hT).Exact ↔
      Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
        (comp_distTriang_mor_zero₁₂ _ hT)) := by
  exact (h.heartSourceH0Complex (C := C) A hT).exact_iff_mono_cokernel_desc

/-- The canonical degree-zero complex of every distinguished heart-source
triangle is exact at its middle object.  This uses the homologicality value
above locally and does not assert `ShortExact`. -/
theorem HeartStabilityData.heartSourceH0Complex_exact
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    (h.heartSourceH0Complex (C := C) A hT).Exact := by
  letI : Functor.IsHomological (h.H0primeFunctor (C := C)) :=
    h.H0primeFunctor_isHomological_unconditional (C := C)
  let hmap := Functor.map_distinguished_exact
    (F := h.H0primeFunctor (C := C)) (Triangle.mk f g δ) hT
  exact (ShortComplex.exact_iff_of_iso
    (h.heartSourceH0primeShortComplexIso (C := C) A hT)).2 hmap

/-- The unconditional obstruction theorem: the canonical map from
`coker(A ⟶ H⁰(X₂))` to `H⁰(X₃)` is monic for every distinguished
heart-source triangle. -/
theorem HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) :=
  (h.heartSourceH0Complex_exact_iff_mono_cokernelDesc (C := C) A hT).mp
    (h.heartSourceH0Complex_exact (C := C) A hT)

end

end CategoryTheory.Triangulated
