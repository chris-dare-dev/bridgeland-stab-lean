/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Tilting.HeartCohomologyHomological

/-!
# Six-term original-heart cohomology sequences

This file packages the exact sequence needed when a distinguished triangle is
also a short exact sequence in an HRS-tilted heart.  For a t-structure `t`, the
six terms are

`H⁻¹_t(X₁) ⟶ H⁻¹_t(X₂) ⟶ H⁻¹_t(X₃) ⟶
  H⁰_t(X₁) ⟶ H⁰_t(X₂) ⟶ H⁰_t(X₃)`.

The construction and exactness proof are unconditional.  The
`originalHeartCohFunctor_isHomological` instance proves that degree-zero
cohomology of any t-structure sends distinguished triangles to exact short
complexes, without stability-function or Harder--Narasimhan hypotheses.

For objects of an HRS-tilted heart, the amplitude bounds supplied by
`HeartCohomology.lean` also show that the first arrow is monic and the last is
epic, giving the expected zeroes at the two ends.
-/

namespace BridgelandStabLean.Tilting

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

attribute [local instance] TStructure.heartFullSubcategoryAbelian

/-! ## Degree comparison -/

/-- The tautological shift sequence on degree-zero original-heart
cohomology. -/
noncomputable instance originalHeartCohFunctor_zero_shiftSequence
    (t : TStructure C) :
    (originalHeartCohFunctor t 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

/-- The shifted degree-zero functor agrees objectwise with the explicit
degree-`n` original-heart cohomology functor. -/
noncomputable def originalHeartCohShiftIso
    (t : TStructure C) (n : ℤ) (X : C) :
    ((originalHeartCohFunctor t 0).shift n).obj X ≅ originalHeartCoh t n X := by
  let e₂ :
      (originalHeartCohFunctor t 0).obj (X⟦(n : ℤ)⟧) ≅
        originalHeartCoh t n X := by
    refine ObjectProperty.isoMk _ ?_
    simpa [originalHeartCohFunctor] using
      (((shiftFunctorZero C ℤ).app
        ((t.truncGELE 0 0).obj (X⟦(n : ℤ)⟧))) ≪≫
          (TStructure.truncGELEObjShiftIso (C := C) t n X).symm)
  exact ((Functor.isoShift (originalHeartCohFunctor t 0) n).app X).symm ≪≫ e₂

/-- Cohomology below a known lower bound vanishes. -/
theorem originalHeartCoh_isZero_of_isGE
    (t : TStructure C) {X : C} {n lower : ℤ}
    (hX : t.IsGE X lower) (hn : n + 1 ≤ lower) :
    IsZero (originalHeartCoh t n X) := by
  letI : t.IsGE X lower := hX
  letI : t.IsGE X (n + 1) := t.isGE_of_ge X (n + 1) lower hn
  have hLE : IsZero ((t.truncLE n).obj X) :=
    t.isZero_truncLE_obj_of_isGE n (n + 1) rfl X
  have hGE : IsZero ((t.truncGE n).obj ((t.truncLE n).obj X)) :=
    (t.truncGE n).map_isZero hLE
  refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
  exact (shiftFunctor C n).map_isZero hGE

/-- Cohomology above a known upper bound vanishes. -/
theorem originalHeartCoh_isZero_of_isLE
    (t : TStructure C) {X : C} {n upper : ℤ}
    (hX : t.IsLE X upper) (hn : upper + 1 ≤ n) :
    IsZero (originalHeartCoh t n X) := by
  letI : t.IsLE X upper := hX
  have hXn : t.IsLE X n := t.isLE_of_le X upper n (by lia)
  let eLE : (t.truncLE n).obj X ≅ X :=
    @asIso _ _ _ _ ((t.truncLEι n).app X)
      ((t.isLE_iff_isIso_truncLEι_app n X).mp hXn)
  letI : t.IsLE X (n - 1) := t.isLE_of_le X upper (n - 1) (by lia)
  have hGE : IsZero ((t.truncGE n).obj X) :=
    t.isZero_truncGE_obj_of_isLE (n - 1) n (by lia) X
  have hGELE : IsZero ((t.truncGE n).obj ((t.truncLE n).obj X)) :=
    hGE.of_iso ((t.truncGE n).mapIso eLE)
  refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
  exact (shiftFunctor C n).map_isZero hGELE

/-- Shift-normal-form cohomology below a lower bound is zero. -/
theorem originalHeartCohFunctor_shift_isZero_of_isGE
    (t : TStructure C) {X : C} {n lower : ℤ}
    (hX : t.IsGE X lower) (hn : n + 1 ≤ lower) :
    IsZero ((originalHeartCohFunctor t 0).shift n |>.obj X) :=
  (originalHeartCoh_isZero_of_isGE t hX hn).of_iso
    (originalHeartCohShiftIso t n X)

/-- Shift-normal-form cohomology above an upper bound is zero. -/
theorem originalHeartCohFunctor_shift_isZero_of_isLE
    (t : TStructure C) {X : C} {n upper : ℤ}
    (hX : t.IsLE X upper) (hn : upper + 1 ≤ n) :
    IsZero ((originalHeartCohFunctor t 0).shift n |>.obj X) :=
  (originalHeartCoh_isZero_of_isLE t hX hn).of_iso
    (originalHeartCohShiftIso t n X)

/-! ## The six-term sequence -/

/-- The six-term original-heart cohomology sequence of a triangle, in the
shift-sequence normal form used by Mathlib's homological-functor API.  The six
objectwise comparison isomorphisms below identify its terms with the explicit
`originalHeartCoh t (-1)` and `originalHeartCoh t 0` objects. -/
noncomputable def originalHeartCohomologySixTermSequence
    (t : TStructure C) (T : Triangle C) :
    ComposableArrows t.heart.FullSubcategory 5 :=
  (originalHeartCohFunctor t 0).homologySequenceComposableArrows₅
    T (-1) 0 rfl

/-- The first term is explicit degree-minus-one cohomology of the first
triangle vertex. -/
noncomputable def originalHeartCohomologySixTermSequence_obj₀Iso
    (t : TStructure C) (T : Triangle C) :
    (originalHeartCohomologySixTermSequence t T).obj' 0 ≅
      originalHeartCoh t (-1) T.obj₁ :=
  originalHeartCohShiftIso t (-1) T.obj₁

/-- The second term is explicit degree-minus-one cohomology of the second
triangle vertex. -/
noncomputable def originalHeartCohomologySixTermSequence_obj₁Iso
    (t : TStructure C) (T : Triangle C) :
    (originalHeartCohomologySixTermSequence t T).obj' 1 ≅
      originalHeartCoh t (-1) T.obj₂ :=
  originalHeartCohShiftIso t (-1) T.obj₂

/-- The third term is explicit degree-minus-one cohomology of the third
triangle vertex. -/
noncomputable def originalHeartCohomologySixTermSequence_obj₂Iso
    (t : TStructure C) (T : Triangle C) :
    (originalHeartCohomologySixTermSequence t T).obj' 2 ≅
      originalHeartCoh t (-1) T.obj₃ :=
  originalHeartCohShiftIso t (-1) T.obj₃

/-- The fourth term is explicit degree-zero cohomology of the first triangle
vertex. -/
noncomputable def originalHeartCohomologySixTermSequence_obj₃Iso
    (t : TStructure C) (T : Triangle C) :
    (originalHeartCohomologySixTermSequence t T).obj' 3 ≅
      originalHeartCoh t 0 T.obj₁ :=
  originalHeartCohShiftIso t 0 T.obj₁

/-- The fifth term is explicit degree-zero cohomology of the second triangle
vertex. -/
noncomputable def originalHeartCohomologySixTermSequence_obj₄Iso
    (t : TStructure C) (T : Triangle C) :
    (originalHeartCohomologySixTermSequence t T).obj' 4 ≅
      originalHeartCoh t 0 T.obj₂ :=
  originalHeartCohShiftIso t 0 T.obj₂

/-- The sixth term is explicit degree-zero cohomology of the third triangle
vertex. -/
noncomputable def originalHeartCohomologySixTermSequence_obj₅Iso
    (t : TStructure C) (T : Triangle C) :
    (originalHeartCohomologySixTermSequence t T).obj' 5 ≅
      originalHeartCoh t 0 T.obj₃ :=
  originalHeartCohShiftIso t 0 T.obj₃

/-- The explicit six-term sequence is exact at all four interior
junctions. -/
theorem originalHeartCohomologySixTermSequence_exact
    (t : TStructure C) (T : Triangle C) (hT : T ∈ distTriang C) :
    (originalHeartCohomologySixTermSequence t T).Exact := by
  exact (originalHeartCohFunctor t 0).homologySequenceComposableArrows₅_exact
    T hT (-1) 0 rfl

/-- If the third vertex has no cohomology below degree `-1`, the first map of
the six-term sequence is monic. -/
theorem originalHeartCohomologySixTermSequence_mono_first
    (t : TStructure C) (T : Triangle C) (hT : T ∈ distTriang C)
    (hX₃ : t.IsGE T.obj₃ (-1)) :
    Mono ((originalHeartCohomologySixTermSequence t T).map' 0 1) := by
  apply ((originalHeartCohFunctor t 0).homologySequence_mono_shift_map_mor₁_iff
    T hT (-2) (-1) rfl).2
  have hZero : IsZero
      ((originalHeartCohFunctor t 0).shift (-2 : ℤ) |>.obj T.obj₃) :=
    originalHeartCohFunctor_shift_isZero_of_isGE t hX₃ (by lia)
  exact hZero.eq_of_src _ _

/-- If the first vertex has no cohomology above degree zero, the last map of
the six-term sequence is epic. -/
theorem originalHeartCohomologySixTermSequence_epi_last
    (t : TStructure C) (T : Triangle C) (hT : T ∈ distTriang C)
    (hX₁ : t.IsLE T.obj₁ 0) :
    Epi ((originalHeartCohomologySixTermSequence t T).map' 4 5) := by
  apply ((originalHeartCohFunctor t 0).homologySequence_epi_shift_map_mor₂_iff
    T hT (0 : ℤ) 1 rfl).2
  have hZero : IsZero
      ((originalHeartCohFunctor t 0).shift (1 : ℤ) |>.obj T.obj₁) :=
    originalHeartCohFunctor_shift_isZero_of_isLE t hX₁ (by lia)
  exact hZero.eq_of_tgt _ _

/-! ## Short exact sequences in the tilted heart -/

variable {t : TStructure C} (P : HeartTorsionPair t)

/-- A short exact sequence in the tilted heart extends to a distinguished
triangle in the ambient category. -/
theorem HeartTorsionPair.exists_distinguished_triangle_of_shortExact
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    ∃ δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧,
      Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  letI := hS.mono_f
  letI := hS.epi_g
  exact TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt S.f S.g S.zero (fun {W} α hα ↦ by
      have hker : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
      exact ⟨hker.lift (KernelFork.ofι α hα),
        hker.fac _ WalkingParallelPair.zero⟩)

/-- The ambient distinguished triangle canonically chosen from a tilted-heart
short exact sequence. -/
noncomputable def HeartTorsionPair.triangleOfShortExact
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    Triangle C :=
  Triangle.mk S.f.hom S.g.hom
    (P.exists_distinguished_triangle_of_shortExact S hS).choose

/-- The chosen triangle of a tilted-heart short exact sequence is
distinguished. -/
theorem HeartTorsionPair.triangleOfShortExact_distinguished
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    P.triangleOfShortExact S hS ∈ distTriang C :=
  (P.exists_distinguished_triangle_of_shortExact S hS).choose_spec

/-- The six original-heart cohomology terms attached to a short exact
sequence in the HRS-tilted heart. -/
noncomputable def HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    ComposableArrows t.heart.FullSubcategory 5 :=
  originalHeartCohomologySixTermSequence t (P.triangleOfShortExact S hS)

/-- The first term is the canonical original `H⁻¹` of the subobject. -/
noncomputable def HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₀Iso
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    (P.originalCohomologySixTermSequenceOfShortExact S hS).obj' 0 ≅
      P.originalHMinusOne S.X₁.property :=
  originalHeartCohomologySixTermSequence_obj₀Iso t
      (P.triangleOfShortExact S hS) ≪≫
    P.originalHeartCohIsoHMinusOne S.X₁.property

/-- The second term is the canonical original `H⁻¹` of the middle object. -/
noncomputable def HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₁Iso
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    (P.originalCohomologySixTermSequenceOfShortExact S hS).obj' 1 ≅
      P.originalHMinusOne S.X₂.property :=
  originalHeartCohomologySixTermSequence_obj₁Iso t
      (P.triangleOfShortExact S hS) ≪≫
    P.originalHeartCohIsoHMinusOne S.X₂.property

/-- The third term is the canonical original `H⁻¹` of the quotient. -/
noncomputable def HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₂Iso
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    (P.originalCohomologySixTermSequenceOfShortExact S hS).obj' 2 ≅
      P.originalHMinusOne S.X₃.property :=
  originalHeartCohomologySixTermSequence_obj₂Iso t
      (P.triangleOfShortExact S hS) ≪≫
    P.originalHeartCohIsoHMinusOne S.X₃.property

/-- The fourth term is the canonical original `H⁰` of the subobject. -/
noncomputable def HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₃Iso
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    (P.originalCohomologySixTermSequenceOfShortExact S hS).obj' 3 ≅
      P.originalHZero S.X₁.property :=
  originalHeartCohomologySixTermSequence_obj₃Iso t
      (P.triangleOfShortExact S hS) ≪≫
    P.originalHeartCohIsoHZero S.X₁.property

/-- The fifth term is the canonical original `H⁰` of the middle object. -/
noncomputable def HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₄Iso
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    (P.originalCohomologySixTermSequenceOfShortExact S hS).obj' 4 ≅
      P.originalHZero S.X₂.property :=
  originalHeartCohomologySixTermSequence_obj₄Iso t
      (P.triangleOfShortExact S hS) ≪≫
    P.originalHeartCohIsoHZero S.X₂.property

/-- The sixth term is the canonical original `H⁰` of the quotient. -/
noncomputable def HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₅Iso
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    (P.originalCohomologySixTermSequenceOfShortExact S hS).obj' 5 ≅
      P.originalHZero S.X₃.property :=
  originalHeartCohomologySixTermSequence_obj₅Iso t
      (P.triangleOfShortExact S hS) ≪≫
    P.originalHeartCohIsoHZero S.X₃.property

/-- A tilted-heart short exact sequence induces an exact six-term sequence
in the original heart. -/
theorem HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_exact
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    (P.originalCohomologySixTermSequenceOfShortExact S hS).Exact :=
  originalHeartCohomologySixTermSequence_exact t
    (P.triangleOfShortExact S hS)
    (P.triangleOfShortExact_distinguished S hS)

/-- The first map in the six-term sequence induced by a tilted-heart short
exact sequence is monic. -/
theorem HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_mono_first
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    Mono ((P.originalCohomologySixTermSequenceOfShortExact S hS).map' 0 1) :=
  originalHeartCohomologySixTermSequence_mono_first t
    (P.triangleOfShortExact S hS)
    (P.triangleOfShortExact_distinguished S hS)
    (P.isGE_neg_one_of_tilt_heart S.X₃.property)

/-- The last map in the six-term sequence induced by a tilted-heart short
exact sequence is epic. -/
theorem HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_epi_last
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    Epi ((P.originalCohomologySixTermSequenceOfShortExact S hS).map' 4 5) :=
  originalHeartCohomologySixTermSequence_epi_last t
    (P.triangleOfShortExact S hS)
    (P.triangleOfShortExact_distinguished S hS)
    (P.isLE_zero_of_tilt_heart S.X₁.property)

/-- Paper-shaped form: the six-term sequence is exact, begins with a mono,
and ends with an epi.  Equivalently it may be displayed with zero objects at
both ends. -/
theorem HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_exact_with_endpoints
    (S : ShortComplex (P.tilt).heart.FullSubcategory) (hS : S.ShortExact) :
    (P.originalCohomologySixTermSequenceOfShortExact S hS).Exact ∧
      Mono ((P.originalCohomologySixTermSequenceOfShortExact S hS).map' 0 1) ∧
      Epi ((P.originalCohomologySixTermSequenceOfShortExact S hS).map' 4 5) :=
  ⟨P.originalCohomologySixTermSequenceOfShortExact_exact S hS,
    P.originalCohomologySixTermSequenceOfShortExact_mono_first S hS,
    P.originalCohomologySixTermSequenceOfShortExact_epi_last S hS⟩

end BridgelandStabLean.Tilting
