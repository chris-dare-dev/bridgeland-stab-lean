/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Tactic

/-!
# Torsion pairs on a heart, and the tilted aisles

Groundwork for the Happel–Reiten–Smalø tilt. **The tilt itself is not
constructed here**; see the trust record and the TODO at the end of this file
for exactly what is missing and why.

## The one design decision worth explaining

The tilted aisles are normally written with cohomology functors:

```
D^{≤0}_† = {X ∈ D^{≤0} : H⁰(X) ∈ T},   D^{≥0}_† = {X ∈ D^{≥-1} : H^{-1}(X) ∈ F}.
```

**Mathlib has no `Hⁿ` for a t-structure at the pin** — `TStructure/` carries
`truncLE`, `truncGE` and the truncation triangle, but no cohomology functor
into the heart. The anchor has an `H0Functor`, but its *homological* property
is present only as a list of case-by-case fragments in
`HeartEquivalence/H0Homological.lean`, not as an unconditional statement.

So the aisles here are defined by **Hom-orthogonality instead**, which needs no
cohomology functor at all. For `X ∈ D^{≤0}` and `F` in the heart the counit
gives `Hom(X, F) ≅ Hom(H⁰X, F)`, and `T` is exactly the left orthogonal of `F`
in the heart, so

```
H⁰(X) ∈ T   ⟺   Hom(X, F) = 0 for every F ∈ F.
```

The right-hand side is what `tiltLE` says. It is equivalent to the usual
definition wherever the usual definition can be stated, and it is available
here, where the usual one is not.

## Status

Established here: the datum, the aisles at every integer level with their
isomorphism-closure, the factorisation lemma standing in for the counit, the
orthogonality characterisation of the torsion class, and **five of the six
non-trivial `TStructure` fields** — both shift axioms, both inclusions, and the
Hom-vanishing axiom.

**`exists_triangle_zero_one` is the one field not proved**, and it is not
declared, not even with `sorry`; see §2 of `CLAUDE.md` for why that rule exists.
So no `TStructure` instance is assembled and there is still no tilt here.
-/

namespace BridgelandStabLean.Tilting

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (t : TStructure C)

/-- A torsion pair on the heart of `t`, phrased inside `C` rather than inside
the heart as a category.

Stating it in `C` avoids the full-subcategory plumbing that carrying an
`Abelian` instance on the heart would require, and the decomposition axiom
becomes a distinguished triangle — which for objects of the heart is the same
thing as a short exact sequence there. `Tilting/TorsionPair.lean` is the
abelian-category version of the same notion; neither is derived from the other
here. -/
structure HeartTorsionPair where
  /-- the torsion class -/
  tors : ObjectProperty C
  /-- the torsion-free class -/
  free : ObjectProperty C
  tors_isLE : ∀ X, tors X → t.IsLE X 0
  tors_isGE : ∀ X, tors X → t.IsGE X 0
  free_isLE : ∀ X, free X → t.IsLE X 0
  free_isGE : ∀ X, free X → t.IsGE X 0
  tors_isClosedUnderIsomorphisms : tors.IsClosedUnderIsomorphisms := by infer_instance
  free_isClosedUnderIsomorphisms : free.IsClosedUnderIsomorphisms := by infer_instance
  /-- no nonzero map from a torsion object to a torsion-free one -/
  hom_eq_zero : ∀ ⦃X Y : C⦄, tors X → free Y → ∀ f : X ⟶ Y, f = 0
  /-- every object of the heart is an extension of a torsion-free object by a
  torsion one -/
  exists_triangle : ∀ X : C, t.IsLE X 0 → t.IsGE X 0 →
    ∃ (T F : C) (_ : tors T) (_ : free F) (f : T ⟶ X) (g : X ⟶ F) (h : F ⟶ T⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C

namespace HeartTorsionPair

attribute [instance] tors_isClosedUnderIsomorphisms free_isClosedUnderIsomorphisms

variable {t}
variable (P : HeartTorsionPair t)

/-! ### The tilted aisles

Both are stated at the level where the tilt lives; the shifted family a full
`TStructure` needs is not built here. -/

/-- The tilted co-aisle `D^{≤0}_†`: objects of `D^{≤0}` with no nonzero map to
a torsion-free object. Under the counit isomorphism this says `H⁰(X) ∈ T`. -/
def tiltLE : ObjectProperty C :=
  fun X => t.IsLE X 0 ∧ ∀ F : C, P.free F → ∀ f : X ⟶ F, f = 0

/-- The tilted aisle `D^{≥1}_†`: objects of `D^{≥0}` with no nonzero map from a
torsion object. Under the counit isomorphism this says `H⁰(X) ∈ F`. -/
def tiltGE : ObjectProperty C :=
  fun X => t.IsGE X 0 ∧ ∀ T : C, P.tors T → ∀ f : T ⟶ X, f = 0

instance tiltLE_isClosedUnderIsomorphisms : P.tiltLE.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hle, horth⟩ := hX
    refine ⟨t.isLE_of_iso e 0, fun F hF f => ?_⟩
    have := horth F hF (e.hom ≫ f)
    calc f = e.inv ≫ (e.hom ≫ f) := by simp
    _ = 0 := by rw [this, comp_zero]

instance tiltGE_isClosedUnderIsomorphisms : P.tiltGE.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hge, horth⟩ := hX
    refine ⟨t.isGE_of_iso e 0, fun T hT f => ?_⟩
    have := horth T hT (f ≫ e.inv)
    calc f = (f ≫ e.inv) ≫ e.hom := by simp
    _ = 0 := by rw [this, zero_comp]

/-! ### The factorisation lemma

Everything the Hom-vanishing axiom needs, and the substitute for the counit
isomorphism `Hom(X, F) ≅ Hom(H⁰X, F)` that a cohomology functor would supply. -/

/-- **Every map into `D^{≥0}` factors through the truncation `τ^{≥0}`.**

This is the half of the counit isomorphism the tilt actually uses. When
additionally `X ∈ D^{≤0}` the target `τ^{≥0}X` lies in the heart and plays the
role of `H⁰(X)`, so this is what lets an orthogonality hypothesis on `X` be
transported to one on `H⁰(X)`.

No hypothesis on `X` is needed: the truncation triangle exists for every
object, and `Hom(τ^{<0}X, F)` vanishes for degree reasons alone. -/
theorem exists_factor_truncGE {X F : C} (hF : t.IsGE F 0) (f : X ⟶ F) :
    ∃ g : ((t.triangleLTGE 0).obj X).obj₃ ⟶ F,
      f = ((t.triangleLTGE 0).obj X).mor₂ ≫ g := by
  refine Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished 0 X) f ?_
  exact t.zero_of_isLE_of_isGE _ (0 - 1) 0 (by lia) inferInstance hF

/-- The factorisation is unique: `τ^{≥0}X` really does corepresent maps out of
`X` into `D^{≥0}`, not merely dominate them. -/
theorem factor_truncGE_unique {X F : C} (hF : t.IsGE F 0)
    {g₁ g₂ : ((t.triangleLTGE 0).obj X).obj₃ ⟶ F}
    (h : ((t.triangleLTGE 0).obj X).mor₂ ≫ g₁
       = ((t.triangleLTGE 0).obj X).mor₂ ≫ g₂) :
    g₁ = g₂ := by
  rw [← sub_eq_zero]
  obtain ⟨h', hh'⟩ :=
    Triangle.yoneda_exact₃ _ (t.triangleLTGE_distinguished 0 X) (g₁ - g₂)
      (by rw [Preadditive.comp_sub, h, sub_self])
  have hzero : h' = 0 :=
    t.zero_of_isLE_of_isGE h' (0 - 1 - 1) 0 (by lia)
      (t.isLE_shift _ (0 - 1) 1 (0 - 1 - 1) (by lia)) hF
  rw [hh', hzero, comp_zero]

/-! ### Orthogonality characterisations

Each class is the orthogonal of the other *inside the heart*. The forward
direction is the `hom_eq_zero` axiom; the converse is where the decomposition
axiom earns its place, and it needs no cohomology functor — only that a
distinguished triangle whose second map vanishes has a zero third object, which
here follows from a degree count. -/

/-- An object of the heart with no nonzero map to a torsion-free object is
torsion. -/
theorem tors_of_orthogonal {A : C} (hle : t.IsLE A 0) (hge : t.IsGE A 0)
    (h : ∀ Y : C, P.free Y → ∀ u : A ⟶ Y, u = 0) : P.tors A := by
  obtain ⟨T, Y, hT, hY, i, p, d, hdist⟩ := P.exists_triangle A hle hge
  haveI := P.tors_isLE T hT
  have hYzero : IsZero Y := by
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ hdist (𝟙 Y) (by show p ≫ 𝟙 Y = 0; simpa using h Y hY p)
    have hk0 : k = 0 :=
      t.zero_of_isLE_of_isGE k (-1) 0 (by lia)
        (t.isLE_shift T 0 1 (-1) (by lia)) (P.free_isGE Y hY)
    rw [IsZero.iff_id_eq_zero, hk, hk0]
    exact comp_zero
  haveI : IsIso i := (Triangle.isZero₃_iff_isIso₁ _ hdist).mp hYzero
  exact ObjectProperty.prop_of_iso P.tors (asIso i) hT

/-! ### The Hom-vanishing axiom

`zero'` for the tilted t-structure, proved without any cohomology functor: the
factorisation lemma moves the orthogonality hypothesis from `X` onto
`τ^{≥0}X`, and `tors_of_orthogonal` then puts that truncation in the torsion
class, where the second aisle's hypothesis kills it. -/

/-- **No nonzero map from the tilted co-aisle to the tilted aisle.** -/
theorem hom_eq_zero_of_tiltLE_of_tiltGE [IsTriangulated C] {X Y : C}
    (hX : P.tiltLE X) (hY : P.tiltGE Y) (f : X ⟶ Y) : f = 0 := by
  obtain ⟨hXle, hXorth⟩ := hX
  obtain ⟨hYge, hYorth⟩ := hY
  haveI := hXle
  obtain ⟨g, hg⟩ := exists_factor_truncGE hYge f
  -- `τ^{≥0}X` lies in the heart: `IsGE` by construction, `IsLE` because `X` is.
  have hobj : ((t.triangleLTGE 0).obj X).obj₃ = (t.truncGE 0).obj X := rfl
  have hle3 : t.IsLE (((t.triangleLTGE 0).obj X).obj₃) 0 := by
    rw [hobj]; infer_instance
  have hge3 : t.IsGE (((t.triangleLTGE 0).obj X).obj₃) 0 := inferInstance
  have hTorth : ∀ Z : C, P.free Z →
      ∀ u : ((t.triangleLTGE 0).obj X).obj₃ ⟶ Z, u = 0 := by
    intro Z hZ u
    refine factor_truncGE_unique (P.free_isGE Z hZ) ?_
    rw [comp_zero]
    exact hXorth Z hZ _
  have htors : P.tors (((t.triangleLTGE 0).obj X).obj₃) :=
    P.tors_of_orthogonal hle3 hge3 hTorth
  rw [hg, hYorth _ htors g]
  exact comp_zero

/-! ### The indexed families

A `Triangulated.TStructure` needs an aisle at every integer, not just at the
level the tilt is defined. Splitting the orthogonality condition off as its own
isomorphism-closed predicate is what keeps the shift axioms to a single
application of `shiftFunctorAdd'` each. -/

/-- Objects with no nonzero map to a torsion-free object. -/
def torsOrth : ObjectProperty C := fun Y => ∀ F : C, P.free F → ∀ f : Y ⟶ F, f = 0

/-- Objects with no nonzero map from a torsion object. -/
def freeOrth : ObjectProperty C := fun Y => ∀ T : C, P.tors T → ∀ f : T ⟶ Y, f = 0

instance torsOrth_isClosedUnderIsomorphisms : P.torsOrth.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX F hF f := by
    have hz := hX F hF (e.hom ≫ f)
    calc f = e.inv ≫ (e.hom ≫ f) := by simp
    _ = 0 := by rw [hz, comp_zero]

instance freeOrth_isClosedUnderIsomorphisms : P.freeOrth.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX T hT f := by
    have hz := hX T hT (f ≫ e.inv)
    calc f = (f ≫ e.inv) ≫ e.hom := by simp
    _ = 0 := by rw [hz, zero_comp]

/-- The tilted co-aisle at level `n`: `X ∈ D^{≤n}_†` iff `X⟦n⟧ ∈ D^{≤0}_†`. -/
def tiltLEAt (n : ℤ) : ObjectProperty C :=
  fun X => t.IsLE X n ∧ P.torsOrth (X⟦n⟧)

/-- The tilted aisle at level `n`: `X ∈ D^{≥n}_†` iff `X⟦n-1⟧ ∈ D^{≥1}_†`,
and `tiltGE` is the level-one member. -/
def tiltGEAt (n : ℤ) : ObjectProperty C :=
  fun X => t.IsGE X (n - 1) ∧ P.freeOrth (X⟦n - 1⟧)

/-! #### Agreement with the level at which the tilt was defined -/

theorem tiltLEAt_zero_iff (X : C) : P.tiltLEAt 0 X ↔ P.tiltLE X := by
  constructor
  · rintro ⟨hle, horth⟩
    exact ⟨hle, ObjectProperty.prop_of_iso P.torsOrth ((shiftFunctorZero C ℤ).app X) horth⟩
  · rintro ⟨hle, horth⟩
    exact ⟨hle, ObjectProperty.prop_of_iso P.torsOrth ((shiftFunctorZero C ℤ).app X).symm horth⟩

theorem tiltGEAt_one_iff (X : C) : P.tiltGEAt 1 X ↔ P.tiltGE X := by
  have h : (1 : ℤ) - 1 = 0 := by ring
  rw [tiltGEAt, tiltGE, h]
  constructor
  · rintro ⟨hge, horth⟩
    exact ⟨hge, ObjectProperty.prop_of_iso P.freeOrth ((shiftFunctorZero C ℤ).app X) horth⟩
  · rintro ⟨hge, horth⟩
    exact ⟨hge, ObjectProperty.prop_of_iso P.freeOrth ((shiftFunctorZero C ℤ).app X).symm horth⟩

/-! #### The shift axioms

Each is one application of `shiftFunctorAdd'` against the orthogonality
predicate's isomorphism-closure, plus the corresponding `IsLE`/`IsGE` shift. -/

/-- The `le_shift` field for the tilted co-aisle. -/
theorem tiltLEAt_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : P.tiltLEAt n X) :
    P.tiltLEAt n' (X⟦a⟧) := by
  obtain ⟨hle, horth⟩ := hX
  haveI := hle
  exact ⟨t.isLE_shift X n a n' h,
    ObjectProperty.prop_of_iso P.torsOrth ((shiftFunctorAdd' C a n' n h).app X) horth⟩

/-- The `ge_shift` field for the tilted aisle. -/
theorem tiltGEAt_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : P.tiltGEAt n X) :
    P.tiltGEAt n' (X⟦a⟧) := by
  obtain ⟨hge, horth⟩ := hX
  haveI := hge
  exact ⟨t.isGE_shift X (n - 1) a (n' - 1) (by lia),
    ObjectProperty.prop_of_iso P.freeOrth
      ((shiftFunctorAdd' C a (n' - 1) (n - 1) (by lia)).app X) horth⟩

/-! #### The two inclusions

Both are pure degree counts: neither uses the orthogonality hypothesis it is
handed, because the shifted object is already separated from the heart by
`t.zero`. -/

/-- The `le_zero_le` field. -/
theorem tiltLEAt_zero_le : P.tiltLEAt 0 ≤ P.tiltLEAt 1 := by
  rintro X ⟨hle, -⟩
  haveI := hle
  refine ⟨t.isLE_of_le X 0 1 (by lia), ?_⟩
  intro F hF f
  exact t.zero_of_isLE_of_isGE f (-1) 0 (by lia)
    (t.isLE_shift X 0 1 (-1) (by lia)) (P.free_isGE F hF)

/-- The `ge_one_le` field. -/
theorem tiltGEAt_one_le : P.tiltGEAt 1 ≤ P.tiltGEAt 0 := by
  rintro X ⟨hge, -⟩
  haveI := hge
  refine ⟨t.isGE_of_ge X (0 - 1) (1 - 1) (by lia), ?_⟩
  intro T hT f
  exact t.zero_of_isLE_of_isGE f 0 1 (by lia) (P.tors_isLE T hT)
    (t.isGE_shift X (1 - 1) (0 - 1) 1 (by lia))

/-- The `zero'` field, transported to the indexed families. -/
theorem tiltAt_zero' [IsTriangulated C] {X Y : C}
    (hX : P.tiltLEAt 0 X) (hY : P.tiltGEAt 1 Y) (f : X ⟶ Y) : f = 0 :=
  P.hom_eq_zero_of_tiltLE_of_tiltGE ((P.tiltLEAt_zero_iff X).mp hX)
    ((P.tiltGEAt_one_iff Y).mp hY) f

/-! ### TODO — what remains of the tilt, and why it is not here

The two aisles above, together with the shifted family, are meant to assemble
into a `Triangulated.TStructure C`. Of its fields:

**Five of the six non-trivial fields are proved. One is not.**

* `le_isClosedUnderIsomorphisms` / `ge_isClosedUnderIsomorphisms` — **done**;
* `le_shift` / `ge_shift` — **done**, as `tiltLEAt_shift` / `tiltGEAt_shift`;
* `le_zero_le` / `ge_one_le` — **done**, as `tiltLEAt_zero_le` /
  `tiltGEAt_one_le`. Neither uses the orthogonality hypothesis it is handed:
  both are pure degree counts against `t.zero`;
* `zero'` — **done**, as `hom_eq_zero_of_tiltLE_of_tiltGE`, and transported to
  the indexed families as `tiltAt_zero'`. No cohomology functor appears in the
  proof. It needs `[IsTriangulated C]`: the octahedral axiom is what makes
  `τ^{≥0}` preserve `D^{≤0}`, which is how `τ^{≥0}X` gets into the heart. That
  hypothesis is real and is carried explicitly rather than assumed globally;
* `free_of_orthogonal` — not a `TStructure` field, and the dual of
  `tors_of_orthogonal`. **Not done**: it is not needed for `zero'`, and the
  inverse-rotation bookkeeping it wants is not worth carrying speculatively;
* `exists_triangle_zero_one` — **the one remaining field, and the real
  obstruction.** Producing the
  truncation triangle for the tilted aisles is the octahedral-axiom step, and
  it needs the long exact cohomology sequence of `H⁰`, i.e. that `H⁰` is a
  homological functor. Mathlib has no `H⁰` for a t-structure at all, and the
  anchor's `HeartEquivalence/H0Homological.lean` establishes exactness only in
  named special cases.

Per `CLAUDE.md` §2 none of these is declared with `sorry`. A sorry-backed
`TStructure` instance would typecheck, get imported, and launder an unproved
tilt into everything downstream.
-/

end HeartTorsionPair

end BridgelandStabLean.Tilting
