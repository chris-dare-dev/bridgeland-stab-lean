/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Bounded t-structures and t-exact functors

Both 2026 target papers state their central hypotheses in this vocabulary.
Polishchuk's inducing theorem (arXiv:2601.22994 Prop 3.4, arXiv:2607.28411
Thm A.17) asks for a *bounded* t-structure and for `Φ Φᴸ` to be *right t-exact*;
without those as definitions the hypothesis cannot be written down at all.

## Main definitions

* `TStructure.IsBounded`: every object is `t`-bounded.
* `TStructure.IsNondegenerate`: no nonzero object is `t`-coconnective in every
  degree, nor `t`-connective in every degree.
* `Functor.IsRightTExact` / `Functor.IsLeftTExact` / `Functor.IsTExact`:
  a functor's compatibility with a t-structure on its source and one on its
  target.

## Namespacing, and why it is not in `CategoryTheory`

Everything here lives under `BridgelandStabLean`. The foundational library
already declares `CategoryTheory.Triangulated.TStructure.IsBounded`
(`BridgelandStability/Slicing/TStructure.lean:215`) with an equivalent meaning
stated through `t.le`/`t.ge` rather than the `IsLE`/`IsGE` classes. Declaring
this file's `IsBounded` in the same namespace makes the root aggregator fail to
import — *"environment already contains ..."* — because both end up in one
environment.

This module is deliberately anchor-free, so it cannot simply reuse the
foundational definition. A bridge lemma identifying the two belongs in a
stability-facing module that already imports the anchor, not here.

## Conventions

Mathlib writes the t-structure as `t.IsLE X n` (`X ∈ Dᵗ≤ⁿ`) and `t.IsGE X n`
(`X ∈ Dᵗ≥ⁿ`), and already supplies `t.plus`, `t.minus` and `t.bounded` as
`ObjectProperty C`. Boundedness of the t-structure itself is then just
`t.bounded = ⊤`, which is the definition taken here.

Right t-exactness preserves the *coconnective* half (`IsLE`), left t-exactness
the *connective* half (`IsGE`). This is the convention under which the derived
functor `Lf*` is right t-exact and `Rf_*` is left t-exact, and it is the one
both papers use.

## A correction to the issue that requested this file

Issue #146 asked for "the nondegenerate ⟺ bounded equivalence". Only one
direction is a theorem: **bounded implies nondegenerate** (`isNondegenerate_of_isBounded`).
The converse is false. A nondegenerate t-structure can have objects that are
bounded in neither direction — nondegeneracy only forbids an object from being
coconnective in *every* degree, which says nothing about an object that is
coconnective in no degree at all. The unbounded derived category of a nonzero
abelian category with its standard t-structure is nondegenerate and not bounded.
So the equivalence is not stated here, and #146's acceptance criterion should be
read as the implication.
-/

universe v v' u u'

namespace BridgelandStabLean

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated


namespace TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section Bounded

variable (t : TStructure C)

/-- A t-structure is **bounded** when every object of the ambient category is
`t`-bounded, i.e. lies in `Dᵗ≤ⁿ` for some `n` and in `Dᵗ≥ᵐ` for some `m`. -/
def IsBounded : Prop := ∀ X : C, t.bounded X

variable {t}

theorem isBounded_iff :
    TStructure.IsBounded t ↔ ∀ X : C, (∃ n : ℤ, t.IsGE X n) ∧ ∃ n : ℤ, t.IsLE X n :=
  Iff.rfl

/-- On a bounded t-structure every object admits a coconnective bound. -/
theorem exists_isLE (h : TStructure.IsBounded t) (X : C) : ∃ n : ℤ, t.IsLE X n := (h X).2

/-- On a bounded t-structure every object admits a connective bound. -/
theorem exists_isGE (h : TStructure.IsBounded t) (X : C) : ∃ n : ℤ, t.IsGE X n := (h X).1

/-- Boundedness is a property of the ambient category, so it transfers along a
shift. -/
theorem isLE_shift_of_isBounded (h : TStructure.IsBounded t) (X : C) (a : ℤ) :
    ∃ n : ℤ, t.IsLE (X⟦a⟧) n := exists_isLE h _

end Bounded

section Nondegenerate

variable (t : TStructure C)

/-- A t-structure is **nondegenerate** when the only object lying in `Dᵗ≤ⁿ` for
every `n` is zero, and likewise for `Dᵗ≥ⁿ`. -/
structure IsNondegenerate : Prop where
  /-- An object coconnective in every degree is zero. -/
  isZero_of_forall_isLE : ∀ X : C, (∀ n : ℤ, t.IsLE X n) → IsZero X
  /-- An object connective in every degree is zero. -/
  isZero_of_forall_isGE : ∀ X : C, (∀ n : ℤ, t.IsGE X n) → IsZero X

variable {t}

/-- **Bounded implies nondegenerate.**

If `X` is coconnective in every degree then it is in particular coconnective in
degree `n - 1` for the `n` supplied by boundedness on the connective side, so
`X` lies in `Dᵗ≥ⁿ ∩ Dᵗ≤ⁿ⁻¹`, which is zero.

The converse is false; see the module docstring. -/
theorem isNondegenerate_of_isBounded (h : TStructure.IsBounded t) : TStructure.IsNondegenerate t where
  isZero_of_forall_isLE X hX := by
    obtain ⟨n, hn⟩ := exists_isGE h X
    haveI := hn
    haveI := hX (n - 1)
    exact t.isZero X (n - 1) n (by lia)
  isZero_of_forall_isGE X hX := by
    obtain ⟨n, hn⟩ := exists_isLE h X
    haveI := hn
    haveI := hX (n + 1)
    exact t.isZero X n (n + 1) (by lia)

end Nondegenerate

end TStructure

namespace Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- `F` is **right t-exact** for `t` on the source and `t'` on the target when it
carries `Dᵗ≤ⁿ` into `D'ᵗ'≤ⁿ` for every `n`. -/
class IsRightTExact (F : C ⥤ D) (t : TStructure C) (t' : TStructure D) : Prop where
  /-- Right t-exactness preserves the coconnective half. -/
  isLE_map : ∀ (X : C) (n : ℤ), t.IsLE X n → t'.IsLE (F.obj X) n

/-- `F` is **left t-exact** for `t` on the source and `t'` on the target when it
carries `Dᵗ≥ⁿ` into `D'ᵗ'≥ⁿ` for every `n`. -/
class IsLeftTExact (F : C ⥤ D) (t : TStructure C) (t' : TStructure D) : Prop where
  /-- Left t-exactness preserves the connective half. -/
  isGE_map : ∀ (X : C) (n : ℤ), t.IsGE X n → t'.IsGE (F.obj X) n

/-- `F` is **t-exact** when it is both left and right t-exact. -/
class IsTExact (F : C ⥤ D) (t : TStructure C) (t' : TStructure D) : Prop
    extends Functor.IsRightTExact F t t', Functor.IsLeftTExact F t t'

variable {F : C ⥤ D} {t : TStructure C} {t' : TStructure D}

theorem isLE_map_of_isRightTExact [Functor.IsRightTExact F t t'] (X : C) (n : ℤ)
    [t.IsLE X n] : t'.IsLE (F.obj X) n :=
  IsRightTExact.isLE_map X n ‹_›

theorem isGE_map_of_isLeftTExact [Functor.IsLeftTExact F t t'] (X : C) (n : ℤ)
    [t.IsGE X n] : t'.IsGE (F.obj X) n :=
  IsLeftTExact.isGE_map X n ‹_›

/-- A t-exact functor carries the heart into the heart. -/
theorem heart_map_of_isTExact [Functor.IsTExact F t t'] (X : C) (hX : t.heart X) :
    t'.heart (F.obj X) := by
  rw [t.mem_heart_iff] at hX
  obtain ⟨hLE, hGE⟩ := hX
  rw [t'.mem_heart_iff]
  exact ⟨IsRightTExact.isLE_map X 0 hLE, IsLeftTExact.isGE_map X 0 hGE⟩

section Comp

variable {E : Type*} [Category E] [Preadditive E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  {G : D ⥤ E} {t'' : TStructure E}


theorem isRightTExact_comp (t' : TStructure D)
    [Functor.IsRightTExact F t t'] [Functor.IsRightTExact G t' t''] :
    Functor.IsRightTExact (F ⋙ G) t t'' where
  isLE_map X n hX :=
    IsRightTExact.isLE_map (F := G) (t := t') (t' := t'') (F.obj X) n
      (IsRightTExact.isLE_map (F := F) (t := t) (t' := t') X n hX)

theorem isLeftTExact_comp (t' : TStructure D)
    [Functor.IsLeftTExact F t t'] [Functor.IsLeftTExact G t' t''] :
    Functor.IsLeftTExact (F ⋙ G) t t'' where
  isGE_map X n hX :=
    IsLeftTExact.isGE_map (F := G) (t := t') (t' := t'') (F.obj X) n
      (IsLeftTExact.isGE_map (F := F) (t := t) (t' := t') X n hX)

theorem isTExact_comp (t' : TStructure D)
    [Functor.IsTExact F t t'] [Functor.IsTExact G t' t''] :
    Functor.IsTExact (F ⋙ G) t t'' :=
  { toIsRightTExact := isRightTExact_comp (F := F) (G := G) t'
    toIsLeftTExact := isLeftTExact_comp (F := F) (G := G) t' }

end Comp

section Id

instance isRightTExact_id : Functor.IsRightTExact (𝟭 C) t t where
  isLE_map _ _ h := h

instance isLeftTExact_id : Functor.IsLeftTExact (𝟭 C) t t where
  isGE_map _ _ h := h

instance isTExact_id : Functor.IsTExact (𝟭 C) t t :=
  { toIsRightTExact := isRightTExact_id, toIsLeftTExact := isLeftTExact_id }

end Id

end Functor

end BridgelandStabLean
