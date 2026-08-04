/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.GroupAction.AutAction

/-!
# `Aut(D)` as an honest group, by quotienting

`StrictAutAction.lean` bought a `MulAction` by *restricting* to autoequivalences
with strict inverses — isomorphisms of categories — which excludes Serre
functors and spherical twists, i.e. the cases that actually matter downstream.

This file does the general thing instead: quotient triangulated
auto-equivalences by natural isomorphism. `AutQuot C` is a genuine `Group`, and
**nothing is excluded** — every triangulated auto-equivalence has a class in it.

## Why the action descends

`act_congr` is the whole point, and it is short: if `Φ⁻¹ ≅ Ψ⁻¹` then for every
`X`, `Φ⁻¹ X ≅ Ψ⁻¹ X`, so `s.P φ (Φ⁻¹ X)` and `s.P φ (Ψ⁻¹ X)` are equivalent
*propositions* — because a slicing's `P` is closed under isomorphism. `propext`
then makes them **equal**, so the two slicings are equal on the nose and
`Slicing.ext` finishes.

So `closedUnderIso`, an axiom of `Slicing` that looks like bookkeeping, is
exactly what makes the quotient action well defined.

## One honest caveat about the relation

The setoid asks for `Φ.functor ≅ Ψ.functor` **and** `Φ.inverse ≅ Ψ.inverse`.
Mathematically the second follows from the first, since adjoints are unique up
to natural isomorphism — but that is **not proved here**, so as stated the
relation is a priori finer than "the functors are naturally isomorphic", and
`AutQuot` a priori larger than the usual `Aut(D)`. Carrying both components
keeps `comp`/`symm` compatibility trivial; closing the gap means importing the
adjoint-uniqueness lemma and dropping the second component.

## Scope

Slicings only. The action on stability conditions additionally needs `K₀`
functoriality, a class-map compatibility datum, and invariance of strict finite
length under an equivalence of interval categories — see
`notes/anchor-api-map.md` §7.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace BridgelandStabLean.GroupAction

universe w u

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A triangulated auto-equivalence, bundled with its instances so that they
travel with it. -/
structure TriEquiv (C : Type u) [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The underlying equivalence. -/
  e : C ≌ C
  fAdd : e.functor.Additive
  iAdd : e.inverse.Additive
  fCS : e.functor.CommShift ℤ
  iCS : e.inverse.CommShift ℤ
  fTri : e.functor.IsTriangulated
  iTri : e.inverse.IsTriangulated

namespace TriEquiv

attribute [instance] fAdd iAdd fCS iCS fTri iTri

/-- The identity auto-equivalence.

`inferInstanceAs` throughout: instance search will not unfold
`Equivalence.refl.functor` to `𝟭 C` on its own. -/
def id : TriEquiv C where
  e := CategoryTheory.Equivalence.refl
  fAdd := inferInstanceAs ((𝟭 C).Additive)
  iAdd := inferInstanceAs ((𝟭 C).Additive)
  fCS := inferInstanceAs ((𝟭 C).CommShift ℤ)
  iCS := inferInstanceAs ((𝟭 C).CommShift ℤ)
  fTri := inferInstanceAs ((𝟭 C).IsTriangulated)
  iTri := inferInstanceAs ((𝟭 C).IsTriangulated)

/-- Composition. -/
def comp (Φ Ψ : TriEquiv C) : TriEquiv C where
  e := Φ.e.trans Ψ.e
  fAdd := inferInstanceAs ((Φ.e.functor ⋙ Ψ.e.functor).Additive)
  iAdd := inferInstanceAs ((Ψ.e.inverse ⋙ Φ.e.inverse).Additive)
  fCS := inferInstanceAs ((Φ.e.functor ⋙ Ψ.e.functor).CommShift ℤ)
  iCS := inferInstanceAs ((Ψ.e.inverse ⋙ Φ.e.inverse).CommShift ℤ)
  fTri := inferInstanceAs ((Φ.e.functor ⋙ Ψ.e.functor).IsTriangulated)
  iTri := inferInstanceAs ((Ψ.e.inverse ⋙ Φ.e.inverse).IsTriangulated)

/-- Inverse: swap the two halves. -/
def symm (Φ : TriEquiv C) : TriEquiv C where
  e := Φ.e.symm
  fAdd := Φ.iAdd
  iAdd := Φ.fAdd
  fCS := Φ.iCS
  iCS := Φ.fCS
  fTri := Φ.iTri
  iTri := Φ.fTri

/-- The induced map on slicings, `(Φ • s).P φ X = s.P φ (Φ⁻¹ X)`. -/
noncomputable def act (Φ : TriEquiv C) (s : Slicing C) : Slicing C := s.mapEquiv Φ.e

@[simp] theorem act_P (Φ : TriEquiv C) (s : Slicing C) (φ : ℝ) (X : C) :
    (Φ.act s).P φ X = s.P φ (Φ.e.inverse.obj X) := rfl

theorem act_id (s : Slicing C) : (TriEquiv.id (C := C)).act s = s := by
  refine Slicing.ext C ?_; funext φ; funext X; rfl

theorem act_comp (Φ Ψ : TriEquiv C) (s : Slicing C) :
    (Φ.comp Ψ).act s = Ψ.act (Φ.act s) := by
  refine Slicing.ext C ?_; funext φ; funext X; rfl

/-- **Descent.** Naturally isomorphic auto-equivalences act identically — not
merely up to isomorphism of slicings, but equally, because `Slicing.P` is
closed under isomorphism and `propext` upgrades the resulting `Iff` to `Eq`. -/
theorem act_congr {Φ Ψ : TriEquiv C} (h : Φ.e.inverse ≅ Ψ.e.inverse) (s : Slicing C) :
    Φ.act s = Ψ.act s := by
  refine Slicing.ext C ?_; funext φ; funext X
  simp only [act_P]
  exact propext ⟨fun hX => ObjectProperty.prop_of_iso _ (h.app X) hX,
                 fun hX => ObjectProperty.prop_of_iso _ (h.app X).symm hX⟩

/-- Isomorphism of auto-equivalences. See the module docstring on why both
components are carried. -/
instance setoid : Setoid (TriEquiv C) where
  r Φ Ψ := Nonempty (Φ.e.functor ≅ Ψ.e.functor) ∧ Nonempty (Φ.e.inverse ≅ Ψ.e.inverse)
  iseqv :=
    { refl := fun _ => ⟨⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
      symm := fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a.symm⟩, ⟨b.symm⟩⟩
      trans := fun ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨d⟩⟩ => ⟨⟨a.trans c⟩, ⟨b.trans d⟩⟩ }

end TriEquiv

/-- `Aut(D)`: triangulated auto-equivalences modulo natural isomorphism.

Unlike `StrictAut`, this excludes nothing. -/
def AutQuot (C : Type u) [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :=
  Quotient (TriEquiv.setoid (C := C))

namespace AutQuot

/-- `a * b` composes `b` first, matching `(a * b) • s = a • (b • s)`. -/
instance group : Group (AutQuot C) where
  mul := Quotient.map₂ (fun A B => B.comp A)
    (by rintro A A' ⟨⟨p⟩, ⟨q⟩⟩ B B' ⟨⟨r⟩, ⟨t⟩⟩
        exact ⟨⟨NatIso.hcomp r p⟩, ⟨NatIso.hcomp q t⟩⟩)
  one := Quotient.mk _ TriEquiv.id
  inv := Quotient.map TriEquiv.symm
    (by rintro A A' ⟨⟨p⟩, ⟨q⟩⟩; exact ⟨⟨q⟩, ⟨p⟩⟩)
  -- Associativity and the unit laws are `Iso.refl` because functor composition
  -- is strictly associative and `𝟭` is a strict unit; only inversion needs a
  -- genuine natural isomorphism, which is exactly the point of quotienting.
  mul_assoc := by
    rintro ⟨A⟩ ⟨B⟩ ⟨D⟩; exact Quotient.sound ⟨⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  one_mul := by rintro ⟨A⟩; exact Quotient.sound ⟨⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  mul_one := by rintro ⟨A⟩; exact Quotient.sound ⟨⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  inv_mul_cancel := by
    rintro ⟨A⟩; exact Quotient.sound ⟨⟨A.e.unitIso.symm⟩, ⟨A.e.unitIso.symm⟩⟩

/-- **`Aut(D)` acts on slicings.** Well defined by `TriEquiv.act_congr`. -/
noncomputable instance mulActionSlicing : MulAction (AutQuot C) (Slicing C) where
  smul a s := Quotient.liftOn a (fun Φ => Φ.act s)
    (fun _ _ h => TriEquiv.act_congr h.2.some s)
  one_smul s := TriEquiv.act_id s
  mul_smul a b s := by
    induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
    exact TriEquiv.act_comp B A s

/-- The class of an auto-equivalence. Stated with an explicit `AutQuot C`
return type: `AutQuot` is a plain `def`, so a bare `Quotient.mk` does not carry
enough type information for `•` to find its instance. -/
def mk (Φ : TriEquiv C) : AutQuot C := Quotient.mk _ Φ

@[simp] theorem mk_smul_P (Φ : TriEquiv C) (s : Slicing C) (φ : ℝ) (X : C) :
    (mk Φ • s).P φ X = s.P φ (Φ.e.inverse.obj X) := rfl

end AutQuot

end BridgelandStabLean.GroupAction
