/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.WeakStability.Basic
import BridgelandStabLean.Tilting.HeartTorsionPair

/-!
# Noetherian torsion subcategories (Definition 14.6)

The noetherian-torsion layer of §14 of arXiv:1902.08184v4: subobject chains
in the heart, the termination condition, noetherian torsion subcategories,
and the identification of a torsion pair's free class with the right
orthogonal of its torsion class — the place `free_of_orthogonal` (#94) was
built for.

## The design decision, recorded (Remark 14.7 as the definition)

Definition 14.6 calls `B ⊆ A` a *noetherian torsion subcategory* if `B` is an
abelian subcategory, `B` is a noetherian abelian category, and `(B, B^⊥)` is
a torsion pair in `A`. The pin supplies an abelian instance on the full heart,
but `B` here is an object property inside the ambient category; there is no
bundled abelian-category/noetherian structure on that property whose
equivalence with the chain condition is available. Remark 14.7 characterises
the notion for extension-closed
`B`: **every increasing chain of `B`-subobjects of a fixed `E ∈ A`
terminates.** That chain condition is statable — a subobject is a heart
monomorphism, which is a map whose cone is again in the heart — and it is
what every use in §14 consumes (Lemmas 14.8, 14.11, Remark 14.14, and the
proof of Proposition 14.16 all run on chain termination, never on the
abstract noetherian-ness). So the chain condition **is the definition
here**, the torsion-pair half is carried as a `HeartTorsionPair`, and the
equivalence of Remark 14.7 is *not* claimed — it is the textbook
justification for the choice, not a theorem of this file.

## What is deliberately NOT declared here

Lemmas 14.8 and 14.11 are **statable but left undeclared**, per the standing
rule that absent beats sorry-backed. What their proofs need, precisely:

* **Lemma 14.8** (`A⁰` noetherian torsion + `Z` over `ℚ[i]` ⟹ `A`
  noetherian): the proof runs on surjection chains, kernels of composites,
  maximal subobjects with `ℑZ = 0` extracted from HN filtrations, and a
  discreteness argument for the charge image. Missing at the pin: kernel and
  image lemmas needed by the maximal-subobject construction and a
  formalization decision for "Z defined over ℚ[i]" that makes the
  discreteness step honest.  The abelian weak-HN package and its existence for
  the slicing heart are now available in `HarderNarasimhan.lean`.
* **Lemma 14.11** (bounded-slope chains terminate): the statement needs only
  `slope` and the chains below; the proof needs `μ⁺`/`μ⁻` from HN data, the
  compact-parallelogram argument, and the finitely-many-HN-classes input of
  Remark 12.3, which is support-property infrastructure.

The remaining kernel/image, discreteness and support inputs should be added in
focused modules before these two lemmas are attempted; #108 records the
definitions and the boundary.
-/

namespace BridgelandStabLean.WeakStability

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated ZeroObject
open BridgelandStabLean.Tilting

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (t : TStructure C)

/-! ### Heart monomorphisms and subobject chains -/

/-- A map between heart objects is a **heart monomorphism** when its cone is
again in the heart: for heart objects, a distinguished triangle
`A ⟶ E ⟶ Q` with `Q` in the heart is a short exact sequence
`0 → A → E → Q → 0`, so this is exactly "`A` is a subobject of `E` with
quotient `Q`". -/
def IsHeartMono {A E : C} (f : A ⟶ E) : Prop :=
  t.heart A ∧ t.heart E ∧
    ∃ (Q : C) (_ : t.heart Q) (g : E ⟶ Q) (h : Q ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C

/-- An increasing chain of `B`-subobjects of a fixed heart object `E`
(Remark 14.7's data): objects `obj i` of class `B`, each a heart subobject
of the next and of `E`, compatibly. -/
structure SubobjectChain (B : ObjectProperty C) (E : C) where
  /-- The chain objects. -/
  obj : ℕ → C
  /-- Every chain object is of class `B`. -/
  prop : ∀ i, B (obj i)
  /-- The inclusion of each chain object into the next. -/
  step : ∀ i, obj i ⟶ obj (i + 1)
  /-- The inclusion of each chain object into `E`. -/
  toAmbient : ∀ i, obj i ⟶ E
  /-- Each step is a heart monomorphism. -/
  step_mono : ∀ i, IsHeartMono t (step i)
  /-- Each inclusion into `E` is a heart monomorphism. -/
  toAmbient_mono : ∀ i, IsHeartMono t (toAmbient i)
  /-- The inclusions are compatible with the steps. -/
  comm : ∀ i, step i ≫ toAmbient (i + 1) = toAmbient i

/-- A chain **terminates** when all steps are eventually isomorphisms. -/
def SubobjectChain.Terminates {B : ObjectProperty C} {E : C}
    (c : SubobjectChain t B E) : Prop :=
  ∃ N, ∀ i, N ≤ i → IsIso (c.step i)

/-! ### Definition 14.6, in the chain form -/

/-- A **noetherian torsion subcategory** of the heart of `t`
(Definition 14.6, with Remark 14.7's chain characterisation as the
noetherian-ness — see the module docstring for why): a torsion pair on the
heart whose torsion class satisfies the ascending chain condition on
subobjects of every heart object. -/
structure NoetherianTorsionSubcategory where
  /-- The torsion pair `(B, B^⊥)`. -/
  pair : HeartTorsionPair t
  /-- Chain termination: every increasing chain of torsion subobjects of a
  heart object terminates. -/
  noetherian : ∀ (E : C), t.heart E →
    ∀ c : SubobjectChain t pair.tors E, c.Terminates

/-- The right orthogonal of a class inside the heart: heart objects
receiving no nonzero map from the class. This is Definition 14.6's `B^⊥`. -/
def rightOrthogonal (B : ObjectProperty C) : ObjectProperty C :=
  fun X => t.heart X ∧ ∀ T : C, B T → ∀ f : T ⟶ X, f = 0

/-- **A torsion pair's free class is the right orthogonal of its torsion
class** — so the pair carried by `NoetherianTorsionSubcategory` really is
`(B, B^⊥)` in Definition 14.6's sense. The forward inclusion is the
`hom_eq_zero` axiom; the reverse is `free_of_orthogonal`, the dual
characterisation added for the #86 review's finding F1. -/
theorem free_iff_rightOrthogonal (P : HeartTorsionPair t) (X : C) :
    P.free X ↔ rightOrthogonal t P.tors X := by
  constructor
  · intro hX
    haveI := P.free_isLE X hX
    haveI := P.free_isGE X hX
    exact ⟨(TStructure.mem_heart_iff t X).mpr ⟨inferInstance, inferInstance⟩,
      fun T hT f => P.hom_eq_zero hT hX f⟩
  · rintro ⟨hheart, horth⟩
    obtain ⟨hle, hge⟩ := (TStructure.mem_heart_iff t X).mp hheart
    exact P.free_of_orthogonal hle hge horth

/-! ### Nonvacuity

The zero subcategory is noetherian torsion for every t-structure: the
torsion pair is `({0}, A)` with the inverse-rotated contractible triangle as
decomposition, and a chain of zero subobjects has every step an isomorphism
already. -/

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Maps between zero objects are isomorphisms. -/
theorem isIso_of_isZero {A B : C} (f : A ⟶ B) (hA : IsZero A) (hB : IsZero B) :
    IsIso f :=
  ⟨0, hA.eq_of_tgt _ _, hB.eq_of_tgt _ _⟩

/-- The degenerate torsion pair with the zero objects as torsion class and
the whole heart torsion-free. -/
def zeroTorsionPair : HeartTorsionPair t where
  tors X := IsZero X
  free X := t.heart X
  tors_isLE _ h := t.isLE_of_isZero h 0
  tors_isGE _ h := t.isGE_of_isZero h 0
  free_isLE _ h := ((TStructure.mem_heart_iff t _).mp h).1
  free_isGE _ h := ((TStructure.mem_heart_iff t _).mp h).2
  tors_isClosedUnderIsomorphisms := ⟨fun {_ _} e h => h.of_iso e.symm⟩
  free_isClosedUnderIsomorphisms := ⟨fun {_ _} e h =>
    ObjectProperty.prop_of_iso t.heart e h⟩
  hom_eq_zero := fun _ _ hX _ f => hX.eq_of_src f 0
  exists_triangle X hle hge :=
    ⟨0, X, isZero_zero C, (TStructure.mem_heart_iff t X).mpr ⟨hle, hge⟩,
      0, 𝟙 X, 0, contractible_distinguished₁ X⟩

/-- **`NoetherianTorsionSubcategory` is nonvacuous for every t-structure**:
the zero subcategory qualifies. -/
def zeroNoetherianTorsion : NoetherianTorsionSubcategory t where
  pair := zeroTorsionPair t
  noetherian _ _ c :=
    ⟨0, fun i _ => isIso_of_isZero _ (c.prop i) (c.prop (i + 1))⟩

/-! ### Inheritance -/

/-- Chain termination passes to sub-properties: a chain in `B'` with
`B' ≤ B` is a chain in `B`. Recorded because the intended instantiation is
`A⁰ ⊆` a larger torsion class, as in the proof of Proposition 14.16. -/
theorem noetherian_mono {B B' : ObjectProperty C} (hBB : ∀ X, B' X → B X)
    (hB : ∀ (E : C), t.heart E → ∀ c : SubobjectChain t B E, c.Terminates)
    (E : C) (hE : t.heart E) (c : SubobjectChain t B' E) : c.Terminates := by
  obtain ⟨N, hN⟩ := hB E hE
    { obj := c.obj
      prop := fun i => hBB _ (c.prop i)
      step := c.step
      toAmbient := c.toAmbient
      step_mono := c.step_mono
      toAmbient_mono := c.toAmbient_mono
      comm := c.comm }
  exact ⟨N, hN⟩

end BridgelandStabLean.WeakStability
