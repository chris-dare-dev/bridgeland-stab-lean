/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.GroupAction.StabilityDistanceTopology

/-!
# Reducing the mass triangle inequality to a semistable left term

`StabilityMassTriangleInequality` — `m(E) ≤ m(A) + m(C)` for every distinguished
triangle `A → E → C` — is the one open input to Proposition 8.1's second clause.
This file does **not** prove it. It proves that the general statement follows
from the special case in which the left-hand object is *semistable*:

```
StabilityMassSemistableTriangleInequality → StabilityMassTriangleInequality
```

That is the third of the three steps recorded for this proof, and it is the one
that is purely categorical. The two that remain are the analytic ones: a
heart-level short-exact mass inequality, and the semistable-left reduction
through cohomology in the heart.

## Why this is progress and not a rename

The reduction is a theorem, not a definition. It strictly shrinks the open
obligation: `StabilityMassSemistableTriangleInequality` quantifies over
triangles whose first vertex lies in a single `P φ`, where the general
proposition quantifies over all of them. Anyone discharging the crux gets the
general statement for free, and nothing else in the conditional Proposition 8.1
chain has to change — the consumers all take
`StabilityMassTriangleInequality` and keep doing so.

## The argument

Induction on the number of HN factors of the left-hand object `A`.

* If `A` is zero the triangle exhibits `E ≅ C`, and `m(A) = 0`.
* Otherwise split `A`'s HN filtration into its top factor `A₁` — semistable, by
  construction — and the tail `Y`, with `m(A) = m(A₁) + m(Y)`
  (`exists_headTail_stabilityMass`). Feed `A₁ → A → E` to the octahedral axiom:
  with `W` the cone of the composite `A₁ → E`, it returns a distinguished
  triangle `Y → W → C`. Now
  * `A₁ → E → W` has semistable left term, so the hypothesis gives
    `m(E) ≤ m(A₁) + m(W)`;
  * `Y → W → C` has a left term with one fewer HN factor, so induction gives
    `m(W) ≤ m(Y) + m(C)`.

  Adding them and folding `m(A₁) + m(Y)` back into `m(A)` closes it.

The octahedral axiom is where `[IsTriangulated C]` is used; it is already a
hypothesis of every declaration in this track.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- HN-mass subadditivity across a distinguished triangle **whose left-hand
object is semistable**.

This is a strictly weaker proposition than
`StabilityMassTriangleInequality`, and it is the remaining open input to
Proposition 8.1: `stabilityMassTriangleInequality_of_semistable` derives the
general statement from it. Like the general one, this is a `def … : Prop` and
deliberately **not** a class — it must be passed explicitly, so no instance
search can discharge it by accident. -/
def StabilityMassSemistableTriangleInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) (T : Triangle C),
    T ∈ distTriang C → σ.slicing.P φ T.obj₁ →
      (stabilityMass σ T.obj₂).toReal ≤
        (stabilityMass σ T.obj₁).toReal + (stabilityMass σ T.obj₃).toReal

/-- Real-valued form of the head/tail mass split. -/
private theorem toReal_stabilityMass_add
    (σ : StabilityCondition.WithClassMap C v) {A A₁ Y : C}
    (h : stabilityMass σ A = stabilityMass σ A₁ + stabilityMass σ Y) :
    (stabilityMass σ A).toReal =
      (stabilityMass σ A₁).toReal + (stabilityMass σ Y).toReal := by
  rw [h, ENNReal.toReal_add (stabilityMass_ne_top σ A₁) (stabilityMass_ne_top σ Y)]

/-- A distinguished triangle with zero left-hand term has `m(E) = m(C)`. -/
private theorem stabilityMass_eq_of_isZero₁
    (σ : StabilityCondition.WithClassMap C v) {T : Triangle C}
    (hT : T ∈ distTriang C) (hz : IsZero T.obj₁) :
    stabilityMass σ T.obj₂ = stabilityMass σ T.obj₃ := by
  have hiso : IsIso T.mor₂ := (Triangle.isZero₁_iff_isIso₂ T hT).1 hz
  exact stabilityMass_congr σ (asIso T.mor₂)

/-- **The octahedral reduction.** Subadditivity of the HN mass across an
arbitrary distinguished triangle follows from subadditivity across the
triangles whose left-hand object is semistable.

This does not prove Proposition 8.1; it moves the whole remaining obligation
onto `StabilityMassSemistableTriangleInequality`. -/
theorem stabilityMassTriangleInequality_of_semistable
    (hsemi : StabilityMassSemistableTriangleInequality (C := C) (v := v)) :
    StabilityMassTriangleInequality (C := C) (v := v) := by
  intro σ T hT
  suffices hmain : ∀ (m : ℕ) (A E B : C) (F : HNFiltration C σ.slicing.P A),
      F.n ≤ m → ∀ (f : A ⟶ E) (g : E ⟶ B) (k : B ⟶ A⟦(1 : ℤ)⟧),
        Triangle.mk f g k ∈ distTriang C →
        (stabilityMass σ E).toReal ≤
          (stabilityMass σ A).toReal + (stabilityMass σ B).toReal by
    obtain ⟨F⟩ := σ.slicing.hn_exists T.obj₁
    exact hmain F.n T.obj₁ T.obj₂ T.obj₃ F le_rfl T.mor₁ T.mor₂ T.mor₃ hT
  intro m
  induction m with
  | zero =>
      intro A E B F hFn f g k hTr
      have hA : IsZero A := F.zero_isZero (by omega)
      have hEB : stabilityMass σ E = stabilityMass σ B :=
        stabilityMass_eq_of_isZero₁ σ hTr hA
      have hA0 : stabilityMass σ A = 0 := (stabilityMass_eq_zero_iff σ A).2 hA
      rw [hEB, hA0]
      simp
  | succ m ih =>
      intro A E B F hFn f g k hTr
      by_cases hA : IsZero A
      · have hEB : stabilityMass σ E = stabilityMass σ B :=
          stabilityMass_eq_of_isZero₁ σ hTr hA
        have hA0 : stabilityMass σ A = 0 := (stabilityMass_eq_zero_iff σ A).2 hA
        rw [hEB, hA0]
        simp
      · have hn : 0 < F.n := F.n_pos C hA
        obtain ⟨Y, G, f₁, g₁, k₁, hT₁, hmass, hGn⟩ :=
          exists_headTail_stabilityMass σ F hn
        -- The cone of the composite `A₁ ⟶ A ⟶ E`.
        obtain ⟨W, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (f₁ ≫ f)
        let oct := Triangulated.someOctahedron rfl hT₁ hTr h₁₃
        -- `A₁ ⟶ E ⟶ W` has a semistable left term.
        have hstep₁ :
            (stabilityMass σ E).toReal ≤
              (stabilityMass σ (F.factor ⟨0, hn⟩)).toReal +
                (stabilityMass σ W).toReal :=
          hsemi σ (F.φ ⟨0, hn⟩) (Triangle.mk (f₁ ≫ f) v₁₃ w₁₃) h₁₃
            (F.semistable ⟨0, hn⟩)
        -- `Y ⟶ W ⟶ B` has a left term with one fewer HN factor.
        have hstep₂ :
            (stabilityMass σ W).toReal ≤
              (stabilityMass σ Y).toReal + (stabilityMass σ B).toReal :=
          ih Y W B G (by omega) oct.m₁ oct.m₃ _ oct.mem
        have hsplit := toReal_stabilityMass_add σ hmass
        linarith
