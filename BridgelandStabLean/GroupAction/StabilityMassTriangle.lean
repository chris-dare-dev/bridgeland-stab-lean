/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.GroupAction.StabilityDistanceTopology
import BridgelandStabLean.GroupAction.HNPolygon
import BridgelandStabLean.GroupAction.H0ExactnessBridge
import BridgelandStability.HeartEquivalence.Reverse

/-!
# The HN mass-triangle chain

This file develops the stronger HN-mass subadditivity route selected for the
repository's topology comparison around Bridgeland's Proposition 8.1.

The general theorem requires the polygonal argument through the heart and
Harder--Narasimhan filtrations.  Here we establish its norm-theoretic base:

* the norm of an object's charge is bounded by its HN mass;
* charge is additive on every distinguished triangle;
* consequently the mass-triangle inequality holds when the middle object is
  semistable;
* in particular it holds when both endpoints are semistable of the same phase,
  since semistable slices are extension-closed;
* the arbitrary-left case reduces, by head--tail octahedral induction, to the
  semistable-left case.

The remaining mathematical inputs are the phase-one boundary-heart polygon
inequality and the cohomological reduction from that boundary case to a
semistable first object.  They are named below but are not assumed as instances
or axioms.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ENNReal BigOperators ZeroObject

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Forget the presentation lattice while retaining the observable charge on
`K₀(C)`.  This is composition of additive homomorphisms, not an operation on
stability conditions.  It lets the ordinary heart-equivalence API be reused
for a condition defined with an arbitrary class map. -/
def StabilityCondition.WithClassMap.observable
    (σ : StabilityCondition.WithClassMap C v) : StabilityCondition C where
  slicing := σ.slicing
  Z := σ.Z.comp v
  compat' := by
    intro φ E hP hE
    simpa using σ.compat' φ E hP hE
  locallyFinite := σ.locallyFinite

@[simp]
theorem StabilityCondition.WithClassMap.observable_slicing
    (σ : StabilityCondition.WithClassMap C v) :
    σ.observable.slicing = σ.slicing := rfl

@[simp]
theorem StabilityCondition.WithClassMap.observable_charge
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    σ.observable.charge E = σ.charge E := rfl

/-- The heart stability function associated to a class-map stability
condition, obtained from its observable ordinary stability condition. -/
def StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart
    (σ : StabilityCondition.WithClassMap C v) :
    @StabilityFunction (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian) :=
  σ.observable.stabilityFunctionOnHeart C

@[simp]
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_Zobj
    (σ : StabilityCondition.WithClassMap C v)
    (E : σ.slicing.toTStructure.heart.FullSubcategory) :
    @StabilityFunction.Zobj _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E = σ.charge E.obj := rfl

/-- The observable heart stability function has Harder--Narasimhan
filtrations. -/
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_hasHN
    (σ : StabilityCondition.WithClassMap C v) :
    @StabilityFunction.HasHNProperty
      (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart :=
  σ.observable.stabilityFunctionOnHeart_hasHN_local C

/-- The norm of the total charge is at most the sum of the norms of the
Harder--Narasimhan factor charges. -/
theorem norm_charge_le_stabilityMass_toReal
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    ‖σ.charge E‖ ≤ (stabilityMass σ E).toReal := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.charge_postnikovTower_eq_sum F.toPostnikovTower,
    stabilityMass_toReal_eq_sum σ F]
  exact norm_sum_le _ _

/-- Shifting an HN filtration by one does not change its mass. -/
theorem HNFiltration.mass_shift_one
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (F.shiftHN C σ.slicing 1).mass σ = F.mass σ := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  simp only [HNFiltration.shiftHN]
  change ENNReal.ofReal ‖σ.charge ((F.triangle i).obj₃⟦(1 : ℤ)⟧)‖ =
    ENNReal.ofReal ‖σ.charge (F.triangle i).obj₃‖
  simp only [PreStabilityCondition.WithClassMap.charge_def,
    cl_shift_one, map_neg, norm_neg]

/-- Shifting an object by one does not change its HN mass. -/
@[simp]
theorem stabilityMass_shift_one
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ (E⟦(1 : ℤ)⟧) = stabilityMass σ E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [stabilityMass_eq_mass σ (F.shiftHN C σ.slicing 1),
    stabilityMass_eq_mass σ F, F.mass_shift_one σ]

/-- Shifting an HN filtration by minus one does not change its mass. -/
theorem HNFiltration.mass_shift_neg_one
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (F.shiftHN C σ.slicing (-1)).mass σ = F.mass σ := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  simp only [HNFiltration.shiftHN]
  change ENNReal.ofReal ‖σ.charge ((F.triangle i).obj₃⟦(-1 : ℤ)⟧)‖ =
    ENNReal.ofReal ‖σ.charge (F.triangle i).obj₃‖
  simp only [PreStabilityCondition.WithClassMap.charge_def,
    cl_shift_neg_one, map_neg, norm_neg]

/-- Shifting an object by minus one does not change its HN mass. -/
@[simp]
theorem stabilityMass_shift_neg_one
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ (E⟦(-1 : ℤ)⟧) = stabilityMass σ E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [stabilityMass_eq_mass σ (F.shiftHN C σ.slicing (-1)),
    stabilityMass_eq_mass σ F, F.mass_shift_neg_one σ]

/-- The charge of the middle object in a distinguished triangle is the sum
of the endpoint charges. -/
theorem StabilityCondition.WithClassMap.charge_triangle
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) :
    σ.charge T.obj₂ = σ.charge T.obj₁ + σ.charge T.obj₃ := by
  simp only [PreStabilityCondition.WithClassMap.charge_def,
    cl_triangle C v T hT, map_add]

/-- Mass is subadditive along a distinguished triangle whose middle object is
semistable. -/
theorem stabilityMass_triangle_le_of_obj₂_semistable
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) {φ : ℝ} (h₂ : σ.slicing.P φ T.obj₂) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  rw [stabilityMass_toReal_eq_norm_charge σ h₂,
    σ.charge_triangle T hT]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_charge_le_stabilityMass_toReal σ T.obj₁)
      (norm_charge_le_stabilityMass_toReal σ T.obj₃))

/-- Mass is subadditive when both endpoints of a distinguished triangle are
semistable of the same phase. -/
theorem stabilityMass_triangle_le_of_same_phase
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) (φ : ℝ)
    (h₁ : σ.slicing.P φ T.obj₁) (h₃ : σ.slicing.P φ T.obj₃) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  exact stabilityMass_triangle_le_of_obj₂_semistable σ T hT
    (σ.slicing.semistable_of_triangle C φ h₁ h₃ hT)

/-- The first major mass-triangle milestone, in its phase-one boundary-heart
form.  For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in the
canonical heart with `C ∈ P(1)`, the mass of `A` is at most the combined
mass of `B` and `C`.

This is a named proof target, not an installed premise. -/
def StabilityMassBoundaryHeartInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory),
    S.ShortExact → σ.slicing.P 1 S.X₃.obj →
      (stabilityMass σ S.X₁.obj).toReal ≤
        (stabilityMass σ S.X₂.obj).toReal +
          (stabilityMass σ S.X₃.obj).toReal

/-- The second paper-level mass-triangle milestone: subadditivity for a
distinguished triangle whose first object is semistable. -/
def StabilityMassSemistableLeftTriangleInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v) (T : Triangle C),
    T ∈ distTriang C →
    ∀ (φ : ℝ), σ.slicing.P φ T.obj₁ →
      (stabilityMass σ T.obj₂).toReal ≤
        (stabilityMass σ T.obj₁).toReal +
          (stabilityMass σ T.obj₃).toReal

/-- The arbitrary-left octahedral milestone.  Once the triangle inequality is
known for semistable first objects, split an HN filtration of the first object
into its head and tail.  The octahedron produces one semistable-left triangle
and a shorter arbitrary-left triangle, so induction proves the unrestricted
statement. -/
theorem stabilityMassTriangleInequality_of_semistable_obj₁
    (hsemistable :
      StabilityMassSemistableLeftTriangleInequality (C := C) (v := v)) :
    StabilityMassTriangleInequality (C := C) (v := v) := by
  intro σ T hT
  obtain ⟨F⟩ := σ.slicing.hn_exists T.obj₁
  suffices hmain :
      ∀ (m : ℕ) (U : Triangle C), U ∈ distTriang C →
        ∀ G : HNFiltration C σ.slicing.P U.obj₁, G.n ≤ m →
          (stabilityMass σ U.obj₂).toReal ≤
            (stabilityMass σ U.obj₁).toReal +
              (stabilityMass σ U.obj₃).toReal by
    exact hmain F.n T hT F le_rfl
  intro m
  induction m with
  | zero =>
      intro U hU G hG
      have hn : G.n = 0 := by omega
      have hzero : IsZero U.obj₁ := G.zero_isZero hn
      haveI : IsIso U.mor₂ := (Triangle.isZero₁_iff_isIso₂ U hU).mp hzero
      rw [stabilityMass_congr σ (asIso U.mor₂)]
      simp [show stabilityMass σ U.obj₁ = 0 from
        (stabilityMass_eq_zero_iff σ U.obj₁).2 hzero]
  | succ m ih =>
      intro U hU G hG
      by_cases hn0 : G.n = 0
      · have hzero : IsZero U.obj₁ := G.zero_isZero hn0
        haveI : IsIso U.mor₂ := (Triangle.isZero₁_iff_isIso₂ U hU).mp hzero
        rw [stabilityMass_congr σ (asIso U.mor₂)]
        simp [show stabilityMass σ U.obj₁ = 0 from
          (stabilityMass_eq_zero_iff σ U.obj₁).2 hzero]
      · have hn : 0 < G.n := Nat.pos_of_ne_zero hn0
        obtain ⟨Y, Gtail, f, _g, _δ, hhead, hmass, hnTail, _hφ⟩ :=
          G.exists_headTail_mass σ hn
        obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ :=
          distinguished_cocone_triangle (f ≫ U.mor₁)
        let oct := Triangulated.someOctahedron rfl hhead hU h₁₃
        have hfirst := hsemistable σ
          (Triangle.mk (f ≫ U.mor₁) v₁₃ w₁₃) h₁₃
          (G.φ ⟨0, hn⟩) (G.semistable ⟨0, hn⟩)
        have hheadMass :
            (stabilityMass σ (G.factor ⟨0, hn⟩)).toReal =
              ‖σ.charge (G.factor ⟨0, hn⟩)‖ :=
          stabilityMass_toReal_eq_norm_charge σ (G.semistable ⟨0, hn⟩)
        change (stabilityMass σ U.obj₂).toReal ≤
          (stabilityMass σ (G.factor ⟨0, hn⟩)).toReal +
            (stabilityMass σ Z).toReal at hfirst
        rw [hheadMass] at hfirst
        have htail :
            (stabilityMass σ Z).toReal ≤
              (stabilityMass σ Y).toReal +
                (stabilityMass σ U.obj₃).toReal := by
          simpa [oct] using ih oct.triangle oct.mem Gtail (by
            rw [hnTail]
            omega)
        linarith

/-- The first remaining polygonal milestone: mass subadditivity for every
short exact sequence in the canonical heart `P((0, 1])`. -/
def StabilityMassHeartShortExactInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory),
    S.ShortExact →
      (stabilityMass σ S.X₂.obj).toReal ≤
        (stabilityMass σ S.X₁.obj).toReal +
          (stabilityMass σ S.X₃.obj).toReal

private theorem heartShortExact_exists_distinguished_triangle
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) :
    ∃ δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧,
      Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : IsNormalMonoCategory t.heart.FullSubcategory :=
    Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory t.heart.FullSubcategory :=
    Abelian.toIsNormalEpiCategory
  letI : Balanced t.heart.FullSubcategory := by infer_instance
  haveI := hS.mono_f
  haveI := hS.epi_g
  exact TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t S.f S.g S.zero (fun {W} α hα ↦ by
      have hker : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
      exact ⟨hker.lift (KernelFork.ofι α hα),
        hker.fac _ WalkingParallelPair.zero⟩)

/-- The global distinguished-triangle inequality restricts to the heart-level
short-exact inequality. -/
theorem stabilityMassHeartShortExactInequality_of_triangle
    (htriangle : StabilityMassTriangleInequality (C := C) (v := v)) :
    StabilityMassHeartShortExactInequality (C := C) (v := v) := by
  intro σ S hS
  obtain ⟨δ, hT⟩ := heartShortExact_exists_distinguished_triangle σ S hS
  exact htriangle σ (Triangle.mk S.f.hom S.g.hom δ) hT

/-- A short exact sequence in the heart of the slicing satisfies the mass
inequality when its middle object is semistable in the ambient slicing. -/
theorem stabilityMass_heart_shortExact_le_of_obj₂_semistable
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) {φ : ℝ} (h₂ : σ.slicing.P φ S.X₂.obj) :
    (stabilityMass σ S.X₂.obj).toReal ≤
      (stabilityMass σ S.X₁.obj).toReal +
        (stabilityMass σ S.X₃.obj).toReal := by
  obtain ⟨δ, hT⟩ := heartShortExact_exists_distinguished_triangle σ S hS
  exact stabilityMass_triangle_le_of_obj₂_semistable σ
    (Triangle.mk S.f.hom S.g.hom δ) hT h₂

/-- A short exact sequence in the heart satisfies the mass inequality when
its endpoint objects are semistable of the same phase. -/
theorem stabilityMass_heart_shortExact_le_of_same_phase
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) (φ : ℝ)
    (h₁ : σ.slicing.P φ S.X₁.obj) (h₃ : σ.slicing.P φ S.X₃.obj) :
    (stabilityMass σ S.X₂.obj).toReal ≤
      (stabilityMass σ S.X₁.obj).toReal +
        (stabilityMass σ S.X₃.obj).toReal := by
  obtain ⟨δ, hT⟩ := heartShortExact_exists_distinguished_triangle σ S hS
  exact stabilityMass_triangle_le_of_same_phase σ
    (Triangle.mk S.f.hom S.g.hom δ) hT φ h₁ h₃

end

end CategoryTheory.Triangulated
