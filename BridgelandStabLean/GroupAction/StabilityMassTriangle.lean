/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.GroupAction.StabilityDistanceTopology
import BridgelandStabLean.GroupAction.ConvexPolygonPerimeter
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

`HNPolygon` supplies the ambient convex hull and distinguished HN path.
`ConvexPolygonPerimeter` proves the independent `t = 0` comparison of closed
vertex polygons, proves that positive-angle support maxima of the ambient HN
polygon occur on the HN path, and derives the boundary-cut mass comparison for
monomorphisms and short exact sequences. `H0ExactnessBridge` identifies the
exact heart-source obstruction as a canonical cokernel map being monic and
discharges it from homological `H⁰`/`H⁰'` data. The remaining integration
input is an unconditional proof of that exactness obstruction. This file now
also proves that heart semistability agrees with the ambient slicing, converts
abelian HN filtrations into ambient HN towers with the same factor mass, and
inhabits the phase-one boundary-heart milestone, including zero objects. No
open premise is assumed as an instance or axiom.
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

/-- The converse half of the heart/slicing semistability comparison.  A
nonzero object that is semistable for the stability function on the canonical
heart is semistable in the ambient slicing, at the same phase. -/
theorem StabilityCondition.WithClassMap.mem_slicing_of_heart_isSemistable
    (σ : StabilityCondition.WithClassMap C v)
    (E : σ.slicing.toTStructure.heart.FullSubcategory)
    (hE : @StabilityFunction.IsSemistable _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E) :
    σ.slicing.P (@StabilityFunction.phase _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E) E.obj := by
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEnz : ¬IsZero E := hE.1
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hEnz <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  have hEheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
  obtain ⟨F, hn, hfirst, hlast⟩ :=
    HNFiltration.exists_both_nonzero C σ.slicing hEobj
  have hall_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    constructor
    · calc
        0 < σ.slicing.phiMinus C E.obj hEobj :=
          gt_phases_of_gtProp C σ.slicing hEobj hEheart.1
        _ = F.φ ⟨F.n - 1, by lia⟩ :=
          σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        _ = σ.slicing.phiPlus C E.obj hEobj := by
          symm
          exact σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst
        _ ≤ 1 := σ.slicing.phiPlus_le_of_leProp C hEobj hEheart.2
  let iFirst : Fin F.n := ⟨0, hn⟩
  have hAheart : t.heart (F.triangle iFirst).obj₃ := by
    rw [σ.slicing.toTStructure_heart_iff C]
    exact ⟨σ.slicing.gtProp_of_semistable C (F.φ iFirst) 0 _
        (F.semistable iFirst) (hall_mem iFirst).1,
      σ.slicing.leProp_of_semistable C (F.φ iFirst) 1 _
        (F.semistable iFirst) (hall_mem iFirst).2⟩
  let A : t.heart.FullSubcategory := ⟨(F.triangle iFirst).obj₃, hAheart⟩
  have hAnz : ¬IsZero A := fun hZ ↦ hfirst ((t.heart).ι.map_isZero hZ)
  have hAss : @StabilityFunction.IsSemistable _ _
      t.heartFullSubcategoryAbelian Z A :=
    σ.observable.stabilityFunctionOnHeart_isSemistable_of_mem_P_phi C
      (hall_mem iFirst) A (F.semistable iFirst) hAnz
  have hAphase : Z.phase A = F.φ iFirst :=
    σ.observable.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi C
      (hall_mem iFirst) A (F.semistable iFirst) hAnz
  have hα : ∃ α : A.obj ⟶ E.obj, α ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact hfirst <|
      F.isZero_factor_zero_of_hom_eq_zero C σ.slicing hn hzero
  obtain ⟨α, hα⟩ := hα
  let αH : A ⟶ E := ObjectProperty.homMk α
  have hIm : ¬IsZero (Limits.image αH) := by
    intro hZ
    apply hα
    have hι : Limits.image.ι αH = 0 := zero_of_source_iso_zero _ hZ.isoZero
    have hαH : αH = 0 := by rw [← Limits.image.fac αH, hι, comp_zero]
    exact congr_arg (·.hom) hαH
  have hImSub : ¬IsZero (imageSubobject αH : t.heart.FullSubcategory) := by
    intro hZ
    exact hIm (hZ.of_iso (imageSubobjectIso αH).symm)
  have hfirst_le : F.φ iFirst ≤ Z.phase E := by
    rw [← hAphase]
    calc
      Z.phase A ≤ Z.phase (Limits.image αH) :=
        phase_le_of_epi Z (factorThruImage αH) hAss hIm
      _ = Z.phase (imageSubobject αH : t.heart.FullSubcategory) :=
        Z.phase_eq_of_iso (imageSubobjectIso αH).symm
      _ ≤ Z.phase E := hE.2 (imageSubobject αH) hImSub
  have hplus_le : σ.slicing.phiPlus C E.obj hEobj ≤ Z.phase E := by
    rw [σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst]
    exact hfirst_le

  let jLast : Fin F.n := ⟨F.n - 1, by lia⟩
  have hXheart : t.heart (F.chain.obj ⟨F.n - 1, by lia⟩) := by
    by_cases hk : F.n - 1 = 0
    · rw [σ.slicing.toTStructure_heart_iff C]
      have hidx : (⟨F.n - 1, by lia⟩ : Fin (F.n + 1)) = 0 :=
        Fin.ext (by simpa using hk)
      have hzero : IsZero (F.chain.obj ⟨F.n - 1, by lia⟩) := by
        rw [hidx]
        simpa [ComposableArrows.left] using F.base_isZero
      exact ⟨Or.inl hzero, Or.inl hzero⟩
    · rw [σ.slicing.toTStructure_heart_iff C]
      constructor
      · exact HNFiltration.chain_obj_gtProp C σ.slicing F (F.n - 1)
          (by lia) (Nat.pos_of_ne_zero hk) 0
          (fun j ↦ (hall_mem ⟨j, by lia⟩).1)
      · exact HNFiltration.chain_obj_leProp C σ.slicing F (F.n - 1)
          (by lia) (Nat.pos_of_ne_zero hk) 1
          (fun j ↦ (hall_mem ⟨j, by lia⟩).2)
  let X : t.heart.FullSubcategory :=
    ⟨F.chain.obj ⟨F.n - 1, by lia⟩, hXheart⟩
  have hBheart : t.heart (F.triangle jLast).obj₃ := by
    rw [σ.slicing.toTStructure_heart_iff C]
    exact ⟨σ.slicing.gtProp_of_semistable C (F.φ jLast) 0 _
        (F.semistable jLast) (hall_mem jLast).1,
      σ.slicing.leProp_of_semistable C (F.φ jLast) 1 _
        (F.semistable jLast) (hall_mem jLast).2⟩
  let B : t.heart.FullSubcategory := ⟨(F.triangle jLast).obj₃, hBheart⟩
  have hBnz : ¬IsZero B := fun hZ ↦ hlast ((t.heart).ι.map_isZero hZ)
  have hBphase : Z.phase B = F.φ jLast :=
    σ.observable.stabilityFunctionOnHeart_phase_eq_of_mem_P_phi C
      (hall_mem jLast) B (F.semistable jLast) hBnz
  let Tlast := F.triangle jLast
  let e₁ := Classical.choice (F.triangle_obj₁ jLast)
  let e₂ := Classical.choice (F.triangle_obj₂ jLast)
  have hobj₂_eq : F.chain.obj' (F.n - 1 + 1) (by lia) = F.chain.right := by
    simp only [ComposableArrows.obj']
    congr 1
    ext
    simp
    lia
  let e₂E : Tlast.obj₂ ≅ E.obj :=
    e₂.trans ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
  let i : X ⟶ E := ObjectProperty.homMk
    (e₁.inv ≫ Tlast.mor₁ ≫ e₂E.hom)
  let q : E ⟶ B := ObjectProperty.homMk (e₂E.inv ≫ Tlast.mor₂)
  let δ : B.obj ⟶ X.obj⟦(1 : ℤ)⟧ := Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
  have hTlast : Triangle.mk i.hom q.hom δ ∈ distTriang C := by
    refine isomorphic_distinguished _ (F.triangle_dist jLast) _ ?_
    exact Triangle.isoMk _ _ e₁.symm e₂E.symm (Iso.refl _)
      (by simp [Tlast, i, e₂E]) (by simp [Tlast, q, e₂E])
      (by simp [Tlast, δ])
  have hiq_hom : i.hom ≫ q.hom = 0 := by
    simpa using comp_distTriang_mor_zero₁₂ _ hTlast
  have hiq : i ≫ q = 0 := by
    ext
    exact hiq_hom
  have hCok : IsColimit (CokernelCofork.ofπ q hiq) := by
    simpa [hiq] using
      Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
        (TStructure.heart_hι t) i q δ hTlast
  letI : Epi q := Cofork.IsColimit.epi hCok
  have hlast_ge : Z.phase E ≤ F.φ jLast := by
    rw [← hBphase]
    exact phase_le_of_epi Z q hE hBnz
  have hminus_ge : Z.phase E ≤ σ.slicing.phiMinus C E.obj hEobj := by
    rw [σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast]
    exact hlast_ge
  have hextreme : σ.slicing.phiPlus C E.obj hEobj =
      σ.slicing.phiMinus C E.obj hEobj := by
    apply le_antisymm
    · exact hplus_le.trans hminus_ge
    · exact σ.slicing.phiMinus_le_phiPlus C E.obj hEobj
  have hP := σ.slicing.semistable_of_phiPlus_eq_phiMinus (C := C) hEobj hextreme
  rwa [show σ.slicing.phiPlus C E.obj hEobj = Z.phase E from
    le_antisymm hplus_le
      ((σ.observable.stabilityFunctionOnHeart_phase_le_phiPlus C E hEnz))] at hP

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

/-- An abelian HN filtration in the canonical heart is also an ambient HN
filtration after replacing each short exact successive quotient by its
distinguished triangle.  Consequently its factor-norm mass is exactly the
ambient `stabilityMass`. -/
theorem AbelianHNFiltration.mass_eq_stabilityMass_toReal
    (σ : StabilityCondition.WithClassMap C v)
    {E : σ.slicing.toTStructure.heart.FullSubcategory}
    (F : @AbelianHNFiltration _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E) :
    @AbelianHNFiltration.mass _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E F =
        (stabilityMass σ E.obj).toReal := by
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let fH (i : Fin F.n) :
      (F.chain i.castSucc : t.heart.FullSubcategory) ⟶
        (F.chain i.succ : t.heart.FullSubcategory) :=
    Subobject.ofLE (F.chain i.castSucc) (F.chain i.succ)
      (le_of_lt (F.chain_strictMono i.castSucc_lt_succ))
  haveI hmono (i : Fin F.n) : Mono (fH i) := by
    dsimp [fH]
    infer_instance
  let S (i : Fin F.n) : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk (fH i) (cokernel.π (fH i)) (cokernel.condition (fH i))
  have hS (i : Fin F.n) : (S i).ShortExact := by
    exact StabilityFunction.shortExact_of_mono (fH i)
  let δ (i : Fin F.n) :
      (cokernel (fH i)).obj ⟶ (F.chain i.castSucc : t.heart.FullSubcategory).obj⟦(1 : ℤ)⟧ :=
    Classical.choose (heartShortExact_exists_distinguished_triangle σ (S i) (hS i))
  have hδ (i : Fin F.n) :
      Triangle.mk (fH i).hom (cokernel.π (fH i)).hom (δ i) ∈ distTriang C := by
    exact Classical.choose_spec
      (heartShortExact_exists_distinguished_triangle σ (S i) (hS i))
  let objFn : Fin (F.n + 1) → C := fun j ↦ (F.chain j : t.heart.FullSubcategory).obj
  let mapSuccFn : ∀ i : Fin F.n, objFn i.castSucc ⟶ objFn i.succ :=
    fun i ↦ (fH i).hom
  let T (i : Fin F.n) : Triangle C :=
    Triangle.mk (fH i).hom (cokernel.π (fH i)).hom (δ i)
  let G : HNFiltration C σ.slicing.P E.obj :=
    { n := F.n
      chain := ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn
      triangle := T
      triangle_dist := fun i ↦ hδ i
      triangle_obj₁ := fun i ↦ ⟨eqToIso (by
        simp only [T, ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
          objFn]
        rfl)⟩
      triangle_obj₂ := fun i ↦ ⟨eqToIso (by
        simp only [T, ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
          objFn]
        rfl)⟩
      base_isZero := by
        change IsZero (objFn 0)
        have hzero : IsZero (F.chain 0 : t.heart.FullSubcategory) :=
          (StabilityFunction.subobject_isZero_iff_eq_bot (F.chain 0)).2 F.chain_bot
        exact (t.heart).ι.map_isZero hzero
      top_iso := by
        have htop : F.chain (Fin.last F.n) = ⊤ := F.chain_top
        let eEq : (F.chain (Fin.last F.n) : t.heart.FullSubcategory) ≅
            ((⊤ : Subobject E) : t.heart.FullSubcategory) :=
          eqToIso (congrArg (fun S : Subobject E ↦
            (S : t.heart.FullSubcategory)) htop)
        let eTop : (F.chain (Fin.last F.n) : t.heart.FullSubcategory) ≅ E :=
          eEq.trans (asIso (⊤ : Subobject E).arrow)
        exact ⟨(t.heart).ι.mapIso eTop⟩
      zero_isZero := fun h ↦ absurd h (Nat.ne_of_gt F.hn)
      φ := F.φ
      hφ := F.φ_anti
      semistable := fun i ↦ by
        have hP := σ.mem_slicing_of_heart_isSemistable
          (cokernel (fH i)) (by simpa [Z, fH] using F.factor_semistable i)
        rw [show Z.phase (cokernel (fH i)) = F.φ i by
          simpa [Z, fH] using F.factor_phase i] at hP
        exact hP }
  rw [stabilityMass_toReal_eq_sum σ G]
  unfold AbelianHNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The phase-one boundary-heart mass inequality.  The nonzero case is the
boundary-cut comparison for abelian HN polygons, transported to ambient mass
by `AbelianHNFiltration.mass_eq_stabilityMass_toReal`; the zero source case is
handled directly. -/
theorem stabilityMassBoundaryHeartInequality :
    StabilityMassBoundaryHeartInequality (C := C) (v := v) := by
  intro σ S hS h₃
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  by_cases h₁ : IsZero S.X₁
  · have h₁obj : IsZero S.X₁.obj := (t.heart).ι.map_isZero h₁
    rw [show stabilityMass σ S.X₁.obj = 0 from
      (stabilityMass_eq_zero_iff σ S.X₁.obj).2 h₁obj]
    positivity
  · haveI := hS.mono_f
    have h₂ : ¬IsZero S.X₂ := by
      intro h₂
      exact h₁ (IsZero.of_mono S.f h₂)
    obtain ⟨F⟩ := σ.observableStabilityFunctionOnHeart_hasHN S.X₁ h₁
    obtain ⟨G⟩ := σ.observableStabilityFunctionOnHeart_hasHN S.X₂ h₂
    have hmass := F.mass_le_add_norm_of_shortExact S hS G
      σ.observableStabilityFunctionOnHeart_hasHN
    calc
      (stabilityMass σ S.X₁.obj).toReal = F.mass :=
        (AbelianHNFiltration.mass_eq_stabilityMass_toReal σ F).symm
      _ ≤ G.mass + ‖Z.Zobj S.X₃‖ := hmass
      _ = (stabilityMass σ S.X₂.obj).toReal +
          (stabilityMass σ S.X₃.obj).toReal := by
        rw [AbelianHNFiltration.mass_eq_stabilityMass_toReal σ G,
          stabilityMass_toReal_eq_norm_charge σ h₃]
        rfl

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
