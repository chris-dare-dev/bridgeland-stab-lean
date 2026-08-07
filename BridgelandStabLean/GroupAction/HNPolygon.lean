/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStability.HeartEquivalence.Reverse
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Order.Interval.Set.Monotone

/-!
# Harder--Narasimhan polygon paths

This file supplies the algebraic path underlying the HN polygon of an object in
an abelian category with a stability function.  Its vertices are the charges of
the subobjects in an abelian HN filtration.  Consecutive edge vectors are
proved to be the charges of the semistable factors, so the polygonal path
length is exactly the usual sum of factor masses.

Convex-hull containment under monomorphisms, strict support of interior path
vertices, and the semistable-descent/maximal-phase algebra needed for the
ambient boundary theorem are proved separately below; none is hidden inside
the path representation.  The remaining step from these ingredients to full
ambient-polygon extremality is likewise kept explicit.
-/

open CategoryTheory CategoryTheory.Limits Complex
open scoped BigOperators

namespace CategoryTheory

noncomputable section

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The HN polygon of an object: the convex hull of the charges of all its
subobjects.  This is the paper's ambient polygon; a chosen HN filtration below
provides its distinguished decreasing-phase boundary path. -/
def StabilityFunction.hnPolygon (Z : StabilityFunction A) (E : A) : Set ℂ :=
  convexHull ℝ (Set.range fun S : Subobject E ↦ Z.Zobj (S : A))

/-- Every subobject charge is a point of the HN polygon. -/
theorem StabilityFunction.subobjectCharge_mem_hnPolygon
    (Z : StabilityFunction A) (E : A) (S : Subobject E) :
    Z.Zobj (S : A) ∈ Z.hnPolygon E :=
  subset_convexHull ℝ (Set.range fun T : Subobject E ↦ Z.Zobj (T : A))
    (Set.mem_range_self S)

/-- A monomorphism induces inclusion of HN polygons: pushing a subobject
forward along the monomorphism does not change its underlying object up to
isomorphism, hence does not change its charge. -/
theorem StabilityFunction.hnPolygon_mono {X Y : A} (Z : StabilityFunction A)
    (f : X ⟶ Y) [Mono f] : Z.hnPolygon X ⊆ Z.hnPolygon Y := by
  apply convexHull_mono
  rintro _ ⟨S, rfl⟩
  let T : Subobject Y := (Subobject.map f).obj S
  have hmap : T = Subobject.mk (S.arrow ≫ f) := by
    calc
      (Subobject.map f).obj S =
          (Subobject.map f).obj (Subobject.mk S.arrow) := by
        rw [Subobject.mk_arrow]
      _ = Subobject.mk (S.arrow ≫ f) := Subobject.map_mk S.arrow f
  let e : (T : A) ≅ (S : A) :=
    Subobject.isoOfEqMk T (S.arrow ≫ f) hmap
  refine ⟨T, ?_⟩
  exact Z.Zobj_eq_of_iso e

namespace ComplexPolygonalPath

/-- The oriented area functional `z ↦ r × z`, regarded as a continuous
real-linear functional on the complex plane. -/
def crossFunctional (r : ℂ) : ℂ →L[ℝ] ℝ :=
  r.re • Complex.imCLM - r.im • Complex.reCLM

@[simp]
theorem crossFunctional_apply (r z : ℂ) :
    crossFunctional r z = r.re * z.im - r.im * z.re := by
  simp [crossFunctional]

/-- The unit complex vector at angle `θ`. -/
def unitRay (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

@[simp]
theorem unitRay_re (θ : ℝ) : (unitRay θ).re = Real.cos θ := by
  simp only [unitRay, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, add_zero]

@[simp]
theorem unitRay_im (θ : ℝ) : (unitRay θ).im = Real.sin θ := by
  simp only [unitRay, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, mul_one, zero_add, add_zero]

/-- A unit ray at an angle strictly between `0` and `π` lies in the open
upper half-plane. -/
theorem unitRay_mem_upperHalfPlaneUnion {θ : ℝ} (hθ₀ : 0 < θ)
    (hθπ : θ < Real.pi) : unitRay θ ∈ upperHalfPlaneUnion := by
  rw [upperHalfPlaneUnion]
  exact Or.inl (by
    change 0 < (unitRay θ).im
    rw [unitRay_im]
    exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ)

/-- On the principal upper-half-plane branch, the argument of `unitRay θ` is
literally `θ`. -/
theorem arg_unitRay {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) :
    Complex.arg (unitRay θ) = θ := by
  unfold unitRay
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], hθπ.le⟩

/-- The cross functional is positive on a vector of strictly larger
upper-half-plane argument. -/
theorem crossFunctional_pos_of_arg_lt {r z : ℂ}
    (hr : r ∈ upperHalfPlaneUnion) (hz : z ∈ upperHalfPlaneUnion)
    (harg : Complex.arg r < Complex.arg z) :
    0 < crossFunctional r z := by
  rw [crossFunctional_apply]
  exact cross_pos_of_arg_lt (arg_pos_of_mem_upperHalfPlaneUnion hr)
    (upperHalfPlaneUnion_ne_zero hr) (upperHalfPlaneUnion_ne_zero hz) harg

/-- The cross functional is negative on a vector of strictly smaller
upper-half-plane argument. -/
theorem crossFunctional_neg_of_arg_lt {r z : ℂ}
    (hr : r ∈ upperHalfPlaneUnion) (hz : z ∈ upperHalfPlaneUnion)
    (harg : Complex.arg z < Complex.arg r) :
    crossFunctional r z < 0 := by
  have hpos := cross_pos_of_arg_lt (arg_pos_of_mem_upperHalfPlaneUnion hz)
    (upperHalfPlaneUnion_ne_zero hz) (upperHalfPlaneUnion_ne_zero hr) harg
  rw [crossFunctional_apply]
  linarith

/-- At every interior vertex of a finite path whose upper-half-plane edge
arguments strictly decrease, some real-linear functional has a strict unique
maximum among the path vertices.  This is the supporting-hyperplane form of
strict clockwise convexity. -/
theorem exists_strict_support_at_interior {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ upperHalfPlaneUnion)
    (harg : StrictAnti (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc)))
    (k : Fin (n + 1)) (hk₀ : 0 < k) (hkn : k < Fin.last n) :
    ∃ l : ℂ →L[ℝ] ℝ, ∀ j, j ≠ k → l (z j) < l (z k) := by
  let iPrev : Fin n := ⟨k.1 - 1, by omega⟩
  let iNext : Fin n := ⟨k.1, by simpa [Fin.last] using hkn⟩
  have hiPrev_lt_iNext : iPrev < iNext := by
    simp only [iPrev, iNext, Fin.mk_lt_mk]
    omega
  have hargNext_lt_argPrev :
      Complex.arg (z iNext.succ - z iNext.castSucc) <
        Complex.arg (z iPrev.succ - z iPrev.castSucc) :=
    harg hiPrev_lt_iNext
  let θ : ℝ :=
    (Complex.arg (z iPrev.succ - z iPrev.castSucc) +
      Complex.arg (z iNext.succ - z iNext.castSucc)) / 2
  have hargNext_lt_θ : Complex.arg (z iNext.succ - z iNext.castSucc) < θ := by
    dsimp [θ]
    linarith
  have hθ_lt_argPrev : θ < Complex.arg (z iPrev.succ - z iPrev.castSucc) := by
    dsimp [θ]
    linarith
  have hθ₀ : 0 < θ :=
    (arg_pos_of_mem_upperHalfPlaneUnion (hedge iNext)).trans hargNext_lt_θ
  have hθπ : θ < Real.pi :=
    hθ_lt_argPrev.trans_le (Complex.arg_le_pi _)
  let r : ℂ := unitRay θ
  let l : ℂ →L[ℝ] ℝ := crossFunctional r
  have hr : r ∈ upperHalfPlaneUnion := by
    exact unitRay_mem_upperHalfPlaneUnion hθ₀ hθπ
  have hr_arg : Complex.arg r = θ := by
    exact arg_unitRay hθ₀ hθπ
  have hstep_before : ∀ m : Fin (n + 1), m < k →
      l (z m) < l (z (Order.succ m)) := by
    intro m hm
    let i : Fin n := ⟨m.1, by omega⟩
    have hi_le : i ≤ iPrev := by
      simp only [i, iPrev, Fin.mk_le_mk]
      omega
    have hθ_lt_arg_i : θ < Complex.arg (z i.succ - z i.castSucc) :=
      hθ_lt_argPrev.trans_le (harg.antitone hi_le)
    have hpos : 0 < l (z i.succ - z i.castSucc) := by
      exact crossFunctional_pos_of_arg_lt hr (hedge i) (by
        rw [hr_arg]
        exact hθ_lt_arg_i)
    have hm_eq : m = i.castSucc := by
      apply Fin.ext
      rfl
    rw [hm_eq, Fin.orderSucc_castSucc]
    rw [map_sub] at hpos
    linarith
  have hstep_after : ∀ m : Fin (n + 1), k < m →
      l (z m) < l (z (Order.pred m)) := by
    intro m hm
    let i : Fin n := ⟨m.1 - 1, by omega⟩
    have hi_ge : iNext ≤ i := by
      simp only [iNext, i, Fin.mk_le_mk]
      omega
    have harg_i_lt_θ : Complex.arg (z i.succ - z i.castSucc) < θ :=
      (harg.antitone hi_ge).trans_lt hargNext_lt_θ
    have hneg : l (z i.succ - z i.castSucc) < 0 := by
      exact crossFunctional_neg_of_arg_lt hr (hedge i) (by
        rw [hr_arg]
        exact harg_i_lt_θ)
    have hm_eq : m = i.succ := by
      apply Fin.ext
      simp only [i, Fin.succ_mk]
      omega
    rw [hm_eq, Fin.orderPred_succ]
    rw [map_sub] at hneg
    linarith
  have hmono : StrictMonoOn (fun j : Fin (n + 1) ↦ l (z j)) (Set.Iic k) :=
    strictMonoOn_Iic_of_lt_succ hstep_before
  have hanti : StrictAntiOn (fun j : Fin (n + 1) ↦ l (z j)) (Set.Ici k) :=
    strictAntiOn_Ici_of_lt_pred hstep_after
  refine ⟨l, fun j hj ↦ ?_⟩
  rcases lt_or_gt_of_ne hj with hjk | hkj
  · exact hmono (Set.mem_Iic.mpr hjk.le) (Set.mem_Iic.mpr le_rfl) hjk
  · exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hkj.le) hkj

/-- The sum of the directed edges of a finite path is its endpoint
displacement. -/
theorem sum_edges_eq_last_sub_zero {n : ℕ} (z : Fin (n + 1) → ℂ) :
    ∑ i : Fin n, (z i.succ - z i.castSucc) = z (Fin.last n) - z 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      let z' : Fin (n + 1) → ℂ := fun i ↦ z i.castSucc
      rw [Fin.sum_univ_castSucc]
      rw [show (∑ x : Fin n, (z x.castSucc.succ - z x.castSucc.castSucc)) =
        z' (Fin.last n) - z' 0 by simpa [z'] using ih z']
      change z (Fin.last n).castSucc - z 0 +
          (z (Fin.last n).succ - z (Fin.last n).castSucc) =
        z (Fin.last (n + 1)) - z 0
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      rw [hlast]
      ring

/-- For an upper-half-plane path with decreasing edge arguments, the
argument of its total displacement is bounded above by the argument of its
first edge. -/
theorem arg_last_sub_zero_le_arg_first {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hn : 0 < n)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ upperHalfPlaneUnion)
    (harg : Antitone (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc))) :
    Complex.arg (z (Fin.last n) - z 0) ≤
      Complex.arg (z (Fin.succ ⟨0, hn⟩) - z (Fin.castSucc ⟨0, hn⟩)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let s : Finset (Fin n) := Finset.univ
  have hs : s.Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [← sum_edges_eq_last_sub_zero]
  refine (arg_sum_le_sup'_of_upperHalfPlane hs (fun i _ ↦ hedge i)).trans ?_
  apply Finset.sup'_le hs
  intro i _
  exact harg (Fin.zero_le i)

/-- The Euclidean length of a finite path in the complex plane.  A path with
`n` edges is represented by its `n + 1` vertices. -/
def length {n : ℕ} (z : Fin (n + 1) → ℂ) : ℝ :=
  ∑ i : Fin n, ‖z i.succ - z i.castSucc‖

/-- The straight chord between the endpoints of a finite complex path is no
longer than the path.  This is the metric primitive used when an HN polygonal
boundary is refined by inserting further vertices. -/
theorem norm_last_sub_zero_le_length {n : ℕ} (z : Fin (n + 1) → ℂ) :
    ‖z (Fin.last n) - z 0‖ ≤ length z := by
  induction n with
  | zero => simp [length]
  | succ n ih =>
      let z' : Fin (n + 1) → ℂ := fun i ↦ z i.castSucc
      have htriangle :
          ‖z (Fin.last (n + 1)) - z 0‖ ≤
            ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ +
              ‖z (Fin.last n).castSucc - z 0‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le
          (z (Fin.last (n + 1)) - z (Fin.last n).castSucc)
          (z (Fin.last n).castSucc - z 0)
      calc
        ‖z (Fin.last (n + 1)) - z 0‖
            ≤ ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ +
                ‖z (Fin.last n).castSucc - z 0‖ := htriangle
        _ ≤ ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ + length z' :=
          by
            simpa [z'] using add_le_add_left (ih z')
              ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖
        _ = length z := by
          unfold length
          rw [Fin.sum_univ_castSucc]
          simp [z', add_comm]

end ComplexPolygonalPath

namespace AbelianHNFiltration

variable {Z : StabilityFunction A} {E : A} (F : AbelianHNFiltration Z E)

/-- If a subobject of `S` maps trivially to the cokernel of `M → S`, it is
already contained in `M`. -/
private theorem le_of_ofLE_comp_cokernel_zero {B M S : Subobject E}
    (hBS : B ≤ S) (hMS : M ≤ S)
    (h : Subobject.ofLE B S hBS ≫
      cokernel.π (Subobject.ofLE M S hMS) = 0) : B ≤ M := by
  have hse : (ShortComplex.mk (Subobject.ofLE M S hMS)
      (cokernel.π (Subobject.ofLE M S hMS))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  let g := hse.fIsKernel.lift (KernelFork.ofι (Subobject.ofLE B S hBS) h)
  have hg : g ≫ Subobject.ofLE M S hMS = Subobject.ofLE B S hBS :=
    hse.fIsKernel.fac (KernelFork.ofι (Subobject.ofLE B S hBS) h)
      WalkingParallelPair.zero
  exact Subobject.le_of_comm g (by
    calc
      g ≫ M.arrow = g ≫ (Subobject.ofLE M S hMS ≫ S.arrow) := by
        congr 1
        exact (Subobject.ofLE_arrow hMS).symm
      _ = (g ≫ Subobject.ofLE M S hMS) ≫ S.arrow :=
        (Category.assoc _ _ _).symm
      _ = Subobject.ofLE B S hBS ≫ S.arrow :=
        congrArg (fun q ↦ q ≫ S.arrow) hg
      _ = B.arrow := Subobject.ofLE_arrow hBS)

/-- A semistable subobject whose phase is strictly larger than every HN
factor from index `k` onward is contained in the `k`-th filtration step.
This public descent lemma is the algebraic engine behind the left boundary of
the HN polygon. -/
theorem semistable_le_chain_of_phase_gt {B : Subobject E}
    (hB : Z.IsSemistable (B : A)) {k : ℕ} (hk : k ≤ F.n)
    (hphase : ∀ j : Fin F.n, k ≤ j.1 → F.φ j < Z.phase (B : A)) :
    B ≤ F.chain ⟨k, by omega⟩ := by
  suffices h : ∀ d m (hm : m < F.n + 1), F.n - m = d → k ≤ m →
      B ≤ F.chain ⟨m, hm⟩ from
    h (F.n - k) k (by omega) rfl le_rfl
  intro d
  induction d with
  | zero =>
      intro m hm hd _
      have hmn : m = F.n := by omega
      subst m
      rw [F.chain_top]
      exact le_top
  | succ d ih =>
      intro m hm hd hkm
      have hstep : B ≤ F.chain ⟨m + 1, by omega⟩ :=
        ih (m + 1) (by omega) (by omega) (by omega)
      let j : Fin F.n := ⟨m, by omega⟩
      have hj_succ_eq : (j.succ : Fin (F.n + 1)) = ⟨m + 1, by omega⟩ := by
        apply Fin.ext
        simp [j]
      have hle_jsucc : B ≤ F.chain j.succ := hj_succ_eq ▸ hstep
      have hcomp : Subobject.ofLE B (F.chain j.succ) hle_jsucc ≫
          cokernel.π (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
            (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))) = 0 :=
        hom_zero_of_semistable_phase_gt Z hB (F.factor_semistable j)
          (F.factor_phase j ▸ hphase j (by omega)) _
      exact le_of_ofLE_comp_cokernel_zero hle_jsucc
        (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) hcomp

/-- No nonzero semistable subobject has phase strictly above the first HN
factor. -/
theorem semistable_phase_le_first {B : Subobject E}
    (hB : Z.IsSemistable (B : A)) :
    Z.phase (B : A) ≤ F.φ ⟨0, F.hn⟩ := by
  by_contra hnot
  have hgt : F.φ ⟨0, F.hn⟩ < Z.phase (B : A) := lt_of_not_ge hnot
  have hle : B ≤ F.chain ⟨0, by omega⟩ :=
    F.semistable_le_chain_of_phase_gt hB (Nat.zero_le _) (fun j _ ↦
      lt_of_le_of_lt (F.φ_anti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hgt)
  rw [F.chain_bot] at hle
  have hBbot : B = ⊥ := le_bot_iff.mp hle
  exact hB.1 ((StabilityFunction.subobject_isZero_iff_eq_bot B).2 hBbot)

/-- The object represented by the `i`-th successive quotient in an abelian HN
filtration. -/
abbrev factorObj (i : Fin F.n) : A :=
  cokernel (Subobject.ofLE (F.chain i.castSucc) (F.chain i.succ)
    (le_of_lt (F.chain_strictMono i.castSucc_lt_succ)))

/-- The charge vertices of the HN polygonal path. -/
def polygonVertex (j : Fin (F.n + 1)) : ℂ := Z.Zobj (F.chain j : A)

/-- A directed edge of the distinguished HN polygonal path. -/
def polygonEdge (i : Fin F.n) : ℂ :=
  F.polygonVertex i.succ - F.polygonVertex i.castSucc

/-- The length of the distinguished, decreasing-phase boundary path of the HN
polygon. -/
def polygonLength : ℝ :=
  ComplexPolygonalPath.length F.polygonVertex

/-- The abelian HN mass: the sum of the norms of the factor charges. -/
def mass : ℝ := ∑ i : Fin F.n, ‖Z.Zobj (F.factorObj i)‖

/-- A consecutive HN polygon edge is the charge of the corresponding
semistable factor. -/
theorem polygonVertex_succ_sub (i : Fin F.n) :
    F.polygonEdge i = Z.Zobj (F.factorObj i) := by
  let f : (F.chain i.castSucc : A) ⟶ (F.chain i.succ : A) :=
    Subobject.ofLE (F.chain i.castSucc) (F.chain i.succ)
      (le_of_lt (F.chain_strictMono i.castSucc_lt_succ))
  haveI : Mono f := by dsimp [f]; infer_instance
  let S : ShortComplex A := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := StabilityFunction.shortExact_of_mono f
  have hadd := Z.additive S hS
  change Z.Zobj (F.chain i.succ : A) - Z.Zobj (F.chain i.castSucc : A) =
    Z.Zobj (cokernel f)
  change Z.Zobj (F.chain i.succ : A) =
    Z.Zobj (F.chain i.castSucc : A) + Z.Zobj (cokernel f) at hadd
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hadd)

/-- Every HN polygon edge lies in Bridgeland's semi-closed upper
half-plane. -/
theorem polygonEdge_mem_upperHalfPlaneUnion (i : Fin F.n) :
    F.polygonEdge i ∈ upperHalfPlaneUnion := by
  rw [F.polygonVertex_succ_sub i]
  exact Z.upper (F.factorObj i) (F.factor_semistable i).1

/-- The argument of an HN polygon edge is `π` times the phase of its
factor. -/
theorem polygonEdge_arg (i : Fin F.n) :
    Complex.arg (F.polygonEdge i) = Real.pi * F.φ i := by
  rw [F.polygonVertex_succ_sub i]
  calc
    Complex.arg (Z.Zobj (F.factorObj i)) =
        Real.pi * Z.phase (F.factorObj i) := by
      unfold StabilityFunction.phase
      field_simp
    _ = Real.pi * F.φ i := by rw [F.factor_phase i]

/-- HN polygon edges turn strictly clockwise: their arguments strictly
decrease along the filtration. -/
theorem polygonEdge_arg_strictAnti :
    StrictAnti (fun i : Fin F.n ↦ Complex.arg (F.polygonEdge i)) := by
  intro i j hij
  change Complex.arg (F.polygonEdge j) < Complex.arg (F.polygonEdge i)
  rw [F.polygonEdge_arg j, F.polygonEdge_arg i]
  exact mul_lt_mul_of_pos_left (F.φ_anti hij) Real.pi_pos

/-- Every interior HN vertex is a strict supporting point of the distinguished
HN path: a continuous real-linear functional has a unique maximum there among
all path vertices.  This is the path-level extremality input used by HN-polygon
containment arguments. -/
theorem polygonVertex_exists_strict_support (k : Fin (F.n + 1)) (hk₀ : 0 < k)
    (hkn : k < Fin.last F.n) :
    ∃ l : ℂ →L[ℝ] ℝ, ∀ j, j ≠ k →
      l (F.polygonVertex j) < l (F.polygonVertex k) := by
  apply ComplexPolygonalPath.exists_strict_support_at_interior F.polygonVertex
    (fun i ↦ F.polygonEdge_mem_upperHalfPlaneUnion i)
    F.polygonEdge_arg_strictAnti k hk₀ hkn

/-- The length of the HN polygonal boundary is exactly its factor mass. -/
theorem polygonLength_eq_mass : F.polygonLength = F.mass := by
  unfold polygonLength ComplexPolygonalPath.length mass
  apply Finset.sum_congr rfl
  intro i _
  rw [show F.polygonVertex i.succ - F.polygonVertex i.castSucc =
    F.polygonEdge i from rfl, F.polygonVertex_succ_sub i]

/-- The initial HN polygon vertex is the origin. -/
@[simp]
theorem polygonVertex_zero : F.polygonVertex 0 = 0 := by
  unfold polygonVertex
  have hbot : F.chain 0 = ⊥ := by
    simpa using F.chain_bot
  rw [hbot]
  exact Z.map_zero' _ ((StabilityFunction.subobject_isZero_iff_eq_bot _).2 rfl)

/-- The terminal HN polygon vertex is the charge of the filtered object. -/
@[simp]
theorem polygonVertex_last :
    F.polygonVertex ⟨F.n, Nat.lt_succ_self F.n⟩ = Z.Zobj E := by
  unfold polygonVertex
  rw [F.chain_top]
  exact Z.Zobj_eq_of_iso (asIso (⊤ : Subobject E).arrow)

/-- The phase of the filtered object is at most the phase of the first HN
factor. -/
theorem phase_le_first : Z.phase E ≤ F.φ ⟨0, F.hn⟩ := by
  have harg := ComplexPolygonalPath.arg_last_sub_zero_le_arg_first
    F.polygonVertex F.hn (fun i ↦ F.polygonEdge_mem_upperHalfPlaneUnion i)
    F.polygonEdge_arg_strictAnti.antitone
  have hlast : F.polygonVertex (Fin.last F.n) = Z.Zobj E := by
    exact F.polygonVertex_last
  rw [hlast, F.polygonVertex_zero, sub_zero,
    show F.polygonVertex (Fin.succ ⟨0, F.hn⟩) -
        F.polygonVertex (Fin.castSucc ⟨0, F.hn⟩) =
      F.polygonEdge ⟨0, F.hn⟩ from rfl,
    F.polygonVertex_succ_sub] at harg
  rw [← F.factor_phase ⟨0, F.hn⟩]
  unfold StabilityFunction.phase
  exact mul_le_mul_of_nonneg_left harg (by positivity)

/-- Assuming the HN property, every nonzero subobject has phase at most the
first phase of a chosen HN filtration.  The proof takes the first HN factor of
the subobject, embeds its first filtration step into the ambient object, and
applies semistable descent. -/
theorem subobject_phase_le_first (hHN : Z.HasHNProperty) {B : Subobject E}
    (hB : B ≠ ⊥) : Z.phase (B : A) ≤ F.φ ⟨0, F.hn⟩ := by
  have hBzero : ¬IsZero (B : A) :=
    StabilityFunction.subobject_not_isZero_of_ne_bot hB
  obtain ⟨G⟩ := hHN (B : A) hBzero
  let i₀ : Fin G.n := ⟨0, G.hn⟩
  let C₁ : Subobject (B : A) := G.chain i₀.succ
  have hchainBot : G.chain i₀.castSucc = ⊥ := by
    simpa [i₀] using G.chain_bot
  have hC₁ss : Z.IsSemistable (C₁ : A) := by
    have hfactorBot :
        Z.IsSemistable (cokernel (Subobject.ofLE ⊥ C₁ bot_le)) :=
      isSemistable_cokernel_ofLE_congr Z hchainBot.symm rfl
        (G.factor_semistable i₀)
    exact Z.isSemistable_of_iso
      (StabilityFunction.Subobject.cokernelBotIso C₁ bot_le) hfactorBot
  have hC₁phase : Z.phase (C₁ : A) = G.φ i₀ := by
    rw [← G.factor_phase i₀]
    exact ((phase_cokernel_ofLE_congr Z hchainBot rfl).trans
      (Z.phase_eq_of_iso
        (StabilityFunction.Subobject.cokernelBotIso C₁ bot_le))).symm
  let D : Subobject E := (Subobject.map B.arrow).obj C₁
  have hmap : D = Subobject.mk (C₁.arrow ≫ B.arrow) := by
    calc
      (Subobject.map B.arrow).obj C₁ =
          (Subobject.map B.arrow).obj (Subobject.mk C₁.arrow) := by
        rw [Subobject.mk_arrow]
      _ = Subobject.mk (C₁.arrow ≫ B.arrow) :=
        Subobject.map_mk C₁.arrow B.arrow
  let e : (D : A) ≅ (C₁ : A) :=
    Subobject.isoOfEqMk D (C₁.arrow ≫ B.arrow) hmap
  have hDss : Z.IsSemistable (D : A) :=
    Z.isSemistable_of_iso e.symm hC₁ss
  calc
    Z.phase (B : A) ≤ G.φ i₀ := G.phase_le_first
    _ = Z.phase (C₁ : A) := hC₁phase.symm
    _ = Z.phase (D : A) := (Z.phase_eq_of_iso e).symm
    _ ≤ F.φ ⟨0, F.hn⟩ := F.semistable_phase_le_first hDss

/-- Every vertex of the distinguished HN path lies in the ambient HN
polygon. -/
theorem polygonVertex_mem_hnPolygon (j : Fin (F.n + 1)) :
    F.polygonVertex j ∈ Z.hnPolygon E :=
  Z.subobjectCharge_mem_hnPolygon E (F.chain j)

/-- The norm of the total charge is bounded by the HN polygon length. -/
theorem norm_charge_le_polygonLength : ‖Z.Zobj E‖ ≤ F.polygonLength := by
  have h := ComplexPolygonalPath.norm_last_sub_zero_le_length F.polygonVertex
  change ‖F.polygonVertex (Fin.last F.n) - F.polygonVertex 0‖ ≤
    F.polygonLength at h
  have hlast : F.polygonVertex (Fin.last F.n) = Z.Zobj E := by
    simp [Fin.last]
  have hzero : F.polygonVertex 0 = 0 := by
    exact F.polygonVertex_zero
  simpa [hlast, hzero] using h

/-- The norm of the total charge is bounded by the sum of the HN factor
masses. -/
theorem norm_charge_le_mass : ‖Z.Zobj E‖ ≤ F.mass := by
  rw [← F.polygonLength_eq_mass]
  exact F.norm_charge_le_polygonLength

end AbelianHNFiltration

end

end CategoryTheory
