/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.WeakStability.TiltSemistable
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Noetherian zero-charge objects after phase tilting

This file proves the noetherianity part of the zero-charge comparison needed
for Proposition 14.16.  The tilted weak function has exactly the original
zero-charge objects.  A subobject of such an object in the tilted heart again
has zero charge; its quotient therefore has zero charge as well.  The
zero-charge comparison puts all three terms back in the original heart, so
the same distinguished triangle exhibits an original-heart subobject.

Consequently the original `NoetherianTorsionSubcategory` chain condition
applies to every tilted-heart subobject chain of a zero-charge object.  The
result is stated using Mathlib's standard `IsNoetherianObject`, which supplies
the well-founded subobject order used to choose maximal zero-charge
subobjects in the remaining torsion-pair assembly.
-/

namespace BridgelandStabLean.WeakStability

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open BridgelandStabLean.Tilting
open scoped ZeroObject

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

variable {Lambda : Type*} [AddCommGroup Lambda]
variable {v : K₀ C →+ Lambda}

/-- In a heart short exact sequence `0 → Q → E → N → 0`, if
`Q` is right-orthogonal to zero-charge objects, then every zero-charge
subobject of `E` maps monomorphically to `N`.

This is the kernel/image argument behind the injectivity sentence in the
proof of Proposition 14.16. -/
theorem mono_comp_of_zeroCharge_of_rightOrthogonal
    (t : TStructure C) (W : WeakStabilityFunction t)
    (S : ShortComplex t.heart.FullSubcategory) (hS : S.ShortExact)
    {A : t.heart.FullSubcategory} (a : A ⟶ S.X₂) [Mono a]
    (hA : W.zeroCharge A.obj)
    (hQ : rightOrthogonal t W.zeroCharge S.X₁.obj) : Mono (a ≫ S.g) := by
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let k : kernel (a ≫ S.g) ⟶ A := kernel.ι (a ≫ S.g)
  have hkzero : W.zeroCharge (kernel (a ≫ S.g)).obj := by
    obtain ⟨hK, -, QK, hQK, q, d, hd⟩ :=
      isHeartMono_of_mono t k
    exact W.zeroCharge_left hK hQK hA hd
  have hcomp : (k ≫ a) ≫ S.g = 0 := by
    simpa only [Category.assoc] using kernel.condition (a ≫ S.g)
  let u : kernel (a ≫ S.g) ⟶ S.X₁ :=
    hS.fIsKernel.lift (KernelFork.ofι (k ≫ a) hcomp)
  have hu_fac : u ≫ S.f = k ≫ a :=
    hS.fIsKernel.fac (KernelFork.ofι (k ≫ a) hcomp)
      WalkingParallelPair.zero
  have hu_zero_ambient : u.hom = 0 := hQ.2 _ hkzero u.hom
  have hu_zero : u = 0 := by
    ext
    exact hu_zero_ambient
  apply Abelian.mono_of_kernel_ι_eq_zero
  apply (cancel_mono a).mp
  rw [← hu_fac, hu_zero, zero_comp]
  simp

/-- A morphism from an original zero-charge object to an original
phase-torsion object which is monic in the tilted heart is already monic in
the original heart.  Its original-heart kernel is again zero-charge, hence is
an object of the tilted heart; tilted monicity then forces that kernel to
vanish. -/
theorem mono_in_originalHeart_of_mono_in_phaseTilt
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    {A N : sigma.slicing.toTStructure.heart.FullSubcategory}
    (hA : sigma.zeroCharge A.obj)
    (hN : phaseTors sigma.slicing beta N.obj)
    (f : A ⟶ N)
    (hmono : Mono (ObjectProperty.homMk f.hom :
      (⟨A.obj,
        ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
          beta hbeta0 hbeta1 A.obj).mpr hA).1⟩ :
          ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart.FullSubcategory)
        ⟶
      ⟨N.obj, (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tors_mem_tilt_heart
        hN⟩)) : Mono f := by
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let At : P.tilt.heart.FullSubcategory :=
    ⟨A.obj, ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 A.obj).mpr hA).1⟩
  let Nt : P.tilt.heart.FullSubcategory := ⟨N.obj, P.tors_mem_tilt_heart hN⟩
  let ft : At ⟶ Nt := ObjectProperty.homMk f.hom
  letI : Mono ft := by simpa [ft, At, Nt] using hmono
  let k : kernel f ⟶ A := kernel.ι f
  have hkzero : sigma.zeroCharge (kernel f).obj := by
    obtain ⟨hK, -, QK, hQK, q, d, hd⟩ := isHeartMono_of_mono t k
    exact sigma.weakStabilityFunctionOnHeart.zeroCharge_left hK hQK hA hd
  let Kt : P.tilt.heart.FullSubcategory :=
    ⟨(kernel f).obj,
      ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 (kernel f).obj).mpr hkzero).1⟩
  let kt : Kt ⟶ At := ObjectProperty.homMk k.hom
  have hktf : kt ≫ ft = 0 := by
    ext
    simp [kt, ft, k]
  have hkt : kt = 0 := (cancel_mono ft).mp (by simpa using hktf)
  apply Abelian.mono_of_kernel_ι_eq_zero
  ext
  simpa [kt, k] using congrArg (fun u : Kt ⟶ At ↦ u.hom) hkt

namespace WeakPreStabilityCondition

/-- Original zero-charge objects lie in the phase-torsion class at every
cutoff below `1`. -/
theorem zeroCharge_phaseTors
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) (hbeta1 : beta < 1)
    {E : C} (hE : sigma.zeroCharge E) :
    phaseTors sigma.slicing beta E := by
  have hP := sigma.zeroCharge_mem_P_one hE.1 hE.2
  exact ⟨sigma.slicing.gtProp_of_semistable C 1 beta E hP hbeta1,
    sigma.slicing.leProp_of_semistable C 1 1 E hP le_rfl⟩

/-- A phase-compatible tilting envelope rotates to a zero-charge subobject of
`F[1]` in the tilted heart whose quotient is right-orthogonal to all
zero-charge objects.  This formalizes the first short exact sequence used in
the proof of Proposition 14.16. -/
theorem phaseTiltingEnvelope_gives_shiftedZeroChargeDecomposition
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {F : C}
    (hF : phaseFree sigma.slicing beta F)
    (henv : sigma.HasPhaseTiltingEnvelope beta F) :
    ∃ (A Q : C)
      (_ : (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt.heart
        (F⟦(1 : ℤ)⟧))
      (_ : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge A)
      (_ : rightOrthogonal
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge Q)
      (i : A ⟶ F⟦(1 : ℤ)⟧) (p : F⟦(1 : ℤ)⟧ ⟶ Q)
      (d : Q ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk i p d ∈ distTriang C := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  obtain ⟨Ftilde, F0, hFtilde, hF0, i, p, d, hd, hhom⟩ := henv
  have hF0new : W.zeroCharge F0 :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 F0).mpr hF0
  have hQheart : P.tilt.heart (Ftilde⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hFtilde
  have hFheart : P.tilt.heart (F⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hF
  have hQorth : rightOrthogonal P.tilt W.zeroCharge (Ftilde⟦(1 : ℤ)⟧) := by
    refine ⟨hQheart, ?_⟩
    intro A0 hA0 f
    exact hhom A0
      ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 A0).mp hA0) f
  exact ⟨F0, Ftilde⟦(1 : ℤ)⟧, hFheart, hF0new, hQorth, d, -i⟦(1 : ℤ)⟧',
    -p⟦(1 : ℤ)⟧', by
      simpa using rot_of_distTriang (Triangle.mk i p d).rotate
        (rot_of_distTriang (Triangle.mk i p d) hd)⟩

/-- **The chain-transfer step in Proposition 14.16.**

Suppose `0 → Q → E → N → 0` is short exact in the tilted heart,
`Q` is right-orthogonal to tilted zero-charge objects, and `N` is an original
phase-torsion object.  Every chain of zero-charge subobjects of `E` then maps
monomorphically to a chain of original zero-charge subobjects of `N`, so the
original noetherian torsion hypothesis forces it to terminate. -/
theorem phaseTilt_zeroChargeChain_terminates_of_rightOrthogonal
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N0 : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN0 : N0.pair.tors = sigma.zeroCharge)
    (S : ShortComplex
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart.FullSubcategory)
    (hS : S.ShortExact)
    (hQ : rightOrthogonal
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge S.X₁.obj)
    (hN : phaseTors sigma.slicing beta S.X₃.obj)
    (c : SubobjectChain
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge
      S.X₂.obj) : c.Terminates := by
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : Abelian P.tilt.heart.FullSubcategory := P.tilt.heartFullSubcategoryAbelian
  have propOld (j : ℕ) : sigma.zeroCharge (c.obj j) :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 (c.obj j)).mp (c.prop j)
  let AH (j : ℕ) : P.tilt.heart.FullSubcategory :=
    ⟨c.obj j, (c.toAmbient_mono j).1⟩
  let AOld (j : ℕ) : t.heart.FullSubcategory :=
    ⟨c.obj j, (propOld j).1⟩
  let NOld : t.heart.FullSubcategory :=
    ⟨S.X₃.obj, mem_heart_of_bounds sigma.slicing
      (sigma.slicing.gtProp_anti C hbeta0 S.X₃.obj hN.1) hN.2⟩
  let stepSharp (j : ℕ) : AH j ⟶ AH (j + 1) :=
    ObjectProperty.homMk (c.step j)
  have stepSharp_mono (j : ℕ) : Mono (stepSharp j) :=
    mono_of_isHeartMono P.tilt (stepSharp j) (c.step_mono j)
  let stepOld (j : ℕ) : AOld j ⟶ AOld (j + 1) :=
    ObjectProperty.homMk (c.step j)
  have stepOld_mono (j : ℕ) : Mono (stepOld j) := by
    apply mono_in_originalHeart_of_mono_in_phaseTilt
      sigma beta hbeta0 hbeta1 (propOld j)
        (sigma.zeroCharge_phaseTors beta hbeta1 (propOld (j + 1)))
    simpa [stepSharp, stepOld, AH, AOld] using stepSharp_mono j
  let aSharp (j : ℕ) : AH j ⟶ S.X₂ :=
    ObjectProperty.homMk (c.toAmbient j)
  have aSharp_mono (j : ℕ) : Mono (aSharp j) :=
    mono_of_isHeartMono P.tilt (aSharp j) (c.toAmbient_mono j)
  have compSharp_mono (j : ℕ) : Mono (aSharp j ≫ S.g) := by
    letI : Mono (aSharp j) := aSharp_mono j
    exact mono_comp_of_zeroCharge_of_rightOrthogonal
      P.tilt W S hS (aSharp j) (c.prop j) hQ
  let toNOld (j : ℕ) : AOld j ⟶ NOld :=
    ObjectProperty.homMk (c.toAmbient j ≫ S.g.hom)
  have toNOld_mono (j : ℕ) : Mono (toNOld j) := by
    apply mono_in_originalHeart_of_mono_in_phaseTilt
      sigma beta hbeta0 hbeta1 (propOld j) hN
    simpa [aSharp, toNOld, AH, AOld, NOld] using compSharp_mono j
  let cOld : SubobjectChain t sigma.zeroCharge S.X₃.obj :=
    { obj := c.obj
      prop := propOld
      step := c.step
      toAmbient := fun j => c.toAmbient j ≫ S.g.hom
      step_mono := fun j => isHeartMono_of_mono t (stepOld j)
      toAmbient_mono := fun j => isHeartMono_of_mono t (toNOld j)
      comm := fun j => by
        rw [← Category.assoc, c.comm j] }
  apply noetherian_mono (t := t)
    (fun X hX => by rw [hN0]; exact hX) N0.noetherian
    S.X₃.obj NOld.property cOld

/-- Every tilted-heart zero-charge object is noetherian when the original
zero-charge class is the torsion class of a noetherian torsion subcategory.

This is independent of the still-open construction of the zero-charge
torsion pair on the whole tilted heart: it proves the intrinsic
noetherianity of the objects which will form that torsion class. -/
theorem phaseTilt_isNoetherianObject_of_zeroCharge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN : N.pair.tors = sigma.zeroCharge)
    (E : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart.FullSubcategory)
    (hE : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge E.obj) :
    IsNoetherianObject E := by
  let t := sigma.slicing.toTStructure
  let tsharp := (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  letI : Abelian tsharp.heart.FullSubcategory :=
    tsharp.heartFullSubcategoryAbelian
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let step (i : ℕ) :
      (f i : tsharp.heart.FullSubcategory) ⟶
        (f (i + 1) : tsharp.heart.FullSubcategory) :=
    Subobject.ofLE (f i) (f (i + 1)) (f.monotone (Nat.le_succ i))
  have propNew (i : ℕ) : W.zeroCharge (f i : tsharp.heart.FullSubcategory).obj := by
    let Q : tsharp.heart.FullSubcategory := cokernel (f i).arrow
    let p : E ⟶ Q := cokernel.π (f i).arrow
    have hp : (f i).arrow ≫ p = 0 := cokernel.condition (f i).arrow
    have hshort : (ShortComplex.mk (f i).arrow p hp).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (f i).arrow)
        inferInstance inferInstance
    obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle
      (C := C) tsharp (f i).arrow p hp (fun {X} a ha => by
        exact ⟨hshort.fIsKernel.lift (KernelFork.ofι a ha),
          hshort.fIsKernel.fac (KernelFork.ofι a ha) WalkingParallelPair.zero⟩)
    exact W.zeroCharge_left (f i : tsharp.heart.FullSubcategory).property
      Q.property hE hd
  have propOld (i : ℕ) : sigma.zeroCharge (f i : tsharp.heart.FullSubcategory).obj :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 (f i : tsharp.heart.FullSubcategory).obj).mp (propNew i)
  have step_mono_old (i : ℕ) : IsHeartMono t (step i).hom := by
    obtain ⟨hA, hB, Q, hQ, g, d, hd⟩ :=
      isHeartMono_of_mono tsharp (step i)
    have hQzero : W.zeroCharge Q :=
      W.zeroCharge_right hA hQ (propNew (i + 1)) hd
    have hQold : sigma.zeroCharge Q :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 Q).mp hQzero
    exact ⟨(propOld i).1, (propOld (i + 1)).1, Q, hQold.1, g, d, hd⟩
  have toAmbient_mono_old (i : ℕ) : IsHeartMono t (f i).arrow.hom := by
    obtain ⟨hA, -, Q, hQ, g, d, hd⟩ :=
      isHeartMono_of_mono tsharp (f i).arrow
    have hQzero : W.zeroCharge Q := W.zeroCharge_right hA hQ hE hd
    have hQold : sigma.zeroCharge Q :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 Q).mp hQzero
    have hEold : sigma.zeroCharge E.obj :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0 hbeta1 E.obj).mp hE
    exact ⟨(propOld i).1, hEold.1, Q, hQold.1, g, d, hd⟩
  have prop (i : ℕ) : N.pair.tors (f i : tsharp.heart.FullSubcategory).obj := by
    rw [hN]
    exact propOld i
  let c : SubobjectChain t N.pair.tors E.obj :=
    { obj := fun i => (f i : tsharp.heart.FullSubcategory).obj
      prop := prop
      step := fun i => (step i).hom
      toAmbient := fun i => (f i).arrow.hom
      step_mono := step_mono_old
      toAmbient_mono := toAmbient_mono_old
      comm := fun i => by
        exact congrArg
          (fun k : (f i : tsharp.heart.FullSubcategory) ⟶ E => k.hom)
          (Subobject.ofLE_arrow (f.monotone (Nat.le_succ i))) }
  have hEold : sigma.zeroCharge E.obj :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
      beta hbeta0 hbeta1 E.obj).mp hE
  obtain ⟨n, hn⟩ := N.noetherian E.obj hEold.1 c
  refine ⟨n, fun m hnm => ?_⟩
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      rw [ih]
      let u : (f m : tsharp.heart.FullSubcategory) ⟶
          (f (m + 1) : tsharp.heart.FullSubcategory) := step m
      haveI : IsIso u.hom := hn m hnm
      let e : (f m : tsharp.heart.FullSubcategory) ≅
          (f (m + 1) : tsharp.heart.FullSubcategory) :=
        { hom := u
          inv := ObjectProperty.homMk (inv u.hom)
          hom_inv_id := by ext; simp
          inv_hom_id := by ext; simp }
      exact Subobject.eq_of_comm e
        (Subobject.ofLE_arrow (f.monotone (Nat.le_succ m)))

/-- Once the original zero-charge objects have been made into a torsion pair
on the tilted heart, their intrinsic noetherianity upgrades that pair to a
`NoetherianTorsionSubcategory`.

The proof factors every chain of torsion subobjects through the torsion term
of the chosen torsion/free decomposition.  That term has zero charge, hence
is a noetherian object by
`phaseTilt_isNoetherianObject_of_zeroCharge`; stabilization in its standard
subobject lattice forces the original chain maps to be isomorphisms. -/
noncomputable def phaseTiltNoetherianTorsionSubcategory
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN : N.pair.tors = sigma.zeroCharge)
    (Psharp : HeartTorsionPair
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt)
    (hP : Psharp.tors =
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt where
  pair := Psharp
  noetherian E hE c := by
    let tsharp := (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
    let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
    letI : Abelian tsharp.heart.FullSubcategory :=
      tsharp.heartFullSubcategoryAbelian
    obtain ⟨hLE, hGE⟩ := (TStructure.mem_heart_iff tsharp E).mp hE
    obtain ⟨T, F, hT, hF, i, p, d, hd⟩ :=
      Psharp.exists_triangle E hLE hGE
    let TH : tsharp.heart.FullSubcategory :=
      ⟨T, (TStructure.mem_heart_iff tsharp T).mpr
        ⟨Psharp.tors_isLE T hT, Psharp.tors_isGE T hT⟩⟩
    let EH : tsharp.heart.FullSubcategory := ⟨E, hE⟩
    let FH : tsharp.heart.FullSubcategory :=
      ⟨F, (TStructure.mem_heart_iff tsharp F).mpr
        ⟨Psharp.free_isLE F hF, Psharp.free_isGE F hF⟩⟩
    let iH : TH ⟶ EH := ObjectProperty.homMk i
    let pH : EH ⟶ FH := ObjectProperty.homMk p
    have hip : iH ≫ pH = 0 := by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hd
    have hshort := TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) tsharp (A := TH) (B := EH) (Q := FH)
        (f := iH) (g := pH) (δ := d) hd
    letI : Mono iH := hshort.mono_f
    let AH (j : ℕ) : tsharp.heart.FullSubcategory :=
      ⟨c.obj j, (c.toAmbient_mono j).1⟩
    let a (j : ℕ) : AH j ⟶ EH := ObjectProperty.homMk (c.toAmbient j)
    haveI a_mono (j : ℕ) : Mono (a j) :=
      mono_of_isHeartMono tsharp (a j) (c.toAmbient_mono j)
    have hap (j : ℕ) : a j ≫ pH = 0 := by
      ext
      exact Psharp.hom_eq_zero (c.prop j) hF (c.toAmbient j ≫ p)
    let g (j : ℕ) : AH j ⟶ TH :=
      hshort.fIsKernel.lift (KernelFork.ofι (a j) (hap j))
    have hgi (j : ℕ) : g j ≫ iH = a j :=
      hshort.fIsKernel.fac (KernelFork.ofι (a j) (hap j))
        WalkingParallelPair.zero
    haveI g_mono (j : ℕ) : Mono (g j) := by
      constructor
      intro X u w huw
      apply (cancel_mono (a j)).mp
      rw [← hgi j, ← Category.assoc, ← Category.assoc, huw]
    let stepH (j : ℕ) : AH j ⟶ AH (j + 1) :=
      ObjectProperty.homMk (c.step j)
    have hstep (j : ℕ) : stepH j ≫ g (j + 1) = g j := by
      apply (cancel_mono iH).mp
      rw [Category.assoc, hgi (j + 1), hgi j]
      ext
      exact c.comm j
    let sub (j : ℕ) : Subobject TH := Subobject.mk (g j)
    have hsub_succ (j : ℕ) : sub j ≤ sub (j + 1) :=
      Subobject.mk_le_mk_of_comm (stepH j) (hstep j)
    let subChain : ℕ →o Subobject TH :=
      ⟨sub, monotone_nat_of_le_succ hsub_succ⟩
    have hTzero : W.zeroCharge TH.obj := by
      rw [← hP]
      exact hT
    letI : IsNoetherianObject TH :=
      sigma.phaseTilt_isNoetherianObject_of_zeroCharge beta hbeta0 hbeta1
        N hN TH hTzero
    obtain ⟨n, hn⟩ :=
      monotone_chain_condition_of_isNoetherianObject subChain
    refine ⟨n, fun j hnj => ?_⟩
    let sj : AH j ⟶ AH (j + 1) := stepH j
    haveI : Mono sj :=
      mono_of_isHeartMono tsharp sj (c.step_mono j)
    have heq : Subobject.mk (g j) = Subobject.mk (g (j + 1)) := by
      change subChain j = subChain (j + 1)
      exact (hn j hnj).symm.trans (hn (j + 1) (by omega))
    haveI : IsIso sj := by
      by_contra hnot
      have hlt : Subobject.mk (g j) < Subobject.mk (g (j + 1)) :=
        Subobject.mk_lt_mk_of_comm sj (hstep j) hnot
      rw [heq] at hlt
      exact (lt_irrefl _) hlt
    simpa [sj, stepH] using
      (tsharp.heart.ι.mapIso (asIso sj)).isIso_hom

/-- Termination of zero-charge subobject chains in every tilted-heart object
produces the zero-charge torsion decompositions by the maximal-subobject
construction in `Noetherian.lean`.

This is the precise order-theoretic seam in the proof of Proposition 14.16:
the envelope argument is responsible only for this relative chain condition;
images, pullbacks, right orthogonality, and the resulting torsion pair are
then automatic. -/
theorem phaseTilt_hasZeroChargeDecompositions_of_chainCondition
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hacc : ∀ (E : C),
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E →
      ∀ c : SubobjectChain
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge E,
        c.Terminates) :
    WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) :=
  WeakStabilityFunction.hasZeroChargeDecompositions_of_chainCondition
    (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) hacc

/-- The noetherian zero-charge obligation after tilting, assembled directly
from zero-charge decompositions in the tilted heart.  This removes the
intermediate `HeartTorsionPair` parameter from
`phaseTiltNoetherianTorsionSubcategory`: once the maximal-subobject argument
has produced the decompositions, both the torsion pair and its chain condition
are automatic. -/
noncomputable def phaseTiltNoetherianTorsionSubcategoryOfDecompositions
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (N : NoetherianTorsionSubcategory sigma.slicing.toTStructure)
    (hN : N.pair.tors = sigma.zeroCharge)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt := by
  let tsharp := (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  exact sigma.phaseTiltNoetherianTorsionSubcategory beta hbeta0 hbeta1 N hN
    (W.zeroChargeTorsionPair tsharp hdec) rfl

/-- Definition 14.12(1) supplies the original noetherian torsion class, so
after the maximal-subobject argument has produced tilted zero-charge
decompositions, the full noetherian torsion obligation of Proposition 14.16
is assembled without any further input. -/
noncomputable def phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt := by
  let N := Classical.choose htilt.zeroCharge_noetherian
  have hN : N.pair.tors = sigma.zeroCharge :=
    Classical.choose_spec htilt.zeroCharge_noetherian
  exact sigma.phaseTiltNoetherianTorsionSubcategoryOfDecompositions
    beta hbeta0 hbeta1 N hN hdec

/-- The full noetherian zero-charge torsion structure, with the relative
chain condition as its only remaining envelope-level input. -/
noncomputable def phaseTiltNoetherianTorsionSubcategoryOfChainCondition
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (hacc : ∀ (E : C),
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E →
      ∀ c : SubobjectChain
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge E,
        c.Terminates) :
    NoetherianTorsionSubcategory
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt :=
  sigma.phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
    beta hbeta0 hbeta1 htilt
      (sigma.phaseTilt_hasZeroChargeDecompositions_of_chainCondition
        beta hbeta0 hbeta1 hacc)

end WeakPreStabilityCondition

end

end BridgelandStabLean.WeakStability
