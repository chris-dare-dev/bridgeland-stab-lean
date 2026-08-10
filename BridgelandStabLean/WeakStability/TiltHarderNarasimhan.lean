/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.WeakStability.HarderNarasimhan
import BridgelandStabLean.WeakStability.TiltNoetherian

/-!
# Harder--Narasimhan reduction after phase tilting

This file isolates the cohomological quotient step used in Proposition 19.5
and in the weak-HN part of Proposition 14.16.  If the last original HN factor
of `F` is `U`, then quotienting an extension of `F[1]` by the shifted prefix
first produces an extension of `U[1]` by a zero-charge object.  Saturating
that extension gives the last tilted semistable quotient.  The kernel of the
composite quotient is again an extension of the shifted prefix by a
zero-charge object, which is the recursive state for the shorter original
HN filtration.

The theorem below assumes that the shifted last factor is already
right-orthogonal to zero-charge objects.  The boundary-phase saturation that
produces this hypothesis is deliberately kept separate from the
kernel--cokernel calculation formalized here.
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

namespace WeakPreStabilityCondition

/-- **The `H⁻¹` last-factor reduction.**

Suppose `G ⟶ F ⟶ U` is the last step of an original HN filtration,
and `F[1] ⟶ E ⟶ V` is an extension by a tilted zero-charge object.
If the shifted semistable factor `U[1]` is saturated, then `E` has a
semistable quotient `B` with the charge of `U[1]`.  Its kernel `K` fits into
an extension `G[1] ⟶ K ⟶ A` with `A` zero-charge.

Thus the first triangle removes the last original HN factor, while the
second triangle is exactly the recursive input attached to the prefix. -/
theorem phaseTilt_hnLastQuotient_of_saturatedFactor
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hdec : WeakStabilityFunction.HasZeroChargeDecompositions
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1))
    {G F U V E : C}
    (hGfree : phaseFree sigma.slicing beta G)
    (hFfree : phaseFree sigma.slicing beta F)
    (hUfree : phaseFree sigma.slicing beta U)
    (hUss : sigma.weakStabilityFunctionOnHeart.IsSemistable U)
    (hUcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
        (U⟦(1 : ℤ)⟧) ≠ 0)
    (hUorth : rightOrthogonal
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge
      (U⟦(1 : ℤ)⟧))
    (hV : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge V)
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    {f : G ⟶ F} {g : F ⟶ U} {d : U ⟶ G⟦(1 : ℤ)⟧}
    (hGFU : Triangle.mk f g d ∈ distTriang C)
    {i : F⟦(1 : ℤ)⟧ ⟶ E} {p : E ⟶ V}
    {delta : V ⟶ F⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
    (hFEV : Triangle.mk i p delta ∈ distTriang C) :
    ∃ (K A B : C)
      (_ : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart K)
      (_ : (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge A)
      (_ : rightOrthogonal
        (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge B)
      (k : K ⟶ E) (q : E ⟶ B) (dk : B ⟶ K⟦(1 : ℤ)⟧),
        Triangle.mk k q dk ∈ distTriang C ∧
          ∃ (u : G⟦(1 : ℤ)⟧ ⟶ K) (r : K ⟶ A)
            (du : A ⟶ G⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
              Triangle.mk u r du ∈ distTriang C ∧
                (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable B ∧
                (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge B =
                  (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
                    (U⟦(1 : ℤ)⟧) := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  have hGshift : P.tilt.heart (G⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hGfree
  have hFshift : P.tilt.heart (F⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hFfree
  have hUshift : P.tilt.heart (U⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hUfree
  let GH : H := ⟨G⟦(1 : ℤ)⟧, hGshift⟩
  let FH : H := ⟨F⟦(1 : ℤ)⟧, hFshift⟩
  let UH : H := ⟨U⟦(1 : ℤ)⟧, hUshift⟩
  let EH : H := ⟨E, hE⟩
  let VH : H := ⟨V, hV.1⟩
  let Tshift := (shiftFunctor (Triangle C) (1 : ℤ)).obj (Triangle.mk f g d)
  have hTshift : Tshift ∈ distTriang C :=
    Triangle.shift_distinguished (Triangle.mk f g d) hGFU 1
  let fH : GH ⟶ FH := ObjectProperty.homMk Tshift.mor₁
  let gH : FH ⟶ UH := ObjectProperty.homMk Tshift.mor₂
  have hfg : fH ≫ gH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hTshift
  have hPrefix : (ShortComplex.mk fH gH hfg).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := GH) (B := FH) (Q := UH)
        (f := fH) (g := gH) (δ := Tshift.mor₃) hTshift
  let iH : FH ⟶ EH := ObjectProperty.homMk i
  let pH : EH ⟶ VH := ObjectProperty.homMk p
  have hip : iH ≫ pH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hFEV
  have hOuter : (ShortComplex.mk iH pH hip).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := FH) (B := EH) (Q := VH)
        (f := iH) (g := pH) (δ := delta) hFEV
  letI : Mono fH := hPrefix.mono_f
  letI : Mono iH := hOuter.mono_f
  let Rseq := cokernelCompShortComplex fH iH
  have hRseq : Rseq.ShortExact := cokernelCompShortComplex_shortExact fH iH
  let eU : Rseq.X₁ ≅ UH :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel fH)
      hPrefix.gIsCokernel
  let eV : Rseq.X₃ ≅ VH :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel iH)
      hOuter.gIsCokernel
  let jR : UH ⟶ Rseq.X₂ := eU.inv ≫ Rseq.f
  let pR : Rseq.X₂ ⟶ VH := Rseq.g ≫ eV.hom
  have hjp : jR ≫ pR = 0 := by
    simp [jR, pR, Rseq]
  let Sred : ShortComplex H := ShortComplex.mk jR pR hjp
  let eRed : Rseq ≅ Sred :=
    ShortComplex.isoMk eU (Iso.refl _) eV
  have hSred : Sred.ShortExact :=
    ShortComplex.shortExact_of_iso eRed hRseq
  letI : Mono jR := hSred.mono_f
  letI : Epi pR := hSred.epi_g
  obtain ⟨dR, hdR⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt jR pR hjp (fun {X} x hx => by
      exact ⟨hSred.fIsKernel.lift (KernelFork.ofι x hx),
        hSred.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  obtain ⟨A, B, hA, hB, a, qR, dA, hAB, hBss, hBcharge⟩ :=
    sigma.phaseTilt_semistableQuotient_of_saturatedExtension
      beta hbeta0 hbeta1 hdec hUfree hUss hUcharge hV
        Rseq.X₂.property hUorth hdR
  let AH : H := ⟨A, hA.1⟩
  let BH : H := ⟨B, hB.1⟩
  let aH : AH ⟶ Rseq.X₂ := ObjectProperty.homMk a
  let qRH : Rseq.X₂ ⟶ BH := ObjectProperty.homMk qR
  have haq : aH ≫ qRH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hAB
  have hSat : (ShortComplex.mk aH qRH haq).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt (A := AH) (B := Rseq.X₂) (Q := BH)
        (f := aH) (g := qRH) (δ := dA) hAB
  let e : EH ⟶ Rseq.X₂ := cokernel.π (fH ≫ iH)
  have hfe : (fH ≫ iH) ≫ e = 0 := cokernel.condition (fH ≫ iH)
  haveI : Epi e := by
    change Epi (coequalizer.π (fH ≫ iH) 0)
    infer_instance
  let qTotal : EH ⟶ BH := e ≫ qRH
  haveI : Epi qRH := hSat.epi_g
  haveI : Epi qTotal := by
    dsimp [qTotal]
    infer_instance
  let KH : H := kernel qTotal
  let kH : KH ⟶ EH := kernel.ι qTotal
  have hkq : kH ≫ qTotal = 0 := kernel.condition qTotal
  have hFinal : (ShortComplex.mk kH qTotal hkq).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel qTotal)
      inferInstance inferInstance
  obtain ⟨dk, hdk⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt kH qTotal hkq (fun {X} x hx => by
      exact ⟨hFinal.fIsKernel.lift (KernelFork.ofι x hx),
        hFinal.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  let Direct : ShortComplex H := ShortComplex.mk (fH ≫ iH) e hfe
  have hDirect : Direct.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (fH ≫ iH))
      inferInstance inferInstance
  let Kseq := kernelCompShortComplex e qRH
  have hKseq : Kseq.ShortExact := kernelCompShortComplex_shortExact e qRH
  let eG : Kseq.X₁ ≅ GH :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel e) hDirect.fIsKernel
  let eK : Kseq.X₂ ≅ KH := by
    dsimp [Kseq, kernelCompShortComplex, qTotal, KH]
    exact Iso.refl _
  let eA : Kseq.X₃ ≅ AH :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel qRH) hSat.fIsKernel
  let uK : GH ⟶ KH := eG.inv ≫ Kseq.f ≫ eK.hom
  let rK : KH ⟶ AH := eK.inv ≫ Kseq.g ≫ eA.hom
  have hur : uK ≫ rK = 0 := by
    simp [uK, rK, Kseq]
  let Sker : ShortComplex H := ShortComplex.mk uK rK hur
  let eKer : Kseq ≅ Sker := ShortComplex.isoMk eG eK eA
    (by
      change eG.hom ≫ (eG.inv ≫ Kseq.f ≫ eK.hom) =
        Kseq.f ≫ eK.hom
      simp)
    (by
      change eK.hom ≫ (eK.inv ≫ Kseq.g ≫ eA.hom) =
        Kseq.g ≫ eA.hom
      simp)
  have hSker : Sker.ShortExact :=
    ShortComplex.shortExact_of_iso eKer hKseq
  letI : Mono uK := hSker.mono_f
  letI : Epi rK := hSker.epi_g
  obtain ⟨du, hdu⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) P.tilt uK rK hur (fun {X} x hx => by
      exact ⟨hSker.fIsKernel.lift (KernelFork.ofι x hx),
        hSker.fIsKernel.fac (KernelFork.ofι x hx)
          WalkingParallelPair.zero⟩)
  exact ⟨KH.obj, A, B, KH.property, hA, hB,
    kH.hom, qTotal.hom, dk, hdk,
    uK.hom, rK.hom, du, hdu, hBss, hBcharge⟩

end WeakPreStabilityCondition

end

end BridgelandStabLean.WeakStability
