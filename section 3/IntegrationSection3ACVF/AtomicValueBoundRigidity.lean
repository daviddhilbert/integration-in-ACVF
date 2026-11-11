import IntegrationSection3ACVF.AtomicFunctionFibres
import IntegrationSection3ACVF.GammaLinearity

/-! An atomic open-ball injection cannot have every output above its
radius-scaled value bound while realizing that same scale on one pair. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.AtomicValueBoundRigidity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem impossible {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (g : M → M) (hg : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) g))
    (hgVF : ∀ x ∈ gammaBall a α true, iVF (g x)) (hinj : Set.InjOn g (gammaBall a α true))
    (s : Values.Gamma (M := M))
    (hBound : ∀ (x : VFType (M := M)) (hx : x.val ∈ gammaBall a α true),
      s.val * α.val < Values.vfValueHom (⟨g x.val,hgVF _ hx⟩ : VFType (M := M)))
    (x y : VFType (M := M)) (hx : x.val ∈ gammaBall a α true) (hy : y.val ∈ gammaBall a α true)
    (hne : y ≠ x)
    (hPair : let gx : VFType (M := M) := ⟨g x.val,hgVF _ hx⟩
      let gy : VFType (M := M) := ⟨g y.val,hgVF _ hy⟩
      Values.vfValueHom (gy-gx) = s.val * Values.vfValueHom (y-x)) : False := by
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  obtain ⟨hImAtomic,hImOpen⟩ := RVInverse.atomic_open_image B h00 δ hδ hδ1 ho hA g hg hgVF hinj
  rcases hImOpen with hAll | ⟨b,β,hImage⟩
  · exact OpenBallConstancy.atomic_not_contains_vf B hImAtomic (hAll.symm ▸ Set.Subset.rfl)
  · have hLin := GammaLinearity.ordinary hκ hs B hsmall h00 δ hδ hδ1 a α hA g hg hgVF hinj b β hImage
    have hxyVal : Values.vfValueHom (y-x) ≠ Values.infinity := by
      intro he
      have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (y-x))).mp he
      exact (sub_ne_zero.mpr hne) ((CanonicalRV.encodedRv_zero_iff (y-x)).mp hz)
    have hNZ : Values.vfValueHom (y-x) ≠ 0 := by
      simpa only [← Values.infinity_eq_zero] using hxyVal
    have hlinPair := hLin x y hx hy
    have hScale : (β/α).val = s.val := mul_right_cancel₀ hNZ (hlinPair.symm.trans hPair)
    have hβ : β = s*α := div_eq_iff_eq_mul.mp (Subtype.ext hScale : β/α = s)
    have hbIm : b.val ∈ g '' gammaBall a α true :=
      (Set.ext_iff.mp hImage b.val).mpr (BallEnlargementGeometry.gammaBall_centre_mem b β true)
    obtain ⟨u,hu,hgu⟩ := hbIm
    let uu : VFType (M := M) := ⟨u,hu.1⟩
    have hgb : (⟨g u,hgVF u hu⟩ : VFType (M := M)) = b := Subtype.ext hgu
    have hbBound := hBound uu hu
    change s.val*α.val < Values.vfValueHom (⟨g u,hgVF u hu⟩ : VFType (M := M)) at hbBound
    rw [hgb] at hbBound
    have hbValue : β.val < Values.vfValueHom b := by
      rw [hβ,Values.gamma_val_mul]
      exact hbBound
    obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative β
    have hbr : v b < v r := by
      apply lt_of_not_ge
      intro he
      have h := (Values.vf_pred_iff_gamma_le r b).mp ((hv r b).mpr he)
      rw [hr] at h
      exact not_le_of_gt hbValue h
    have h0Ball : (0 : VFType (M := M)).val ∈ gammaBall b β true := by
      apply (GammaCosetGeometry.gammaBall_mem_valuation v hv b r β hr 0).mpr
      simpa only [zero_sub,Valuation.map_neg] using hbr
    have h0Im : (0 : VFType (M := M)).val ∈ g '' gammaBall a α true :=
      (Set.ext_iff.mp hImage _).mpr h0Ball
    have hnAlg := AtomicFunctionFibres.no_algebraic_point B h00 δ hδ1
      (Or.inr ⟨b,β,hImage⟩) hImAtomic 0 h0Im
    apply hnAlg
    exact (definableClosureAt_function_symbol B.real Fn.vfZero Fin.elim0
      (fun j => j.elim0) (fun j => j.elim0)).algebraic

end IntegrationInACVF.Section3ACVF.AtomicValueBoundRigidity
