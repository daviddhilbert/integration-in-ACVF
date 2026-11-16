module

public import Integration7.GammaCorrectedBlowupMaps
public import Integration7.GammaBlowupHeadJacobians
public import Integration7.ElementaryBlowupIsomorphism

@[expose] public section

/-! Elementary comparison can retain the original Gamma parameter base.
The actual volume Jacobian proof uses the same corrected map, now with a
Gamma head Jacobian and Gamma packed essential charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem exists_gamma_elementaryBlowupIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M))
    {U V WU WV : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U V) (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV)
    (hU : RVMapGamma U.underlying.obj.volume B)
    (hV : RVMapGamma V.underlying.obj.volume B)
    (hω : RVMapGamma U.form.map B) (hπ : RVMapGamma V.form.map B)
    (hf : f.GammaDefinable B)
    (hb : RVMapGamma b.packedEssentialChartMap B)
    (hcchart : RVMapGamma c.packedEssentialChartMap B) :
    ∃ e : RVVolumeIso WU WV, e.GammaDefinable B := by
  obtain ⟨J,hJΓ,hJ⟩ := ElementaryBlowup.exists_headJacobian_after_blowup_gamma hc C B b c f hU hV hf
  let e := b.correctedIso c f J
  have heΓ : RVMapGamma (finiteIsoMap e) B :=
    (b.gamma_corrected_map hc B c f J hf
      (gamma_raw_head_correction_map hc f J hU hV hω hπ hf hJΓ) hb hcchart).congr (fun _ => rfl)
  have heVolume : RVAlmostEverywhere WU.essential.obj.domain (k+1) (fun w =>
      IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
        (WU.essential.obj.value w) (WV.essential.obj.value (finiteIsoMap e w))
        (WU.essentialForm.value w / WV.essentialForm.value (finiteIsoMap e w))) := by
    obtain ⟨ω,D,hD,hd,hω⟩ := exists_definable_generic_RVJacobian hc C (Nat.zero_lt_succ k)
      e WU.essential_nonzero WV.essential_nonzero
    have hdefined : RVAlmostEverywhere WU.essential.obj.domain (k+1) (fun w =>
        IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
          (WU.essential.obj.value w) (WV.essential.obj.value (finiteIsoMap e w)) ((ω w).val 0)) :=
      ⟨D,hD,hd,hω⟩
    apply RVAlmostEverywhere.mono (hJ.and hc C hdefined)
    rintro w ⟨hJ,hω⟩
    have he := b.correctedJacobian_eq_volumeRatio C c f J w hJ hω
    change (ω w).val 0 = WU.essentialForm.value w /
      WV.essentialForm.value (finiteIsoMap e w) at he
    rw [← he]
    exact hω
  exact ⟨⟨e,b.correctedIso_gamma c f J,heVolume⟩,heΓ⟩

end IntegrationInACVF.Section7
