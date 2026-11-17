module

public import Integration7.VolumeFamilyRealizationIdentifications

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Positive homogeneous function integration descends to the actual
almost-everywhere quotient, using genuine cofull full-lift realizations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

theorem selected_family_outside_base_row_empty
    (F : SelectedVFVolumeFamily C n a k)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (x : (rawVFSpace (M := M) n).Carrier) (hx : x ∈ E.carrier) :
    ((F.outsideBase E).rowInContext x).underlying.obj.domain.carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  let P := Map.fst (rawVFSpace (M := M) n) (rawRVSpace a) (C.base : Set M) F.domain
  change (x,r) ∈ F.domain.carrier ∧ (x,r) ∉ (definableMapPreimage P E).carrier at hr
  exact hr.2 ((mem_definableMapPreimage P E ⟨(x,r),hr.1⟩).mpr hx)

theorem selected_family_canonical_integral_ae_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hAE : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F =
      selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated G := by
  obtain ⟨E,hE,hRows⟩ := hAE
  have hGood : ∀ x, VolumeBlowupEquivalent ((F.outsideBase E).rowInContext x) ((G.outsideBase E).rowInContext x) := by
    intro x
    by_cases hx : x ∈ E.carrier
    · exact VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x)
        (RVVolumeIso.of_empty hc (vfParameterVolumeContext C x) _ _
          (selected_family_outside_base_row_empty F E x hx) (selected_family_outside_base_row_empty G E x hx))
    · exact (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mp
        ((positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x) (selectedFamilyOutsideBaseRowIso hc F E x hx)).trans
          ((hRows x hx).trans
            (positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x) (selectedFamilyOutsideBaseRowIso hc G E x hx)).symm))
  exact (selected_family_canonical_integral_remove_small_base hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F E hE).trans
    ((selected_family_canonical_integral_value_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (F.outsideBase E) (G.outsideBase E) hGood).trans
        (selected_family_canonical_integral_remove_small_base hc C Ξ hΞ hGenerated hNames γ hγ hγ1 G E hE).symm)

def aeRVVolumeFunctionIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    AERVVolumeFunction hc C n k → PositiveVolumeBlowupClasses hc C ((k+1)+n) :=
  Quotient.lift (fun F => selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F.2)
    (fun F G h => selected_family_canonical_integral_ae_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2 G.2 h)

theorem ae_rv_volume_function_integral_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVolumeFunctionPresentation C (n+1) k) :
    aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (Quotient.mk _ F) =
      selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F.2 := rfl

end IntegrationInACVF.Section7
