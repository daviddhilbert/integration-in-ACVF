module

public import Integration7.GammaVolumeSliceAssemblyGeometry
public import Integration7.GammaRVIndexedVolumeUniformity
public import Integration7.GammaVolumeIsoSchemaContexts

@[expose] public section

/-! Common original-Gamma volume witnesses for every RV-prefix slice
give common forward volume blowups of the original objects. All index and
joint presentations and their containing contexts are constructed internally. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV GammaRVFiniteObject rvObjectArity rvObjectDomain)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}

theorem gamma_volume_slice_density_common_gamma_uniformity {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (C : BaseContext M) (U V : GammaRVFiniteObject B (e+(k+1)))
    (hUC : U.codes ⊆ (C.base : Set M)) (hVC : V.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object)) (ε : Fin (rvObjectArity V.object))
    (hδ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (hε : ∀ v : rvObjectDomain V.object, (v.val ε).val ≠ iRVZero)
    (NF NG : ℕ)
    (hWitness : ∀ t : Fin e → RV (M := M),
      ∃ H : GammaVolumeCommonSchema ((gammaVolumeSliceDensitySchema U δ).withBound NF)
        ((gammaVolumeSliceDensitySchema V ε).withBound NG), H.valid (rvValues t)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent B (D.base : Set M) (e+k)
        ⟨(gammaCoordinateDensityObject hc C U hUC δ hδ).extend hCD,
          (gamma_coordinate_density_object_graphs hc C U hUC δ hδ).extend hCD⟩
        ⟨(gammaCoordinateDensityObject hc C V hVC ε hε).extend hCD,
          (gamma_coordinate_density_object_graphs hc C V hVC ε hε).extend hCD⟩ := by
  let F := (gammaVolumeSliceDensitySchema U δ).withBound NF
  let G := (gammaVolumeSliceDensitySchema V ε).withBound NG
  have hF : ∀ t : Fin e → RV (M := M), F.valid (rvValues t) := by
    intro t
    obtain ⟨H,hH⟩ := hWitness t
    exact hH.1
  have hG : ∀ t : Fin e → RV (M := M), G.valid (rvValues t) := by
    intro t
    obtain ⟨H,hH⟩ := hWitness t
    exact hH.2.1
  obtain ⟨BP⟩ := gamma_identity_index_presentation_exists B e
  let P := F.indexedVolumePresentation BP (fun t _ => hF t)
  let Q := G.indexedVolumePresentation BP (fun t _ => hG t)
  have hB : B.real ⊆ (C.base : Set M) := U.real_contains.trans hUC
  obtain ⟨C₁,hCC₁,hBP₁⟩ := finiteVolumePresentationContainingContext C BP hB
  obtain ⟨C₂,hC₁C₂,hP₂⟩ := P.exists_containingContext C₁ (hB.trans hCC₁)
  obtain ⟨C₃,hC₂C₃,hQ₃⟩ := Q.exists_containingContext C₂ (hB.trans (hCC₁.trans hC₁C₂))
  let hCC₃ := hCC₁.trans (hC₁C₂.trans hC₂C₃)
  let hP₃ := hP₂.trans hC₂C₃
  let hBP₃ := hBP₁.trans (hC₁C₂.trans hC₂C₃)
  obtain ⟨D,hC₃D,hPQ⟩ := gamma_rv_indexed_volume_witness_gamma_uniformity hc hκ hs hreal hgamma
    F G BP (fun t _ => hF t) (fun t _ => hG t) (fun t _ => hWitness t)
    C₃ P Q hP₃ hQ₃ hBP₃ (hB.trans hCC₃)
  let hCD := hCC₃.trans hC₃D
  let eU := gammaVolumeSliceDensityAssemblyIso hc D U (hUC.trans hCD) δ hδ BP NF P
    (hP₃.trans hC₃D)
  let eV := gammaVolumeSliceDensityAssemblyIso hc D V (hVC.trans hCD) ε hε BP NG Q
    (hQ₃.trans hC₃D)
  have heU := gamma_volume_slice_assembly_iso hc D U (hUC.trans hCD) δ hδ BP NF P (hP₃.trans hC₃D)
  have heV := gamma_volume_slice_assembly_iso hc D V (hVC.trans hCD) ε hε BP NG Q (hQ₃.trans hC₃D)
  refine ⟨D,hCD,GammaVolumeBlowupEquivalent.trans hc D B ?_ (hPQ.trans hc D B ?_)⟩
  · exact GammaVolumeBlowupEquivalent.of_iso D B (eU.symm hc D) (heU.symm hc D B)
  · exact GammaVolumeBlowupEquivalent.of_iso D B eV heV

end IntegrationInACVF.Section7
