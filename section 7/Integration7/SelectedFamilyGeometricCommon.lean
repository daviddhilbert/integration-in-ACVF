module

public import Integration7.GammaTermContextVolumeGeometry
public import Integration7.GammaGeometricCommonWitnesses
public import Integration7.SelectedFamilyVolumePreparation

@[expose] public section

/-! The paper's ordinary named-fibre common-blowup hypothesis supplies
original-Gamma geometric witnesses for the actual density-graph families. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (VF)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeSchema.commonInNamedContext_to_geometry
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (z : Fin p → M) (h : F.commonInNamedContext G z) : F.commonByGammaGeometry G z := by
  obtain ⟨C,hBase,U,V,ha,hb,PU,PV,h⟩ := h
  let Bz : Base (M := M) := ⟨B.real ∪ Set.range z,B.gamma⟩
  have hU : VolumeObjectGamma U Bz := .of_term_context hc C hBase U
  have hV : VolumeObjectGamma V Bz := .of_term_context hc C hBase V
  exact ⟨C,⟨U,hU⟩,⟨V,hV⟩,ha,hb,PU,PV,
    volume_common_gamma_in_term_context (B := Bz) hc C hBase h⟩

theorem selected_densityGraph_geometric_common
    (hc : CanonicalStructure.IsCanonical (M := M)) (Ξ : Set (Values.Gamma (M := M)))
    {C : BaseContext M} {n : ℕ}
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VF (M := M))
    (h : VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x)) :
    (F.densityGraphSchema hc Ξ).commonByGammaGeometry (G.densityGraphSchema hc Ξ) (fun j => (x j).val) := by
  exact GammaRVVolumeSchema.commonInNamedContext_to_geometry hc _ _ _
    (selected_densityGraph_named_common hc Ξ F G 0 0 x h)

end IntegrationInACVF.Section7
