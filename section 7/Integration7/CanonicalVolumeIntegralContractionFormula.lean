module

public import Integration7.CanonicalVolumeFamilyIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Compute a family integral using any actual specified standard
contraction, with the selected VF block restored to its original order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem selected_family_canonical_integral_standard_formula
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) {σ : Equiv.Perm (Fin (n+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F =
      positiveVolumeBlowupClass hc C (F.canonicalIntegralObject hc Ξ T) :=
  (selected_family_canonical_integral_realization hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F).trans
    (selected_coordinate_volume_realization_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (nativeMixedVolumeDomain hc F.densityGraph.domain) F.densityGraph.selected F.densityGraph.finite_selected
      (Fin.last a) F.densityGraph_label_nonzero T)

end IntegrationInACVF.Section7
