import Integration7.OrdinaryUnitSelectedVolumeFamilies
import Integration7.UnaryUnitSelectedContractionCharts
import Integration7.SelectedRetainedContractionIntegrals
import Integration7.FieldBaseUnaryVolumeIntegrals

/-! The chosen positive unit presentation of an ordinary unary family
integrates to the point times its actual ordinary unary VF integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a : ℕ}

theorem ordinary_unit_selected_field_appended_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVFVolumeFamily C 1 a) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase F.unitSelectedFamily =
      rvVolumeBlowupClassesProduct hc C 1 1
        (positiveVolumeBlowupClass hc C (degreeOnePointVolumeObject (C.base : Set M)))
        (unaryFieldVolumeIntegral hc C Ξ FBase F.fullVFObject) := by
  let U := F.fullVFObject
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  let T := unaryFieldVolumeContraction hc C Ξ FBase U
  let hδ := unary_density_graph_label_nonzero U
  have hIntegral := selected_family_field_appended_integral_retained_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1
    F.unitSelectedFamily (Fin.last a) (ordinary_unit_selected_form_retained F) hδ T
  exact hIntegral.trans (positiveVolumeBlowupClass_iso hc C
    (unaryUnitSelectedRawProductIso hc C Ξ A U.densityGraph.finite_labels (Fin.last a) hδ
      (fun p hp => ordinary_unit_selected_density_label F ⟨p,hp⟩) T))
end IntegrationInACVF.Section7
