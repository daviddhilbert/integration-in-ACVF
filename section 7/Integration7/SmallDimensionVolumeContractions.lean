import Integration7.StandardVolumeContractionLiftMaps
import Integration7.VolumeLiftFullDimension
import Integration7.EssentialEmptyVolumeIsomorphisms
import Integration7.GammaVolumeBlowupEquivalence

/-! Arbitrary actual standard contractions of VF-small volume objects
have no essential labels, and hence compare by an actual Gamma volume
isomorphism. This is independent of the chosen contraction order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem standard_volume_contraction_essential_empty_of_small_dimension
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (hsmall : vfDim (rawRVSpace (M := M) 1) U.domain < k+1)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    (U.standardContractionObject hc C Ξ T).essential.obj.domain.carrier = ∅ := by
  apply essential_empty_of_volume_lift_small_dimension hc C
  rw [standard_volume_contraction_lift_dimension]
  exact hsmall

theorem small_dimension_standard_volume_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (hU : vfDim (rawRVSpace (M := M) 1) U.domain < k+1)
    (hV : vfDim (rawRVSpace (M := M) 1) V.domain < k+1)
    {σ τ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) τ) :
    let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    GammaVolumeBlowupEquivalent B (C.base : Set M) k
      ⟨U.standardContractionObject hc C Ξ T,U.standardContractionObject_gamma hc C Ξ T⟩
      ⟨V.standardContractionObject hc C Ξ E,V.standardContractionObject_gamma hc C Ξ E⟩ := by
  intro B
  have hTU := standard_volume_contraction_essential_empty_of_small_dimension hc C Ξ U hU T
  have hEV := standard_volume_contraction_essential_empty_of_small_dimension hc C Ξ V hV E
  let e := RVVolumeIso.of_essential_empty hc C _ _ hTU hEV
  exact GammaVolumeBlowupEquivalent.of_iso C B e (gamma_volume_iso_of_essential_empty e hTU)

end IntegrationInACVF.Section7
