module

public import Integration7.PositiveVolumeIntegrationEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Arithmetic reindexing of a positive VF volume degree changes no
geometry. Its actual integration value is heterogeneously unchanged. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a b : ℕ}

def PositiveVFVolumeObject.reindexDegree (U : PositiveVFVolumeObject (M := M) S b) (h : a=b) :
    PositiveVFVolumeObject (M := M) S a where
  arity := U.arity
  domain := by cases h; exact U.domain
  finite_labels := by cases h; exact U.finite_labels
  form := by cases h; exact U.form

theorem positive_vf_volume_integration_reindex_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) b) (h : a=b) :
    HEq (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C (U.reindexDegree h)))
      (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (positiveVFVolumeIsoClass hc C U)) := by
  cases h
  rfl

end IntegrationInACVF.Section7
