import Integration7.GammaFunAddition
import Integration7.GammaNamedCoproductLifts
import Integration7.VolumeLiftCoproductBijections

/-! Additivity of Gamma contraction objects: in any Gamma setting, the standard contraction
object of a coproduct of Gamma VF volume objects is common-context equivalent to the coproduct
of the standard contraction objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

set_option maxHeartbeats 3200000 in
/-- **Contraction of coproducts.** -/
theorem gamma_coprod_contraction (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField G.real) x → AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (W₁ W₂ : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (h₁ : VFVolumeObjectGamma W₁ G) (h₂ : VFVolumeObjectGamma W₂ G) (h₁₂ : VFVolumeObjectGamma (W₁.coprod W₂) G)
    {σ₁ σ₂ σ : Equiv.Perm (Fin (k+1))}
    (E₁ : StandardContraction (nativeMixedVolumeDomain hc W₁.densityGraph.domain) σ₁)
    (E₂ : StandardContraction (nativeMixedVolumeDomain hc W₂.densityGraph.domain) σ₂)
    (E : StandardContraction (nativeMixedVolumeDomain hc (W₁.coprod W₂).densityGraph.domain) σ)
    (hE₁ : GammaProgramDefinable G E₁.program) (hE₂ : GammaProgramDefinable G E₂.program)
    (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨(W₁.coprod W₂).standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC _ h₁₂ E hE⟩
      (GammaVolumeObjects.coprod ⟨W₁.standardContractionObject hc C G.gamma E₁,standard_contraction_object_gamma hc C G hGC _ h₁ E₁ hE₁⟩
        ⟨W₂.standardContractionObject hc C G.gamma E₂,standard_contraction_object_gamma hc C G hGC _ h₂ E₂ hE₂⟩) := by
  obtain ⟨P₁,⟨e₁,he₁⟩,hP₁⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    W₁ h₁ E₁ hE₁
  obtain ⟨P₂,⟨e₂,he₂⟩,hP₂⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    W₂ h₂ E₂ hE₂
  obtain ⟨P,⟨e,he⟩,hP⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    (W₁.coprod W₂) h₁₂ E hE
  have hL := volume_lift_coprod_iso_gamma hc C hGC P₁.property P₂.property
  let f : VFVolumeIso (rvVolumeLift P.val) (rvVolumeLift (P₁.coprod P₂).val) :=
    ((e.symm hc C).trans hc C ((e₁.coprod hc C e₂).trans hc C (volumeLiftCoprodIso hc C P₁.val P₂.val)))
  have hf : f.GammaDefinable G :=
    (he.symm hc C).trans hc C ((he₁.coprod hc C he₂).trans hc C hL)
  have hK := rv_volume_lift_common_context_kernel hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 P (P₁.coprod P₂) f hf
  exact ((hP.symm hc).trans hc hK).trans hc (CommonContextVolumeEquivalent.coprod hc hP₁ hP₂)

end IntegrationInACVF.Section7.GammaNamed
