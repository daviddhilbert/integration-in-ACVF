module

public import Integration7.OrdinaryVolumeFamilyAEHeadComparisons

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! First-head integration of ordinary-valued AE functions is well-defined
on the actual quotient. Any chosen head preparation gives its value. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

def aeOrdinaryRVVolumeFunctionHeadIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    AEOrdinaryRVVolumeFunction hc C (n+1) → AERVVolumeFunction hc C n 0 :=
  Quotient.lift (fun F =>
    let T := ordinaryFamilyHeadPreparation hc Ξ hGenerated F.2
    Quotient.mk _ ⟨1+T.arity,F.2.headIntegral hc Ξ T⟩) (by
      intro F G h
      apply Quotient.sound
      exact ordinary_family_head_integral_comparison_of_ae hc Ξ hΞ hNames γ hγ hγ1 F.2 G.2 h
        (ordinaryFamilyHeadPreparation hc Ξ hGenerated F.2)
        (ordinaryFamilyHeadPreparation hc Ξ hGenerated G.2))

theorem ae_ordinary_rv_volume_function_head_integral_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVFVolumeFamily C ((n+1)+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)) :
    aeOrdinaryRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (Quotient.mk _ ⟨a,F⟩) =
      Quotient.mk _ ⟨1+T.arity,F.headIntegral hc Ξ T⟩ := by
  apply Quotient.sound
  exact ordinary_family_head_integral_comparison_of_ae hc Ξ hΞ hNames γ hγ hγ1 F F
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun _ => rfl))
    (ordinaryFamilyHeadPreparation hc Ξ hGenerated F) T

end IntegrationInACVF.Section7
