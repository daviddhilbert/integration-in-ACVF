module

public import Integration7.AERVVolumeFunctionAdditiveStructure
public import Integration7.VolumeFamilyIntegralAdditivity
public import Integration7.AERVVolumeFunctionIntegrals

@[expose] public section

/-! The canonical integral is an additive homomorphism on the actual
almost-everywhere positive homogeneous volume-function quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def aeRVVolumeFunctionIntegralAddHom
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n k : ℕ) :
    AERVVolumeFunction hc C n k →+ PositiveVolumeBlowupClasses hc C ((k+1)+n) where
  toFun := aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  map_zero' := selected_family_canonical_integral_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k
  map_add' f g := Quotient.inductionOn₂ f g (fun F G =>
    selected_family_canonical_integral_add hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2 G.2)

theorem ae_rv_volume_function_integral_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) {n k : ℕ}
    (f g : AERVVolumeFunction hc C n k) :
    aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (f+g) =
      aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f +
        aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 g :=
  (aeRVVolumeFunctionIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k).map_add f g

end IntegrationInACVF.Section7
