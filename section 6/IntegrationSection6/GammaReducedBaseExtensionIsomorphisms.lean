import IntegrationSection6.GammaDefinableBaseReduction
import IntegrationSection6.GammaFiniteBaseExtension
import IntegrationSection6.FiniteGammaIsoLaws

/-! Extending the code presentation and then eliminating definable base
names gives the original finite object up to its actual identity-label
Gamma isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {n : ℕ}

def gammaReducedBaseExtensionIso (H : GammaDefinableBaseReduction C B)
    (hG : B.gamma ⊆ C.gamma) (U : GammaRVFiniteObject B n) :
    GammaRVIso U.toGammaRVObject
      (H.finiteObject (gammaFiniteBaseExtension U H.real_subset hG)).toGammaRVObject :=
  FiniteRV.gammaIsoOfFiniteEquiv U _ (Equiv.refl _) (FiniteRV.gammaIsoRefl U).graph (fun _ => rfl)

end IntegrationInACVF.Section6
