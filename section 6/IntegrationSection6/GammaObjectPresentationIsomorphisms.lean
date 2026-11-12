import IntegrationSection6.GammaIspUniversalPresentation
import IntegrationSection6.FiniteGammaIsoLaws

/-! Extending only an internal real presentation gives an actual
identity-label Gamma RV isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}

def gammaObjectPresentationIso (U : GammaRVFiniteObject B n) (hUS : U.codes ⊆ S) :
    GammaRVIso U.toGammaRVObject (gammaObjectAtExtend U hUS).toGamma.toGammaRVObject :=
  gammaIsoOfFiniteEquiv U (gammaObjectAtExtend U hUS).toGamma (Equiv.refl _) (gammaIsoRefl U).graph (fun _ => rfl)

end IntegrationInACVF.Section6.FiniteRV
