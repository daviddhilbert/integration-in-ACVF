import Integration7.ConstantLabelPreparationCommonNames
import Integration7.TwoOrderProductPreparations

/-! Present both constructed product preparations over a prescribed
common-name set. No inclusion of their arbitrary old code set is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.TwoOrderProductPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S R : Set M} {d : ℕ}
variable {X Y : DefSet (M := M) S 2 0} {D E : DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}

def present (F : TwoOrderProductPreparations X Y D E r t z hz P)
    (hSR : S ⊆ R) (hNames : commonRealNames P ⊆ R) :
    TwoOrderProductPreparations (extendBase X hSR) (extendBase Y hSR)
      (extendBase D hSR) (extendBase E hSR) r t z (fun j => hSR (hz j)) P where
  codes := R
  contains := Set.Subset.refl _
  dArity := F.dArity
  eArity := F.eArity
  dTarget := gammaNativePresentation F.dTarget (F.dGamma.target P F.dSpecial.chain) hNames
  eTarget := gammaNativePresentation F.eTarget (F.eGamma.target P F.eSpecial.chain) hNames
  dSpecial := gammaSpecialPresentation F.dSpecial F.dGamma hNames
  eSpecial := gammaSpecialPresentation F.eSpecial F.eGamma hNames
  dGamma := gamma_chain_presentation_gamma F.dSpecial.chain F.dGamma hNames
  eGamma := gamma_chain_presentation_gamma F.eSpecial.chain F.eGamma hNames
  dPullback := F.dPullback
  ePullback := F.ePullback
  headSaturated := F.headSaturated
  tailSaturated := F.tailSaturated
  headPreparation := F.headPreparation.present F.eGamma hNames
  tailPreparation := F.tailPreparation.present F.dGamma hNames

end IntegrationInACVF.Section7.TwoOrderProductPreparations
