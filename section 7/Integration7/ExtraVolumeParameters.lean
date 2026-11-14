import Integration7.GammaVolumeIsomorphismSchemata

/-! Drop an auxiliary parameter block while retaining all geometric
coordinates. Extra parameters will be allowed only inside the exceptional
set certificate; the volume objects and comparison chart stay fixed. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

def dropExtraVolumeParameters (p q d : ℕ) : Fin (p+d) → Fin ((p+q)+d) :=
  Fin.addCases (fun i => Fin.castAdd d (Fin.castAdd q i)) (Fin.natAdd (p+q))

theorem append_dropExtraVolumeParameters {X : Type} {p q d : ℕ}
    (z : Fin p → X) (y : Fin q → X) (r : Fin d → X) :
    Fin.append (Fin.append z y) r ∘ dropExtraVolumeParameters p q d = Fin.append z r := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [Function.comp_apply,dropExtraVolumeParameters,Fin.addCases_left,
      Fin.addCases_right,Fin.append_left,Fin.append_right]

end IntegrationInACVF.Section7
