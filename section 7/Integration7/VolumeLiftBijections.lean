import Integration7.RVVolumeLiftIsomorphism
import Integration7.VFVolumeBijections
import Integration7.VFVolumeLifts
import Integration7.EssentialVolumeRestriction

/-! The checked lift theorem yields full volume-preserving bijections
between the actual essential lifts, without an extra graph assumption. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem RVVolumeIso.nonempty_lift_bijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    Nonempty (VFVolumeBijection (rvVolumeLift U.essentialCore) (rvVolumeLift V.essentialCore)) := by
  obtain ⟨G, hG, _, Z, hz, hJ⟩ := e.exists_preserving_lift hc C Ξ hGenerated
  exact ⟨⟨G, hG, VFAlmostEverywhere.of_exception Z hz hJ⟩⟩

end IntegrationInACVF.Section7
