module

public import Integration7.CentralVolumePointClasses
public import Integration7.VolumeIntegrationGroupification

@[expose] public section

/-! The actual point remains central in the universal groupification
of the geometric RV common-blowup quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def volumePointRing
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) : RVVolumeBlowupRing hc C :=
  semiringGroupificationOf (RVVolumeBlowupSemiring hc C) (volumePointClass hc C)

theorem volume_point_ring_commutes
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (a : RVVolumeBlowupRing hc C) : Commute a (volumePointRing hc C) := by
  have hOf (x : RVVolumeBlowupSemiring hc C) :
      Commute (semiringGroupificationOf _ x) (volumePointRing hc C) :=
    (volume_point_class_commutes hc C x).map (semiringGroupificationOf _).toMonoidHom
  obtain ⟨x,y,rfl⟩ := semiringGroupification_exists_difference a
  change (semiringGroupificationOf _ x - semiringGroupificationOf _ y) * volumePointRing hc C =
    volumePointRing hc C * (semiringGroupificationOf _ x - semiringGroupificationOf _ y)
  rw [sub_mul,mul_sub,(hOf x).eq,(hOf y).eq]

instance volumePointRingCentralFact
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Fact (∀ a : RVVolumeBlowupRing hc C, Commute a (volumePointRing hc C)) :=
  ⟨volume_point_ring_commutes hc C⟩

end IntegrationInACVF.Section7
