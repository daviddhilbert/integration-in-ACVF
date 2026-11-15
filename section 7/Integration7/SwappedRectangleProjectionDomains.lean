import Integration7.RectangleFamilySecondStagePreparations
import IntegrationSection6.SpecialEqualityTransport

/-! Swapping the two VF coordinates exchanges the actual labelled
unary projection domains, with no added names or chosen representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m : ℕ}

theorem swapped_rectangle_head_projection (H : DefSet (M := M) S 2 m) :
    Map.image (coordinateProjectMap 0 (vfPermutationImage H (Equiv.swap 0 1))) =
      Map.image (coordinateProjectMap 1 H) := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨p,hp⟩ := a.property
    exact ⟨p,(congrArg (coordinateProject 0) hp).trans ha⟩
  · rintro ⟨p,hp⟩
    exact ⟨vfPermutationBijection H (Equiv.swap 0 1) p,hp⟩

theorem swapped_rectangle_tail_projection (H : DefSet (M := M) S 2 m) :
    Map.image (coordinateProjectMap 1 (vfPermutationImage H (Equiv.swap 0 1))) =
      Map.image (coordinateProjectMap 0 H) := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨p,hp⟩ := a.property
    exact ⟨p,(congrArg (coordinateProject 1) hp).trans ha⟩
  · rintro ⟨p,hp⟩
    exact ⟨vfPermutationBijection H (Equiv.swap 0 1) p,hp⟩

end IntegrationInACVF.Section7
