module

public import Integration7.TranslatedRVCoordinateSaturation

@[expose] public section

/-! Independent saturation in the two VF coordinates is the full
RV-pullback property, with every carried RV label fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m : ℕ}

def TailSaturated (H : Set (Point (M := M) 2 m)) : Prop :=
  ∀ p ∈ H, ∀ x : VF (M := M), rv x=rv (vfAt p 1) → replace 1 p x ∈ H

theorem is_rv_pullback_of_two_coordinate_saturation {H : Set (Point (M := M) 2 m)}
    (hHead : HeadSaturated H) (hTail : TailSaturated H) : IsRVPullback H := by
  apply (isRVPullback_iff H).mpr
  intro p hp q he
  obtain ⟨hVF,hRV⟩ := (sameRV_iff _ _).mp he
  have hp₀ := hHead p hp (vfAt q 0) (hVF 0).symm
  have hp₁ := hTail (replace 0 p (vfAt q 0)) hp₀ (vfAt q 1) (hVF 1).symm
  have hValue : replace 1 (replace 0 p (vfAt q 0)) (vfAt q 1) = q := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · exact hRV
  exact (congrArg (fun z => z ∈ H) hValue).mp hp₁

theorem swapped_tail_saturated_of_head (H : DefSet (M := M) S 2 m) (hH : HeadSaturated (carrier H)) :
    TailSaturated (carrier (vfPermutationImage H (Equiv.swap 0 1))) := by
  rintro p ⟨q,rfl⟩ x hx
  change rv x=rv (vfAt q.val 0) at hx
  let b : H := ⟨replace 0 q.val x,hH q.val q.property x hx⟩
  refine ⟨b,?_⟩
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

end IntegrationInACVF.Section7
