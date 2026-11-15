import Integration7.SelectedRVVFTailCoordinateFibres
import IntegrationSection5.HeadContractionGeometry

/-! Realizing fixed selected RV labels does not change the RV-pullback
property of any active unary coordinate fibre. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a d : ℕ}

theorem selected_vf_tail_coordinate_fibres_pullback
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S n a) (ρ : Fin d → Fin a) (i : Fin n)
    (hA : ∀ u, IsRVPullback (carrier (coordinateFibre A i u)))
    (u : Fin (n+d) → VF (M := M)) :
    IsRVPullback (carrier (coordinateFibre (nativeSelectedRVVFTailLift hc A ρ) (Fin.castAdd d i) u)) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  have hP := (selected_vf_tail_coordinate_fibre hc A ρ i u p).mp hp
  apply (selected_vf_tail_coordinate_fibre hc A ρ i u q).mpr
  refine ⟨(isRVPullback_iff _).mp (hA (u ∘ Fin.castAdd d)) p hP.1 q he,?_⟩
  rw [← ((sameRV_iff p q).mp he).2]
  exact hP.2

end IntegrationInACVF.Section7
