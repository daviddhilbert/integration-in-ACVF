import Integration7.RectangleFamilyAllOrderComparisons

/-! Actual Gamma contraction programs of a shared-label rectangle
family in any specified VF-two order. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

theorem rectangle_family_contraction_in_order_exists (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (H : DefSet (M := M) (C.base : Set M) 2 m) (hH : GammaSetDefinable G (carrier H))
    (hRect : RectangularRVFibres (carrier H)) (σ : Equiv.Perm (Fin 2)) :
    ∃ T : StandardContraction H σ, GammaProgramDefinable G T.program := by
  rcases vf_two_order_cases σ with rfl | rfl
  · exact rectangle_family_standard_contraction_exists C hNames γ hγ hγ1 H hH hRect
  · exact rectangle_family_swapped_standard_contraction_exists C hNames γ hγ hγ1 H hH hRect

end IntegrationInACVF.Section7
