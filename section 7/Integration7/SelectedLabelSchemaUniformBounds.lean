import Integration7.UniformVolumeSchemaBounds
import IntegrationSection6.GammaSelectedLabelFamilies
import IntegrationSection6.GammaVFParameterBases

/-! Selected-label finite rows have one uniform valid formula bound,
also when there are zero selected coordinates and the rows are ordinary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a k : ℕ}

theorem selected_label_schema_uniform_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (U : DefSet (M := M) S p a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin p → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) :
    ∃ N : ℕ, ∀ x : Fin p → VF (M := M),
      ((gammaSelectedLabelSchema U hU ρ).withBound N).valid (fun j => (x j).val) := by
  let A := PresentedSet.univ (pointSpace (M := M) p 0) B.real
  have hA : GammaSetDefinable B (carrier A) := (gammaLogicInput B).real_set _ (setDefinable A)
  obtain ⟨N,hN⟩ := finiteSchema_uniform_valid_bound hκ hs hreal hgamma (gammaSelectedLabelSchema U hU ρ)
    (rawVFParameter '' carrier A) (gamma_raw_vf_parameter_base hA) (by
      rintro z ⟨x,hx,rfl⟩
      exact gammaSelectedLabelSchema_finiteRows U hU ρ hfin x.1)
  exact ⟨N,fun x => hN _ ⟨(x,Fin.elim0),Set.mem_univ _,rfl⟩⟩

end IntegrationInACVF.Section7
