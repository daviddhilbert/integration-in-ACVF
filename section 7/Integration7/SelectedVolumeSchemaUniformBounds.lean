import Integration7.GammaSelectedVolumeSchemata
import Integration7.UniformVolumeSchemaBounds
import IntegrationSection6.GammaVFParameterBases

/-! A selected coordinate projection with finite fibres and a retained
nonzero density has a single finite valid formula bound over all VF rows. -/

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

theorem selected_volume_schema_uniform_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (U : DefSet (M := M) S p a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hNZ : ∀ q ∈ carrier U, (q.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin p → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) :
    ∃ N : ℕ, ∀ x : Fin p → VF (M := M),
      ((gammaSelectedVolumeSchema U hU ρ δ).withBound N).valid (fun j => (x j).val) := by
  let A := PresentedSet.univ (pointSpace (M := M) p 0) B.real
  have hA : GammaSetDefinable B (carrier A) := (gammaLogicInput B).real_set _ (setDefinable A)
  obtain ⟨N,hN⟩ := (gammaSelectedVolumeSchema U hU ρ δ).uniform_valid_bound hκ hs hreal hgamma
    (rawVFParameter '' carrier A) (gamma_raw_vf_parameter_base hA)
    (by
      rintro z ⟨x,hx,rfl⟩
      exact gammaSelectedLabelSchema_finiteRows U hU ρ hfin x.1)
    (by
      rintro z ⟨x,hx,rfl⟩
      exact gammaSelectedVolumeSchema_density_valid U hU ρ δ hNZ x.1)
  exact ⟨N,fun x => hN _ ⟨(x,Fin.elim0),Set.mem_univ _,rfl⟩⟩

end IntegrationInACVF.Section7
