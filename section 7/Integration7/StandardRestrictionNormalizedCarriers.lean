import Integration7.NormalizedRVLabelCutCarriers
import Integration7.StandardTargetRestrictionPresentations
import IntegrationSection6.FiniteContractionLabels

/-! An actual target restriction presentation identifies its normalized
RV domain with the literal old-label cut of the original normalized
domain. Its density selectors remain the original ones. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.StandardTargetRestrictionPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a k : ℕ}
variable {U A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

theorem old_label_index {T : StandardContraction U σ} {B : DefSet (M := M) S 0 T.arity}
    (D : StandardTargetRestrictionPresentation (G := G) T A B) (i : Fin a) :
    FiniteRV.contractionOldLabelIndex D.contraction i = FiniteRV.contractionOldLabelIndex T i := rfl

theorem normalized_carrier {T : StandardContraction U σ}
    (hT : GammaProgramDefinable G T.program) (ρ : Fin k → Fin a)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S)
    (D : StandardTargetRestrictionPresentation (G := G) T A
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (ρ j)) R hR hNames))
    (r : Fin (n+T.arity) → RV (M := M)) :
    r ∈ carrier (rvObjectDomain D.contraction.normalizedObject) ↔
      r ∈ carrier (rvObjectDomain T.normalizedObject) ∧
        (Fin.elim0,r ∘ (fun j => FiniteRV.contractionOldLabelIndex T (ρ j))) ∈ R := by
  change r ∈ carrier (rvObjectDomain (firstVolumeObject
    (Map.image (rawLabelMap (rvLabelCut T.target (gamma_program_final_set T.program hT)
      (fun j => suffixIndex T.program.rvArity_le (ρ j)) R hR hNames))) D.contraction.volumeIndex)) ↔ _
  rw [D.volumeIndex]
  exact first_volume_label_cut_mem T.target (gamma_program_final_set T.program hT)
    (fun j => suffixIndex T.program.rvArity_le (ρ j)) R hR hNames T.volumeIndex r

end IntegrationInACVF.Section7.StandardTargetRestrictionPresentation
