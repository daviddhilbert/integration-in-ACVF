import IntegrationSection6.OrderedRVLabelRestriction
import IntegrationSection6.StandardProgramPresentations

/-! Restricting a standard contraction by selected original RV labels
retains its coordinate order and its entire VF-volume selector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a k : ℕ}
variable {U : DefSet (M := M) Set.univ n a} {σ : Equiv.Perm (Fin n)}

theorem rvLabelSlice_vfPermutation (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)) :
    rvLabelSlice (vfPermutationImage U σ) (gamma_vfPermutationImage U hU σ) ρ t =
      vfPermutationImage (rvLabelSlice U hU ρ t) σ := by
  apply defSet_eq_of_carrier_eq
  ext q
  rw [rvLabelSlice_carrier]
  change ((q.1,q.2) ∈ carrier (vfPermutationImage U σ) ∧ q.2 ∘ ρ = t) ↔
    (q.1,q.2) ∈ carrier (vfPermutationImage (rvLabelSlice U hU ρ t) σ)
  rw [vfPermutationImage_row, vfPermutationImage_row]
  rfl

theorem standard_rv_label_restriction_exists (C : StandardContraction U σ)
    (hU : GammaSetDefinable B (carrier U)) (hC : GammaProgramDefinable B C.program)
    (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)) :
    ∃ D : StandardContraction (rvLabelSlice U hU ρ t) σ,
      GammaProgramDefinable ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ D.program ∧
      D.arity = C.arity ∧
      HEq D.target (rvLabelSlice C.target (gamma_program_final_set C.program hC)
        (fun j => suffixIndex C.program.rvArity_le (ρ j)) t) ∧
      HEq D.volumeIndex C.volumeIndex := by
  obtain ⟨P,hP,hV,hSel⟩ := ordered_rv_label_restriction_exists C.program
    (gamma_vfPermutationImage U hU σ) hC ρ t
  let hStart := rvLabelSlice_vfPermutation (σ := σ) hU ρ t
  let D := standardFromProgram (rvLabelSlice U hU ρ t) σ P hStart
  refine ⟨D,gamma_standardFromProgram _ _ _ _ hP,rfl,heq_of_eq rfl,?_⟩
  apply heq_of_eq
  funext i
  exact congrFun ((orderedCastSource_volumeIndex P hStart).trans hV) (σ.symm i)

end IntegrationInACVF.Section6
