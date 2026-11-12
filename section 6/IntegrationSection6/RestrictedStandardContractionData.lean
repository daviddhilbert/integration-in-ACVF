import IntegrationSection6.StandardRVLabelRestriction

/-! A fixed-target representation of the actual restricted contraction,
so that no equality casts on its final RV arity are needed. -/
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

structure RestrictedStandardData (C : StandardContraction U σ)
    (hU : GammaSetDefinable B (carrier U)) (hC : GammaProgramDefinable B C.program)
    (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)) where
  program : OrderedContractionProgram Set.univ (vfPermutationImage (rvLabelSlice U hU ρ t) σ)
    (rvLabelSlice C.target (gamma_program_final_set C.program hC)
      (fun j => suffixIndex C.program.rvArity_le (ρ j)) t)
  gamma : GammaProgramDefinable ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ program
  volume : program.volumeIndex = C.program.volumeIndex

theorem restrictedStandardData_exists (C : StandardContraction U σ)
    (hU : GammaSetDefinable B (carrier U)) (hC : GammaProgramDefinable B C.program)
    (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)) : Nonempty (RestrictedStandardData C hU hC ρ t) := by
  obtain ⟨P,hP,hV,_⟩ := ordered_rv_label_restriction_exists C.program
    (gamma_vfPermutationImage U hU σ) hC ρ t
  let hStart := rvLabelSlice_vfPermutation (σ := σ) hU ρ t
  exact ⟨⟨orderedCastSource P hStart,gamma_orderedCastSource P hStart hP,
    (orderedCastSource_volumeIndex P hStart).trans hV⟩⟩

def RestrictedStandardData.contraction {C : StandardContraction U σ}
    {hU : GammaSetDefinable B (carrier U)} {hC : GammaProgramDefinable B C.program}
    {ρ : Fin k → Fin a} {t : Fin k → RV (M := M)} (D : RestrictedStandardData C hU hC ρ t) :
    StandardContraction (rvLabelSlice U hU ρ t) σ := ⟨C.arity,_,D.program⟩

theorem RestrictedStandardData.volumeIndex {C : StandardContraction U σ}
    {hU : GammaSetDefinable B (carrier U)} {hC : GammaProgramDefinable B C.program}
    {ρ : Fin k → Fin a} {t : Fin k → RV (M := M)} (D : RestrictedStandardData C hU hC ρ t) :
    D.contraction.volumeIndex = C.volumeIndex := by
  funext i
  exact congrFun D.volume (σ.symm i)

end IntegrationInACVF.Section6
