import Integration7.OrderedRVLabelCutRestrictions
import IntegrationSection6.StandardProgramPresentations

/-! Standard contractions restrict to arbitrary original-Gamma label
predicates in the same small presentation, retaining the exact target
cut, coordinate order, VF-volume selector and recursive selections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a k : ℕ}
variable {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

theorem rv_label_cut_vf_permutation (hU : GammaSetDefinable G (carrier U))
    (ρ : Fin k → Fin a) (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S) :
    rvLabelCut (vfPermutationImage U σ) (gamma_vfPermutationImage U hU σ) ρ R hR hNames =
      vfPermutationImage (rvLabelCut U hU ρ R hR hNames) σ := by
  apply defSet_eq_of_carrier_eq
  ext q
  change ((q.1,q.2) ∈ carrier (vfPermutationImage U σ) ∧ (Fin.elim0,q.2 ∘ ρ) ∈ R) ↔
    (q.1,q.2) ∈ carrier (vfPermutationImage (rvLabelCut U hU ρ R hR hNames) σ)
  rw [vfPermutationImage_row,vfPermutationImage_row]
  rfl

structure StandardLabelCutRestriction (C : StandardContraction U σ)
    (hU : GammaSetDefinable G (carrier U)) (hC : GammaProgramDefinable G C.program)
    (ρ : Fin k → Fin a) (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S) where
  program : OrderedContractionProgram S (vfPermutationImage (rvLabelCut U hU ρ R hR hNames) σ)
    (rvLabelCut C.target (gamma_program_final_set C.program hC)
      (fun j => suffixIndex C.program.rvArity_le (ρ j)) R hR hNames)
  gamma : GammaProgramDefinable G program
  volume : program.volumeIndex = C.program.volumeIndex
  selected : ∀ {d : ℕ} (τ : Fin d → Fin a), orderedSelectedIndex program τ = orderedSelectedIndex C.program τ

theorem standard_label_cut_restriction_exists (C : StandardContraction U σ)
    (hU : GammaSetDefinable G (carrier U)) (hC : GammaProgramDefinable G C.program)
    (ρ : Fin k → Fin a) (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S) : Nonempty (StandardLabelCutRestriction C hU hC ρ R hR hNames) := by
  obtain ⟨P,hP,hV,hSel⟩ := ordered_rv_label_cut_restriction_exists C.program
    (gamma_vfPermutationImage U hU σ) hC ρ R hR hNames
  let hStart := rv_label_cut_vf_permutation (σ := σ) hU ρ R hR hNames
  refine ⟨⟨orderedCastSource P hStart,gamma_orderedCastSource P hStart hP,
    (orderedCastSource_volumeIndex P hStart).trans hV,?_⟩⟩
  intro d τ
  exact (orderedCastSource_selectedIndex P hStart τ).trans (hSel d τ)

namespace StandardLabelCutRestriction
variable {C : StandardContraction U σ} {hU : GammaSetDefinable G (carrier U)}
variable {hC : GammaProgramDefinable G C.program} {ρ : Fin k → Fin a}
variable {R : Set (Point (M := M) 0 k)} {hR : GammaSetDefinable G R} {hNames : commonRealNames G ⊆ S}

def contraction (D : StandardLabelCutRestriction C hU hC ρ R hR hNames) :
    StandardContraction (rvLabelCut U hU ρ R hR hNames) σ := ⟨C.arity,_,D.program⟩

theorem volumeIndex (D : StandardLabelCutRestriction C hU hC ρ R hR hNames) :
    D.contraction.volumeIndex = C.volumeIndex := funext (fun i => congrFun D.volume (σ.symm i))

end StandardLabelCutRestriction
end IntegrationInACVF.Section7
