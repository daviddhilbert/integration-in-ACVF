module

public import Integration7.StandardRVLabelCutRestrictions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A restricted standard contraction can retain its original target
arity literally, including when the source piece has a different native
presentation of the same label cut. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a k : ℕ}
variable {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

structure StandardTargetRestrictionPresentation (C : StandardContraction U σ)
    (A : DefSet (M := M) S n a) (B : DefSet (M := M) S 0 C.arity) where
  program : OrderedContractionProgram S (vfPermutationImage A σ) B
  gamma : GammaProgramDefinable G program
  volume : program.volumeIndex = C.program.volumeIndex
  selected : ∀ {d : ℕ} (ρ : Fin d → Fin a), orderedSelectedIndex program ρ = orderedSelectedIndex C.program ρ

theorem standard_label_cut_presentation_on_equal_source (C : StandardContraction U σ)
    (hU : GammaSetDefinable G (carrier U)) (hC : GammaProgramDefinable G C.program)
    (ρ : Fin k → Fin a) (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S) (A : DefSet (M := M) S n a)
    (hA : rvLabelCut U hU ρ R hR hNames = A) :
    Nonempty (StandardTargetRestrictionPresentation (G := G) C A
      (rvLabelCut C.target (gamma_program_final_set C.program hC)
        (fun j => suffixIndex C.program.rvArity_le (ρ j)) R hR hNames)) := by
  obtain ⟨D⟩ := standard_label_cut_restriction_exists C hU hC ρ R hR hNames
  let he := congrArg (fun X => vfPermutationImage X σ) hA
  exact ⟨⟨orderedCastSource D.program he,gamma_orderedCastSource _ _ D.gamma,
    (orderedCastSource_volumeIndex _ _).trans D.volume,
    fun ρ => (orderedCastSource_selectedIndex _ _ ρ).trans (D.selected ρ)⟩⟩

namespace StandardTargetRestrictionPresentation
variable {C : StandardContraction U σ} {A : DefSet (M := M) S n a} {B : DefSet (M := M) S 0 C.arity}

def contraction (D : StandardTargetRestrictionPresentation (G := G) C A B) : StandardContraction A σ :=
  ⟨C.arity,B,D.program⟩

theorem volumeIndex (D : StandardTargetRestrictionPresentation (G := G) C A B) :
    D.contraction.volumeIndex = C.volumeIndex := funext (fun i => congrFun D.volume (σ.symm i))

end StandardTargetRestrictionPresentation
end IntegrationInACVF.Section7
