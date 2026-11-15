import Integration7.SelectedVFTailPermutationDomains
import Integration7.SelectedRVVFTailFullPrograms
import IntegrationSection6.StandardProgramPresentations

/-! Completing a specified standard contraction after VF tail realization
produces an actual standard contraction in the extended original order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a d r : ℕ}
variable {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

def selectedRVVFTailStandardContraction (hc : CanonicalStructure.IsCanonical (M := M))
    (T : StandardContraction A σ) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V) :
    StandardContraction (nativeProgramSelectedRVVFTailLift hc A ρ) (selectedVFTailPermutation d σ) :=
  standardFromProgram _ _ (selectedRVVFTailFullProgram hc T.program ρ E)
    (native_program_selected_vf_tail_permutation hc A ρ σ)

theorem gamma_selected_rv_vf_tail_standard_contraction
    (hc : CanonicalStructure.IsCanonical (M := M))
    (T : StandardContraction A σ) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V)
    (h : GammaProgramDefinable G (selectedRVVFTailFullProgram hc T.program ρ E)) :
    GammaProgramDefinable G (selectedRVVFTailStandardContraction hc T ρ E).program :=
  gamma_standardFromProgram _ _ _ _ h

theorem selected_rv_vf_tail_standard_volume_index
    (hc : CanonicalStructure.IsCanonical (M := M))
    (T : StandardContraction A σ) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V) (i : Fin (d+n)) :
    (selectedRVVFTailStandardContraction hc T ρ E).volumeIndex i =
      (selectedRVVFTailFullProgram hc T.program ρ E).volumeIndex ((selectedVFTailPermutation d σ).symm i) := by
  change (orderedCastSource _ _).volumeIndex _ = _
  rw [orderedCastSource_volumeIndex]

end IntegrationInACVF.Section7
