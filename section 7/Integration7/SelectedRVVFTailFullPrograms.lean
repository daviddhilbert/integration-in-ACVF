module

public import Integration7.GammaSelectedRVVFTailPartialPrograms
public import Integration7.PartialOrderedContractionAppending
public import Integration7.SelectedRVVFTailPullbacks
public import IntegrationSection6.CanonicalContractionPrograms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Complete the lifted specified contraction by canonical identity
heads on the added VF tail. Every actual head and its original-Gamma
certificate is constructed, without an order-comparison premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a l d r : ℕ}

def selectedRVVFTailFullProgram (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U) (ρ : Fin d → Fin a)
    {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S
      (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U (suffixIndex T.rvArity_le ∘ ρ)) V) :
    OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := n) (d := d) hc A ρ) V :=
  appendPartialOrderedProgram (selectedRVVFTailPartialProgram hc T ρ) E

theorem selected_rv_vf_tail_full_program_exists
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U)
    (hA : GammaSetDefinable G (carrier A)) (hT : GammaProgramDefinable G T) (ρ : Fin d → Fin a) :
    ∃ r : ℕ, ∃ V : DefSet (M := M) S 0 r,
    ∃ E : OrderedContractionProgram S
      (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U (suffixIndex T.rvArity_le ∘ ρ)) V,
      GammaProgramDefinable G E ∧
      (∀ p, (E.naturalMap p).val.1 = p.val.1) ∧ Contractible E.toMap ∧
      GammaProgramDefinable G (selectedRVVFTailFullProgram hc T ρ E) := by
  let F := nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U (suffixIndex T.rvArity_le ∘ ρ)
  have hF : GammaSetDefinable G (carrier F) :=
    gamma_native_program_selected_rv_vf_tail_lift hc U _ (gamma_program_final_set T hT)
  have hPull : IsRVPullback (carrier F) :=
    native_program_selected_rv_vf_tail_lift_pullback hc U _ (isRVPullback_zeroVF (carrier U))
  obtain ⟨r,V,E,hE,hVF,hCon⟩ := canonical_ordered_contraction_exists F hF hPull
  refine ⟨r,V,E,hE,hVF,hCon,?_⟩
  exact gamma_append_partial_ordered_program (selectedRVVFTailPartialProgram hc T ρ) E
    (gamma_selected_rv_vf_tail_partial_program hc T hA hT ρ) hE

end IntegrationInACVF.Section7
