import IntegrationSection6.ProgramEqualityTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a l : ℕ}
variable {U : DefSet (M := M) S n a} {V V' : DefSet (M := M) S 0 l}

def orderedCastTarget (T : OrderedContractionProgram S U V) (h : V = V') : OrderedContractionProgram S U V' := h ▸ T

theorem orderedCastTarget_volumeIndex (T : OrderedContractionProgram S U V) (h : V = V') :
    (orderedCastTarget T h).volumeIndex = T.volumeIndex := by cases h; rfl

theorem orderedCastTarget_selectedIndex (T : OrderedContractionProgram S U V) (h : V = V')
    {k : ℕ} (ρ : Fin k → Fin a) : orderedSelectedIndex (orderedCastTarget T h) ρ = orderedSelectedIndex T ρ := by
  cases h
  rfl

theorem gamma_orderedCastTarget (T : OrderedContractionProgram S U V) (h : V = V')
    (hT : GammaProgramDefinable B T) : GammaProgramDefinable B (orderedCastTarget T h) := by
  cases h
  exact hT

end IntegrationInACVF.Section6
