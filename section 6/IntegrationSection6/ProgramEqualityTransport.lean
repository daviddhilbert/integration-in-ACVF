import IntegrationSection6.OrderedSelectedVolume

/-! Equality transport of the source of an actual ordered contraction
preserves its volume selectors and original-Gamma certificate. -/
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
variable {U U' : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}

def orderedCastSource (T : OrderedContractionProgram S U V) (h : U = U') : OrderedContractionProgram S U' V := h ▸ T

theorem orderedCastSource_volumeIndex (T : OrderedContractionProgram S U V) (h : U = U') :
    (orderedCastSource T h).volumeIndex = T.volumeIndex := by cases h; rfl

theorem orderedCastSource_selectedIndex (T : OrderedContractionProgram S U V) (h : U = U')
    {k : ℕ} (ρ : Fin k → Fin a) : orderedSelectedIndex (orderedCastSource T h) ρ = orderedSelectedIndex T ρ := by
  cases h
  rfl

theorem gamma_orderedCastSource (T : OrderedContractionProgram S U V) (h : U = U')
    (hT : GammaProgramDefinable B T) : GammaProgramDefinable B (orderedCastSource T h) := by
  cases h
  exact hT

end IntegrationInACVF.Section6
