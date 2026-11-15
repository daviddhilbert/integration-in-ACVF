import IntegrationSection5.GammaPartialContraction

/-! Literal endpoint equality transport for partial contraction
programs retains their volume selectors and Gamma certificates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {p n a b : ℕ}
variable {A A' : DefSet (M := M) S (p+n) a} {B B' : DefSet (M := M) S p b}

def partialCastSource (T : PartialContractionProgram S p (n := n) A B) (h : A = A') :
    PartialContractionProgram S p (n := n) A' B := h ▸ T

def partialCastTarget (T : PartialContractionProgram S p (n := n) A B) (h : B = B') :
    PartialContractionProgram S p (n := n) A B' := h ▸ T

theorem partial_cast_source_volume_index (T : PartialContractionProgram S p (n := n) A B) (h : A = A') :
    (partialCastSource T h).volumeIndex = T.volumeIndex := by cases h; rfl

theorem partial_cast_target_volume_index (T : PartialContractionProgram S p (n := n) A B) (h : B = B') :
    (partialCastTarget T h).volumeIndex = T.volumeIndex := by cases h; rfl

theorem gamma_partial_cast_source (T : PartialContractionProgram S p (n := n) A B) (h : A = A')
    (hT : GammaPartialProgramDefinable G T) : GammaPartialProgramDefinable G (partialCastSource T h) := by
  cases h
  exact hT

theorem gamma_partial_cast_target (T : PartialContractionProgram S p (n := n) A B) (h : B = B')
    (hT : GammaPartialProgramDefinable G T) : GammaPartialProgramDefinable G (partialCastTarget T h) := by
  cases h
  exact hT

end IntegrationInACVF.Section7
