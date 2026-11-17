module

public import Integration7.GammaVolumeParameterGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Equal mathematical real/Gamma bases carry the same actual volume
objects and geometric common-blowup witnesses. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B B' : Base (M := M)} {S : Set M} {k : ℕ}

def GammaVolumeObjects.rebase (U : GammaVolumeObjects B S k) (h : B=B') : GammaVolumeObjects B' S k :=
  ⟨U.val,h ▸ U.property⟩

theorem GammaVolumeBlowupEquivalent.rebase {U V : GammaVolumeObjects B S k}
    (g : GammaVolumeBlowupEquivalent B S k U V) (h : B=B') :
    GammaVolumeBlowupEquivalent B' S k (U.rebase h) (V.rebase h) := by
  subst B'
  exact g

end IntegrationInACVF.Section7
