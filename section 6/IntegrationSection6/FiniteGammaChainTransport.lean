import IntegrationSection6.FiniteGammaIterations

/-! Changing the endpoints of a finite Gamma-certified forward chain. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}

variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

variable {r : ℕ} {U V W : GammaObjectAt B S n}

theorem GammaIteratedBlowup.sourceIso (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V)
    (e : GammaIsoAt W U) : GammaIteratedBlowup hκ hs h00 hsmall  r W V := by
  simpa only [Nat.zero_add] using (GammaIteratedBlowup.zero ⟨e⟩).append H

theorem GammaIteratedBlowup.targetIso (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V)
    (e : GammaIsoAt V W) : GammaIteratedBlowup hκ hs h00 hsmall  r U W := by
  simpa only [Nat.add_zero] using H.append (GammaIteratedBlowup.zero ⟨e⟩)

end IntegrationInACVF.Section6.FiniteRV
