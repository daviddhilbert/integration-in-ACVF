import IntegrationSection6.GammaIsoRestrictions

/-! Equality transport changes no underlying set or isomorphism. -/
noncomputable section
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open FirstOrder.Language
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ SpecialTransformations.Milestone0.Axioms.ACVF]
variable {B C : Base (M := M)} {n a m b : ℕ}
variable {U : Set (Point (M := M) n a)} {V : Set (Point (M := M) m b)}

def GammaIso.rebase (f : GammaIso B U V) (h : B = C) : GammaIso C U V := h ▸ f

end IntegrationInACVF.Section6
