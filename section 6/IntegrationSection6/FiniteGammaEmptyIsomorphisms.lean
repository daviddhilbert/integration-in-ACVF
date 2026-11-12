import IntegrationSection6.FiniteGammaIsoClasses
import IntegrationSection6.FiniteGammaAmbientIsos
import Section4.RVEmptyIso

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaEmptyIsoAt (U : GammaObjectAt B S k)
    (hU : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)) = ∅) :
    GammaIsoAt U (gammaEmptyAt U.real_contains) := by
  apply GammaIsoAt.ofAmbient (@rvEmptyIso M N S k U.object.obj hU)
  apply GammaGraphDefinable.congr (gamma_empty_graph (B := B) (rvObjectArity U.object.obj) 0)
  intro p q
  constructor
  · intro h; exact h.elim
  · rintro ⟨u,_,_⟩
    exact (hU.le u.property).elim

theorem gammaIsoClassAt_eq_zero [Fact (B.real ⊆ S)] (U : GammaObjectAt B S k)
    (hU : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)) = ∅) :
    gammaIsoClassAt U = 0 :=
  (gammaIsoClassAt_iso (gammaEmptyIsoAt U hU)).trans (gammaIsoClassAt_empty U.real_contains)

end IntegrationInACVF.Section6.FiniteRV
