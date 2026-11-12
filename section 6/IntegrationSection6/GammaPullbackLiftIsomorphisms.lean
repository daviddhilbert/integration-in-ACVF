import IntegrationSection6.CanonicalPullbackPresentation
import Section5.GammaInvariantLogic
import Section5.GammaLift
import IntegrationSection6.ElementaryLiftIsomorphism

/-! An actual RV-pullback is isomorphic to the lift of its canonical RV
data, with the full original-Gamma graph of the canonical bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}

def gammaPullbackLiftIso (hBS : B.real ⊆ S) (A : DefSet (M := M) S n a)
    (hA : GammaSetDefinable B (carrier A)) (hAP : IsRVPullback (carrier A)) :
    GammaIso B (carrier A) (gammaPullbackObject (gammaLogicInput B) hBS A hA).lift := by
  let T := SpecialBijection.canonical A
  let e : GammaIso B (carrier A) (carrier (canonicalImage A)) :=
    ⟨T.equiv,GammaPrimitiveDefinable.graph (gammaLogicInput B) (.canonical A) hA⟩
  exact e.congr rfl ((canonicalImage_carrier_eq_typedLift A hAP).trans (typedLift_carrier (pullbackObject A)))

end IntegrationInACVF.Section6
