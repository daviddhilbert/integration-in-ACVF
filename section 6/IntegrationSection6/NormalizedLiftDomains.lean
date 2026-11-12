import Section7.LiftingDefinability
import Section3.CanonicalContext
import IntegrationSection6.RootDomainNormalization

/-! Raw lift-domain predicates agree with their normalized presentations.
The VF guards ensure that only properly sorted RV-map values are used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem rawLiftDomain_normalize (A : Set (Fin (n+n) → M)) :
    @rawLiftDomain M N n A = @rawLiftDomain M sM n A := by
  ext z
  simp only [rawLiftDomain,Set.mem_ofPred_eq,rawTupleFibre_normalize]

end IntegrationInACVF.Section6
