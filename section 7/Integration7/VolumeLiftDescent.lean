import Integration7.Section2VolumeBridge
import IntegrationSection2.VolumeDescentTheorem

/-! A volume-preserving lift compatible with an actual essential label
isomorphism descends to the two RV volume conditions. The graph-field
construction is supplied by the checked Section 2 theorem. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def RVVolumeIso.of_preserving_lift
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (e : U.essential ≅ V.essential)
    (f : Map (rvLift U.essential.obj) (rvLift V.essential.obj))
    (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.essential.obj,
      (finiteIsoMap e).graph p.val.2 (f p).val.2)
    (hMeasure : Section2.ConcreteVolumeForms.PreservesOff
      U.essentialForm.toSection2 V.essentialForm.toSection2 f) : RVVolumeIso U V :=
  .ofSection2 e (Section2.corollary_2_34_nonzero hc C (Nat.zero_lt_succ k) e
    U.essential_nonzero V.essential_nonzero
    U.essentialForm.toSection2 V.essentialForm.toSection2 f hf hlabel hMeasure)

end IntegrationInACVF.Section7
