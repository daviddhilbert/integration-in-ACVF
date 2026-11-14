import Integration7.BlowupParameterExtension

/-! Literal coherence of the geometric constructions under parameter
extension. Proof witnesses change; labels, maps and densities do not. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S T R : Set M} {k : ℕ}

@[simp] theorem PositiveRVVolumeObject.extend_trans
    (U : PositiveRVVolumeObject (M := M) S k) (hST : S ⊆ T) (hTR : T ⊆ R) :
    (U.extend hST).extend hTR = U.extend (hST.trans hTR) := rfl

@[simp] theorem PositiveRVVolumeObject.coprod_extend
    (U V : PositiveRVVolumeObject (M := M) S k) (hST : S ⊆ T) :
    (U.coprod V).extend hST = (U.extend hST).coprod (V.extend hST) := rfl

@[simp] theorem elementaryVolumeObject_extend (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hAd : BlowupAdmissible U) :
    (elementaryVolumeObject C U hAd).extend hCD =
      elementaryVolumeObject D (U.extend hCD) (hAd.extend hCD) := rfl

end IntegrationInACVF.Section7
