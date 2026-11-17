module

public import Integration7.HKUpstreamRVZero
public import Integration7.HKZeroVolumeDescent
public import IntegrationSection2.WeightedZeroVolumeDescent

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The Section 7 zero-degree descent consumes Section 2's corrected
result in the actual published upstream category. The label map stays
the given ordinary isomorphism throughout the adapter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def upstreamZeroVolumeDescent (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : ZeroRVVolumeObject (M := M) S} (e : U.underlying ≅ V.underlying)
    (f : Map (rvLift U.underlying.obj) (rvLift V.underlying.obj))
    (hlabel : ∀ p, liftLabelMap V.underlying.obj (f p) = finiteIsoMap e (liftLabelMap U.underlying.obj p))
    (hMeasure : ∀ p, ∃ J : VFType (M := M), HasMixedVFJacobianAt f p J ∧
      (zeroLift U).form.value p = (zeroLift V).form.value (f p) * CanonicalRV.encodedRv J) :
    U.toUpstream ≅ V.toUpstream :=
  IntegrationInACVF.Section2.WeightedZeroVolumeDescent.corollary_2_34_zero_weighted hc
    (U := U.toUpstream) (V := V.toUpstream) e f hlabel hMeasure

@[simp] theorem upstreamZeroVolumeDescent_labels (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : ZeroRVVolumeObject (M := M) S} (e : U.underlying ≅ V.underlying)
    (f : Map (rvLift U.underlying.obj) (rvLift V.underlying.obj))
    (hlabel : ∀ p, liftLabelMap V.underlying.obj (f p) = finiteIsoMap e (liftLabelMap U.underlying.obj p))
    (hMeasure : ∀ p, ∃ J : VFType (M := M), HasMixedVFJacobianAt f p J ∧
      (zeroLift U).form.value p = (zeroLift V).form.value (f p) * CanonicalRV.encodedRv J) :
    (upstreamZeroVolumeDescent hc e f hlabel hMeasure).hom.map = finiteIsoMap e := rfl

end IntegrationInACVF.Section7.HK
