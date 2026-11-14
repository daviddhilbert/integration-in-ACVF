import Integration7.VolumeDegreeTransport

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def RVVolumeIso.reindexDegree
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {a b : ℕ} {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) b}
    (f : RVVolumeIso U V) (h : a=b) : RVVolumeIso (U.reindexDegree h) (V.reindexDegree h) :=
  ((volumeCastReindexIso hc C U h).trans hc C (f.cast h.symm)).trans hc C
    ((volumeCastReindexIso hc C V h).symm hc C)

end IntegrationInACVF.Section7
