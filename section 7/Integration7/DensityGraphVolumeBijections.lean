module

public import Integration7.VolumeDensityGraphs

@[expose] public section

/-! Actual volume-preserving bijections between the density graphs of
arbitrary volume objects. Both directions of the graph presentation are
composed in the existing VF volume category. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {k : ℕ}

def VFVolumeBijection.onDensityGraphs
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeBijection U V) : VFVolumeBijection U.densityGraph V.densityGraph :=
  (((volumeDensityGraphBijection hc C U).symm hc C).trans hc C f).trans hc C
    (volumeDensityGraphBijection hc C V)

end IntegrationInACVF.Section7
