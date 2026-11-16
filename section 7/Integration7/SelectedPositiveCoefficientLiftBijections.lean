module

public import Integration7.AppendedCoefficientLiftProductBijections
public import Integration7.SelectedDefinableAppendedLiftBijections
public import Integration7.SelectedVolumeFamilyPositiveProducts
public import Integration7.VFVolumeProductBijections

@[expose] public section

/-! The selected positive coefficient action has the actual
coefficient-first Cartesian VF realization, including the explicit
arithmetic total-degree identification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}

def VFVolumeBijection.reindexDegree {S : Set M} {i j : ℕ}
    {U V : PositiveVFVolumeObject (M := M) S j} (f : VFVolumeBijection U V) (h : i=j) :
    VFVolumeBijection (U.reindexDegree h) (V.reindexDegree h) := by
  cases h
  exact f

def selectedPositiveCoefficientAppendedLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : SelectedVFVolumeFamily C n a k) :
    VFVolumeBijection (selectedVolumeFamilyLeftProduct U F).appendedFullLift
      (((rvVolumeLift U).prod F.appendedFullLift).reindexDegree (appended_positive_coefficient_degree_eq n p k)) := by
  let h := appended_positive_coefficient_degree_eq n p k
  let e := ((VFVolumeBijection.refl hc C (rvVolumeLift U)).prod hc
    (selectedToDefinableAppendedLiftBijection hc F)).reindexDegree h
  exact (definableVolumeFamilyAppendedSelectionBijection hc (F.toDefinable.mulConstant U)).trans hc C
    (((appendedCoefficientLiftProductBijection hc F.toDefinable U).symm hc C).trans hc C (e.symm hc C))

end IntegrationInACVF.Section7
