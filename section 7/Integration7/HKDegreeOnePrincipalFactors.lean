module

public import Integration7.HKDegreeOneVolumeFactors
public import Integration7.HKWeightedZeroBlowups
public import Integration7.HKRVProductBridges
public import Integration7.BasicVolumeRelation
public import Integration7.ElementaryBlowupIsomorphism

@[expose] public section

/-! Every elementary relation from a degree-one source factors through
the same genuine weighted zero object and the unit-form point/cone pair.
This is the geometric step missing under ordinary measured degree zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def degreeOneHeadConeVolumeIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) 0} (b : ElementaryBlowup U W) :
    RVVolumeIso W (zeroProduct (degreeOneHeadFactor C U b.admissible)
      (degreeOneConeVolumeObject (C.base : Set M))) := by
  let H := degreeOneHeadFactor C U b.admissible
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  let e := elementaryVolumeBlowup C P (degreeOnePointAdmissible hc (C.base : Set M))
  let f := elementaryBlowupIso hc C (degreeOneHeadPointVolumeIso C U b.admissible)
    b (weightedZeroElementary e H)
  exact f.trans hc C (zeroProductIso hc C (ZeroRVVolumeIso.refl H) (degreeOneBasicElementaryIso hc C))

theorem elementary_degree_one_weighted_factorization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) 0} (b : ElementaryBlowup U W) :
    ∃ H : ZeroRVVolumeObject (M := M) (C.base : Set M),
      Nonempty (RVVolumeIso U (zeroProduct H (degreeOnePointVolumeObject (C.base : Set M)))) ∧
      Nonempty (RVVolumeIso W (zeroProduct H (degreeOneConeVolumeObject (C.base : Set M)))) :=
  ⟨degreeOneHeadFactor C U b.admissible, ⟨degreeOneHeadPointVolumeIso C U b.admissible⟩,
    ⟨degreeOneHeadConeVolumeIso hc C b⟩⟩

theorem elementary_degree_one_product_factorization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) 0} (b : ElementaryBlowup U W) :
    ∃ H : RVVolumeObject (M := M) (C.base : Set M) 0,
      Nonempty (RVVolumeIso U (product (C.base : Set M) 0 1 H (degreeOnePointVolumeObject (C.base : Set M)))) ∧
      Nonempty (RVVolumeIso W (product (C.base : Set M) 0 1 H (degreeOneConeVolumeObject (C.base : Set M)))) := by
  obtain ⟨H,⟨hU⟩,⟨hW⟩⟩ := elementary_degree_one_weighted_factorization hc C b
  refine ⟨H,⟨hU.trans hc C ?_⟩,⟨hW.trans hc C ?_⟩⟩
  · exact (productZeroPositiveIso hc C H (degreeOnePointVolumeObject (C.base : Set M))).symm hc C
  · exact (productZeroPositiveIso hc C H (degreeOneConeVolumeObject (C.base : Set M))).symm hc C

end IntegrationInACVF.Section7.HK
