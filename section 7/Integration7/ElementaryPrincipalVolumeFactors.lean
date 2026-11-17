module

public import Integration7.AdmissibleHeadPointIsomorphisms
public import Integration7.BasicVolumeRelation
public import Integration7.ElementaryBlowupIsomorphism
public import Integration7.ElementaryVolumeProducts
public import Integration7.RVVolumeProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The geometric factors of the principal blowup relation, when the
remaining degree is positive. The cone factor follows by transporting
the elementary blowup through the actual point-factor isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def elementaryHeadConeVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)}
    (b : ElementaryBlowup U W) :
    RVVolumeIso W ((admissibleHeadVolumeFactor C U b.admissible).prod
      (degreeOneConeVolumeObject (C.base : Set M))) := by
  let H := admissibleHeadVolumeFactor C U b.admissible
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  let e := elementaryVolumeBlowup C P (degreeOnePointAdmissible hc (C.base : Set M))
  let f := elementaryBlowupIso hc C (admissibleHeadPointVolumeIso C U b.admissible)
    b (e.product_left H)
  exact f.trans hc C ((RVVolumeIso.refl hc C H).prod hc C (degreeOneBasicElementaryIso hc C))

theorem elementary_volume_positive_factorization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)}
    (b : ElementaryBlowup U W) :
    ∃ H : PositiveRVVolumeObject (M := M) (C.base : Set M) k,
      Nonempty (RVVolumeIso U (H.prod (degreeOnePointVolumeObject (C.base : Set M)))) ∧
      Nonempty (RVVolumeIso W (H.prod (degreeOneConeVolumeObject (C.base : Set M)))) :=
  ⟨admissibleHeadVolumeFactor C U b.admissible,⟨admissibleHeadPointVolumeIso C U b.admissible⟩,
    ⟨elementaryHeadConeVolumeIso hc C b⟩⟩

end IntegrationInACVF.Section7
