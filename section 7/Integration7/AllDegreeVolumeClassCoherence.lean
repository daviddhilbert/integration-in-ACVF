import Integration7.AllDegreeVolumeClasses
import Integration7.AllDegreeVolumeProductAssociativity
import Integration7.AllDegreeVolumeProductUnits
import Integration7.AllDegreeVolumeProductZeros
import Integration7.AllDegreeVolumeLeftDistributivity
import Integration7.AllDegreeVolumeRightDistributivity

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

-- The degree-zero family reduces to an ordinary quotient, so instance
-- search cannot reconstruct its erased degree parameter. Name this case.
instance rvVolumeIsoClassesZeroAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    AddCommMonoid (RVVolumeIsoClasses hc C 0) := rvVolumeIsoClassesAddCommMonoid hc C 0

instance rvVolumeBlowupClassesZeroAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    AddCommMonoid (RVVolumeBlowupClasses hc C 0) := rvVolumeBlowupClassesAddCommMonoid hc C 0

theorem rvVolumeIsoClass_heq_of_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (h : n=m) (U : RVVolumeObject (M := M) (C.base : Set M) n)
    (V : RVVolumeObject (M := M) (C.base : Set M) m)
    (e : RVVolumeIsoInDegree (C.base : Set M) n U (h.symm ▸ V)) :
    HEq (rvVolumeIsoClass hc C U) (rvVolumeIsoClass hc C V) := by
  cases h
  exact heq_of_eq (Quotient.sound ⟨e⟩)

theorem rvVolumeBlowupClass_heq_of_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (h : n=m) (U : RVVolumeObject (M := M) (C.base : Set M) n)
    (V : RVVolumeObject (M := M) (C.base : Set M) m)
    (e : RVVolumeIsoInDegree (C.base : Set M) n U (h.symm ▸ V)) :
    HEq (rvVolumeBlowupClass hc C U) (rvVolumeBlowupClass hc C V) := by
  cases h
  exact heq_of_eq (Quotient.sound (muIsp_of_iso hc C (n := n) (U := U) (V := V) e))

@[simp] theorem rvVolumeIsoClass_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n m : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) (V : RVVolumeObject (M := M) (C.base : Set M) m) :
    rvVolumeIsoClassesProduct hc C n m (rvVolumeIsoClass hc C U) (rvVolumeIsoClass hc C V) =
      rvVolumeIsoClass hc C (rvVolumeProduct _ n m U V) := rfl

@[simp] theorem rvVolumeBlowupClass_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n m : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) (V : RVVolumeObject (M := M) (C.base : Set M) m) :
    rvVolumeBlowupClassesProduct hc C n m (rvVolumeBlowupClass hc C U) (rvVolumeBlowupClass hc C V) =
      rvVolumeBlowupClass hc C (rvVolumeProduct _ n m U V) := rfl

end IntegrationInACVF.Section7
