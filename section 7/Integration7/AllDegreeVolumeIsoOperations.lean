import Integration7.AllDegreeVolumeClasses

noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvVolumeIsoRefl (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    RVVolumeIsoInDegree (C.base : Set M) n U U := by
  cases n with
  | zero => exact Iso.refl U
  | succ k => exact RVVolumeIso.refl hc C U

def rvVolumeIsoSymm (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U V : RVVolumeObject (M := M) (C.base : Set M) n}
    (f : RVVolumeIsoInDegree (C.base : Set M) n U V) : RVVolumeIsoInDegree (C.base : Set M) n V U := by
  cases n with
  | zero => exact f.symm
  | succ k => exact f.symm hc C

def rvVolumeIsoTrans (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U V W : RVVolumeObject (M := M) (C.base : Set M) n}
    (f : RVVolumeIsoInDegree (C.base : Set M) n U V)
    (g : RVVolumeIsoInDegree (C.base : Set M) n V W) : RVVolumeIsoInDegree (C.base : Set M) n U W := by
  cases n with
  | zero => exact f.trans g
  | succ k => exact f.trans hc C g

end IntegrationInACVF.Section7
