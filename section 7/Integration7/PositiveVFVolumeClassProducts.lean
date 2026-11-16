module

public import Integration7.VFVolumeProductIsomorphisms
public import Integration7.VFVolumeClasses

@[expose] public section

/-! Cartesian multiplication on the actual positive VF volume
isomorphism quotients, defined by multiplying representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

def positiveVFVolumeClassesProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (a : PositiveVFVolumeIsoClasses hc C n) (b : PositiveVFVolumeIsoClasses hc C m) :
    PositiveVFVolumeIsoClasses hc C ((n+1)+m) :=
  Quotient.map₂ PositiveVFVolumeObject.prod (by
    rintro U U' ⟨f⟩ V V' ⟨g⟩
    exact ⟨f.prod hc C g⟩) a b

@[simp] theorem positive_vf_volume_classes_product_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveVFVolumeObject (M := M) (C.base : Set M) m) :
    positiveVFVolumeClassesProduct hc C (positiveVFVolumeIsoClass hc C U)
      (positiveVFVolumeIsoClass hc C V) = positiveVFVolumeIsoClass hc C (U.prod V) := rfl

end IntegrationInACVF.Section7
