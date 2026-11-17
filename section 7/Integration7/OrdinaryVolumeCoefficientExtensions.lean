module

public import Integration7.AllDegreeVolumeBlowupSemiring
public import Integration7.VolumeIsoParameterExtension

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Ordinary degree-zero coefficient classes extend along the actual
parameter-base inclusion as a semiring homomorphism. Every operation is
the genuine finite RV coproduct or product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ordinaryVolumeCoefficientExtend
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) :
    RVVolumeBlowupClasses hc C 0 →+* RVVolumeBlowupClasses hc D 0 where
  toFun := Quotient.map (Section6.FiniteRV.extendObject hCD) (by
    rintro Z T ⟨g⟩
    exact ⟨finiteVolumeIsoExtend hCD g⟩)
  map_zero' := Quotient.sound ⟨finiteIsoOfNondegenerateBijection (Map.id _) Function.bijective_id
    (fun _ i => i.elim0) (fun _ i => i.elim0)⟩
  map_one' := Quotient.sound ⟨finiteIsoOfNondegenerateBijection (Map.id _) Function.bijective_id
    (fun _ i => i.elim0) (fun _ i => i.elim0)⟩
  map_add' z t := Quotient.inductionOn₂ z t (fun Z T => Quotient.sound
    ⟨finiteIsoOfNondegenerateBijection (Map.id _) Function.bijective_id
      (fun _ i => i.elim0) (fun _ i => i.elim0)⟩)
  map_mul' z t := Quotient.inductionOn₂ z t (fun Z T => Quotient.sound
    ⟨finiteIsoOfNondegenerateBijection (Map.id _) Function.bijective_id
      (fun _ i => i.elim0) (fun _ i => i.elim0)⟩)

end IntegrationInACVF.Section7
