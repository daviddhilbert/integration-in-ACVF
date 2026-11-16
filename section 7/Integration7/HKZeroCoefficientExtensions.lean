module

public import Integration7.HKZeroCoefficientSemiring
public import Integration7.HKZeroVolumeFamilies
public import Integration7.VolumeIsoParameterExtension

@[expose] public section

/-! Weighted measured-zero coefficient classes extend along the actual
parameter-base inclusion as a semiring homomorphism. Every operation is
the genuine finite RV coproduct or product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def zeroVolumeCoefficientExtend
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) :
    RVBlowupClasses hc C 0 →+* RVBlowupClasses hc D 0 where
  toFun := Quotient.map (fun Z => Z.extend hCD) (by
    rintro Z T ⟨g⟩
    exact ⟨⟨finiteVolumeIsoExtend hCD g.iso,fun _ => g.density _⟩⟩)
  map_zero' := Quotient.sound ⟨ZeroRVVolumeIso.ofBijection (Map.id _) Function.bijective_id (fun _ => rfl)⟩
  map_one' := Quotient.sound ⟨ZeroRVVolumeIso.ofBijection (Map.id _) Function.bijective_id (fun _ => rfl)⟩
  map_add' z t := Quotient.inductionOn₂ z t (fun Z T => Quotient.sound
    ⟨ZeroRVVolumeIso.ofBijection (Map.id _) Function.bijective_id (fun _ => rfl)⟩)
  map_mul' z t := Quotient.inductionOn₂ z t (fun Z T => Quotient.sound
    ⟨ZeroRVVolumeIso.ofBijection (Map.id _) Function.bijective_id (fun _ => rfl)⟩)

end IntegrationInACVF.Section7.HK
