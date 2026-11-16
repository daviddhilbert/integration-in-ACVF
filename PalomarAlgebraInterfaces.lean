module
public import PalomarGeometryInterfaces
public section
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
theorem palomar_rvVolumeIsoClassesAddCommMonoid_toAdd (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
  (rvVolumeIsoClassesAddCommMonoid hc C n).toAdd = rvVolumeIsoClassesAdd hc C n := rfl

theorem palomar_rvVolumeIsoClassesAddCommMonoid_toZero (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
  (rvVolumeIsoClassesAddCommMonoid hc C n).toZero = rvVolumeIsoClassesZero hc C n := rfl

theorem palomar_rvVolumeIsoClassesGMonoid_toGMul (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeIsoClassesGMonoid hc C).toGMul = rvVolumeIsoClassesGMul hc C := rfl

theorem palomar_rvVolumeIsoClassesGMonoid_toGOne (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeIsoClassesGMonoid hc C).toGOne = rvVolumeIsoClassesGOne hc C := rfl

theorem palomar_rvVolumeIsoClassesGNonUnital_toGMul (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeIsoClassesGNonUnitalNonAssocSemiring hc C).toGMul = rvVolumeIsoClassesGMul hc C := rfl

theorem palomar_rvVolumeIsoClassesGSemiring_toGNonUnitalNonAssocSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeIsoClassesGSemiring hc C).toGNonUnitalNonAssocSemiring = rvVolumeIsoClassesGNonUnitalNonAssocSemiring hc C := rfl

theorem palomar_rvVolumeIsoClassesGSemiring_toGMonoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeIsoClassesGSemiring hc C).toGMonoid = rvVolumeIsoClassesGMonoid hc C := rfl

theorem palomar_rvVolumeBlowupClassesAddCommMonoid_toAdd (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
  (rvVolumeBlowupClassesAddCommMonoid hc C n).toAdd = rvVolumeBlowupClassesAdd hc C n := rfl

theorem palomar_rvVolumeBlowupClassesAddCommMonoid_toZero (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
  (rvVolumeBlowupClassesAddCommMonoid hc C n).toZero = rvVolumeBlowupClassesZero hc C n := rfl

theorem palomar_rvVolumeBlowupClassesGMonoid_toGMul (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeBlowupClassesGMonoid hc C).toGMul = rvVolumeBlowupClassesGMul hc C := rfl

theorem palomar_rvVolumeBlowupClassesGMonoid_toGOne (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeBlowupClassesGMonoid hc C).toGOne = rvVolumeBlowupClassesGOne hc C := rfl

theorem palomar_rvVolumeBlowupClassesGNonUnital_toGMul (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeBlowupClassesGNonUnitalNonAssocSemiring hc C).toGMul = rvVolumeBlowupClassesGMul hc C := rfl

theorem palomar_rvVolumeBlowupClassesGSemiring_toGNonUnitalNonAssocSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeBlowupClassesGSemiring hc C).toGNonUnitalNonAssocSemiring = rvVolumeBlowupClassesGNonUnitalNonAssocSemiring hc C := rfl

theorem palomar_rvVolumeBlowupClassesGSemiring_toGMonoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeBlowupClassesGSemiring hc C).toGMonoid = rvVolumeBlowupClassesGMonoid hc C := rfl

theorem palomar_rvVolumeIsoClassesAddCommMonoid_nsmul (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
  (rvVolumeIsoClassesAddCommMonoid hc C n).nsmul = nsmulRec := rfl

theorem palomar_rvVolumeIsoClassesGMonoid_gnpow (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeIsoClassesGMonoid hc C).gnpow = GradedMonoid.GMonoid.gnpowRec := rfl

theorem palomar_rvVolumeIsoClassesGSemiring_natCast (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
  (rvVolumeIsoClassesGSemiring hc C).natCast n = n • rvVolumeIsoClass hc C (n := 0) (unit (C.base : Set M)) := rfl

theorem palomar_rvVolumeBlowupClassesAddCommMonoid_nsmul (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
  (rvVolumeBlowupClassesAddCommMonoid hc C n).nsmul = nsmulRec := rfl

theorem palomar_rvVolumeBlowupClassesGMonoid_gnpow (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
  (rvVolumeBlowupClassesGMonoid hc C).gnpow = GradedMonoid.GMonoid.gnpowRec := rfl

theorem palomar_rvVolumeBlowupClassesGSemiring_natCast (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
  (rvVolumeBlowupClassesGSemiring hc C).natCast n = n • rvVolumeBlowupClass hc C (n := 0) (unit (C.base : Set M)) := rfl

theorem palomar_iso_add_classes (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    (U V : RVVolumeObject (M := M) (C.base : Set M) n) :
  (rvVolumeIsoClassesAdd hc C n).add (rvVolumeIsoClass hc C U) (rvVolumeIsoClass hc C V) =
    rvVolumeIsoClass hc C (coprod (C.base : Set M) n U V) := rfl

end IntegrationInACVF.Section7.HK
