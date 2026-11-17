module

public import Integration7.MixedRVFactorDomains
public import Integration7.DefinableVFVolumeFamilies
public import Integration7.GradedVolumeProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual family multiplication by a constant positive RV volume
object. Old domain labels are kept first, while the volume tuple is
coefficient first, followed by the family's original tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}

def volumeFamilyConstantBaseProjection (F : DefinableVFVolumeFamily C n a k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    Map (mixedRVFactorDomain F.domain U.underlying.obj.domain) F.domain :=
  (Map.prodFst F.domain U.underlying.obj.domain).comp (mixedRVFactorUnpack F.domain U.underlying.obj.domain)

def volumeFamilyConstantCoefficientProjection (F : DefinableVFVolumeFamily C n a k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    Map (mixedRVFactorDomain F.domain U.underlying.obj.domain) U.underlying.obj.domain :=
  (Map.prodSnd F.domain U.underlying.obj.domain).comp (mixedRVFactorUnpack F.domain U.underlying.obj.domain)

def volumeFamilyConstantVolumeMap (F : DefinableVFVolumeFamily C n a k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    Map (mixedRVFactorDomain F.domain U.underlying.obj.domain)
      (DefSet.univ (rawRVSpace (M := M) ((p+1)+(k+1))) (C.base : Set M)) :=
  (rvAppendMap (C.base : Set M) (p+1) (k+1)).comp
    (((U.underlying.obj.volume.comp (volumeFamilyConstantCoefficientProjection F U)).pair
      (F.volume.comp (volumeFamilyConstantBaseProjection F U))).toUniv)

@[simp] theorem volume_family_constant_volume
    (F : DefinableVFVolumeFamily C n a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : mixedRVFactorDomain F.domain U.underlying.obj.domain) :
    (volumeFamilyConstantVolumeMap F U q).val =
      Fin.append (U.underlying.obj.value (volumeFamilyConstantCoefficientProjection F U q))
        (F.volume (volumeFamilyConstantBaseProjection F U q)).val := rfl

def volumeFamilyConstantForm (F : DefinableVFVolumeFamily C n a k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    VolumeForm (mixedRVFactorDomain F.domain U.underlying.obj.domain) :=
  (F.form.prod U.form).pullback (mixedRVFactorUnpack F.domain U.underlying.obj.domain)

@[simp] theorem volume_family_constant_density
    (F : DefinableVFVolumeFamily C n a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : mixedRVFactorDomain F.domain U.underlying.obj.domain) :
    (volumeFamilyConstantForm F U).value q =
      U.form.value (volumeFamilyConstantCoefficientProjection F U q) *
        F.form.value (volumeFamilyConstantBaseProjection F U q) := mul_comm _ _

end IntegrationInACVF.Section7
