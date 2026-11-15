import Integration7.OrdinaryVolumeFamilyScalarProducts
import Integration7.MixedRVFactorZeroLiftCharts
import Integration7.ZeroFactorVFVolumeClassProducts

/-! The actual VF realization of an ordinary finite-factor family is
the Cartesian product with the coefficient's degree-zero VF lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}

def ordinaryVolumeScalarRealizationBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    VFVolumeBijection (F.prodZero Z).fullVFObject (F.fullVFObject.prod_zero Z) := by
  have he : (F.prodZero Z).fullVFObject.domain.carrier=(F.fullVFObject.prod_zero Z).domain.carrier :=
    mixed_rv_factor_zero_lift_carrier F.domain Z
  let f : Map (F.prodZero Z).fullVFObject.domain (F.fullVFObject.prod_zero Z).domain := Map.inclusion he.le
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have hv := congrArg (fun w : (F.fullVFObject.prod_zero Z).domain => w.val) h
      exact Subtype.ext hv
    · intro p
      exact ⟨⟨p.val,he.ge p.property⟩,rfl⟩
  exact VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl) (fun _ => rfl)

theorem ordinary_volume_family_scalar_full_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    positiveVFVolumeIsoClass hc C (F.prodZero Z).fullVFObject =
      positiveVFZeroCoefficientProduct hc C (positiveVFVolumeIsoClass hc C F.fullVFObject)
        (rvVolumeBlowupClass hc C (n := 0) Z) :=
  (positiveVFVolumeIsoClass_eq_iff hc C).mpr
    ⟨VFVolumeIso.of_bijection (ordinaryVolumeScalarRealizationBijection hc F Z)⟩

end IntegrationInACVF.Section7
