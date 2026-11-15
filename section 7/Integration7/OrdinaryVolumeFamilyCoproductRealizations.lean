import Integration7.OrdinaryVolumeFamilyCoproducts
import Integration7.VFVolumeBijections
import Integration7.PositiveVolumeIntegrationEquivalence

/-! The full VF realization of an ordinary family coproduct is the
actual VF coproduct, with its unit form verified on both summands. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

def ordinaryVolumeFamilyCoprodRealizationBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b) :
    VFVolumeBijection (F.coprod G).fullVFObject (F.fullVFObject.coprod G.fullVFObject) := by
  refine VFVolumeBijection.of_preserving_vf_and_density hc C (Map.id _) Function.bijective_id
    (fun _ => rfl) ?_
  intro q
  rcases vf_volume_coprod_cases F.fullVFObject G.fullVFObject q with ⟨u,rfl⟩ | ⟨v,rfl⟩
  · exact (vf_volume_coprod_density_left F.fullVFObject G.fullVFObject u).symm
  · exact (vf_volume_coprod_density_right F.fullVFObject G.fullVFObject v).symm

theorem ordinary_volume_family_coprod_full_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b) :
    positiveVFVolumeIsoClass hc C (F.coprod G).fullVFObject =
      positiveVFVolumeIsoClass hc C F.fullVFObject + positiveVFVolumeIsoClass hc C G.fullVFObject :=
  (positiveVFVolumeIsoClass_eq_iff hc C).mpr
    ⟨VFVolumeIso.of_bijection (ordinaryVolumeFamilyCoprodRealizationBijection hc F G)⟩

end IntegrationInACVF.Section7
