import Integration7.SelectedFamilyRestrictions
import Integration7.EssentialVolumeLiftIsomorphisms
import Integration7.VFVolumeComposition
import Integration7.VFVolumeClasses

/-! Removing a definable VF-small base exception from an RV-valued
family gives an actual cofull volume isomorphism of its full VF realization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

def selectedFamilyFullLiftRestrictionBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C n a k)
    (L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier) :
    VFVolumeBijection (F.fullLift.restrict (F.restrict L hL).fullLift.domain
      (selected_family_full_lift_restrict_subset F L hL)) (F.restrict L hL).fullLift :=
  VFVolumeBijection.of_preserving_vf_and_density hc C
    (U := F.fullLift.restrict (F.restrict L hL).fullLift.domain
      (selected_family_full_lift_restrict_subset F L hL))
    (V := (F.restrict L hL).fullLift) (Map.id _)
    Function.bijective_id (fun _ => rfl) (fun _ => rfl)

def selectedFamilyCofullLiftIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C n a k)
    (L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier)
    (hSmall : vfDim (rawRVSpace (M := M) 1) (F.domain.sdiff L) < n) :
    VFVolumeIso F.fullLift (F.restrict L hL).fullLift :=
  ((vfVolumeCofullRestrictionIso hc C F.fullLift (F.restrict L hL).fullLift.domain
    (selected_family_full_lift_restrict_cofull F L hL hSmall)).symm hc C).trans hc C
      (VFVolumeIso.of_bijection (selectedFamilyFullLiftRestrictionBijection hc C F L hL))

theorem selected_family_full_lift_class_remove_small
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C n a k)
    (L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier)
    (hSmall : vfDim (rawRVSpace (M := M) 1) (F.domain.sdiff L) < n) :
    positiveVFVolumeIsoClass hc C F.fullLift = positiveVFVolumeIsoClass hc C (F.restrict L hL).fullLift :=
  (positiveVFVolumeIsoClass_eq_iff hc C).mpr ⟨selectedFamilyCofullLiftIso hc C F L hL hSmall⟩

theorem selected_family_full_lift_class_remove_small_base
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C n a k)
    (L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (hE : vfDim (rawRVSpace (M := M) 1) E < n)
    (hBad : ∀ p : F.domain.sdiff L, p.val.1 ∈ E.carrier) :
    positiveVFVolumeIsoClass hc C F.fullLift = positiveVFVolumeIsoClass hc C (F.restrict L hL).fullLift :=
  selected_family_full_lift_class_remove_small hc C F L hL
    ((mixed_domain_vf_dim_le_base (F.domain.sdiff L) E hBad).trans_lt hE)

end IntegrationInACVF.Section7
