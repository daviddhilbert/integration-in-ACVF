module

public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.VFBaseDimensionBounds
public import Integration7.DefinableMapPreimages
public import Integration7.VFVolumeComposition
public import Integration7.VFVolumeClasses

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Removing a VF-small base exception from an ordinary family does
not change its actual unit-density VF volume class. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}

def OrdinaryVFVolumeFamily.restrict (F : OrdinaryVFVolumeFamily C n a)
    (L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier) : OrdinaryVFVolumeFamily C n a where
  domain := L
  finite_labels x := (F.finite_labels x).subset (fun r hr => hL hr)

def OrdinaryVFVolumeFamily.outsideBase (F : OrdinaryVFVolumeFamily C n a)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M)) : OrdinaryVFVolumeFamily C n a :=
  F.restrict (F.domain.sdiff (definableMapPreimage
    (Map.fst (rawVFSpace (M := M) n) (rawRVSpace a) (C.base : Set M) F.domain) E)) Set.sdiff_subset

theorem ordinary_volume_family_outside_base_mem (F : OrdinaryVFVolumeFamily C n a)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (q : (rawMixedSpace (M := M) n a).Carrier) :
    q ∈ (F.outsideBase E).domain.carrier ↔ q ∈ F.domain.carrier ∧ q.1 ∉ E.carrier := by
  let P := Map.fst (rawVFSpace (M := M) n) (rawRVSpace a) (C.base : Set M) F.domain
  change (q ∈ F.domain.carrier ∧ q ∉ (definableMapPreimage P E).carrier) ↔ _
  constructor
  · rintro ⟨hq,h⟩
    exact ⟨hq,fun he => h ((mem_definableMapPreimage P E ⟨q,hq⟩).mpr he)⟩
  · rintro ⟨hq,h⟩
    exact ⟨hq,fun he => h ((mem_definableMapPreimage P E ⟨q,hq⟩).mp he)⟩

theorem ordinary_volume_full_class_outside_base
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : OrdinaryVFVolumeFamily C (n+1) a)
    (E : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (hE : vfDim (rawRVSpace (M := M) 1) E < n+1) :
    positiveVFVolumeIsoClass hc C F.fullVFObject =
      positiveVFVolumeIsoClass hc C (F.outsideBase E).fullVFObject := by
  let L := (F.outsideBase E).domain
  have hL : VFCofull F.domain L := ⟨Set.sdiff_subset,
    (mixed_domain_vf_dim_le_base (F.domain.sdiff L) E (by
      intro q
      by_contra he
      exact q.property.2 ((ordinary_volume_family_outside_base_mem F E q.val).mpr ⟨q.property.1,he⟩))).trans_lt hE⟩
  exact (positiveVFVolumeIsoClass_eq_iff hc C).mpr ⟨
    (vfVolumeCofullRestrictionIso hc C F.fullVFObject L hL).symm hc C⟩

end IntegrationInACVF.Section7
