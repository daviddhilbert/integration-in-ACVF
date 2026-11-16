module

public import Integration7.FixedVFVolumeCoproductBijections

@[expose] public section

/-! Restricting each summand agrees, including its actual density,
with restricting the disjoint union to the corresponding tagged locus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem vf_volume_coprod_restrict_subset
    (U V : PositiveVFVolumeObject (M := M) S k)
    (L : DefSet (rawMixedSpace (M := M) (k+1) U.arity) S)
    (K : DefSet (rawMixedSpace (M := M) (k+1) V.arity) S)
    (hL : L.carrier ⊆ U.domain.carrier) (hK : K.carrier ⊆ V.domain.carrier) :
    ((U.restrict L hL).coprod (V.restrict K hK)).domain.carrier ⊆ (U.coprod V).domain.carrier := by
  rintro p (⟨u,hu⟩ | ⟨v,hv⟩)
  · exact Or.inl ⟨⟨u.val,hL u.property⟩,hu⟩
  · exact Or.inr ⟨⟨v.val,hK v.property⟩,hv⟩

theorem vf_volume_coprod_restrict_density
    (U V : PositiveVFVolumeObject (M := M) S k)
    (L : DefSet (rawMixedSpace (M := M) (k+1) U.arity) S)
    (K : DefSet (rawMixedSpace (M := M) (k+1) V.arity) S)
    (hL : L.carrier ⊆ U.domain.carrier) (hK : K.carrier ⊆ V.domain.carrier)
    (p : ((U.restrict L hL).coprod (V.restrict K hK)).domain) :
    (U.coprod V).form.value ⟨p.val,vf_volume_coprod_restrict_subset U V L K hL hK p.property⟩ =
      ((U.restrict L hL).coprod (V.restrict K hK)).form.value p := by
  rcases vf_volume_coprod_cases (U.restrict L hL) (V.restrict K hK) p with ⟨u,rfl⟩ | ⟨v,rfl⟩
  · rw [vf_volume_coprod_density_left]
    exact vf_volume_coprod_density_left U V ⟨u.val,hL u.property⟩
  · rw [vf_volume_coprod_density_right]
    exact vf_volume_coprod_density_right U V ⟨v.val,hK v.property⟩

def vfVolumeCoprodRestrictionBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (L : DefSet (rawMixedSpace (M := M) (k+1) U.arity) (C.base : Set M))
    (K : DefSet (rawMixedSpace (M := M) (k+1) V.arity) (C.base : Set M))
    (hL : L.carrier ⊆ U.domain.carrier) (hK : K.carrier ⊆ V.domain.carrier) :
    VFVolumeBijection ((U.restrict L hL).coprod (V.restrict K hK))
      ((U.coprod V).restrict ((U.restrict L hL).coprod (V.restrict K hK)).domain
        (vf_volume_coprod_restrict_subset U V L K hL hK)) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (Map.id _)
    Function.bijective_id (fun _ => rfl)
    (fun p => (vf_volume_coprod_restrict_density U V L K hL hK p).symm)

end IntegrationInACVF.Section7
