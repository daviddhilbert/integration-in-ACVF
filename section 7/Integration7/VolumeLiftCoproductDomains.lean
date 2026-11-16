module

public import Integration7.FixedVFVolumeCoproducts
public import Integration7.VFVolumeLifts

@[expose] public section

/-! Lifting an RV coproduct gives exactly the two tagged VF lifts,
including every original RV label and the coordinate-zero fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem volume_lift_coprod_domain
    (U V : PositiveRVVolumeObject (M := M) S k)
    (p : (Fin (k+1) → VFType (M := M)) ×
      (Fin (1+(U.underlying.obj.arity+V.underlying.obj.arity)) → CanonicalRV.RVSort M)) :
    p ∈ (rvVolumeLift (U.coprod V)).domain.carrier ↔
      p ∈ ((rvVolumeLift U).coprod (rvVolumeLift V)).domain.carrier := by
  constructor
  · rintro ⟨u,hu,hvol⟩
    change (rvCoprodObject U.underlying.obj V.underlying.obj).value u = tupleRV p.1 at hvol
    rcases u.property with ⟨v,hv⟩ | ⟨w,hw⟩
    · have he : rvCoprodLeftMap U.underlying.obj V.underlying.obj v = u := Subtype.ext hv
      rw [← he,rvCoprod_value_left] at hvol
      refine Or.inl ⟨⟨(p.1,v.val),⟨v,rfl,hvol⟩⟩,?_⟩
      exact Prod.ext rfl (hv.trans hu)
    · have he : rvCoprodRightMap U.underlying.obj V.underlying.obj w = u := Subtype.ext hw
      rw [← he,rvCoprod_value_right] at hvol
      refine Or.inr ⟨⟨(p.1,w.val),⟨w,rfl,hvol⟩⟩,?_⟩
      exact Prod.ext rfl (hw.trans hu)
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · obtain ⟨r,hr,hval⟩ := u.property
      refine ⟨rvCoprodLeftMap U.underlying.obj V.underlying.obj r,?_,?_⟩
      · exact (congrArg (rvLeftTag V.underlying.obj.arity) hr).trans (congrArg Prod.snd hu)
      · change (rvCoprodObject U.underlying.obj V.underlying.obj).value
          (rvCoprodLeftMap U.underlying.obj V.underlying.obj r) = tupleRV p.1
        rw [rvCoprod_value_left]
        exact hval.trans (congrArg tupleRV (congrArg Prod.fst hu))
    · obtain ⟨r,hr,hval⟩ := v.property
      refine ⟨rvCoprodRightMap U.underlying.obj V.underlying.obj r,?_,?_⟩
      · exact (congrArg (rvRightTag U.underlying.obj.arity) hr).trans (congrArg Prod.snd hv)
      · change (rvCoprodObject U.underlying.obj V.underlying.obj).value
          (rvCoprodRightMap U.underlying.obj V.underlying.obj r) = tupleRV p.1
        rw [rvCoprod_value_right]
        exact hval.trans (congrArg tupleRV (congrArg Prod.fst hv))

def volumeLiftCoprodMap (U V : PositiveRVVolumeObject (M := M) S k) :
    Map ((rvVolumeLift U).coprod (rvVolumeLift V)).domain (rvVolumeLift (U.coprod V)).domain :=
  Map.inclusion (fun p hp => (volume_lift_coprod_domain U V p).mpr hp)

theorem volume_lift_coprod_map_bijective (U V : PositiveRVVolumeObject (M := M) S k) :
    Function.Bijective (volumeLiftCoprodMap U V) := by
  constructor
  · intro p q h
    exact Subtype.ext (congrArg (fun r : (rvVolumeLift (U.coprod V)).domain => r.val) h)
  · intro p
    exact ⟨⟨p.val,(volume_lift_coprod_domain U V p.val).mp p.property⟩,rfl⟩

end IntegrationInACVF.Section7
