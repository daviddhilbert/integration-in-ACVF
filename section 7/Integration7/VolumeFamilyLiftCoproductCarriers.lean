module

public import Integration7.DefinableVolumeFamilyLiftCarriers
public import Integration7.DefinableVolumeFamilyCoproducts
public import Integration7.FixedVFVolumeCoproducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Full family realization commutes with tagged coproducts on the
literal carrier: the VF tail realizes the same volume tuple on each
summand, and the old RV tag is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

theorem volume_family_lift_coprod_carrier
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k) :
    (F.coprod G).fullLift.domain.carrier = (F.fullLift.coprod G.fullLift).domain.carrier := by
  ext w
  rcases w with ⟨x,r⟩
  constructor
  · intro hw
    obtain ⟨p,hp,ht⟩ := (mem_definable_volume_family_full_lift (F.coprod G) x r).mp hw
    rcases definable_volume_family_coprod_cases F G p with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · change (u.val.1,rvLeftTag b u.val.2) = (x ∘ Fin.castAdd (k+1),r) at hp
      have hx := congrArg Prod.fst hp
      have hr := congrArg Prod.snd hp
      have hv := congrArg Subtype.val (volume_family_coprod_volume_left F G u)
      have hu : (x,u.val.2) ∈ F.fullLift.domain.carrier :=
        (mem_definable_volume_family_full_lift F x u.val.2).mpr ⟨u,Prod.ext hx rfl,ht.trans hv⟩
      exact Or.inl ⟨⟨(x,u.val.2),hu⟩,Prod.ext rfl hr⟩
    · change (v.val.1,rvRightTag a v.val.2) = (x ∘ Fin.castAdd (k+1),r) at hp
      have hx := congrArg Prod.fst hp
      have hr := congrArg Prod.snd hp
      have hv := congrArg Subtype.val (volume_family_coprod_volume_right F G v)
      have hvLift : (x,v.val.2) ∈ G.fullLift.domain.carrier :=
        (mem_definable_volume_family_full_lift G x v.val.2).mpr ⟨v,Prod.ext hx rfl,ht.trans hv⟩
      exact Or.inr ⟨⟨(x,v.val.2),hvLift⟩,Prod.ext rfl hr⟩
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · change (u.val.1,rvLeftTag b u.val.2) = (x,r) at hu
      have hx := congrArg Prod.fst hu
      have hr := congrArg Prod.snd hu
      let p := F.fullLiftBaseProjection u
      have hp := F.fullLiftBaseProjection_value u
      have hpVF := congrArg Prod.fst hp
      have hpRV := congrArg Prod.snd hp
      apply (mem_definable_volume_family_full_lift (F.coprod G) x r).mpr
      refine ⟨volumeFamilyCoprodLeftMap F G p,?_,?_⟩
      · change (p.val.1,rvLeftTag b p.val.2) = _
        exact Prod.ext (hpVF.trans (congrArg (fun y => y ∘ Fin.castAdd (k+1)) hx))
          ((congrArg (rvLeftTag b) hpRV).trans hr)
      · have ht := F.fullLift_volume_constraint u
        have hvol := congrArg Subtype.val (volume_family_coprod_volume_left F G p)
        exact (congrArg (fun y => tupleRV (y ∘ Fin.natAdd n)) hx).symm.trans (ht.trans hvol.symm)
    · change (v.val.1,rvRightTag a v.val.2) = (x,r) at hv
      have hx := congrArg Prod.fst hv
      have hr := congrArg Prod.snd hv
      let p := G.fullLiftBaseProjection v
      have hp := G.fullLiftBaseProjection_value v
      have hpVF := congrArg Prod.fst hp
      have hpRV := congrArg Prod.snd hp
      apply (mem_definable_volume_family_full_lift (F.coprod G) x r).mpr
      refine ⟨volumeFamilyCoprodRightMap F G p,?_,?_⟩
      · change (p.val.1,rvRightTag a p.val.2) = _
        exact Prod.ext (hpVF.trans (congrArg (fun y => y ∘ Fin.castAdd (k+1)) hx))
          ((congrArg (rvRightTag a) hpRV).trans hr)
      · have ht := G.fullLift_volume_constraint v
        have hvol := congrArg Subtype.val (volume_family_coprod_volume_right F G p)
        exact (congrArg (fun y => tupleRV (y ∘ Fin.natAdd n)) hx).symm.trans (ht.trans hvol.symm)

end IntegrationInACVF.Section7
