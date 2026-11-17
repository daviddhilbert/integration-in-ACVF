module

public import Integration7.DefinableVolumeFamilyCoproductData

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The tagged disjoint union is an actual definable positive volume
family. Fixing a VF tuple and a volume tuple leaves only finitely many
RV labels in each summand. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

def DefinableVFVolumeFamily.coprod (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k) :
    DefinableVFVolumeFamily C n (1+(a+b)) k where
  domain := volumeFamilyCoprodDomain F G
  volume := volumeFamilyCoprodVolumeMap F G
  form := volumeFamilyCoprodForm F G
  finite_volume x t := by
    apply (((F.finite_volume x t).image (rvLeftTag b)).union
      ((G.finite_volume x t).image (rvRightTag a))).subset
    rintro r ⟨p,hp,ht⟩
    rcases p.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · left
      have hPoint : volumeFamilyCoprodLeftMap F G u=p := Subtype.ext hu
      have hV := congrArg Subtype.val (volume_family_coprod_volume_left F G u)
      rw [hPoint] at hV
      have he := hu.trans hp
      change (u.val.1,rvLeftTag b u.val.2)=(x,r) at he
      have hx := congrArg Prod.fst he
      have hRV := congrArg Prod.snd he
      exact ⟨u.val.2,⟨u,Prod.ext hx rfl,hV.symm.trans ht⟩,hRV⟩
    · right
      have hPoint : volumeFamilyCoprodRightMap F G v=p := Subtype.ext hv
      have hV := congrArg Subtype.val (volume_family_coprod_volume_right F G v)
      rw [hPoint] at hV
      have he := hv.trans hp
      change (v.val.1,rvRightTag a v.val.2)=(x,r) at he
      have hx := congrArg Prod.fst he
      have hRV := congrArg Prod.snd he
      exact ⟨v.val.2,⟨v,Prod.ext hx rfl,hV.symm.trans ht⟩,hRV⟩

theorem definable_volume_family_coprod_cases
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k) (p : (F.coprod G).domain) :
    (∃ u : F.domain,volumeFamilyCoprodLeftMap F G u=p) ∨
      (∃ v : G.domain,volumeFamilyCoprodRightMap F G v=p) := by
  rcases p.property with ⟨u,hu⟩ | ⟨v,hv⟩
  · exact Or.inl ⟨u,Subtype.ext hu⟩
  · exact Or.inr ⟨v,Subtype.ext hv⟩

end IntegrationInACVF.Section7
