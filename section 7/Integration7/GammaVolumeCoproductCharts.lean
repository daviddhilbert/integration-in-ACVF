module

public import Integration7.GammaRVLabelIdentity
public import Integration7.VolumeCoproductIsomorphism

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Original-Gamma charts of actual volume isomorphisms are closed
under coproducts. No Gamma presentation of an entire ambient object is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem RVVolumeIso.GammaDefinable.coprod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) {k : ℕ}
    {U V U' V' : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {f : RVVolumeIso U U'} {g : RVVolumeIso V V'}
    (hf : f.GammaDefinable B) (hg : g.GammaDefinable B) :
    (f.coprod hc C g).GammaDefinable B := by
  let L := gammaLogicInput B
  have hl := L.comp_graph
    (L.swap_graph (gamma_rv_left_tag B U.underlying.obj.arity V.underlying.obj.arity))
    (L.comp_graph hf (gamma_rv_left_tag B U'.underlying.obj.arity V'.underlying.obj.arity))
  have hr := L.comp_graph
    (L.swap_graph (gamma_rv_right_tag B U.underlying.obj.arity V.underlying.obj.arity))
    (L.comp_graph hg (gamma_rv_right_tag B U'.underlying.obj.arity V'.underlying.obj.arity))
  apply GammaGraphDefinable.congr (L.union_graph hl hr)
  intro p q
  constructor
  · rintro (⟨z,hp,w,⟨a,ha,hw⟩,hq⟩ | ⟨z,hp,w,⟨a,ha,hw⟩,hq⟩)
    · refine ⟨coprodEssentialLeftMap U V a,?_,?_⟩
      · exact (congrArg (rvLeftTag (M := M) V.underlying.obj.arity) ha).trans hp
      · change (finiteIsoMap (RVVolumeIso.coprodUnderlying f g) (coprodEssentialLeftMap U V a)).val = q.2
        rw [RVVolumeIso.coprodUnderlying_left]
        exact (congrArg (rvLeftTag (M := M) V'.underlying.obj.arity) hw).trans hq
    · refine ⟨coprodEssentialRightMap U V a,?_,?_⟩
      · exact (congrArg (rvRightTag (M := M) U.underlying.obj.arity) ha).trans hp
      · change (finiteIsoMap (RVVolumeIso.coprodUnderlying f g) (coprodEssentialRightMap U V a)).val = q.2
        rw [RVVolumeIso.coprodUnderlying_right]
        exact (congrArg (rvRightTag (M := M) U'.underlying.obj.arity) hw).trans hq
  · rintro ⟨a,ha,hq⟩
    rcases coprodEssential_cover U V a with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · change (finiteIsoMap (RVVolumeIso.coprodUnderlying f g) (coprodEssentialLeftMap U V u)).val = q.2 at hq
      rw [RVVolumeIso.coprodUnderlying_left] at hq
      exact Or.inl ⟨(Fin.elim0,u.val),ha,(Fin.elim0,(finiteIsoMap f.iso u).val),⟨u,rfl,rfl⟩,hq⟩
    · change (finiteIsoMap (RVVolumeIso.coprodUnderlying f g) (coprodEssentialRightMap U V v)).val = q.2 at hq
      rw [RVVolumeIso.coprodUnderlying_right] at hq
      exact Or.inr ⟨(Fin.elim0,v.val),ha,(Fin.elim0,(finiteIsoMap g.iso v).val),⟨v,rfl,rfl⟩,hq⟩

end IntegrationInACVF.Section7
