module

public import Integration7.GammaVolumeBlowupRowPromotion
public import Integration7.FiniteVolumeIsoMaps
public import Section5.GammaInvariantLogic

@[expose] public section

/-! Original-Gamma charts of actual volume isomorphisms are closed
under composition and inverse, with no parameter-base enlargement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (GammaGraphDefinable gammaLogicInput)
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem RVVolumeIso.GammaDefinable.trans
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) {k : ℕ}
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {f : RVVolumeIso U V} {g : RVVolumeIso V W}
    (hf : f.GammaDefinable B) (hg : g.GammaDefinable B) :
    (f.trans hc C g).GammaDefinable B := by
  apply GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph hf hg)
  intro p q
  constructor
  · rintro ⟨m,⟨u,hu,hm⟩,⟨v,hv,hq⟩⟩
    have he : v = finiteIsoMap f.iso u := Subtype.ext (hv.trans hm.symm)
    refine ⟨u,hu,?_⟩
    exact (congrArg (fun z => (finiteIsoMap g.iso z).val) he).symm.trans hq
  · rintro ⟨u,hu,hq⟩
    exact ⟨(Fin.elim0,(finiteIsoMap f.iso u).val),⟨u,hu,rfl⟩,
      ⟨finiteIsoMap f.iso u,rfl,hq⟩⟩

theorem RVVolumeIso.GammaDefinable.symm
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {f : RVVolumeIso U V} (hf : f.GammaDefinable B) :
    (f.symm hc C).GammaDefinable B := by
  apply GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph hf)
  intro p q
  constructor
  · rintro ⟨u,hu,hp⟩
    refine ⟨finiteIsoMap f.iso u,hp,?_⟩
    exact (congrArg (fun z : U.essential.obj.domain => z.val)
      (finiteIsoMap_symm_apply f.iso u)).trans hu
  · rintro ⟨v,hv,hq⟩
    refine ⟨finiteIsoMap f.iso.symm v,hq,?_⟩
    exact (congrArg (fun z : V.essential.obj.domain => z.val)
      (finiteIsoMap_apply_symm f.iso v)).trans hv

end IntegrationInACVF.Section7
