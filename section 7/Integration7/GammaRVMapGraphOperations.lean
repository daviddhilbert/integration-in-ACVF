module

public import Integration7.GammaRealRVMaps
public import IntegrationSection6.GammaRVProductRelations
public import Section4.RVAppend

@[expose] public section

/-! Full Gamma graphs of actual raw RV maps are closed under
composition and pairing their output tuples on a common source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable gammaLogicInput rvCoordinatePointMap)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b c : ℕ}

def RVMapGamma {A : DefSet (rawRVSpace (M := M) a) S}
    {D : DefSet (rawRVSpace (M := M) b) S} (f : Map A D) (B : Base (M := M)) : Prop :=
  GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
    ∃ u : A, u.val = p.2 ∧ (f u).val = q.2)

theorem RVMapGamma.comp
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    {E : DefSet (rawRVSpace (M := M) c) S} {f : Map A D} {g : Map D E}
    (hf : RVMapGamma f B) (hg : RVMapGamma g B) : RVMapGamma (g.comp f) B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph hf hg)
  intro p q
  constructor
  · rintro ⟨m,⟨u,hu,hm⟩,⟨v,hv,hq⟩⟩
    have he : v = f u := Subtype.ext (hv.trans hm.symm)
    exact ⟨u,hu,(congrArg (fun z => (g z).val) he).symm.trans hq⟩
  · rintro ⟨u,hu,hq⟩
    exact ⟨(Fin.elim0,(f u).val),⟨u,hu,rfl⟩,⟨f u,rfl,hq⟩⟩

theorem RVMapGamma.congr
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    {E : DefSet (rawRVSpace (M := M) b) S} {f : Map A D} {g : Map A E}
    (hf : RVMapGamma f B) (hfg : ∀ u, (f u).val = (g u).val) : RVMapGamma g B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hf
  intro p q
  exact exists_congr (fun u => and_congr Iff.rfl (by rw [hfg u]))

theorem RVMapGamma.append
    {A : DefSet (rawRVSpace (M := M) a) S}
    {f : Map A (DefSet.univ (rawRVSpace (M := M) b) S)}
    {g : Map A (DefSet.univ (rawRVSpace (M := M) c) S)}
    (hf : RVMapGamma f B) (hg : RVMapGamma g B) :
    RVMapGamma ((rvAppendMap S b c).comp (f.pair g).toUniv) B := by
  have hl := hf.preimage_maps (rvCoordinatePointMap id B.real) (rvCoordinatePointMap (Fin.castAdd c) B.real)
  have hr := hg.preimage_maps (rvCoordinatePointMap id B.real) (rvCoordinatePointMap (Fin.natAdd b) B.real)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (hl.inter hr)
  intro p q
  constructor
  · rintro ⟨⟨u,hu,hf⟩,⟨v,hv,hg⟩⟩
    have he : v = u := Subtype.ext (hv.trans hu.symm)
    refine ⟨u,hu,?_⟩
    change Fin.append (f u).val (g u).val = q.2
    exact (congrArg₂ Fin.append hf (he ▸ hg)).trans Fin.append_castAdd_natAdd
  · rintro ⟨u,hu,hq⟩
    have hl : (f u).val = q.2 ∘ Fin.castAdd c := by
      funext i
      exact (Fin.append_left (f u).val (g u).val i).symm.trans (congrFun hq (Fin.castAdd c i))
    have hr : (g u).val = q.2 ∘ Fin.natAdd b := by
      funext i
      exact (Fin.append_right (f u).val (g u).val i).symm.trans (congrFun hq (Fin.natAdd b i))
    exact ⟨⟨u,hu,hl⟩,⟨u,hu,hr⟩⟩

end IntegrationInACVF.Section7
