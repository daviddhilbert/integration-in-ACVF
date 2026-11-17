module

public import Integration7.GammaRVMapGraphOperations
public import Integration7.GammaRVLabelIdentity
public import Section4.RVCoproduct

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A map out of the actual RV tagged coproduct has its full Gamma graph
when its two prescribed branch maps do. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k c : ℕ}

theorem gamma_tagged_rv_map_graph (U V : RVObject (M := M) S k)
    {D : DefSet (rawRVSpace (M := M) c) S}
    (F : Map (rvCoprodObject U V).domain D)
    (f : Map U.domain (DefSet.univ (rawRVSpace (M := M) c) S))
    (g : Map V.domain (DefSet.univ (rawRVSpace (M := M) c) S))
    (hf : RVMapGamma f B) (hg : RVMapGamma g B)
    (hl : ∀ u, (F (rvCoprodLeftMap U V u)).val = (f u).val)
    (hr : ∀ v, (F (rvCoprodRightMap U V v)).val = (g v).val) : RVMapGamma F B := by
  let L := gammaLogicInput B
  have hleft := L.comp_graph (L.swap_graph (gamma_rv_left_tag B U.arity V.arity)) hf
  have hright := L.comp_graph (L.swap_graph (gamma_rv_right_tag B U.arity V.arity)) hg
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.union_graph hleft hright)
  intro p q
  constructor
  · rintro (⟨z,htag,u,hu,hq⟩ | ⟨z,htag,v,hv,hq⟩)
    · refine ⟨rvCoprodLeftMap U V u,(congrArg (rvLeftTag V.arity) hu).trans htag,?_⟩
      exact (hl u).trans hq
    · refine ⟨rvCoprodRightMap U V v,(congrArg (rvRightTag U.arity) hv).trans htag,?_⟩
      exact (hr v).trans hq
  · rintro ⟨w,hw,hq⟩
    rcases w.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · have he : w = rvCoprodLeftMap U V u := Subtype.ext hu.symm
      refine Or.inl ⟨(Fin.elim0,u.val),hu.trans hw,u,rfl,?_⟩
      rw [he,hl] at hq
      exact hq
    · have he : w = rvCoprodRightMap U V v := Subtype.ext hv.symm
      refine Or.inr ⟨(Fin.elim0,v.val),hv.trans hw,v,rfl,?_⟩
      rw [he,hr] at hq
      exact hq

end IntegrationInACVF.Section7
