module

public import Integration7.GammaRVMapGraphOperations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Full original-Gamma map graphs retain their domain, image and
bijective inverse, without enlarging the real parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b : ℕ}
variable {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
variable {f : Map A D}

theorem RVMapGamma.domain (hf : RVMapGamma f B) :
    GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier} := by
  have h := (gammaLogicInput B).image_graph ((gammaLogicInput B).swap_graph hf)
  convert h using 1
  ext p
  constructor
  · intro hp
    let u : A := ⟨p.2,hp⟩
    exact ⟨(Fin.elim0,(f u).val),u,rfl,rfl⟩
  · rintro ⟨q,u,hu,_⟩
    exact (congrArg (fun r => r ∈ A.carrier) hu).mp u.property

theorem RVMapGamma.range (hf : RVMapGamma f B) (hs : Function.Surjective f) :
    GammaSetDefinable B {q : Point (M := M) 0 b | q.2 ∈ D.carrier} := by
  have h := (gammaLogicInput B).image_graph hf
  convert h using 1
  ext q
  constructor
  · intro hq
    obtain ⟨u,hu⟩ := hs ⟨q.2,hq⟩
    exact ⟨(Fin.elim0,u.val),u,rfl,congrArg Subtype.val hu⟩
  · rintro ⟨p,u,_,hq⟩
    exact (congrArg (fun r => r ∈ D.carrier) hq).mp (f u).property

theorem RVMapGamma.inverse (hf : RVMapGamma f B) (hb : Function.Bijective f) :
    RVMapGamma (f.inverse hb) B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph hf)
  intro q p
  constructor
  · rintro ⟨u,hu,hq⟩
    refine ⟨f u,hq,?_⟩
    exact (congrArg Subtype.val (Map.inverse_apply f hb u)).trans hu
  · rintro ⟨v,hv,hp⟩
    refine ⟨f.inverse hb v,hp,?_⟩
    exact (congrArg Subtype.val (Map.apply_inverse f hb v)).trans hv

end IntegrationInACVF.Section7
