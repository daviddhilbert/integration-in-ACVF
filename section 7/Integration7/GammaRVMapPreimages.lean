module

public import Integration7.GammaRVMapRestrictions
public import Integration7.DefinableMapPreimages

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Preimages under actual full Gamma raw RV maps retain their original
Gamma definition, including the map's exact source domain. -/

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

theorem RVMapGamma.preimage
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    {f : Map A D} (hf : RVMapGamma f B)
    (E : DefSet (rawRVSpace (M := M) b) S)
    (hE : GammaSetDefinable B {q : Point (M := M) 0 b | q.2 ∈ E.carrier}) :
    GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ (definableMapPreimage f E).carrier} := by
  have h := (gammaLogicInput B).image_graph
    ((gammaLogicInput B).restrict_graph hE ((gammaLogicInput B).swap_graph hf))
  convert h using 1
  ext p
  constructor
  · rintro ⟨u,hu,hE⟩
    exact ⟨(Fin.elim0,(f u).val),hE,u,hu,rfl⟩
  · rintro ⟨q,hq,u,hu,he⟩
    exact ⟨u,hu,(congrArg (fun r => r ∈ E.carrier) he).mpr hq⟩

end IntegrationInACVF.Section7
