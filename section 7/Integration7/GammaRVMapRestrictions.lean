module

public import Integration7.GammaRVMapInverseGraphs
public import Integration7.RVCoordinateSelection

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Restricting or corestricting an actual raw RV map retains its full
Gamma graph when the new source is Gamma-definable. -/

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

theorem RVMapGamma.restrict (hf : RVMapGamma f B)
    {A' : DefSet (rawRVSpace (M := M) a) S} (hA : A'.carrier ⊆ A.carrier)
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A'.carrier}) :
    RVMapGamma (f.restrict hA) B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hΓ hf)
  intro p q
  constructor
  · rintro ⟨hp,u,hu,hq⟩
    let v : A' := ⟨p.2,hp⟩
    have he : (⟨v.val,hA v.property⟩ : A) = u := Subtype.ext hu.symm
    exact ⟨v,rfl,(congrArg (fun t => (f t).val) he).trans hq⟩
  · rintro ⟨v,hv,hq⟩
    exact ⟨(congrArg (fun r => r ∈ A'.carrier) hv).mp v.property,⟨v.val,hA v.property⟩,hv,hq⟩

theorem RVMapGamma.corestrict (hf : RVMapGamma f B)
    {D' : DefSet (rawRVSpace (M := M) b) S} (hD : ∀ u, (f u).val ∈ D'.carrier) :
    RVMapGamma (f.corestrict hD) B := hf.congr (fun _ => rfl)

theorem RVMapGamma.identity (hc : CanonicalStructure.IsCanonical (M := M))
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier}) :
    RVMapGamma (Map.id A) B :=
  gamma_real_rv_map_graph hc B _ (rvCoordinateSelectMap B.real id) hA (fun _ => rfl)

end IntegrationInACVF.Section7
