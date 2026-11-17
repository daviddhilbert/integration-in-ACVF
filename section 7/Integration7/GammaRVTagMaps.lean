module

public import Integration7.GammaRVMapRestrictions
public import Section4.RVTagging

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual RV coproduct tag maps retain full Gamma graphs on their
given source domains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a : ℕ}

theorem gamma_rv_left_tag_map (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) a) S) (b : ℕ)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier}) :
    RVMapGamma (rvLeftTagMap A b) B :=
  gamma_real_rv_map_graph hc B _ (rvLeftTagMap (DefSet.univ (rawRVSpace (M := M) a) B.real) b)
    hA (fun _ => rfl)

theorem gamma_rv_right_tag_map (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) a) S) (b : ℕ)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier}) :
    RVMapGamma (rvRightTagMap A b) B :=
  gamma_real_rv_map_graph hc B _ (rvRightTagMap (DefSet.univ (rawRVSpace (M := M) a) B.real) b)
    hA (fun _ => rfl)

end IntegrationInACVF.Section7
