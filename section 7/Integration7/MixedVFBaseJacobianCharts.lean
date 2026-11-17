module

public import Integration7.VFBaseJacobianDensities
public import Integration7.MixedJacobianRestriction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Changing only a VF base has the same Jacobian with any fixed RV
labels attached. The actual family restriction has that Jacobian whenever
both Jacobians are defined; no boundary definedness is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}
variable {X Y : DefSet (rawVFSpace (M := M) n) S}

theorem has_mixed_vf_jacobian_base_product
    (φ : Map X Y) (p : X.prod (DefSet.univ (rawRVSpace (M := M) a) S))
    (J : VFType (M := M))
    (hJ : HasMixedVFJacobianAt (pureVFMixedMap φ) (pureVFEmptyGraphMap X ⟨p.val.1,p.property.1⟩) J) :
    HasMixedVFJacobianAt (Map.prodMap φ (Map.id (DefSet.univ (rawRVSpace (M := M) a) S))) p J := by
  obtain ⟨F,⟨ρ,hρ⟩,hJF⟩ := hJ
  refine ⟨F,⟨ρ,?_⟩,hJF⟩
  intro z hz
  obtain ⟨hzX,hF⟩ := hρ z hz
  refine ⟨⟨hzX.1,Set.mem_univ _⟩,?_⟩
  change ((φ ⟨z,hzX.1⟩).val,p.val.2) = (F z,p.val.2)
  have h := congrArg (fun q : (Fin n → VFType (M := M)) × (Fin 0 → CanonicalRV.RVSort M) => q.1) hF
  exact Prod.ext h rfl

theorem mixed_vf_base_jacobian_eq
    (φ : Map X Y) (U : DefSet (rawMixedSpace (M := M) n a) S)
    (hU : ∀ p : U, p.val.1 ∈ X.carrier) (p : U) (J K : VFType (M := M))
    (hBase : HasMixedVFJacobianAt (pureVFMixedMap φ) (pureVFEmptyGraphMap X ⟨p.val.1,hU p⟩) J)
    (hFamily : HasMixedVFJacobianAt (mixedVFBaseMap φ U hU).toImage p K) : J = K := by
  let R := DefSet.univ (rawRVSpace (M := M) a) S
  have hLA : U.carrier ⊆ (X.prod R).carrier := fun q hq => ⟨hU ⟨q,hq⟩,Set.mem_univ _⟩
  exact mixedVFJacobian_eq_of_restriction hLA (Map.prodMap φ (Map.id R))
    (mixedVFBaseMap φ U hU).toImage (fun _ => rfl) p
    (has_mixed_vf_jacobian_base_product φ ⟨p.val,hLA p.property⟩ J hBase) hFamily

end IntegrationInACVF.Section7
