import Integration7.GammaVolumeRestrictionIdentities
import Integration7.EssentialVolumeRestriction

/-! The full domain of a Gamma volume object is Gamma-definable. A
restriction containing every essential label compares by its actual
original-Gamma identity chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

theorem VolumeObjectGamma.domain_graph
    {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U B) :
    GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ U.underlying.obj.domain.carrier} := by
  have h := (gammaLogicInput B).image_graph ((gammaLogicInput B).swap_graph hU.coordinates)
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨(Fin.elim0,U.underlying.obj.value ⟨p.2,hp⟩),⟨p.2,hp⟩,rfl,rfl⟩
  · rintro ⟨q,u,hu,_⟩
    change p.2 ∈ U.underlying.obj.domain.carrier
    exact hu ▸ u.property

theorem gamma_volume_containing_essential_restriction_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hess : U.essential.obj.domain.carrier ⊆ A.carrier)
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    (volumeIsoOfContainingEssentialRestriction hc C U A hA hess).GammaDefinable B :=
  gamma_volume_iso_of_label_identity hc _ (hU.restrict A hA hΓ) rfl (fun _ => rfl)

end IntegrationInACVF.Section7
