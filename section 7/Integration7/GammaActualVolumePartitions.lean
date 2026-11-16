module

public import Integration7.GammaVolumeRestrictionIdentities
public import Integration7.VolumePartition

@[expose] public section

/-! Complementary Gamma cuts partition arbitrary actual Gamma volume
objects with a full original-Gamma volume chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_actual_volume_complement_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    (volumeComplementPartitionIso hc C U A hA).GammaDefinable B := by
  let D := U.underlying.obj.domain.sdiff A
  let L := U.restrict A hA
  let R := U.restrict D Set.sdiff_subset
  have hD := (gammaLogicInput B).sdiff hU.coordinates.domain hΓ
  let F := finiteIsoMap (volumeComplementPartitionUnderlying U A hA)
  have hF : RVMapGamma F B := by
    apply gamma_tagged_rv_map_graph L.underlying.obj R.underlying.obj F
      (Map.id A).toUniv (Map.id D).toUniv
      ((RVMapGamma.identity hc hΓ).congr (fun _ => rfl))
      ((RVMapGamma.identity hc hD).congr (fun _ => rfl))
    · intro u
      exact congrArg Subtype.val (volumeComplementPartitionUnderlying_left U A hA u)
    · intro v
      exact congrArg Subtype.val (volumeComplementPartitionUnderlying_right U A hA v)
  exact gamma_volume_iso_of_full_map _ F
    (gamma_essential_volume_domain _ ((hU.restrict A hA hΓ).coprod
      (hU.restrict D Set.sdiff_subset hD)).coordinates) hF (fun _ => rfl)

end IntegrationInACVF.Section7
