import Integration7.VolumeAlmostEverywhereImages
import Integration7.RVJacobianRestriction
import Integration7.GammaVolumeCriterion
import Section9.GenericRVJacobian

/-! Gluing actual volume isomorphisms over two definable embedded pieces.
Generic Jacobian existence is obtained from the native finite-volume theorem;
the local Jacobians identify it using tangent-graph inclusion. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

structure EmbeddedVolumeIso (U V : PositiveRVVolumeObject (M := M) S k)
    (e : U.essential ≅ V.essential) where
  source : PositiveRVVolumeObject S k
  target : PositiveRVVolumeObject S k
  iso : RVVolumeIso source target
  inclusion : Map source.essential.obj.domain U.essential.obj.domain
  injective : Function.Injective inclusion
  source_coordinates : ∀ u, U.essential.obj.value (inclusion u) = source.essential.obj.value u
  target_coordinates : ∀ u, V.essential.obj.value (finiteIsoMap e (inclusion u)) =
    target.essential.obj.value (finiteIsoMap iso.iso u)
  source_density : ∀ u, U.essentialForm.value (inclusion u) = source.essentialForm.value u
  target_density : ∀ u, V.essentialForm.value (finiteIsoMap e (inclusion u)) =
    target.essentialForm.value (finiteIsoMap iso.iso u)

namespace EmbeddedVolumeIso

variable {U V : PositiveRVVolumeObject (M := M) S k} {e : U.essential ≅ V.essential}

theorem volumeRatio_eq (p : EmbeddedVolumeIso U V e) (u : p.source.essential.obj.domain) :
    volumeRatio U V e (p.inclusion u) = volumeRatio p.source p.target p.iso.iso u := by
  unfold volumeRatio
  rw [p.source_density, p.target_density]

theorem correspondence_subset (p : EmbeddedVolumeIso U V e) :
    (volumeCorrespondence (finiteIsoMap p.iso.iso)).carrier ⊆
      (volumeCorrespondence (finiteIsoMap e)).carrier := by
  rintro z ⟨u, rfl⟩
  refine ⟨p.inclusion u, ?_⟩
  change productTuple (U.essential.obj.value (p.inclusion u))
    (V.essential.obj.value (finiteIsoMap e (p.inclusion u))) = _
  rw [p.source_coordinates, p.target_coordinates]

theorem absolute_volumeRatio (p : EmbeddedVolumeIso U V e) (u : p.source.essential.obj.domain) :
    RVOperations.absoluteHom (volumeRatio U V e (p.inclusion u)) =
      (∏ i, RVOperations.absoluteHom (V.essential.obj.value (finiteIsoMap e (p.inclusion u)) i)) /
        ∏ i, RVOperations.absoluteHom (U.essential.obj.value (p.inclusion u) i) := by
  rw [p.volumeRatio_eq, p.source_coordinates, p.target_coordinates]
  exact p.iso.absolute_volumeRatio u

theorem jacobian_of_defined (p : EmbeddedVolumeIso U V e) (u : p.source.essential.obj.domain)
    (hlocal : IsRVJacobianAt (volumeCorrespondence (finiteIsoMap p.iso.iso)).carrier
      (p.source.essential.obj.value u) (p.target.essential.obj.value (finiteIsoMap p.iso.iso u))
      (volumeRatio p.source p.target p.iso.iso u))
    {ω : CanonicalRV.RVSort M}
    (hglobal : IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
      (U.essential.obj.value (p.inclusion u)) (V.essential.obj.value (finiteIsoMap e (p.inclusion u))) ω) :
    IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
      (U.essential.obj.value (p.inclusion u)) (V.essential.obj.value (finiteIsoMap e (p.inclusion u)))
      (volumeRatio U V e (p.inclusion u)) := by
  have hglobal' := hglobal
  rw [p.source_coordinates, p.target_coordinates] at hglobal'
  have he := rvJacobian_eq_of_subset p.correspondence_subset hlocal hglobal'
  rw [p.volumeRatio_eq, he]
  exact hglobal

end EmbeddedVolumeIso

def RVVolumeIso.glue (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (e : U.essential ≅ V.essential) (p q : EmbeddedVolumeIso U V e)
    (hcover : ∀ u, (∃ a, p.inclusion a = u) ∨ (∃ b, q.inclusion b = u)) : RVVolumeIso U V where
  iso := e
  gamma u := by
    apply gammaVolumeEquation_of_absoluteRatio e u
    rcases hcover u with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact p.absolute_volumeRatio a
    · exact q.absolute_volumeRatio b
  rv := by
    obtain ⟨ω, D, hD, hd, hω⟩ := exists_definable_generic_RVJacobian hc C (Nat.zero_lt_succ k)
      e U.essential_nonzero V.essential_nonzero
    have hdefined : RVAlmostEverywhere U.essential.obj.domain (k + 1) (fun u =>
        IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
          (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)) ((ω u).val 0)) :=
      ⟨D, hD, hd, hω⟩
    have hp := RVAlmostEverywhere.extend_injective p.inclusion p.injective p.iso.rv
    have hq := RVAlmostEverywhere.extend_injective q.inclusion q.injective q.iso.rv
    apply RVAlmostEverywhere.mono ((hp.and hc C hq).and hc C hdefined)
    rintro u ⟨⟨hp, hq⟩, hu⟩
    rcases hcover u with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact p.jacobian_of_defined a (hp a rfl) hu
    · exact q.jacobian_of_defined b (hq b rfl) hu

end IntegrationInACVF.Section7
