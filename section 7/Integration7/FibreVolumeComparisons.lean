import Integration7.VolumeIsomorphismGluing
import Integration7.FibreRVJacobianComparison

/-! Actual comparisons on fibres of a correspondence with a fixed head.
The fibre coordinates gain a common head; the density stays unchanged. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {d k : ℕ}

structure FibreVolumeComparison (U V : PositiveRVVolumeObject (M := M) S (d+k))
    (e : U.essential ≅ V.essential) where
  source : PositiveRVVolumeObject S k
  target : PositiveRVVolumeObject S k
  iso : RVVolumeIso source target
  head : Fin d → CanonicalRV.RVSort M
  inclusion : Map source.essential.obj.domain U.essential.obj.domain
  injective : Function.Injective inclusion
  source_coordinates : ∀ u, U.essential.obj.value (inclusion u) =
    Fin.append head (source.essential.obj.value u)
  target_coordinates : ∀ u, V.essential.obj.value (finiteIsoMap e (inclusion u)) =
    Fin.append head (target.essential.obj.value (finiteIsoMap iso.iso u))
  source_density : ∀ u, U.essentialForm.value (inclusion u) = source.essentialForm.value u
  target_density : ∀ u, V.essentialForm.value (finiteIsoMap e (inclusion u)) =
    target.essentialForm.value (finiteIsoMap iso.iso u)

namespace FibreVolumeComparison

variable {U V : PositiveRVVolumeObject (M := M) S (d+k)} {e : U.essential ≅ V.essential}

theorem volumeRatio_eq (p : FibreVolumeComparison U V e) (u : p.source.essential.obj.domain) :
    volumeRatio U V e (p.inclusion u) = volumeRatio p.source p.target p.iso.iso u := by
  unfold volumeRatio
  rw [p.source_density,p.target_density]

theorem correspondence_insertion (p : FibreVolumeComparison U V e) :
    ∀ z ∈ (volumeCorrespondence (finiteIsoMap p.iso.iso)).carrier,
      insertHeadPair p.head p.head z ∈ (volumeCorrespondence (finiteIsoMap e)).carrier := by
  rintro z ⟨u,rfl⟩
  refine ⟨p.inclusion u,?_⟩
  change productTuple (U.essential.obj.value (p.inclusion u))
    (V.essential.obj.value (finiteIsoMap e (p.inclusion u))) = _
  rw [p.source_coordinates,p.target_coordinates,insertHeadPair_productTuple]

theorem jacobian_eq_ratio (p : FibreVolumeComparison U V e)
    (hHead : ∀ z ∈ (volumeCorrespondence (finiteIsoMap e)).carrier, ∀ i : Fin d,
      z (productLeft ((d+k)+1) ((d+k)+1) (Fin.castAdd (k+1) i)) =
        z (productRight ((d+k)+1) ((d+k)+1) (Fin.castAdd (k+1) i)))
    (u : p.source.essential.obj.domain)
    (hlocal : IsRVJacobianAt (volumeCorrespondence (finiteIsoMap p.iso.iso)).carrier
      (p.source.essential.obj.value u) (p.target.essential.obj.value (finiteIsoMap p.iso.iso u))
      (volumeRatio p.source p.target p.iso.iso u))
    {ω : CanonicalRV.RVSort M}
    (hglobal : IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
      (U.essential.obj.value (p.inclusion u)) (V.essential.obj.value (finiteIsoMap e (p.inclusion u))) ω) :
    ω = volumeRatio U V e (p.inclusion u) := by
  rw [p.source_coordinates,p.target_coordinates] at hglobal
  exact (rvJacobian_eq_fixed_head_fibre (n := d) (m := k+1) hHead p.head _ _ p.correspondence_insertion
    hglobal hlocal).trans (p.volumeRatio_eq u).symm

end FibreVolumeComparison
end IntegrationInACVF.Section7
