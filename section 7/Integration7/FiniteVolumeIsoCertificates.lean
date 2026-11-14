import Integration7.GenericCertifiedVolumeCharts

/-! A finite-support certificate for the RV volume equation. Its exception
has an actual finite-fibre map to fewer RV coordinates. Every checked volume
isomorphism supplies such a certificate; a certificate proves its equation. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

structure RVVolumeIsoCertificate (U V : PositiveRVVolumeObject (M := M) S k)
    (e : U.essential ≅ V.essential) where
  supports : Finset (VolumeChartSupport (k+1))
  exception : DefSet (rawRVSpace (M := M) U.essential.obj.arity) S
  contained : exception.carrier ⊆ U.essential.obj.domain.carrier
  arity : ℕ
  arity_lt : arity < k+1
  projection : Map exception (DefSet.univ (rawRVSpace (M := M) arity) S)
  projection_finite : projection.FiniteFibres
  chart : ∀ u : U.essential.obj.domain, u.val ∉ exception.carrier → ∃ σ ∈ supports,
    VolumeChartValue σ (volumeCorrespondence (finiteIsoMap e)).carrier
      (productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)))
      (fun _ => volumeRatio U V e u)

theorem RVVolumeIsoCertificate.rv {U V : PositiveRVVolumeObject (M := M) S k}
    {e : U.essential ≅ V.essential} (H : RVVolumeIsoCertificate U V e) :
    RVAlmostEverywhere U.essential.obj.domain (k+1) (fun u =>
      IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
        (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)) (volumeRatio U V e u)) := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  refine ⟨H.exception,H.contained,
    ((rvDim_le_of_finite_map H.projection H.projection_finite).trans (rvDim_le_arity _)).trans_lt
      H.arity_lt,?_⟩
  intro u hu
  obtain ⟨σ,_,h⟩ := H.chart u hu
  have hj := h.isRVJacobianAt
  have hl : productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)) ∘
      productLeft (k+1) (k+1) = U.essential.obj.value u := funext (productTuple_left _ _)
  have hr : productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)) ∘
      productRight (k+1) (k+1) = V.essential.obj.value (finiteIsoMap e u) :=
    funext (productTuple_right _ _)
  simpa only [hl,hr] using hj

theorem RVVolumeIso.exists_finite_certificate
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (B.base : Set M) k} (e : RVVolumeIso U V) :
    Nonempty (RVVolumeIsoCertificate U V e.iso) := by
  obtain ⟨A,D,hDU,hd,hA⟩ := e.exists_finite_volume_charts hc B
  obtain ⟨f,hf⟩ := rvDim_attained D
  exact ⟨⟨A,D,hDU,rvDim D,hd,f,hf,hA⟩⟩

end IntegrationInACVF.Section7
