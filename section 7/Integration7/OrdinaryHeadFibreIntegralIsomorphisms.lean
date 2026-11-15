import Integration7.OrdinaryVolumeHeadFibres
import Integration7.FieldBaseUnaryVolumeIntegrals
import Integration7.OrdinaryVolumeFamilyHeadIntegrals
import Integration7.HeadCoordinateFibreVolumeSelectors
import Integration7.VolumeRelabeling
import Section4.RVIsoTools

/-! The ordinary head-integral row is the raw unary contraction of its
actual frozen unit-density VF realization, with full volume data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ} {C : BaseContext M}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (D : BaseContext M)
variable (F : OrdinaryVFVolumeFamily C (n+1) a)
variable (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
variable (x : Fin n → VFType (M := M))
variable (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))

theorem ordinary_head_fibre_volume_index :
    (ordinaryHeadFibreStandardContraction hc D F T x hD).volumeIndex 0 = Fin.castAdd T.arity (0 : Fin 1) := by
  change (orderedCastSource _ _).volumeIndex 0 = _
  rw [orderedCastSource_volumeIndex]
  exact ((headCoordinateFibreContraction T x).extendBase_volumeIndex
    (head_fibre_contraction_base_subset C D x hD) 0).trans (head_coordinate_fibre_volume_index T x)

theorem ordinary_head_fibre_density_index :
    suffixIndex (ordinaryHeadFibreStandardContraction hc D F T x hD).program.rvArity_le (Fin.last a) =
      Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a)) :=
  head_coordinate_fibre_old_label_index T x (Fin.last a)

def ordinaryHeadFibreVolumeObject (Ξ : Set (Values.Gamma (M := M))) :
    PositiveRVVolumeObject (M := M) (D.base : Set M) 0 :=
  let U := ((F.headFibre x).extendContext hD).fullVFObject
  rawStandardVolumeObject hc D Ξ (nativeMixedVolumeDomain hc U.densityGraph.domain)
    U.densityGraph.finite_labels (Fin.last a) (unary_density_graph_label_nonzero U)
    (ordinaryHeadFibreStandardContraction hc D F T x hD)

def ordinaryHeadFibreIntegralVolumeIso (Ξ : Set (Values.Gamma (M := M))) :
    RVVolumeIso (((F.headIntegral hc Ξ T).rowInContext x).extend hD)
      (ordinaryHeadFibreVolumeObject hc D F T x hD Ξ) := by
  let U := ((F.headIntegral hc Ξ T).rowInContext x).extend hD
  let R := ordinaryHeadFibreStandardContraction hc D F T x hD
  let V := ordinaryHeadFibreVolumeObject hc D F T x hD Ξ
  have hUV : U.underlying.obj.domain.carrier = V.underlying.obj.domain.carrier := by
    ext r
    exact ((rawContractionDomain_iff R (Fin.elim0,r)).trans
      (head_coordinate_fibre_contraction_domain T x r)).symm
  have hcoord (u : U.underlying.obj.domain) :
      V.underlying.obj.value ⟨u.val,hUV.le u.property⟩ = U.underlying.obj.value u := by
    funext i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    change u.val (R.volumeIndex 0) = u.val (Fin.castAdd T.arity (0 : Fin 1))
    exact congrArg u.val (ordinary_head_fibre_volume_index hc D F T x hD)
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient
    (U := U.underlying) (V := V.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain
      U.underlying.obj.volume V.underlying.obj.volume hUV hcoord)
  apply RVVolumeIso.of_preserving_coordinates_full hc D e hcoord
  intro u
  change u.val (suffixIndex R.program.rvArity_le (Fin.last a)) =
    u.val (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a)))
  rw [ordinary_head_fibre_density_index]

end IntegrationInACVF.Section7
