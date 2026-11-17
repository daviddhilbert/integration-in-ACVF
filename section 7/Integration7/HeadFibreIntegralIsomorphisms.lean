module

public import Integration7.HeadFibreContractionCoordinates
public import Integration7.VolumeFamilyHeadIntegrals
public import Integration7.VolumeRelabeling
public import Section4.RVIsoTools

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual head-integral row is volume-isomorphic to the actual
unary frozen-family contraction object, retaining every label and its
nonzero density in a proved containing context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

def headFibreIntegralVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    RVVolumeIso (((F.headIntegral hc Ξ T).rowInContext x).extend hD)
      (((F.headFibre x).extendContext hD).standardAppendObject hc Ξ
        (headFibreStandardContraction hc C D F T x hD)) := by
  let U := ((F.headIntegral hc Ξ T).rowInContext x).extend hD
  let R := headFibreStandardContraction hc C D F T x hD
  let V := ((F.headFibre x).extendContext hD).standardAppendObject hc Ξ R
  have hUV : U.underlying.obj.domain.carrier = V.underlying.obj.domain.carrier := by
    ext r
    exact ((mem_rawVolumeContractionLabels hc R.target r).trans
      (head_fibre_contraction_label_domain hc C D F T x hD r)).symm
  have hcoord (u : U.underlying.obj.domain) :
      V.underlying.obj.value ⟨u.val,hUV.le u.property⟩ = U.underlying.obj.value u := by
    change u.val ∘ orderedAppendVolumeIndex R.program F.densityGraph.selected =
      u.val ∘ headAppendVolumeIndex T F.densityGraph.selected
    rw [head_fibre_contraction_append_index]
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient
    (U := U.underlying) (V := V.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain
      U.underlying.obj.volume V.underlying.obj.volume hUV hcoord)
  apply RVVolumeIso.of_preserving_coordinates_full hc D e hcoord
  intro u
  change u.val (orderedAppendDensityIndex R.program (Fin.last a)) =
    u.val (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a)))
  rw [head_fibre_contraction_density_index]

end IntegrationInACVF.Section7
