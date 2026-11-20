import Integration7.HeadFibreIntegralIsomorphisms
import Integration7.GammaFunLemma75
import Integration7.GammaVolumeRestrictionIdentities
import Integration7.HeadCoordinateFibreContraction

/-! **Gamma head fibres.** The head fibre of a Gamma family over a frozen VF tuple is a Gamma unary
family over the row Gamma base; the fibre contraction of a Gamma head preparation is a Gamma
standard contraction; and the identification of the head-integral row with the fibre's standard
append object is Gamma-definable (it is the identity on labels). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {n a k : ℕ}

/-- The head fibre of a Gamma family is a Gamma unary family over the row base. -/
theorem SelectedVFVolumeFamily.Gamma.headFibre (hc : CanonicalStructure.IsCanonical (M := M))
    {C D : BaseContext M} {F : SelectedVFVolumeFamily C (n+1) a k} (hF : F.Gamma G)
    (x : Fin n → VFType (M := M)) (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    ((F.headFibre x).extendContext hD).Gamma (rowGammaBase G x) := by
  constructor
  · have h := gamma_head_fibre (nativeMixedVolumeDomain hc F.domain) (by rw [nativeMixedVolumeDomain_carrier]; exact hF.domain) x
    convert h using 1
    ext p
    change (Fin.cons (p.1 0) x,p.2) ∈ F.domain.carrier ↔ coordinateInsert 0 (headFrozenTuple x) p ∈ F.domain.carrier
    rw [coordinateInsert_head]
    rfl
  · have h := gamma_head_fibre (nativeMixedVolumeDomain hc F.densityGraph.domain) (hF.native_domain hc) x
    have he := congrArg carrier (head_fibre_density_contraction_source hc C D F x hD)
    rw [nativeMixedVolumeDomain_carrier] at he
    convert h using 1
    exact he.symm

/-- The fibre contraction of a Gamma head preparation is Gamma over the row base. -/
theorem gamma_head_fibre_standard_contraction (hc : CanonicalStructure.IsCanonical (M := M))
    (C D : BaseContext M) (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (hT : GammaGraphDefinable G (pointMapGraph T.map)) (hTarget : GammaSetDefinable G (carrier T.target))
    (x : Fin n → VFType (M := M)) (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    GammaProgramDefinable (rowGammaBase G x) (headFibreStandardContraction hc C D F T x hD).program :=
  gamma_orderedCastSource _ _ ((headCoordinateFibreContraction T x).program.extendBase_gamma
    (head_fibre_contraction_base_subset C D x hD) (gamma_head_coordinate_fibre_contraction T hT hTarget x))

/-- The head-integral row as a fibre standard append object, Gamma-definably. -/
theorem head_fibre_integral_volume_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C D : BaseContext M) (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (x : Fin n → VFType (M := M)) (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (hRow : VolumeObjectGamma (((F.headIntegral hc Ξ T).rowInContext x).extend hD) (rowGammaBase G x)) :
    (headFibreIntegralVolumeIso hc C D Ξ F T x hD).GammaDefinable (rowGammaBase G x) :=
  gamma_volume_iso_of_label_identity hc _ hRow rfl (fun _ => rfl)

end IntegrationInACVF.Section7
