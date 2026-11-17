module

public import Integration7.CanonicalVolumeLabels
public import Integration7.RVVolumeDensityGraphs
public import Integration7.NativeCoordinateDensityVolumeObjects
public import Section4.RVIsoTools

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every actual positive RV coefficient admits an original-base native
presentation with literal coordinate and density labels, through a full
coordinate-preserving volume isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)

def rvCoordinateDensityPresentation := canonicalVolumeLabels U.densityGraph

def rvCoordinateDensityPresentationIso : RVVolumeIso U (rvCoordinateDensityPresentation C U) :=
  (rvVolumeDensityGraphIso hc C U).trans hc C (canonicalVolumeLabelsIso hc C U.densityGraph)

theorem rv_coordinate_density_presentation_coordinates
    (u : (rvCoordinateDensityPresentation C U).underlying.obj.domain) :
    (rvCoordinateDensityPresentation C U).underlying.obj.value u = u.val ∘ Fin.castAdd (U.underlying.obj.arity+1) :=
  canonicalVolumeLabels_coordinates U.densityGraph u

theorem rv_coordinate_density_presentation_density
    (u : (rvCoordinateDensityPresentation C U).underlying.obj.domain) :
    (rvCoordinateDensityPresentation C U).form.value u =
      u.val (Fin.natAdd (k+1) (Fin.last U.underlying.obj.arity)) :=
  canonicalVolumeLabels_density_label U.densityGraph (Fin.last U.underlying.obj.arity) U.densityGraph_density_last u

def rvCoordinateDensityNativeDomain : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0
    ((k+1)+(U.underlying.obj.arity+1)) :=
  nativeMixedVolumeDomain hc ((DefSet.univ (rawVFSpace (M := M) 0) (C.base : Set M)).prod
    (rvCoordinateDensityPresentation C U).underlying.obj.domain)

theorem rv_coordinate_density_native_finite (t : Fin (k+1) → CanonicalRV.RVSort M) :
    {r : Fin ((k+1)+(U.underlying.obj.arity+1)) → CanonicalRV.RVSort M |
      (Fin.elim0,r) ∈ SpecialTransformations.Section5.carrier (rvCoordinateDensityNativeDomain hc C U) ∧
        r ∘ Fin.castAdd (U.underlying.obj.arity+1)=t}.Finite := by
  let V := rvCoordinateDensityPresentation C U
  apply ((V.underlying.property ⟨t,Set.mem_univ _⟩).image Subtype.val).subset
  rintro r ⟨hr,ht⟩
  refine ⟨⟨r,hr.2⟩,?_,rfl⟩
  apply Subtype.ext
  exact (rv_coordinate_density_presentation_coordinates C U ⟨r,hr.2⟩).trans ht

theorem rv_coordinate_density_native_nonzero
    (q : rvCoordinateDensityNativeDomain hc C U) :
    (q.val.2 (Fin.natAdd (k+1) (Fin.last U.underlying.obj.arity))).val ≠ iRVZero := by
  let V := rvCoordinateDensityPresentation C U
  let u : V.underlying.obj.domain := ⟨q.val.2,q.property.2⟩
  exact (rv_nonzero_iff_raw _).mp (fun hz => V.form.nonzero u
    ((rv_coordinate_density_presentation_density C U u).trans hz))

def rvCoordinateDensityNativeObject : PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
  nativeCoordinateDensityVolumeObject hc C (rvCoordinateDensityNativeDomain hc C U)
    (Fin.castAdd (U.underlying.obj.arity+1)) (Fin.natAdd (k+1) (Fin.last U.underlying.obj.arity))
    (rv_coordinate_density_native_finite hc C U) (rv_coordinate_density_native_nonzero hc C U)

def rvCoordinateDensityNativeIso : RVVolumeIso U (rvCoordinateDensityNativeObject hc C U) := by
  let V := rvCoordinateDensityPresentation C U
  let W := rvCoordinateDensityNativeObject hc C U
  have hVW : V.underlying.obj.domain.carrier=W.underlying.obj.domain.carrier := by
    ext r
    change r ∈ (rvCoordinateDensityPresentation C U).underlying.obj.domain.carrier ↔
      r ∈ (rawVolumeContractionLabels hc (rvCoordinateDensityNativeDomain hc C U)).carrier
    rw [mem_rawVolumeContractionLabels]
    change (r ∈ V.underlying.obj.domain.carrier) ↔ (Fin.elim0 ∈ Set.univ ∧ r ∈ V.underlying.obj.domain.carrier)
    simp only [Set.mem_univ,true_and]
  have hCoord (u : V.underlying.obj.domain) : W.underlying.obj.value ⟨u.val,hVW.le u.property⟩=V.underlying.obj.value u :=
    (rv_coordinate_density_presentation_coordinates C U u).symm
  let e : V.underlying ≅ W.underlying := rvFiniteIsoOfAmbient (U := V.underlying) (V := W.underlying)
    (rvIsoOfCarrierEq V.underlying.obj.domain W.underlying.obj.domain
      V.underlying.obj.volume W.underlying.obj.volume hVW hCoord)
  exact (rvCoordinateDensityPresentationIso hc C U).trans hc C
    (RVVolumeIso.of_preserving_coordinates_full hc C e hCoord
      (fun u => (rv_coordinate_density_presentation_density C U u).symm))
end IntegrationInACVF.Section7
