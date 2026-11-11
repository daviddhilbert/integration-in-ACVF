import IntegrationSection2.FibreVolumeEquations
import IntegrationSection2.LiftFibreGeometry
import IntegrationSection2.VolumeCharacteristic
import Section4.ParameterInvariance
import Section9.GammaPolydiscDescent

/-! Pointwise Gamma-volume descent on every actual RV label fibre.
The measure equation fixes one finite nonzero Jacobian value. The
checked polydisc theorem descends that value without discarding any
exceptional RV label. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section2.ConcreteVolumeForms

namespace IntegrationInACVF.Section2.GammaVolumeDescent

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}

theorem pointwise_equation (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M)
    {U V : RVFiniteObject (M := M) (C.base : Set M) k} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (ω : RVForm U) (π : RVForm V)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) k).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2)
    (hMeasure : PreservesOff ω π f) (hgraph : HenselizedGaussGraphInput (VFType (M := M))) :
    let E := (finiteVolumeProperty (C.base : Set M) k).ι.mapIso e
    ∀ u : U.obj.domain, gammaValue ω u = gammaValue π (E.hom.map u) *
      rvGammaJacobian (U.obj.value u) (V.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u)) := by
  letI := VolumeCharacteristic.charZero C.model00
  let E := (finiteVolumeProperty (C.base : Set M) k).ι.mapIso e
  dsimp only
  intro u
  obtain ⟨Z,hZ,hMeasure⟩ := hMeasure
  obtain ⟨a,ha0,ha⟩ := LiftFibreGeometry.nonzero_representatives (U.obj.value u) (hU u)
  obtain ⟨b,hb0,hb⟩ := LiftFibreGeometry.nonzero_representatives (V.obj.value (E.hom.map u)) (hV (E.hom.map u))
  obtain ⟨c,hcRV⟩ := CanonicalRV.encodedRv_surjective (value ω u / value π (E.hom.map u))
  have hc0 : c ≠ 0 := (RVOperations.rv_ne_zero c).mp (by
    rw [hcRV]
    exact div_ne_zero (value_ne_zero ω u) (value_ne_zero π (E.hom.map u)))
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  let T := FixedLabelLift.labelBase E u
  let f₀ := FixedLabelLift.fibreMap E f hlabel u
  have hZT : vfDim (rawRVSpace (M := M) 1) (Z.extend (FixedLabelLift.base_subset E u)) < k :=
    (vfDim_extend_le (rawRVSpace (M := M) 1) (FixedLabelLift.base_subset E u) Z).trans_lt hZ
  have hconst (p : FixedLabelLift.source E u) (hp : p.val ∉ (Z.extend (FixedLabelLift.base_subset E u)).carrier) :
      ∃ J : VFType (M := M), HasMixedVFJacobianAt f₀ p J ∧ v J = v c := by
    let q : rvLift U.obj := ⟨p.val,((FixedLabelLift.source_mem E u p.val).mp p.property).1⟩
    obtain ⟨J,hJ,hm⟩ := hMeasure q hp
    have he : CanonicalRV.encodedRv J = CanonicalRV.encodedRv c :=
      (FibreVolumeEquations.ratio E ω π f hlabel u p J hm).trans hcRV.symm
    refine ⟨J,FixedLabelLift.jacobian E f hlabel u p hJ,?_⟩
    exact (Values.vf_value_eq_iff v hv J c).mp (congrArg Values.vrv he)
  have hdesc := gammaDescent_polydiscs_of_vfSmall_exception hc C.uncountable C.saturated C.model00
    (FixedLabelLift.small_base C.uncountable.le C.small E u) v hv f₀
    (FixedLabelLift.fibreMap_bijective E f hf hlabel u) a b ha0 hb0
    (LiftFibreGeometry.projection v hv U.obj u (FixedLabelLift.source_base_subset E u) a ha)
    (LiftFibreGeometry.projection v hv V.obj (E.hom.map u) (FixedLabelLift.target_base_subset E u) b hb)
    c hc0 (Z.extend (FixedLabelLift.base_subset E u)) hZT hconst hgraph
  have he : v c = v ((∏ i, b i) / ∏ i, a i) := by
    simpa only [map_div₀,map_prod] using hdesc
  have hActual : Values.vfValueHom c =
      (∏ i, Values.vfValueHom (b i)) / ∏ i, Values.vfValueHom (a i) := by
    have h := (Values.vf_value_eq_iff v hv c ((∏ i, b i) / ∏ i, a i)).mpr he
    change Values.vfValueHom c = Values.vfValueHom ((∏ i, b i) / ∏ i, a i) at h
    simpa only [map_div₀,map_prod] using h
  exact FibreVolumeEquations.gamma_equation_of_ratio ω π a b (hU u) (hV (E.hom.map u)) ha hb c hcRV hActual

end IntegrationInACVF.Section2.GammaVolumeDescent
