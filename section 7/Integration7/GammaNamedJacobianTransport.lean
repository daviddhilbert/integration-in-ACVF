import Integration7.GammaNamedFormGraphs
import Integration7.VFVolumeDensityTransport
import Integration7.RVCoordinateSelection
import Section9.GammaMixedJacobianValue
import Section5.VerticalConstruction

/-! Gamma transport of densities along Gamma mixed bijections.

The Jacobian density of `transportedVFVolumeForm` is chosen by
`Classical.choose`, so its values off the differentiability locus are
uncontrolled. Here the density is built from an arbitrary Jacobian value map
`j` (correct wherever the mixed derivative exists). The provider's Gamma
Jacobian theorem supplies such a `j` with a Gamma graph, so the transported
density has a Gamma graph. This discharges `GammaVolumeTransportInput` in
positive VF dimension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a b : ℕ}

section Forms
variable {A : DefSet (rawMixedSpace (M := M) n a) S}
variable {B : DefSet (rawMixedSpace (M := M) n b) S}

/-- The nonzero density read off from a VF-valued Jacobian map. -/
def jacobianValueDensityForm (j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) : VolumeForm A where
  map := (nonzeroRVScalarMap S).comp ((scalarEncodedRVMap S).comp j)
  nonzero p := nonzero_rv_scalar_map_nonzero S _

/-- `j` computes the Jacobian determinant of `f` wherever the mixed derivative exists. -/
def IsJacobianValueMap (f : Map A B) (j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) : Prop :=
  ∀ (p : A) (L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M))),
    HasMixedVFDerivativeAt f p L → (j p).val 0 = (LinearMap.toMatrix' L).det

theorem jacobian_value_density_form_of_derivative (f : Map A B)
    (j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (hj : IsJacobianValueMap f j) (p : A)
    (L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)))
    (hL : HasMixedVFDerivativeAt f p L) (h0 : (LinearMap.toMatrix' L).det ≠ 0) :
    (jacobianValueDensityForm j).value p = CanonicalRV.encodedRv (LinearMap.toMatrix' L).det := by
  have hjp := hj p L hL
  have hnz : ((scalarEncodedRVMap S) (j p)).val 0 ≠ 0 := by
    rw [scalar_encoded_rv_map_value,hjp]
    exact (RVOperations.rv_ne_zero _).mpr h0
  change (nonzeroRVScalarMap S ((scalarEncodedRVMap S) (j p))).val 0 = _
  rw [nonzero_rv_scalar_map_of_nonzero S _ hnz,scalar_encoded_rv_map_value,hjp]

/-- Transport of a density along a bijection, divided by the density of `j`. -/
def jacobianTransportedForm (f : Map A B) (hf : Function.Bijective f)
    (j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (ω : VolumeForm A) : VolumeForm B :=
  (ω.div (jacobianValueDensityForm j)).pullback (f.inverse hf)

theorem jacobian_transported_form_value (f : Map A B) (hf : Function.Bijective f)
    (j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (ω : VolumeForm A) (p : A) :
    (jacobianTransportedForm f hf j ω).value (f p) = ω.value p / (jacobianValueDensityForm j).value p := by
  change (ω.div (jacobianValueDensityForm j)).value (f.inverse hf (f p)) = _
  rw [Map.inverse_apply,VolumeForm.div_value]

end Forms

theorem preserves_jacobian_transported_form
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (f : Map A B) (hf : Function.Bijective f)
    (j : Map A (DefSet.univ (rawVFSpace (M := M) 1) (C.base : Set M))) (hj : IsJacobianValueMap f j)
    (ω : VolumeForm A) : PreservesVFVolume ω (jacobianTransportedForm f hf j ω) f := by
  have hD := mixed_differentiability_almost_everywhere hc C hn f
  have hN := mixed_bijective_jacobian_nonzero_ae hc C hn f hf
  apply (vfAlmostEverywhere_and hc C hD hN).mono
  rintro p ⟨⟨L,hL⟩,J,hJ,hJ0⟩
  have hLJ : HasMixedVFJacobianAt f p (LinearMap.toMatrix' L).det := by
    obtain ⟨F,hF,hD⟩ := hL
    exact ⟨F,hF,hD.hasJacobianAt⟩
  have he : (LinearMap.toMatrix' L).det = J := hLJ.unique hJ
  have hValue : (jacobianValueDensityForm j).value p = CanonicalRV.encodedRv J := by
    rw [jacobian_value_density_form_of_derivative f j hj p L hL (he ▸ hJ0),he]
  refine ⟨J,hJ,?_⟩
  rw [jacobian_transported_form_value,← hValue]
  exact (div_mul_cancel₀ _ ((jacobianValueDensityForm j).value_ne_zero p)).symm

/-! Gamma graphs. -/

/-- The RV reduction `Point 1 0 → Point 0 1` as a real global map. -/
theorem gamma_scalar_rv_graph :
    GammaGraphDefinable G (fun (z : Point (M := M) 1 0) (w : Point (M := M) 0 1) =>
      w = (Fin.elim0, fun _ => SpecialTransformations.Section5.rv (z.1 0))) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((gammaLogicInput G).real_map_graph
      (SpecialTransformations.Section5.headKeyMap
        (SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace (M := M) (0+1) 0) G.real)))
  intro z w
  constructor
  · rintro ⟨u,hu,hw⟩
    rw [← hw, SpecialTransformations.Section5.headKeyMap_apply, hu]
    refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
    funext i
    fin_cases i
    rfl
  · intro hw
    refine ⟨⟨z,Set.mem_univ _⟩,rfl,?_⟩
    rw [SpecialTransformations.Section5.headKeyMap_apply, hw]
    refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
    funext i
    fin_cases i
    rfl

/-- One RV coordinate of a pair as a real global map. -/
theorem gamma_rv_pair_coordinate_graph (i : Fin 2) :
    GammaGraphDefinable G (fun (w : Point (M := M) 0 2) (y : Point (M := M) 0 1) =>
      y = (Fin.elim0, fun _ => w.2 i)) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (gamma_global_map_graph (B := G) (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin 0)
      (fun _ : Fin 1 => i) G.real))
  intro w y
  constructor
  · intro h
    rw [← h]
    refine Prod.ext (funext (fun i => Fin.elim0 i)) rfl
  · intro h
    rw [h]
    refine Prod.ext (funext (fun i => Fin.elim0 i)) rfl

/-- The real RV operation `(s, t) ↦ s * (nz t)⁻¹`. -/
def rvDivNonzeroMap (T : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 2) T) (DefSet.univ (rawRVSpace (M := M) 1) T) :=
  rvScalarMul (rvCoordinateSelectMap T ![0])
    ((rvInverse T).comp ((nonzeroRVScalarMap T).comp (rvCoordinateSelectMap T ![1])))

theorem gamma_univ_rv_set :
    GammaSetDefinable G {p : Point (M := M) 0 2 | p.2 ∈ (DefSet.univ (rawRVSpace (M := M) 2) G.real).carrier} := by
  have h := (gammaLogicInput G).image_graph
    ((gammaLogicInput G).swap_graph (gamma_global_map_graph (B := G)
      (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 2 → Fin 2) G.real)))
  convert h using 1
  ext p
  constructor
  · intro _
    exact ⟨p,Prod.ext rfl rfl⟩
  · intro _
    exact Set.mem_univ _

theorem gamma_rv_div_nonzero_graph (hc : CanonicalStructure.IsCanonical (M := M)) :
    GammaGraphDefinable G (fun (p : Point (M := M) 0 2) (q : Point (M := M) 0 1) =>
      ∃ u : DefSet.univ (rawRVSpace (M := M) 2) G.real, u.val = p.2 ∧ (rvDivNonzeroMap G.real u).val = q.2) :=
  gamma_real_rv_map_graph hc G (rvDivNonzeroMap G.real) (rvDivNonzeroMap G.real) gamma_univ_rv_set
    (fun _ => rfl)

theorem gamma_jacobian_transported_form_graph (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S} {B : DefSet (rawMixedSpace (M := M) n b) S}
    (f : Map A B) (hf : Function.Bijective f)
    (hfΓ : GammaGraphDefinable G (vfMixedMapGraph f))
    (j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hjΓ : GammaGraphDefinable G (fun (p : Point (M := M) n a) (z : Point (M := M) 1 0) =>
      ∃ u : A, u.val = p ∧ (j u).val = z.1))
    (ω : VolumeForm A) (hω : GammaGraphDefinable G (volumeFormGraph ω)) :
    GammaGraphDefinable G (volumeFormGraph (jacobianTransportedForm f hf j ω)) := by
  have L := gammaLogicInput G
  have hJr := L.comp_graph hjΓ (gamma_scalar_rv_graph (G := G))
  have hP₀ := L.comp_graph hω (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 0))
  have hP₁ := L.comp_graph hJr (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 1))
  have hV := L.comp_graph (hP₀.inter hP₁) (gamma_rv_div_nonzero_graph (G := G) hc)
  have hη := L.comp_graph (L.swap_graph hfΓ) hV
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hη
  intro q y
  constructor
  · rintro ⟨p,⟨u,rfl,rfl⟩,w,⟨⟨y₀,⟨u₀,hu₀,hy₀⟩,hw₀⟩,⟨y₁,⟨z,⟨u₁,hu₁,hz⟩,rfl⟩,hw₁⟩⟩,t,ht,hty⟩
    have e₀ : u = u₀ := (Subtype.ext hu₀).symm
    have e₁ : u = u₁ := (Subtype.ext hu₁).symm
    subst e₀ e₁
    have et : t = ⟨w.2,Set.mem_univ _⟩ := Subtype.ext ht
    subst et
    refine ⟨f u,rfl,?_⟩
    rw [← hty]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have hw0 : w.2 0 = (ω.map u).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₀).symm.trans (congrFun hy₀ 0).symm
    have hw1 : w.2 1 = SpecialTransformations.Section5.rv ((j u).val 0) :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₁).symm.trans
        (congrArg (fun v : Fin 1 → _ => SpecialTransformations.Section5.rv (v 0)) hz.symm)
    change (jacobianTransportedForm f hf j ω).value (f u) = (rvDivNonzeroMap G.real ⟨w.2,Set.mem_univ _⟩).val 0
    rw [jacobian_transported_form_value]
    change _ = w.2 0 * ((nonzeroRVScalarMap G.real (rvCoordinateSelectMap G.real ![1] ⟨w.2,Set.mem_univ _⟩)).val 0)⁻¹
    rw [div_eq_mul_inv]
    change (ω.map u).val 0 * ((nonzeroRVScalarMap S ((scalarEncodedRVMap S) (j u))).val 0)⁻¹ = _
    rw [← hw0]
    congr 2
    classical
    change (if (CanonicalRV.encodedRv ((j u).val 0)).val = iRVZero then 1 else
        CanonicalRV.encodedRv ((j u).val 0)) =
      (if (w.2 1).val = iRVZero then 1 else w.2 1)
    rw [hw1]
    rfl
  · rintro ⟨v,rfl,hv⟩
    let u := f.inverse hf v
    have hfu : f u = v := Map.apply_inverse f hf v
    let w : Point (M := M) 0 2 :=
      (Fin.elim0, ![(ω.map u).val 0, SpecialTransformations.Section5.rv ((j u).val 0)])
    let z : Point (M := M) 1 0 := ((j u).val, Fin.elim0)
    refine ⟨u.val,⟨u,rfl,by rw [hfu]⟩,w,⟨⟨(Fin.elim0,(ω.map u).val),⟨u,rfl,rfl⟩,?_⟩,
      ⟨_,⟨z,⟨u,rfl,rfl⟩,rfl⟩,?_⟩⟩,⟨w.2,Set.mem_univ _⟩,rfl,?_⟩
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · rw [← hv, ← hfu]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      change (rvDivNonzeroMap G.real ⟨w.2,Set.mem_univ _⟩).val 0 = (jacobianTransportedForm f hf j ω).value (f u)
      rw [jacobian_transported_form_value, div_eq_mul_inv]
      rfl

end IntegrationInACVF.Section7
