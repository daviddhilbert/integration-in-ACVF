import Integration7.GammaFunLinearResults
import Integration7.GammaFunJacobianAdditivity
import Integration7.GammaFunZeroJacobians

/-! **Coefficient linearity of Gamma Jacobian transforms.** Jacobian value maps transport along
coefficient products (their VF fibres agree with those of the underlying family); Jacobian
transforms of one presentation with two Gamma Jacobian value maps agree almost everywhere; and
the Jacobian transform of a coefficient product is almost everywhere the coefficient product of
the Jacobian transform. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open SpecialTransformations.Section4 (rawMixedSpace rawRVSpace rawVFSpace)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a a' : ℕ}

/-- **Transport of Jacobian value maps along fibre-preserving projections.** -/
theorem is_jacobian_value_map_comp {X Y : DefSet (rawVFSpace (M := M) n) S} (φ : Map X Y)
    {A : DefSet (rawMixedSpace (M := M) n a) S} {A' : DefSet (rawMixedSpace (M := M) n a') S}
    (hA : ∀ p : A, p.val.1 ∈ X.carrier) (hA' : ∀ p : A', p.val.1 ∈ X.carrier)
    (π : Map A A') (hπ : ∀ p : A, (π p).val.1 = p.val.1)
    (hfib : ∀ (p : A) (x : Fin n → VFType (M := M)), (x,p.val.2) ∈ A.carrier → (x,(π p).val.2) ∈ A'.carrier)
    (j : Map A' (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hj : IsJacobianValueMap (mixedVFBaseMap φ A' hA').toImage j) :
    IsJacobianValueMap (mixedVFBaseMap φ A hA).toImage (j.comp π) := by
  intro p L hL
  obtain ⟨F,⟨ρ,hρ⟩,hD⟩ := hL
  have hp1 := hπ p
  refine hj (π p) L ⟨F,⟨ρ,fun x hx => ?_⟩,?_⟩
  · rw [hp1] at hx
    obtain ⟨hxA,hxF⟩ := hρ x hx
    refine ⟨hfib p x hxA,?_⟩
    have h1 := congrArg Prod.fst hxF
    change (φ ⟨x,hA ⟨(x,p.val.2),hxA⟩⟩).val = F x at h1
    change ((φ ⟨x,hA' ⟨(x,(π p).val.2),hfib p x hxA⟩⟩).val,(π p).val.2) = (F x,(π p).val.2)
    rw [← h1]
  · rw [hp1]
    exact hD

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The Gamma Jacobian transform of a supported presentation with a prescribed Gamma value map. -/
def Presentation.jacobianWith {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X)
    (j : Map F.family.domain (DefSet.univ (rawVFSpace (M := M) 1) 𝔖))
    (hjΓ : GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) F.arity) (z : Point (M := M) 1 0) =>
      ∃ u : F.family.domain, u.val = p ∧ (j u).val = z.1)) : Presentation C Ξ hΞ n k where
  arity := F.arity
  family := F.family.jacobianPushforwardWith φ.map φ.bijective hF j
  gamma := by
    have hfΓ := gamma_mixed_vf_base_map_graph φ.map φ.gamma _ F.gamma.domain hF
    refine ⟨?_,?_⟩
    · convert (gammaLogicInput 𝔅).image_graph hfΓ using 1
      ext q
      constructor
      · rintro ⟨u,hu⟩
        exact ⟨u.val,u,rfl,hu⟩
      · rintro ⟨_,u,rfl,hu⟩
        exact ⟨u,hu⟩
    · exact density_graph_of_volume_form_graph _
        (gamma_jacobian_transported_form_graph hc _ _ hfΓ _ hjΓ F.family.form
          (volume_form_graph_of_density_graph F.family.form F.gamma.densityGraph))

/-- The Gamma Jacobian transform of a supported zero presentation with a prescribed Gamma value map. -/
def ZeroPresentation.jacobianWith {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X)
    (j : Map F.family.domain (DefSet.univ (rawVFSpace (M := M) 1) 𝔖))
    (hjΓ : GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) F.arity) (z : Point (M := M) 1 0) =>
      ∃ u : F.family.domain, u.val = p ∧ (j u).val = z.1)) : ZeroPresentation C Ξ hΞ n where
  arity := F.arity
  family := F.family.jacobianPushforwardWith φ.map φ.bijective hF j
  gamma := by
    have hfΓ := gamma_mixed_vf_base_map_graph φ.map φ.gamma _ F.gamma.domain hF
    refine ⟨?_,?_⟩
    · convert (gammaLogicInput 𝔅).image_graph hfΓ using 1
      ext q
      constructor
      · rintro ⟨u,hu⟩
        exact ⟨u.val,u,rfl,hu⟩
      · rintro ⟨_,u,rfl,hu⟩
        exact ⟨u,hu⟩
    · exact density_graph_of_volume_form_graph _
        (gamma_jacobian_transported_form_graph hc _ _ hfΓ _ hjΓ F.family.form
          (volume_form_graph_of_density_graph F.family.form F.gamma.densityGraph))

theorem presentation_jacobian_eq_with {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    F.jacobian hc C Ξ hΞ φ hF = F.jacobianWith hc C Ξ hΞ φ hF (F.jacobianValue hc C Ξ hΞ φ hF)
      (Classical.choose_spec (presentation_jacobian_value_exists hc C Ξ hΞ F φ hF)).1 := rfl

theorem zero_presentation_jacobian_eq_with {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    F.jacobian hc C Ξ hΞ φ hF = F.jacobianWith hc C Ξ hΞ φ hF (F.jacobianValue hc C Ξ hΞ φ hF)
      (F.jacobianValue_gamma hc C Ξ hΞ φ hF) := rfl

theorem gamma_vf_set_empty_small (n : ℕ) :
    SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
      (GammaVFSet.empty C Ξ hΞ n).set < n+1 :=
  (SpecialTransformations.DefinableGeometry.Dimension.dim_empty SpecialTransformations.Section4.rawVFSpace
    (SpecialTransformations.Section4.AuxiliaryCoordinates.space (SpecialTransformations.Section4.rawRVSpace (M := M) 1))
    (SpecialTransformations.Section4.AuxiliaryCoordinates.rv 0)).trans_lt (Nat.zero_lt_succ n)

/-- The density identity behind the comparison of two value maps. -/
theorem jacobian_with_density_eq {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) {a : ℕ}
    (A : DefSet (rawMixedSpace (M := M) (n+1) a) 𝔖) (hA : ∀ p : A, p.val.1 ∈ X.set.carrier)
    (ω : VolumeForm A) (j₁ j₂ : Map A (DefSet.univ (rawVFSpace (M := M) 1) 𝔖)) (E : GammaVFSet C Ξ hΞ n)
    (hg : ∀ y : Y.set, y.val ∉ E.set.carrier →
      (∀ u : A, (j₁ u).val 0 ≠ (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hA u⟩)).val 0 →
          u.val.1 ≠ (φ.map.inverse φ.bijective y).val) ∧
      (∀ u : A, (j₂ u).val 0 ≠ (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hA u⟩)).val 0 →
          u.val.1 ≠ (φ.map.inverse φ.bijective y).val))
    (y : Fin (n+1) → VFType (M := M)) (hy : y ∉ E.set.carrier) (p : A)
    (hp : (mixedVFBaseMap φ.map A hA p).val.1 = y) :
    (jacobianTransportedForm (mixedVFBaseMap φ.map A hA).toImage
        (mixed_vf_base_map_to_image_bijective φ.map φ.bijective.1 A hA) j₂ ω).value
        ((mixedVFBaseMap φ.map A hA).toImage p) =
      (jacobianTransportedForm (mixedVFBaseMap φ.map A hA).toImage
        (mixed_vf_base_map_to_image_bijective φ.map φ.bijective.1 A hA) j₁ ω).value
        ((mixedVFBaseMap φ.map A hA).toImage p) := by
  have hyY : y ∈ Y.set.carrier := by
    have := (φ.map ⟨p.val.1,hA p⟩).property
    rw [show (φ.map ⟨p.val.1,hA p⟩).val = y from hp] at this
    exact this
  let y' : Y.set := ⟨y,hyY⟩
  have hpx : p.val.1 = (φ.map.inverse φ.bijective y').val := by
    have h1 : φ.map ⟨p.val.1,hA p⟩ = y' := Subtype.ext hp
    rw [← h1,SpecialTransformations.DefinableGeometry.Map.inverse_apply]
  obtain ⟨hg1,hg2⟩ := hg y' hy
  have hj1 : (j₁ p).val 0 = (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨p.val.1,hA p⟩)).val 0 := by
    by_contra hne
    exact hg1 p hne hpx
  have hj2 : (j₂ p).val 0 = (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨p.val.1,hA p⟩)).val 0 := by
    by_contra hne
    exact hg2 p hne hpx
  rw [jacobian_transported_form_value,jacobian_transported_form_value,
    jacobian_value_density_congr j₂ j₁ p p (hj2.trans hj1.symm)]

end IntegrationInACVF.Section7.GammaFun
