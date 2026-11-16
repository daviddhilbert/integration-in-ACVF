module

public import Integration7.MixedVFBaseDensityAgreement

@[expose] public section

/-! The actual inverse family Jacobian agrees with the inverse pure-base
Jacobian at generic source points and hence outside a definable small set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a : ℕ}

theorem inverse_mixed_vf_base_density_at_generic
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (U : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hU : ∀ p : U, p.val.1 ∈ X.carrier) (p : U)
    (hp : AlgebraicIndependent (vfParameterField (C.base : Set M)) p.val.1) :
    let f := (mixedVFBaseMap φ U hU).toImage
    let hf := mixed_vf_base_map_to_image_bijective φ hφ.1 U hU
    (mixedJacobianDensityForm (f.inverse hf)).value (f p) =
      (pureVFInverseJacobianDensityForm φ hφ).value (φ ⟨p.val.1,hU p⟩) := by
  intro f hf
  let x : X := ⟨p.val.1,hU p⟩
  let q := pureVFEmptyGraphMap X x
  have hq : AlgebraicIndependent (vfParameterField (C.base : Set M)) q.val.1 := hp
  have hFamily := (mixed_inverse_jacobian_density_balance_ae hc C hn f hf).at_independent hc p hp
  have hPure := (mixed_inverse_jacobian_density_balance_ae hc C hn (pureVFMixedMap φ)
    (pure_vf_mixed_map_bijective φ hφ)).at_independent hc q hq
  have hImage : pureVFMixedMap φ q = pureVFEmptyGraphMap Y (φ x) :=
    Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
  rw [hImage] at hPure
  change (pureVFInverseJacobianDensityForm φ hφ).value (φ x) *
    (pureVFJacobianDensityForm φ).value x = 1 at hPure
  have hForward := mixed_vf_base_jacobian_density_at_generic hc C hn φ hφ U hU p hp
  change (mixedJacobianDensityForm f).value p = (pureVFJacobianDensityForm φ).value x at hForward
  rw [hForward] at hFamily
  exact mul_right_cancel₀ ((pureVFJacobianDensityForm φ).value_ne_zero x) (hFamily.trans hPure.symm)

theorem inverse_mixed_vf_base_density_agreement_ae
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (U : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hU : ∀ p : U, p.val.1 ∈ X.carrier) :
    let f := (mixedVFBaseMap φ U hU).toImage
    let hf := mixed_vf_base_map_to_image_bijective φ hφ.1 U hU
    VFAlmostEverywhere U (fun p =>
      (mixedJacobianDensityForm (f.inverse hf)).value (f p) =
        (pureVFInverseJacobianDensityForm φ hφ).value (φ ⟨p.val.1,hU p⟩)) := by
  intro f hf
  let ω := (mixedJacobianDensityForm (f.inverse hf)).pullback f
  let η := (pureVFInverseJacobianDensityForm φ hφ).pullback (φ.comp (mixedVFBaseSourceProjection U hU))
  have hMaps : VFAlmostEverywhere U (fun p => (ω.map p).val = (η.map p).val) := by
    apply vf_almost_everywhere_maps_eq_of_generic hc C hn ω.map η.map
    intro p hp
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact inverse_mixed_vf_base_density_at_generic hc C hn φ hφ U hU p hp
  exact hMaps.mono (fun p h => congrFun h 0)

end IntegrationInACVF.Section7
