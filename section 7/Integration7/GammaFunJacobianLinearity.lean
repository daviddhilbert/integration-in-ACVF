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
