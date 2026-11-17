module

public import Integration7.MixedVFBaseJacobianCharts
public import Integration7.VFAlmostEverywhereGenericValues

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! At every generic mixed-family point, the actual family Jacobian
density is exactly the density of its pure VF base map. -/
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

theorem mixed_vf_base_jacobian_density_at_generic
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (U : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hU : ∀ p : U, p.val.1 ∈ X.carrier) (p : U)
    (hp : AlgebraicIndependent (vfParameterField (C.base : Set M)) p.val.1) :
    (mixedJacobianDensityForm (mixedVFBaseMap φ U hU).toImage).value p =
      (mixedJacobianDensityForm (pureVFMixedMap φ)).value (pureVFEmptyGraphMap X ⟨p.val.1,hU p⟩) := by
  let q := pureVFEmptyGraphMap X ⟨p.val.1,hU p⟩
  have hq : AlgebraicIndependent (vfParameterField (C.base : Set M)) q.val.1 := hp
  obtain ⟨J,hJ,hJ0,hPure⟩ :=
    (mixed_bijective_jacobian_density_ae hc C hn (pureVFMixedMap φ)
      (pure_vf_mixed_map_bijective φ hφ)).at_independent hc q hq
  obtain ⟨K,hK,hK0,hFamily⟩ :=
    (mixed_bijective_jacobian_density_ae hc C hn (mixedVFBaseMap φ U hU).toImage
      (mixed_vf_base_map_to_image_bijective φ hφ.1 U hU)).at_independent hc p hp
  have hJK := mixed_vf_base_jacobian_eq φ U hU p J K hJ hK
  exact hFamily.trans ((congrArg CanonicalRV.encodedRv hJK).symm.trans hPure.symm)

end IntegrationInACVF.Section7
