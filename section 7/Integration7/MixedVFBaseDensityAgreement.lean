import Integration7.MixedVFBaseJacobianDensities
import Integration7.VFAlmostEverywhereMapEquality

/-! The Jacobian of the actual mixed-family base map agrees almost
everywhere with the pure base Jacobian pulled back to that family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

def mixedVFBaseSourceProjection {X : DefSet (rawVFSpace (M := M) n) S}
    (U : DefSet (rawMixedSpace (M := M) n a) S) (hU : ∀ p : U, p.val.1 ∈ X.carrier) : Map U X :=
  (Map.fst (rawVFSpace (M := M) n) (rawRVSpace a) S U).corestrict hU

def pureVFJacobianDensityForm {X Y : DefSet (rawVFSpace (M := M) n) S} (φ : Map X Y) : VolumeForm X :=
  (mixedJacobianDensityForm (pureVFMixedMap φ)).pullback (pureVFEmptyGraphMap X)

theorem mixed_vf_base_jacobian_density_agreement_ae
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (U : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hU : ∀ p : U, p.val.1 ∈ X.carrier) :
    VFAlmostEverywhere U (fun p =>
      (mixedJacobianDensityForm (mixedVFBaseMap φ U hU).toImage).value p =
        (pureVFJacobianDensityForm φ).value ⟨p.val.1,hU p⟩) := by
  let ω := mixedJacobianDensityForm (mixedVFBaseMap φ U hU).toImage
  let η := (pureVFJacobianDensityForm φ).pullback (mixedVFBaseSourceProjection U hU)
  have hMaps : VFAlmostEverywhere U (fun p => (ω.map p).val = (η.map p).val) := by
    apply vf_almost_everywhere_maps_eq_of_generic hc C hn ω.map η.map
    intro p hp
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact mixed_vf_base_jacobian_density_at_generic hc C hn φ hφ U hU p hp
  exact hMaps.mono (fun p h => congrFun h 0)

end IntegrationInACVF.Section7
