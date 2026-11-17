module

public import Integration7.MixedVFBaseBijections
public import Integration7.InverseJacobianVolumeForms
public import Integration7.RVCoordinateSelection

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A pure VF base map has a literal mixed presentation with an empty
RV tuple. Its inverse-Jacobian density pulls back to the actual pure VF
target and can be used to correct a family pushforward. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
variable {X Y : DefSet (rawVFSpace (M := M) n) S}

def pureVFEmptyGraphMap (X : DefSet (rawVFSpace (M := M) n) S) :
    Map X (X.prod (DefSet.univ (rawRVSpace (M := M) 0) S)) :=
  (Map.id X).pair ((rvCoordinateSelectMap S (Fin.elim0 : Fin 0 → Fin 1)).comp (rvScalarOne X))

theorem pure_vf_empty_graph_map_value (X : DefSet (rawVFSpace (M := M) n) S) (x : X) :
    (pureVFEmptyGraphMap X x).val = (x.val,Fin.elim0) :=
  Prod.ext rfl (Subsingleton.elim _ _)

theorem pure_vf_empty_graph_map_bijective (X : DefSet (rawVFSpace (M := M) n) S) :
    Function.Bijective (pureVFEmptyGraphMap X) := by
  constructor
  · intro x y h
    exact Subtype.ext (congrArg (fun q : X.prod (DefSet.univ (rawRVSpace (M := M) 0) S) => q.val.1) h)
  · intro p
    exact ⟨⟨p.val.1,p.property.1⟩,Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))⟩

def pureVFMixedMap (φ : Map X Y) :
    Map (X.prod (DefSet.univ (rawRVSpace (M := M) 0) S))
      (Y.prod (DefSet.univ (rawRVSpace (M := M) 0) S)) :=
  Map.prodMap φ (Map.id _)

theorem pure_vf_mixed_map_bijective (φ : Map X Y) (hφ : Function.Bijective φ) :
    Function.Bijective (pureVFMixedMap φ) :=
  Map.prodMap_bijective φ (Map.id _) hφ Function.bijective_id

def pureVFInverseJacobianDensityForm (φ : Map X Y) (hφ : Function.Bijective φ) : VolumeForm Y :=
  (mixedJacobianDensityForm ((pureVFMixedMap φ).inverse (pure_vf_mixed_map_bijective φ hφ))).pullback
    (pureVFEmptyGraphMap Y)

theorem pure_vf_inverse_jacobian_density_value (φ : Map X Y) (hφ : Function.Bijective φ) (y : Y) :
    (pureVFInverseJacobianDensityForm φ hφ).value y =
      (mixedJacobianDensityForm ((pureVFMixedMap φ).inverse (pure_vf_mixed_map_bijective φ hφ))).value
        (pureVFEmptyGraphMap Y y) := rfl

end IntegrationInACVF.Section7
