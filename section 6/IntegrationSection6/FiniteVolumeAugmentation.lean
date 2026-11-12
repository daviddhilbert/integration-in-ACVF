import IntegrationSection6.GammaRVKeyGraphs

/-! Appending selected RV labels to the volume keeps the object in the
finite category. This supports the E ∪ I_n projection in6.14. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n e : ℕ}

/-- The literal packed volume tuple, on the unchanged finite RV domain. -/
def augmentedVolumeMap (U : RVFiniteObject (M := M) S n) (ρ : Fin e → Fin U.obj.arity) :=
  (@rvPack M sM S n e
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M sM (@SpecialTransformations.Section4.rawRVSpace M sM n) S)
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M sM (@SpecialTransformations.Section4.rawRVSpace M sM e) S)).comp
    (U.obj.volume.pair (@selectRVTuple M sM S U.obj.arity e ρ U.obj.domain))

def addVolumeLabelsObject (U : RVFiniteObject (M := M) S n) (ρ : Fin e → Fin U.obj.arity) :
    RVFiniteObject (M := M) S (n+e) := by
  let F := augmentedVolumeMap U ρ
  refine ⟨RVObject.mk U.obj.arity U.obj.domain F,?_⟩
  intro t
  apply (U.property ⟨fun j => t.val (Fin.castAdd e j),Set.mem_univ _⟩).subset
  intro u hu
  apply Subtype.ext
  funext j
  have h := congrFun (congrArg Subtype.val hu) (Fin.castAdd e j)
  change Fin.append (U.obj.value u) (fun j => u.val (ρ j)) (Fin.castAdd e j) = t.val (Fin.castAdd e j) at h
  exact (Fin.append_left _ _ j).symm.trans h

@[simp] theorem addVolumeLabelsObject_value (U : RVFiniteObject (M := M) S n) (ρ : Fin e → Fin U.obj.arity)
    (u : U.obj.domain) :
    (addVolumeLabelsObject U ρ).obj.value u = Fin.append (U.obj.value u) (fun j => u.val (ρ j)) := rfl

variable {B : Base (M := M)}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def GammaObjectAt.addVolumeLabels (U : GammaObjectAt B S n) (ρ : Fin e → Fin (rvObjectArity U.object.obj)) :
    GammaObjectAt B S (n+e) where
  object := @addVolumeLabelsObject M N S n e U.object ρ
  real_contains := U.real_contains
  domain_graph := U.domain_graph
  volume_graph := by
    let H := @selectRVTuple M N B.real (rvObjectArity U.object.obj) e ρ
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) B.real)
    exact gamma_volume_key_graph U H
      (fun u => (@RVObject.value M N S (n+e) (@addVolumeLabelsObject M N S n e U.object ρ).obj u)) (fun _ => rfl)

end IntegrationInACVF.Section6.FiniteRV
