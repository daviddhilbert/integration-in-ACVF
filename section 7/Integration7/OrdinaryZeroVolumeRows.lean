import Integration7.VFRVFibres
import Integration7.RVCoordinateSelection
import Integration7.GradedVolumeBlowups
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

def ordinaryZeroVolumeRow (A : DefSet (rawMixedSpace (M := M) n a) S)
    (hfin : ∀ x : Fin n → VFType (M := M), {r | (x,r) ∈ A.carrier}.Finite)
    (x : Fin n → VFType (M := M)) : RVVolumeObject (M := M) (S ∪ Set.range (fun i => (x i).val)) 0 where
  obj := ⟨a,vfRVFibre A x,(rvCoordinateSelectMap _ (Fin.elim0 : Fin 0 → Fin a)).restrict (Set.subset_univ _)⟩
  property := by
    intro t
    apply (hfin x).of_injOn (f := fun r : vfRVFibre A x => r.val)
    · intro r hr
      exact r.property
    · intro r hr r' hr' he
      exact Subtype.ext he

theorem ordinaryZeroVolumeRow_refl
    (A : DefSet (rawMixedSpace (M := M) n a) S)
    (hfin : ∀ x : Fin n → VFType (M := M), {r | (x,r) ∈ A.carrier}.Finite)
    (x : Fin n → VFType (M := M)) :
    MuIsp (S ∪ Set.range (fun i => (x i).val)) 0
      (ordinaryZeroVolumeRow A hfin x) (ordinaryZeroVolumeRow A hfin x) := ⟨Iso.refl _⟩
end IntegrationInACVF.Section7
