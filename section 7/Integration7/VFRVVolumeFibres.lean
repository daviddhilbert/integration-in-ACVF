import Integration7.VFRVFibres
import Integration7.RVVolumeObjects
import Integration7.RVCoordinateSelection
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p a k : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) p a) S}

def vfRVVolumeFibre (ω : VolumeForm A) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin p → VFType (M := M)) (t : Fin (k+1) → CanonicalRV.RVSort M),
      {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ A.carrier ∧ r ∘ ρ=t}.Finite)
    (x : Fin p → VFType (M := M)) :
    PositiveRVVolumeObject (M := M) (S ∪ Set.range (fun i => (x i).val)) k where
  underlying := {
    obj := ⟨a,vfRVFibre A x,(rvCoordinateSelectMap _ ρ).restrict (Set.subset_univ _)⟩
    property := by
      intro y
      apply (hfin x y.val).of_injOn (f := fun r : vfRVFibre A x => r.val)
      · intro r hr
        exact ⟨r.property,congrArg Subtype.val hr⟩
      · intro r hr r' hr' he
        exact Subtype.ext he }
  form := ω.vfRVFibre x

@[simp] theorem vfRVVolumeFibre_volume (ω : VolumeForm A) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin p → VFType (M := M)) (t : Fin (k+1) → CanonicalRV.RVSort M),
      {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ A.carrier ∧ r ∘ ρ=t}.Finite)
    (x : Fin p → VFType (M := M)) (r : (vfRVVolumeFibre ω ρ hfin x).underlying.obj.domain) :
    (vfRVVolumeFibre ω ρ hfin x).underlying.obj.value r=r.val ∘ ρ := rfl

@[simp] theorem vfRVVolumeFibre_density (ω : VolumeForm A) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin p → VFType (M := M)) (t : Fin (k+1) → CanonicalRV.RVSort M),
      {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ A.carrier ∧ r ∘ ρ=t}.Finite)
    (x : Fin p → VFType (M := M)) (r : (vfRVVolumeFibre ω ρ hfin x).underlying.obj.domain) :
    (vfRVVolumeFibre ω ρ hfin x).form.value r=ω.value ⟨(x,r.val),r.property⟩ := rfl
end IntegrationInACVF.Section7
