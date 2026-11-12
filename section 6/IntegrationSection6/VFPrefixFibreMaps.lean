import IntegrationSection6.VFPrefixMaps
import IntegrationSection5.RelativeSpecialExtension

/-! Maps preserving the frozen VF tail induce actual maps on prefix fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n p a b : ℕ}
variable {U : DefSet (M := M) S (n+p) a} {V : DefSet (M := M) S (n+p) b}

def VFPrefixRelative (f : Map U V) : Prop :=
  ∀ u : U, ∀ j : Fin n, (f u).val.1 ⟨p+j.val,by omega⟩ = u.val.1 ⟨p+j.val,by omega⟩

def vfPrefixFibreMap (f : Map U V) (hi : VFPrefixRelative f) (x : Fin n → VF (M := M)) :
    Map (vfPrefixFibre U x) (vfPrefixFibre V x) :=
  let hSR : S ⊆ S ∪ Set.range (fun j => (x j).val) := Set.subset_union_left
  let g := Map.comp (vfPrefixProjectMap (p := p) (extendBase V hSR))
    (Map.comp (extendPointMap f hSR) (vfPrefixFibreEmbedding U x))
  mapIntoSubset g (vfPrefixFibre V x) (by
    intro q
    let u : U := ⟨vfPrefixInsert x q.val,q.property⟩
    change vfPrefixInsert x (vfPrefixProject (f u).val) ∈ carrier V
    have ht : VFPrefixTailFixed x (f u).val := fun j =>
      (hi u j).trans (vfPrefixTuple_tail x q.val.1 j)
    rw [vfPrefixInsert_project x (f u).val ht]
    exact (f u).property)

theorem vfPrefixFibreMap_apply (f : Map U V) (hi : VFPrefixRelative f)
    (x : Fin n → VF (M := M)) (q : vfPrefixFibre U x) :
    (vfPrefixFibreMap f hi x q).val = vfPrefixProject (f ⟨vfPrefixInsert x q.val,q.property⟩).val := rfl

theorem vfPrefixFibreMap_insert (f : Map U V) (hi : VFPrefixRelative f)
    (x : Fin n → VF (M := M)) (q : vfPrefixFibre U x) :
    vfPrefixInsert x (vfPrefixFibreMap f hi x q).val = (f ⟨vfPrefixInsert x q.val,q.property⟩).val := by
  rw [vfPrefixFibreMap_apply]
  apply vfPrefixInsert_project
  intro j
  exact (hi ⟨vfPrefixInsert x q.val,q.property⟩ j).trans (vfPrefixTuple_tail x q.val.1 j)

theorem vfPrefixFibreMap_bijective (f : Map U V) (hf : Function.Bijective f)
    (hi : VFPrefixRelative f) (x : Fin n → VF (M := M)) : Function.Bijective (vfPrefixFibreMap f hi x) := by
  constructor
  · intro u v he
    have h := congrArg (fun q : vfPrefixFibre V x => vfPrefixInsert x q.val) he
    rw [vfPrefixFibreMap_insert,vfPrefixFibreMap_insert] at h
    have huv := hf.1 (Subtype.ext h)
    exact Subtype.ext (vfPrefixInsert_injective x (congrArg (fun q : U => q.val) huv))
  · intro v
    let y : V := ⟨vfPrefixInsert x v.val,v.property⟩
    let u := Map.inverse f hf y
    have ht : VFPrefixTailFixed x u.val := by
      intro j
      have h := congrArg (fun q : V => q.val.1 ⟨p+j.val,by omega⟩) (Map.apply_inverse f hf y)
      exact (hi u j).symm.trans (h.trans (vfPrefixTuple_tail x v.val.1 j))
    have hr := vfPrefixInsert_project x u.val ht
    let q : vfPrefixFibre U x := ⟨vfPrefixProject u.val,by
      change vfPrefixInsert x (vfPrefixProject u.val) ∈ carrier U
      rw [hr]
      exact u.property⟩
    refine ⟨q,Subtype.ext ?_⟩
    apply vfPrefixInsert_injective x
    rw [vfPrefixFibreMap_insert]
    have he : (⟨vfPrefixInsert x q.val,q.property⟩ : U) = u := Subtype.ext hr
    rw [he]
    exact congrArg Subtype.val (Map.apply_inverse f hf y)

end IntegrationInACVF.Section6
