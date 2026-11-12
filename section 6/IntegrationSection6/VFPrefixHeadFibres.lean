import IntegrationSection6.VFPrefixFibreMaps
import IntegrationSection6.VFPrefixHeadCoordinates
import IntegrationSection5.RelativeSpecialRestriction

/-! Exact head-coordinate fibres and parameter inclusion after freezing a
VF tail. These identify the actual unary special witnesses on both sides. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n p a b : ℕ}
variable {U : DefSet (M := M) S (n+(p+1)) a} {V : DefSet (M := M) S (n+(p+1)) b}

theorem vfPrefixRelative_of_unaryHead (f : Map U V) (hi : UnaryRelative f 0) :
    VFPrefixRelative (p := p+1) f := by
  intro u j
  apply hi u ⟨(p+1)+j.val,by omega⟩
  intro h
  have he := congrArg Fin.val h
  change (p+1)+j.val = 0 at he
  omega

theorem vfPrefixFibreMap_unaryHead (f : Map U V) (hi : UnaryRelative f 0)
    (x : Fin n → VF (M := M)) :
    UnaryRelative (vfPrefixFibreMap f (vfPrefixRelative_of_unaryHead f hi) x) 0 := by
  intro u j hj
  change (f ⟨vfPrefixInsert x u.val,u.property⟩).val.1 ⟨j.val,by omega⟩ = u.val.1 j
  have hne : (⟨j.val,by omega⟩ : Fin (n+(p+1))) ≠ 0 := by
    intro h
    apply hj
    apply Fin.ext
    exact congrArg (fun i : Fin (n+(p+1)) => i.val) h
  exact (hi ⟨vfPrefixInsert x u.val,u.property⟩ _ hne).trans (vfPrefixTuple_head x u.val.1 j)

theorem vfPrefixHeadFibre_carrier (A : DefSet (M := M) S (n+(p+1)) a)
    (x : Fin n → VF (M := M)) (u : Fin (p+1) → VF (M := M)) :
    carrier (coordinateFibre (vfPrefixFibre A x) 0 u) = carrier (coordinateFibre A 0 (vfPrefixTuple x u)) := by
  ext q
  change (vfPrefixInsert x (coordinateInsert 0 u q) ∈ carrier A) ↔ _
  rw [vfPrefixInsert_coordinateInsert]
  rfl

theorem vfPrefixHeadFibre_parameters (x : Fin n → VF (M := M)) (u : Fin (p+1) → VF (M := M)) :
    coordinateFibreBase S 0 (vfPrefixTuple x u) ⊆
      coordinateFibreBase (S ∪ Set.range (fun j => (x j).val)) 0 u := by
  intro c hc
  rcases hc with hc | ⟨j,rfl⟩
  · exact Or.inl (Or.inl hc)
  · by_cases hj : j.val.val < p+1
    · have hne : (⟨j.val.val,hj⟩ : Fin (p+1)) ≠ 0 := by
        intro h
        apply j.property
        apply Fin.ext
        exact congrArg (fun i : Fin (p+1) => i.val) h
      refine Or.inr ⟨⟨⟨j.val.val,hj⟩,hne⟩,?_⟩
      simp only [vfPrefixTuple,dite_eq_left hj]
    · refine Or.inl (Or.inr ⟨⟨j.val.val-(p+1),by have h := j.val.isLt; omega⟩,?_⟩)
      simp only [vfPrefixTuple,dite_eq_right hj]

end IntegrationInACVF.Section6
