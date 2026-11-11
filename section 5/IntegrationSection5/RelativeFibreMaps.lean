import IntegrationSection5.CoordinateFibreMaps

/-! Relatively unary maps induce actual definable maps of coordinate fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem coordinateInsert_other (i : Fin n) (u : Fin n → VF (M := M))
    (p : Point (M := M) 1 m) (j : Fin n) (hj : j ≠ i) :
    vfAt (coordinateInsert i u p) j = u j := Function.update_of_ne hj _ _

def coordinateFibreMap (f : Map A B) (i : Fin n) (hi : UnaryRelative f i)
    (u : Fin n → VF (M := M)) : Map (coordinateFibre A i u) (coordinateFibre B i u) :=
  let R := coordinateFibreBase S i u
  let hSR : S ⊆ R := Set.subset_union_left
  let fR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
    (@CanonicalStructure.normalize M sM) (pointSpace n m) (pointSpace n l) S R A B f hSR
  let g := Map.comp (coordinateProjectMap i (extendBase B hSR))
    (Map.comp fR (coordinateFibreEmbedding A i u))
  mapIntoSubset g (coordinateFibre B i u) (by
    intro p
    let a : A := ⟨coordinateInsert i u p.val,p.property⟩
    change coordinateInsert i u (coordinateProject i (f a).val) ∈ carrier B
    have hOther : ∀ j, j ≠ i → vfAt (f a).val j = u j := by
      intro j hj
      exact (hi a j hj).trans (coordinateInsert_other i u p.val j hj)
    rw [coordinateInsert_project i u (f a).val hOther]
    exact (f a).property)

theorem coordinateFibreMap_apply (f : Map A B) (i : Fin n) (hi : UnaryRelative f i)
    (u : Fin n → VF (M := M)) (p : coordinateFibre A i u) :
    (coordinateFibreMap f i hi u p).val =
      coordinateProject i (f ⟨coordinateInsert i u p.val,p.property⟩).val := rfl

theorem coordinateFibreMap_insert (f : Map A B) (i : Fin n) (hi : UnaryRelative f i)
    (u : Fin n → VF (M := M)) (p : coordinateFibre A i u) :
    coordinateInsert i u (coordinateFibreMap f i hi u p).val =
      (f ⟨coordinateInsert i u p.val,p.property⟩).val := by
  rw [coordinateFibreMap_apply]
  apply coordinateInsert_project
  intro j hj
  exact (hi ⟨coordinateInsert i u p.val,p.property⟩ j hj).trans (coordinateInsert_other i u p.val j hj)

theorem coordinateFibreMap_bijective (f : Map A B) (hf : Function.Bijective f)
    (i : Fin n) (hi : UnaryRelative f i) (u : Fin n → VF (M := M)) :
    Function.Bijective (coordinateFibreMap f i hi u) := by
  constructor
  · intro a b he
    have h := congrArg (fun p : coordinateFibre B i u => coordinateInsert i u p.val) he
    rw [coordinateFibreMap_insert,coordinateFibreMap_insert] at h
    have hab := hf.1 (Subtype.ext h)
    apply Subtype.ext
    apply coordinateInsert_injective i u
    exact congrArg (fun c : A => c.val) hab
  · intro b
    let y : B := ⟨coordinateInsert i u b.val,b.property⟩
    let x := Map.inverse f hf y
    have hOther : ∀ j, j ≠ i → vfAt x.val j = u j := by
      intro j hj
      exact (unaryRelative_inverse f hf hi y j hj).trans (coordinateInsert_other i u b.val j hj)
    have hRestore := coordinateInsert_project i u x.val hOther
    let a : coordinateFibre A i u := ⟨coordinateProject i x.val,by
      change coordinateInsert i u (coordinateProject i x.val) ∈ carrier A
      rw [hRestore]
      exact x.property⟩
    refine ⟨a,Subtype.ext ?_⟩
    apply coordinateInsert_injective i u
    rw [coordinateFibreMap_insert]
    have hax : (⟨coordinateInsert i u a.val,a.property⟩ : A) = x := Subtype.ext hRestore
    rw [hax]
    exact congrArg Subtype.val (Map.apply_inverse f hf y)

end IntegrationInACVF.Section5
