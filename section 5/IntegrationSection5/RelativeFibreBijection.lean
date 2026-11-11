import IntegrationSection5.RelativeSpecial

/-! Actual fibrewise bijectivity is equivalent to global bijectivity for a
map fixing the complementary VF coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem coordinateFibreMap_bijective_iff (f : Map A B) (i : Fin n) (hi : UnaryRelative f i) :
    Function.Bijective f ↔ ∀ u, Function.Bijective (coordinateFibreMap f i hi u) := by
  constructor
  · exact fun hf u => coordinateFibreMap_bijective f hf i hi u
  · intro hF
    constructor
    · intro a b hab
      let u := a.val.1
      have ha : coordinateInsert i u (coordinateProject i a.val) = a.val :=
        coordinateInsert_project i u a.val (fun _ _ => rfl)
      have hb : coordinateInsert i u (coordinateProject i b.val) = b.val := by
        apply coordinateInsert_project
        intro j hj
        have h := congrArg (fun z : B => vfAt z.val j) hab
        exact (hi b j hj).symm.trans (h.symm.trans (hi a j hj))
      let x : coordinateFibre A i u := ⟨coordinateProject i a.val,by
        change coordinateInsert i u (coordinateProject i a.val) ∈ carrier A
        rw [ha]
        exact a.property⟩
      let y : coordinateFibre A i u := ⟨coordinateProject i b.val,by
        change coordinateInsert i u (coordinateProject i b.val) ∈ carrier A
        rw [hb]
        exact b.property⟩
      have hx : (⟨coordinateInsert i u x.val,x.property⟩ : A) = a := Subtype.ext ha
      have hy : (⟨coordinateInsert i u y.val,y.property⟩ : A) = b := Subtype.ext hb
      have hxy : coordinateFibreMap f i hi u x = coordinateFibreMap f i hi u y := by
        apply Subtype.ext
        rw [coordinateFibreMap_apply,coordinateFibreMap_apply,hx,hy,hab]
      have hval := congrArg (fun z : coordinateFibre A i u => coordinateInsert i u z.val) ((hF u).1 hxy)
      exact Subtype.ext (ha.symm.trans (hval.trans hb))
    · intro b
      let u := b.val.1
      have hb : coordinateInsert i u (coordinateProject i b.val) = b.val :=
        coordinateInsert_project i u b.val (fun _ _ => rfl)
      let y : coordinateFibre B i u := ⟨coordinateProject i b.val,by
        change coordinateInsert i u (coordinateProject i b.val) ∈ carrier B
        rw [hb]
        exact b.property⟩
      obtain ⟨x,hx⟩ := (hF u).2 y
      refine ⟨⟨coordinateInsert i u x.val,x.property⟩,Subtype.ext ?_⟩
      exact (coordinateFibreMap_insert f i hi u x).symm.trans
        ((congrArg (fun z : coordinateFibre B i u => coordinateInsert i u z.val) hx).trans hb)

theorem specialRelative_bijective {f : Map A B} {i : Fin n} (h : SpecialRelative f i) :
    Function.Bijective f := by
  obtain ⟨hi,hT⟩ := h
  apply (coordinateFibreMap_bijective_iff f i hi).mpr
  intro u
  obtain ⟨T,he⟩ := hT u
  have hm : T.toMap = coordinateFibreMap f i hi u := Map.ext he
  rw [← hm]
  exact T.bijective

end IntegrationInACVF.Section5
