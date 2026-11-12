import IntegrationSection5.RelativeSpecialRestriction

/-! Restriction of an actual relatively special map to any definable
source subset. The existing unary special-chain restriction is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}

theorem specialRelative_restrict {X : DefSet (M := M) S n m} {Y : DefSet (M := M) S n l}
    (f : Map X Y) (A : DefSet (M := M) S n m) (hAX : carrier A ⊆ carrier X) {i : Fin n}
    (hf : SpecialRelative f i) :
    SpecialRelative (restrictPointMap f A hAX) i := by
  obtain ⟨hi,hT⟩ := hf
  have hiA : UnaryRelative (restrictPointMap f A hAX) i := fun a j hj => hi ⟨a.val,hAX a.property⟩ j hj
  refine ⟨hiA,?_⟩
  intro u
  obtain ⟨T,hT⟩ := hT u
  have hsub : carrier (coordinateFibre A i u) ⊆ carrier (coordinateFibre X i u) := fun p hp => hAX hp
  obtain ⟨B,U,hUa,hUe,hB,hU⟩ := special_restrict_boundary T (coordinateFibre A i u) hsub none T.alternating
  have hF (p : coordinateFibre A i u) :
      coordinateInsert i u (T.toMap ⟨p.val,hsub p.property⟩).val =
        (f ⟨coordinateInsert i u p.val,hAX p.property⟩).val := by
    rw [hT]
    exact coordinateFibreMap_insert f i hi u ⟨p.val,hsub p.property⟩
  have hEq : B = coordinateFibre (restrictPointImage f A hAX) i u := by
    apply defSet_eq_of_carrier_eq
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp⟩ := U.bijective.2 ⟨q,hq⟩
      change ∃ a : A, (f ⟨a.val,hAX a.property⟩).val = coordinateInsert i u q
      refine ⟨⟨coordinateInsert i u p.val,p.property⟩,?_⟩
      have he := (hU p).symm.trans (congrArg (fun z : B => z.val) hp)
      exact (hF p).symm.trans (congrArg (coordinateInsert i u) he)
    · rintro ⟨a,ha⟩
      have hOther : ∀ j, j ≠ i → vfAt a.val j = u j := by
        intro j hj
        have h := congrArg (fun z : Point (M := M) n l => vfAt z j) ha
        exact (hi ⟨a.val,hAX a.property⟩ j hj).symm.trans (h.trans (coordinateInsert_other i u q j hj))
      have hRestore := coordinateInsert_project i u a.val hOther
      let p : coordinateFibre A i u := ⟨coordinateProject i a.val,by
        change coordinateInsert i u (coordinateProject i a.val) ∈ carrier A
        rw [hRestore]
        exact a.property⟩
      have hax : (⟨coordinateInsert i u p.val,hAX p.property⟩ : X) = ⟨a.val,hAX a.property⟩ := Subtype.ext hRestore
      have he : (U.toMap p).val = q := by
        apply coordinateInsert_injective i u
        rw [hU p,hF p,hax]
        exact ha
      exact he ▸ (U.toMap p).property
  refine ⟨specialCastTarget U hEq,?_⟩
  intro p
  apply Subtype.ext
  apply coordinateInsert_injective i u
  rw [specialCastTarget_val,hU p,hF p,coordinateFibreMap_insert]
  rfl

end IntegrationInACVF.Section6
