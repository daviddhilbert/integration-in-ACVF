import IntegrationSection5.RelativeSpecialExtension
import Section5.UnarySets

/-! Restriction of actual fibre-special chains, retaining their end kind.
The primitive restriction is the pinned focus/canonical construction. -/
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
variable {S : Set M} {n m l : ℕ}

theorem chain_restrict_boundary {X : DefSet (M := M) S n m} {Y : DefSet (M := M) S n l}
    (T : Chain S n X Y) (A : DefSet (M := M) S n m) (hAX : carrier A ⊆ carrier X)
    (previous : Option Bool) (hT : T.Alternating previous) :
    ∃ B : DefSet (M := M) S n l, ∃ U : Chain S n A B,
      U.Alternating previous ∧ U.lastKind previous = T.lastKind previous ∧ carrier B ⊆ carrier Y ∧
        ∀ a : A, (U.toMap a).val = (T.toMap ⟨a.val,hAX a.property⟩).val := by
  induction T generalizing previous with
  | nil X => exact ⟨A,.nil A,trivial,rfl,hAX,fun _ => rfl⟩
  | cons p tail ih =>
    obtain ⟨hprev,htail⟩ := (Chain.cons_alternating_iff p tail previous).mp hT
    obtain ⟨A',q,hkind,hsub,hq⟩ := p.restrict A hAX
    obtain ⟨B,U,hU,hEnd,hB,hu⟩ := ih A' hsub (some p.kind) htail
    refine ⟨B,.cons q U,?_,?_,hB,?_⟩
    · apply (Chain.cons_alternating_iff q U previous).mpr
      simpa only [hkind] using And.intro hprev hU
    · rw [Chain.lastKind_cons,Chain.lastKind_cons,hkind]
      exact hEnd
    · intro a
      change (U.toMap (q.toMap a)).val = (tail.toMap (p.toMap ⟨a.val,hAX a.property⟩)).val
      have he : (⟨(q.toMap a).val,hsub (q.toMap a).property⟩ : _) =
          p.toMap ⟨a.val,hAX a.property⟩ := Subtype.ext (hq a)
      rw [hu (q.toMap a),he]

theorem special_restrict_boundary {X : DefSet (M := M) S n m} {Y : DefSet (M := M) S n l}
    (T : SpecialBijection X Y) (A : DefSet (M := M) S n m) (hAX : carrier A ⊆ carrier X)
    (previous : Option Bool) (hT : T.chain.Alternating previous) :
    ∃ B : DefSet (M := M) S n l, ∃ U : SpecialBijection A B,
      U.chain.Alternating previous ∧ U.chain.lastKind previous = T.chain.lastKind previous ∧
        carrier B ⊆ carrier Y ∧ ∀ a : A, (U.toMap a).val = (T.toMap ⟨a.val,hAX a.property⟩).val := by
  obtain ⟨B,U,hU,hEnd,hB,hu⟩ := chain_restrict_boundary T.chain A hAX previous hT
  exact ⟨B,⟨U,U.alternating_none previous hU⟩,hU,hEnd,hB,hu⟩

theorem defSet_eq_of_carrier_eq {X Y : DefSet (M := M) S n m} (h : carrier X = carrier Y) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

def restrictPointImage {X : DefSet (M := M) S n m} {Y : DefSet (M := M) S n l}
    (f : Map X Y) (A : DefSet (M := M) S n m) (hAX : carrier A ⊆ carrier X) :=
  Map.image (Map.comp f (Map.inclusion hAX))

def restrictPointMap {X : DefSet (M := M) S n m} {Y : DefSet (M := M) S n l}
    (f : Map X Y) (A : DefSet (M := M) S n m) (hAX : carrier A ⊆ carrier X) :
    Map A (restrictPointImage f A hAX) := Map.toImage (Map.comp f (Map.inclusion hAX))

theorem specialRelativeBoundary_restrict {X : DefSet (M := M) S n m} {Y : DefSet (M := M) S n l}
    (f : Map X Y) (A : DefSet (M := M) S n m) (hAX : carrier A ⊆ carrier X) {i : Fin n}
    {previous ending : Option Bool} (hf : SpecialRelativeBoundary f i previous ending) :
    SpecialRelativeBoundary (restrictPointMap f A hAX) i previous ending := by
  obtain ⟨hi,hT⟩ := hf
  have hiA : UnaryRelative (restrictPointMap f A hAX) i := fun a j hj => hi ⟨a.val,hAX a.property⟩ j hj
  refine ⟨hiA,?_⟩
  intro u
  obtain ⟨T,hTa,hTe,hT⟩ := hT u
  have hsub : carrier (coordinateFibre A i u) ⊆ carrier (coordinateFibre X i u) := fun p hp => hAX hp
  obtain ⟨B,U,hUa,hUe,hB,hU⟩ := special_restrict_boundary T (coordinateFibre A i u) hsub previous hTa
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
  refine ⟨specialCastTarget U hEq,?_,?_,?_⟩
  · rw [specialCastTarget_alternating]
    exact hUa
  · rw [specialCastTarget_lastKind,hUe,hTe]
  · intro p
    apply Subtype.ext
    apply coordinateInsert_injective i u
    rw [specialCastTarget_val,hU p,hF p,coordinateFibreMap_insert]
    rfl

end IntegrationInACVF.Section5
