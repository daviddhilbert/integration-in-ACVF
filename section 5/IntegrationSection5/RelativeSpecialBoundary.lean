import IntegrationSection5.CoordinateCanonicalFibre
import IntegrationSection5.FibreFocusAssembly
import Section5.Centering

/-! Fibrewise special composition with explicit alternation boundaries. -/
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
variable {S : Set M} {n m l r : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n r}

def SpecialRelativeBoundary (f : Map A B) (i : Fin n) (previous ending : Option Bool) : Prop :=
  ∃ hi : UnaryRelative f i, ∀ u : Fin n → VF (M := M),
    ∃ T : SpecialBijection (coordinateFibre A i u) (coordinateFibre B i u),
      T.chain.Alternating previous ∧ T.chain.lastKind previous = ending ∧
        ∀ p, T.toMap p = coordinateFibreMap f i hi u p

theorem specialRelativeBoundary_forget {f : Map A B} {i : Fin n} {previous ending : Option Bool}
    (h : SpecialRelativeBoundary f i previous ending) : SpecialRelative f i := by
  obtain ⟨hi,hT⟩ := h
  exact ⟨hi,fun u => by obtain ⟨T,_,_,he⟩ := hT u; exact ⟨T,he⟩⟩

theorem mapComp_unaryRelative (f : Map A B) (g : Map B C) {i : Fin n}
    (hf : UnaryRelative f i) (hg : UnaryRelative g i) : UnaryRelative (Map.comp g f) i :=
  fun a j hj => (hg (f a) j hj).trans (hf a j hj)

theorem coordinateFibreMap_comp (f : Map A B) (g : Map B C) (i : Fin n)
    (hf : UnaryRelative f i) (hg : UnaryRelative g i) (u : Fin n → VF (M := M))
    (p : coordinateFibre A i u) :
    coordinateFibreMap (Map.comp g f) i (mapComp_unaryRelative f g hf hg) u p =
      coordinateFibreMap g i hg u (coordinateFibreMap f i hf u p) := by
  apply Subtype.ext
  apply coordinateInsert_injective i u
  rw [coordinateFibreMap_insert,coordinateFibreMap_insert]
  have hb : (⟨coordinateInsert i u (coordinateFibreMap f i hf u p).val,
      (coordinateFibreMap f i hf u p).property⟩ : B) = f ⟨coordinateInsert i u p.val,p.property⟩ :=
    Subtype.ext (coordinateFibreMap_insert f i hf u p)
  rw [hb]
  rfl

theorem specialCastTarget_alternating {R : Set M} {a b c : ℕ} {X : DefSet (M := M) R a b}
    {Y Z : DefSet (M := M) R a c} (T : SpecialBijection X Y) (h : Y = Z) (previous : Option Bool) :
    (specialCastTarget T h).chain.Alternating previous ↔ T.chain.Alternating previous := by subst Z; rfl

theorem specialCastTarget_lastKind {R : Set M} {a b c : ℕ} {X : DefSet (M := M) R a b}
    {Y Z : DefSet (M := M) R a c} (T : SpecialBijection X Y) (h : Y = Z) (previous : Option Bool) :
    (specialCastTarget T h).chain.lastKind previous = T.chain.lastKind previous := by subst Z; rfl

theorem specialRelativeBoundary_id (A : DefSet (M := M) S n m) (i : Fin n) (previous : Option Bool) :
    SpecialRelativeBoundary (Map.id A) i previous previous := by
  refine ⟨unaryRelative_id i,fun u => ⟨SpecialBijection.refl _,trivial,rfl,?_⟩⟩
  intro p
  apply Subtype.ext
  exact (coordinateProject_insert i u p.val).symm

theorem coordinateCanonical_specialRelativeBoundary (A : DefSet (M := M) S n m)
    (i : Fin n) (previous : Option Bool) (hp : previous ≠ some false) :
    SpecialRelativeBoundary (coordinateCanonicalBijection A i) i previous (some false) := by
  refine ⟨coordinateCanonical_unaryRelative A i,fun u => ⟨coordinateCanonicalFibre A i u,?_,?_,?_⟩⟩
  · unfold coordinateCanonicalFibre
    rw [specialCastTarget_alternating]
    exact ⟨hp,trivial⟩
  · unfold coordinateCanonicalFibre
    rw [specialCastTarget_lastKind]
    rfl
  · intro p
    apply Subtype.ext
    apply coordinateInsert_injective i u
    rw [coordinateFibreMap_insert]
    unfold coordinateCanonicalFibre
    rw [specialCastTarget_val]
    exact coordinateInsert_canonical i u p.val

theorem specialRelativeBoundary_comp (f : Map A B) (g : Map B C) (i : Fin n)
    {previous middle ending : Option Bool}
    (hf : SpecialRelativeBoundary f i previous middle) (hg : SpecialRelativeBoundary g i middle ending) :
    SpecialRelativeBoundary (Map.comp g f) i previous ending := by
  obtain ⟨hfi,hTf⟩ := hf
  obtain ⟨hgi,hTg⟩ := hg
  refine ⟨mapComp_unaryRelative f g hfi hgi,?_⟩
  intro u
  obtain ⟨T,hTa,hTe,hT⟩ := hTf u
  obtain ⟨U,hUa,hUe,hU⟩ := hTg u
  have hUa' : U.chain.Alternating (T.chain.lastKind previous) := by rwa [hTe]
  have hAlt := T.chain.append_alternating U.chain previous hTa hUa'
  let V : SpecialBijection (coordinateFibre A i u) (coordinateFibre C i u) :=
    ⟨T.chain.append U.chain,(T.chain.append U.chain).alternating_none previous hAlt⟩
  refine ⟨V,hAlt,?_,?_⟩
  · change (T.chain.append U.chain).lastKind previous = ending
    rw [Chain.lastKind_append,hTe]
    exact hUe
  · intro p
    have he : V.toMap p = U.toMap (T.toMap p) :=
      congrArg (fun g : Map (coordinateFibre A i u) (coordinateFibre C i u) => g p)
        (T.chain.append_toMap U.chain)
    rw [he,hT p,hU]
    exact (coordinateFibreMap_comp f g i hfi hgi u p).symm

end IntegrationInACVF.Section5
