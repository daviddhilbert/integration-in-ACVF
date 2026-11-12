import IntegrationSection6.GammaSortedRelationPromotion
import IntegrationSection6.GammaSortedBijectionGluing

/-! An actual definable bijection over a named parameter tuple promotes
to a valid original-base chart near that tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
variable {sp : Fin p → SortTag} {sx : Fin a → SortTag} {sy : Fin b → SortTag}
variable {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)}

theorem bijectiveMapRowValid_of_equiv (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (e : {x : Fin a → M | Fin.append z x ∈ D} ≃ {y : Fin b → M | Fin.append z y ∈ E})
    {H : Set (Fin ((p+a)+b) → M)}
    (he : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : {x : Fin a → M | Fin.append z x ∈ D}, u.val = x ∧ (e u).val = y) :
    bijectiveMapRowValid sp sy D E H z := by
  refine ⟨⟨hz,?_,?_,?_⟩,?_⟩
  · intro x hx
    refine ⟨(e ⟨x,hx⟩).val,(he x _).mpr ⟨⟨x,hx⟩,rfl,rfl⟩,?_⟩
    intro y hy
    obtain ⟨u,hu,hy⟩ := (he x y).mp hy
    have hu' : u = ⟨x,hx⟩ := Subtype.ext hu
    exact hy.symm.trans (congrArg (fun v => (e v).val) hu')
  · intro x y hxy
    obtain ⟨u,hu,_⟩ := (he x y).mp hxy
    exact hu ▸ u.property
  · intro y hy
    have hf : {x : Fin a → M | Fin.append (Fin.append z x) y ∈ H}.Subsingleton := by
      intro x hx x' hx'
      obtain ⟨u,hu,hyu⟩ := (he x y).mp hx
      obtain ⟨v,hv,hyv⟩ := (he x' y).mp hx'
      have huv := e.injective (Subtype.ext (hyu.trans hyv.symm))
      exact hu.symm.trans ((congrArg Subtype.val huv).trans hv)
    exact ⟨hf.finite,(Set.ncard_le_one hf.finite).mpr hf⟩
  · intro y
    constructor
    · intro hy
      let u := e.symm ⟨y,hy⟩
      exact ⟨u.val,(he _ _).mpr ⟨u,rfl,congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)⟩⟩
    · rintro ⟨x,hxy⟩
      obtain ⟨u,_,hu⟩ := (he x y).mp hxy
      exact hu ▸ (e u).property

theorem gamma_promote_row_bijection (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (e : {x : Fin a → M | Fin.append z x ∈ D} ≃ {y : Fin b → M | Fin.append z y ∈ E})
    (W : Set (Fin (a+b) → M))
    (hW : DefinableOverBase ⟨B.real ∪ Set.range z,B.gamma⟩ (Fin.append sx sy) W)
    (he : ∀ x y, Fin.append x y ∈ W ↔
      ∃ u : {x : Fin a → M | Fin.append z x ∈ D}, u.val = x ∧ (e u).val = y) :
    ∃ C : GammaSortedBijectionChart B sp sx sy, C.valid D E z := by
  obtain ⟨H,hH,hrow⟩ := gamma_sorted_tuple_relation_promotion B sp sx sy z hz W hW
  exact ⟨⟨H,hH⟩,bijectiveMapRowValid_of_equiv z hz e (fun x y => (hrow x y).trans (he x y))⟩

end IntegrationInACVF.Section6
