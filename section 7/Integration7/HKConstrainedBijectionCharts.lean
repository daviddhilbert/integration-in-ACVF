module

public import IntegrationSection6.GammaSortedParameterPreservation

@[expose] public section

/-! Finite gluing and compactness retain a fixed definable graph constraint.
The application is exact equality of the two density values. This extends
Section 6's checked bijection-chart construction, without an extra uniform
choice or saturation premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
variable {sp : Fin p → SortTag} {sx : Fin a → SortTag} {sy : Fin b → SortTag}
variable {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)}

theorem finite_bijection_glue_within
    (hD : DefinableOverBase B (Fin.append sp sx) D) (hE : DefinableOverBase B (Fin.append sp sy) E)
    (K : Set (Fin ((p+a)+b) → M))
    (J : Finset {C : GammaSortedBijectionChart B sp sx sy // C.carrier ⊆ K}) :
    ∃ C : GammaSortedBijectionChart B sp sx sy,
      C.carrier ⊆ K ∧ ∀ z, (∃ W ∈ J, W.val.valid D E z) → C.valid D E z := by
  induction J using Finset.induction_on with
  | empty =>
    exact ⟨⟨∅,DefinableOverBase.empty B _⟩,Set.empty_subset _,by simp⟩
  | @insert W J hnot ih =>
    obtain ⟨C,hCK,hC⟩ := ih
    let st := Fin.append (Fin.append sp sx) sy
    let idx : Fin p → Fin ((p+a)+b) := fun j => Fin.castAdd b (Fin.castAdd a j)
    let V := {w : Fin ((p+a)+b) → M | W.val.valid D E (w ∘ idx) ∧ w ∈ sortedUniverse st}
    have hV : DefinableOverBase B st V := (W.val.valid_definable hD hE).preimage_real st idx
    let H := (W.val.carrier ∩ V) ∪ (C.carrier ∩ (sortedUniverse st \ V))
    have hH : DefinableOverBase B st H := (W.val.definable.inter hV).union (C.definable.inter hV.compl)
    refine ⟨⟨H,hH⟩,?_,?_⟩
    · intro q hq
      rcases hq with hq | hq
      · exact W.property hq.1
      · exact hCK hq.1
    intro z hz
    have hidx (x : Fin a → M) (y : Fin b → M) :
        Fin.append (Fin.append z x) y ∘ idx = z := by
      funext j
      simp only [idx,Function.comp_apply,Fin.append_left]
    by_cases hw : W.val.valid D E z
    · apply bijectiveMapRowValid.congr hw
      intro x y
      have hwp := W.val.definable.proper (Fin.append (Fin.append z x) y)
      have hcp := C.definable.proper (Fin.append (Fin.append z x) y)
      change _ ↔ (_ ∧ _) ∨ (_ ∧ _ ∧ _)
      simp only [V,Set.mem_setOf_eq,hidx]
      constructor
      · intro hh
        exact Or.inl ⟨hh,hw,hwp hh⟩
      · rintro (⟨hh,_⟩ | ⟨hh,_,hn⟩)
        · exact hh
        · exact False.elim (hn ⟨hw,hcp hh⟩)
    · have hzC : ∃ W ∈ J, W.val.valid D E z := by
        obtain ⟨Q,hQ,hq⟩ := hz
        rcases Finset.mem_insert.mp hQ with rfl | hqJ
        · exact False.elim (hw hq)
        · exact ⟨Q,hqJ,hq⟩
      apply bijectiveMapRowValid.congr (hC z hzC)
      intro x y
      have hcp := C.definable.proper (Fin.append (Fin.append z x) y)
      change _ ↔ (_ ∧ _) ∨ (_ ∧ _ ∧ _)
      simp only [V,Set.mem_setOf_eq,hidx,hw,false_and,and_false,or_false,false_or,not_false_eq_true,and_true]
      exact ⟨fun hh => ⟨hh,hcp hh⟩,And.left⟩

theorem uniform_bijection_chart_within {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (hD : DefinableOverBase B (Fin.append sp sx) D) (hE : DefinableOverBase B (Fin.append sp sy) E)
    (K : Set (Fin ((p+a)+b) → M))
    (hrow : ∀ z ∈ A, ∃ C : GammaSortedBijectionChart B sp sx sy,
      C.carrier ⊆ K ∧ C.valid D E z) :
    ∃ C : GammaSortedBijectionChart B sp sx sy, C.carrier ⊆ K ∧ ∀ z ∈ A, C.valid D E z := by
  let I := {C : GammaSortedBijectionChart B sp sx sy // C.carrier ⊆ K}
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses hκ hs hreal hgamma sp A hA
    (fun C : I => {z | C.val.valid D E z})
    (fun C => C.val.valid_definable hD hE) (by
      intro z hz
      obtain ⟨C,hCK,hC⟩ := hrow z hz
      exact ⟨⟨C,hCK⟩,hC⟩)
  obtain ⟨C,hCK,hC⟩ := finite_bijection_glue_within hD hE K J
  exact ⟨C,hCK,fun z hz => hC z (hJ z hz)⟩

theorem promote_row_bijection_within
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (K : Set (Fin ((p+a)+b) → M))
    (hK : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) K)
    (e : GammaSortedIso ⟨B.real ∪ Set.range z,B.gamma⟩ sx sy
      {x : Fin a → M | Fin.append z x ∈ D} {y : Fin b → M | Fin.append z y ∈ E})
    (he : ∀ u, Fin.append (Fin.append z u.val) (e.equiv u).val ∈ K) :
    ∃ C : GammaSortedBijectionChart B sp sx sy, C.carrier ⊆ K ∧ C.valid D E z := by
  obtain ⟨H,hH,hrow⟩ := gamma_sorted_tuple_relation_promotion B sp sx sy z hz
    {w | ∃ u, Fin.append u.val (e.equiv u).val = w} e.graph
  refine ⟨⟨H ∩ K,hH.inter hK⟩,Set.inter_subset_right,?_⟩
  apply bijectiveMapRowValid_of_equiv z hz e.equiv
  intro x y
  constructor
  · intro h
    exact (e.graph_iff x y).mp ((hrow x y).mp h.1)
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨(hrow u.val (e.equiv u).val).mpr ⟨u,rfl⟩,he u⟩

end IntegrationInACVF.Section7.HK
