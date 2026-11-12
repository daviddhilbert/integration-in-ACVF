import IntegrationSection6.GammaFamilyBijectionValidity
import IntegrationSection6.GammaWitnessUniformity

/-! Finite definable gluing of bijection charts over a sorted parameter
base. This applies to mixed VF/RV fibres, with no finiteness of the base. -/
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

theorem bijectiveMapRowValid.congr {H K : Set (Fin ((p+a)+b) → M)} {z : Fin p → M}
    (h : bijectiveMapRowValid sp sy D E H z)
    (he : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔ Fin.append (Fin.append z x) y ∈ K) :
    bijectiveMapRowValid sp sy D E K z := by
  unfold bijectiveMapRowValid finiteMapRowValid at *
  simpa only [← he] using h

structure GammaSortedBijectionChart (B : Base (M := M)) (sp : Fin p → SortTag)
    (sx : Fin a → SortTag) (sy : Fin b → SortTag) where
  carrier : Set (Fin ((p+a)+b) → M)
  definable : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) carrier

def GammaSortedBijectionChart.valid (C : GammaSortedBijectionChart B sp sx sy)
    (D : Set (Fin (p+a) → M)) (E : Set (Fin (p+b) → M)) (z : Fin p → M) : Prop :=
  bijectiveMapRowValid sp sy D E C.carrier z

theorem GammaSortedBijectionChart.valid_definable
    (C : GammaSortedBijectionChart B sp sx sy)
    (hD : DefinableOverBase B (Fin.append sp sx) D) (hE : DefinableOverBase B (Fin.append sp sy) E) :
    DefinableOverBase B sp {z | C.valid D E z} :=
  gamma_bijection_validity_definable sp sx sy hD hE C.definable

theorem gamma_finite_bijection_glue
    (hD : DefinableOverBase B (Fin.append sp sx) D) (hE : DefinableOverBase B (Fin.append sp sy) E)
    (J : Finset (GammaSortedBijectionChart B sp sx sy)) :
    ∃ C : GammaSortedBijectionChart B sp sx sy,
      ∀ z, (∃ W ∈ J, W.valid D E z) → C.valid D E z := by
  induction J using Finset.induction_on with
  | empty =>
    exact ⟨⟨∅,DefinableOverBase.empty B _⟩,by simp⟩
  | @insert W J hnot ih =>
    obtain ⟨C,hC⟩ := ih
    let st := Fin.append (Fin.append sp sx) sy
    let idx : Fin p → Fin ((p+a)+b) := fun j => Fin.castAdd b (Fin.castAdd a j)
    let V := {w : Fin ((p+a)+b) → M | W.valid D E (w ∘ idx) ∧ w ∈ sortedUniverse st}
    have hV : DefinableOverBase B st V := (W.valid_definable hD hE).preimage_real st idx
    let H := (W.carrier ∩ V) ∪ (C.carrier ∩ (sortedUniverse st \ V))
    have hH : DefinableOverBase B st H := (W.definable.inter hV).union (C.definable.inter hV.compl)
    refine ⟨⟨H,hH⟩,?_⟩
    intro z hz
    have hidx (x : Fin a → M) (y : Fin b → M) :
        Fin.append (Fin.append z x) y ∘ idx = z := by
      funext j
      simp only [idx,Function.comp_apply,Fin.append_left]
    by_cases hw : W.valid D E z
    · apply bijectiveMapRowValid.congr hw
      intro x y
      have hwp := W.definable.proper (Fin.append (Fin.append z x) y)
      have hcp := C.definable.proper (Fin.append (Fin.append z x) y)
      change _ ↔ (_ ∧ _) ∨ (_ ∧ _ ∧ _)
      simp only [V,Set.mem_setOf_eq,hidx]
      constructor
      · intro hh
        exact Or.inl ⟨hh,hw,hwp hh⟩
      · rintro (⟨hh,_⟩ | ⟨hh,_,hn⟩)
        · exact hh
        · exact False.elim (hn ⟨hw,hcp hh⟩)
    · have hzC : ∃ W ∈ J, W.valid D E z := by
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

theorem gamma_uniform_bijection_chart {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (hD : DefinableOverBase B (Fin.append sp sx) D) (hE : DefinableOverBase B (Fin.append sp sy) E)
    (hrow : ∀ z ∈ A, ∃ C : GammaSortedBijectionChart B sp sx sy, C.valid D E z) :
    ∃ C : GammaSortedBijectionChart B sp sx sy, ∀ z ∈ A, C.valid D E z := by
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses hκ hs hreal hgamma sp A hA
    (fun C : GammaSortedBijectionChart B sp sx sy => {z | C.valid D E z})
    (fun C => C.valid_definable hD hE) hrow
  obtain ⟨C,hC⟩ := gamma_finite_bijection_glue hD hE J
  exact ⟨C,fun z hz => hC z (hJ z hz)⟩

end IntegrationInACVF.Section6
