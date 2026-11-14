import IntegrationSection6.GammaParameterRecoding
import IntegrationSection6.GammaRecodingValidity

/-! Prepending ignored parameters to finite RV formulas preserves their
exact rows. This lets an old parameter tuple be kept in an existential
exception certificate while the geometric formulas are prepared separately. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5

namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def ignoreParameterPrefix (q p a : ℕ) : Fin (p+a) → Fin ((q+p)+a) :=
  Fin.addCases (fun i => Fin.castAdd a (Fin.natAdd q i)) (Fin.natAdd (q+p))

def ignoreParameterPrefixRelation (q p a b : ℕ) : Fin ((p+a)+b) → Fin (((q+p)+a)+b) :=
  Fin.addCases (fun i => Fin.castAdd b (ignoreParameterPrefix q p a i)) (Fin.natAdd ((q+p)+a))

theorem append_ignoreParameterPrefix {X : Type}
    (t : Fin q → X) (z : Fin p → X) (x : Fin a → X) :
    Fin.append (Fin.append t z) x ∘ ignoreParameterPrefix q p a = Fin.append z x := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [Function.comp_apply,ignoreParameterPrefix,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

theorem append_ignoreParameterPrefixRelation {X : Type}
    (t : Fin q → X) (z : Fin p → X) (x : Fin a → X) (y : Fin b → X) :
    Fin.append (Fin.append (Fin.append t z) x) y ∘ ignoreParameterPrefixRelation q p a b =
      Fin.append (Fin.append z x) y := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Function.comp_apply,ignoreParameterPrefixRelation,Fin.addCases_left,Fin.append_left]
    exact congrFun (append_ignoreParameterPrefix t z x) i
  · simp only [Function.comp_apply,ignoreParameterPrefixRelation,Fin.addCases_right,Fin.append_right]

def GammaParameterRecode.ignorePrefix (B : Base (M := M)) (sp : Fin p → SortTag) (sq : Fin q → SortTag) :
    GammaParameterRecode B p (q+p) sp (Fin.append sq sp) where
  domain {a} D := ⟨{w | w ∘ ignoreParameterPrefix q p a ∈ D.val ∧
      w ∈ sortedUniverse (Fin.append (Fin.append sq sp) (fun _ : Fin a => .rv))},
    D.property.preimage_real _ (ignoreParameterPrefix q p a)⟩
  relation {a b} H := ⟨{w | w ∘ ignoreParameterPrefixRelation q p a b ∈ H.val ∧
      w ∈ sortedUniverse (Fin.append (Fin.append (Fin.append sq sp) (fun _ : Fin a => .rv))
        (fun _ : Fin b => .rv))},
    H.property.preimage_real _ (ignoreParameterPrefixRelation q p a b)⟩

private theorem append_sorted {m n : ℕ} {sm : Fin m → SortTag} {sn : Fin n → SortTag}
    {x : Fin m → M} {y : Fin n → M}
    (hx : ∀ i, sortEval (sm i) (x i)) (hy : ∀ i, sortEval (sn i) (y i)) :
    ∀ i, sortEval (Fin.append sm sn i) (Fin.append x y i) := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [Fin.append_left,Fin.append_right]
  · exact hx i
  · exact hy i

theorem GammaParameterRecode.ignorePrefix_rows
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i)) :
    GammaSchemaRowAgreement F z ((GammaParameterRecode.ignorePrefix B sp sq).object F) (Fin.append t z) := by
  apply gammaSchemaRowAgreement_of_typed
  · intro x
    have hx : ∀ i, sortEval (SortTag.rv) (rvValues x i) := fun i => (x i).property
    have hNew : Fin.append (Fin.append t z) (rvValues x) ∈
        sortedUniverse (Fin.append (Fin.append sq sp) (fun _ : Fin a => .rv)) :=
      append_sorted (append_sorted ht hz) hx
    change (Fin.append z (rvValues x) ∈ F.domain) ↔
      ((Fin.append (Fin.append t z) (rvValues x) ∘ ignoreParameterPrefix q p a ∈ F.domain) ∧ _)
    rw [append_ignoreParameterPrefix]
    exact (and_iff_left hNew).symm
  · intro x y
    have hx : ∀ i, sortEval (SortTag.rv) (rvValues x i) := fun i => (x i).property
    have hy : ∀ i, sortEval (SortTag.rv) (rvValues y i) := fun i => (y i).property
    have hNew : Fin.append (Fin.append (Fin.append t z) (rvValues x)) (rvValues y) ∈
        sortedUniverse (Fin.append (Fin.append (Fin.append sq sp) (fun _ : Fin a => .rv))
          (fun _ : Fin k => .rv)) := append_sorted (append_sorted (append_sorted ht hz) hx) hy
    change (Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ F.volume) ↔
      ((Fin.append (Fin.append (Fin.append t z) (rvValues x)) (rvValues y) ∘
        ignoreParameterPrefixRelation q p a k ∈ F.volume) ∧ _)
    rw [append_ignoreParameterPrefixRelation]
    exact (and_iff_left hNew).symm

theorem GammaParameterRecode.ignorePrefix_valid
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (t : Fin q → M)
    (hF : F.valid z) (ht : ∀ i, sortEval (sq i) (t i)) :
    ((GammaParameterRecode.ignorePrefix B sp sq).object F).valid (Fin.append t z) :=
  F.valid_of_rowAgreement _ z (Fin.append t z) (append_sorted ht hF.1) rfl
    (GammaParameterRecode.ignorePrefix_rows F z t hF.1 ht) hF

end IntegrationInACVF.Section6
