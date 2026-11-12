import IntegrationSection6.PartialSelectedVolume
import IntegrationSection6.EmptySelectedContractions

/-! The ordinary active-coordinate volume of a partial contraction has
finite fibres. The recursive selected tuple uses only those same labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p n a l : ℕ}
variable {U : DefSet (M := M) S (p+n) a} {V : DefSet (M := M) S p l}

theorem partial_suffixIndex_step {n a l : ℕ} {U : DefSet (M := M) S (p+(n+1)) a}
    {V : DefSet (M := M) S p l} (T : HeadPreparation U)
    (tail : PartialContractionProgram S p (n := n) T.contractedSet V) (j : Fin a) :
    suffixIndex tail.rvArity_le (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) j)) =
      suffixIndex (PartialContractionProgram.step T tail).rvArity_le j := by
  apply Fin.ext
  have hT := specialRelative_rvArity_le T.special
  have htail := tail.rvArity_le
  change l-(1+T.arity)+(1+(T.arity-a+j.val)) = l-a+j.val
  omega

theorem partialSelectedIndex_cases (T : PartialContractionProgram S p (n := n) U V)
    {k : ℕ} (ρ : Fin k → Fin a) (j : Fin (orderedVolumeDegree n k)) :
    (∃ i : Fin n, partialSelectedIndex T ρ j = T.volumeIndex i) ∨
      ∃ i : Fin k, partialSelectedIndex T ρ j = suffixIndex T.rvArity_le (ρ i) := by
  induction T generalizing k with
  | zero U =>
    right
    exact ⟨j,Fin.ext (by simp [partialSelectedIndex,suffixIndex])⟩
  | @step n a l U V T tail ih =>
    rcases ih (headVolumeIndex T ρ) j with ⟨i,hi⟩ | ⟨i,hi⟩
    · exact Or.inl ⟨i.succ,hi⟩
    · cases i using Fin.addCases with
      | left i =>
        have hi0 : i = 0 := Subsingleton.elim _ _
        subst i
        exact Or.inl ⟨0,hi⟩
      | right i =>
        right
        refine ⟨i,?_⟩
        simp only [headVolumeIndex,Fin.append_right,headSelectedLabelIndex] at hi
        exact hi.trans (partial_suffixIndex_step (p := p) (n := n) T tail (ρ i))

theorem partialEmptySelectedFactor_exists (T : PartialContractionProgram S p (n := n) U V)
    (j : Fin (orderedVolumeDegree n 0)) :
    ∃ i : Fin n, partialSelectedIndex T (Fin.elim0 : Fin 0 → Fin a) j = T.volumeIndex i := by
  rcases partialSelectedIndex_cases T (Fin.elim0 : Fin 0 → Fin a) j with h | ⟨i,_⟩
  · exact h
  · exact i.elim0

def partialEmptySelectedFactor (T : PartialContractionProgram S p (n := n) U V) :
    Fin (orderedVolumeDegree n 0) → Fin n := fun j => Classical.choose (partialEmptySelectedFactor_exists T j)

theorem partialEmptySelectedFactor_spec (T : PartialContractionProgram S p (n := n) U V)
    (j : Fin (orderedVolumeDegree n 0)) :
    partialSelectedIndex T (Fin.elim0 : Fin 0 → Fin a) j = T.volumeIndex (partialEmptySelectedFactor T j) :=
  Classical.choose_spec (partialEmptySelectedFactor_exists T j)

theorem partial_volume_fibres_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (T : PartialContractionProgram S p (n := n) U V) (hT : GammaPartialProgramDefinable B T)
    (hfin : ∀ x : Fin (p+n) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite) :
    ∀ (x : Fin p → VF (M := M)) (t : Fin n → RV (M := M)),
      {r : Fin l → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ T.volumeIndex = t}.Finite := by
  intro x t
  have h := partial_selected_fibres_finite hκ hs hr T hT (Fin.elim0 : Fin 0 → Fin a)
    (FiniteRV.empty_selected_fibres U hfin) x (t ∘ partialEmptySelectedFactor T)
  apply h.subset
  intro r hr
  refine ⟨hr.1,?_⟩
  funext j
  change r (partialSelectedIndex T (Fin.elim0 : Fin 0 → Fin a) j) = t (partialEmptySelectedFactor T j)
  rw [partialEmptySelectedFactor_spec]
  exact congrFun hr.2 _

end IntegrationInACVF.Section6
