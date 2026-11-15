import IntegrationSection6.VFPrefixStandardPresentations
import IntegrationSection6.PartialContractionFiniteVolume

/-! Freezing a partial program preserves its entire ordered VF-tag tuple
and every old density label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n p a l : ℕ}
variable {U : DefSet (M := M) S (n+p) a} {V : DefSet (M := M) S n l}

theorem restrict_partial_prefix_volume_index
    (T : PartialContractionProgram S n (n := p) U V) (x : Fin n → VF (M := M)) :
    (restrictPartialToPrefix T x).volumeIndex = T.volumeIndex := by
  induction T with
  | zero U => rfl
  | step T tail ih =>
    funext i
    cases i using Fin.cases with
    | zero => apply Fin.ext; rfl
    | succ i =>
      change (orderedCastSource (restrictPartialToPrefix tail x) _).volumeIndex i = tail.volumeIndex i
      rw [orderedCastSource_volumeIndex,ih]

theorem partial_retained_density_nonzero
    (T : PartialContractionProgram S n (n := p) U V) (δ : Fin a)
    (hδ : ∀ q : U, (q.val.2 δ).val ≠ iRVZero) :
    ∀ q : V, (q.val.2 (suffixIndex T.rvArity_le δ)).val ≠ iRVZero := by
  intro q
  obtain ⟨u,rfl⟩ := T.surjective q
  rw [T.oldLabels]
  exact hδ u

end IntegrationInACVF.Section7
