import IntegrationSection6.FiniteRVGeometry

/-! Isomorphism changes for chains entirely inside RV[k]. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {k r : ℕ} {U V W : RVFiniteObject (M := M) S k}

theorem IteratedBlowup.sourceIso (h : IteratedBlowup r U V) (e : W ≅ U) : IteratedBlowup r W V := by
  cases h with
  | zero h => exact .zero (h.map e.trans)
  | cons h ht => exact .cons (h.sourceIso ((finiteVolumeProperty S k).ι.mapIso e)) ht

theorem IteratedBlowup.targetIso (h : IteratedBlowup r U V) (e : V ≅ W) : IteratedBlowup r U W := by
  induction h with
  | zero h => exact .zero (h.map (fun f => f.trans e))
  | cons h _ ih => exact .cons h (ih e)

end IntegrationInACVF.Section6.FiniteRV
