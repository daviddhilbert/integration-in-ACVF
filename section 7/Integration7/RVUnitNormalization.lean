import Integration7.ScalarRVAlgebra
import Section3.GammaCodeDefinability

/-! A definable total unit-valued replacement of an RV scalar. It keeps
the scalar when its absolute value is one and uses one otherwise. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rvAbsoluteOne_iff_order (t : CanonicalRV.RVSort M) :
    RVOperations.absoluteHom t = 1 ↔ iLe t.val iRVOne ∧ iLe iRVOne t.val := by
  have hl := Values.valueEquiv_rv_le Values.presentationValuation Values.presentation_compatible
    t (1 : CanonicalRV.RVSort M)
  have hr := Values.valueEquiv_rv_le Values.presentationValuation Values.presentation_compatible
    (1 : CanonicalRV.RVSort M) t
  change iLe t.val (1 : CanonicalRV.RVSort M).val ↔ RVOperations.absoluteHom 1 ≤ RVOperations.absoluteHom t at hl
  change iLe (1 : CanonicalRV.RVSort M).val t.val ↔ RVOperations.absoluteHom t ≤ RVOperations.absoluteHom 1 at hr
  rw [RVOperations.one_val, map_one] at hl hr
  exact ⟨fun h => ⟨hl.mpr h.ge, hr.mpr h.le⟩, fun h => (hr.mp h.2).antisymm (hl.mp h.1)⟩

def rvUnitNormalize (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 1) S)
      (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let p (z : Fin 1 → M) := iLe (z 0) iRVOne ∧ iLe iRVOne (z 0)
  have hc : S.DefinableFun LRV (fun _ : Fin 1 → M => iRVOne) :=
    SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol (L := LRV)
        Fn.rvOne Fin.elim0 (fun i => i.elim0))
  have hp : S.Definable LRV {z | p z} := by
    have hl := (GammaParameters.raw_le_definable S).preimage_map
      (show S.DefinableMap LRV (fun z : Fin 1 → M => ![z 0, iRVOne]) from
        fun i => by fin_cases i; exact Set.DefinableFun.proj LRV; exact hc)
    have hr := (GammaParameters.raw_le_definable S).preimage_map
      (show S.DefinableMap LRV (fun z : Fin 1 → M => ![iRVOne, z 0]) from
        fun i => by fin_cases i; exact hc; exact Set.DefinableFun.proj LRV)
    exact hl.inter hr
  let F (z : Fin 1 → M) : Fin 1 → M := fun i => if p z then z i else iRVOne
  have hF : S.DefinableMap LRV F := fun _ =>
    Set.DefinableFun.ite hp (Set.DefinableFun.proj LRV) hc
  let f (t : Fin 1 → CanonicalRV.RVSort M) := if p (rvValues t) then t else fun _ => 1
  have hcode (c : (rawRVSpace (M := M) 1).domain) :
      rvValues (f ((rawRVSpace 1).decode c)) = F c.val := by
    funext i
    by_cases h : p c.val
    · simp only [f, rvValues_decode, h, ite_true, F]
    · simp only [f, rvValues_decode, h, ite_false, F]
      exact RVOperations.one_val
  refine Map.ofCodes _ f F hF (fun c => ⟨f ((rawRVSpace 1).decode c), hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

theorem rvUnitNormalize_value (S : Set M)
    (t : DefSet.univ (rawRVSpace (M := M) 1) S) :
    (rvUnitNormalize S t).val 0 = if RVOperations.absoluteHom (t.val 0) = 1 then t.val 0 else 1 := by
  change (if iLe (t.val 0).val iRVOne ∧ iLe iRVOne (t.val 0).val then t.val else fun _ => 1) 0 = _
  by_cases h : RVOperations.absoluteHom (t.val 0) = 1
  · simp only [(rvAbsoluteOne_iff_order _).mp h, h, and_self, ite_true]
  · have hn := mt (rvAbsoluteOne_iff_order _).mpr h
    simp only [hn, h, ite_false]

theorem rvUnitNormalize_absolute (S : Set M)
    (t : DefSet.univ (rawRVSpace (M := M) 1) S) :
    RVOperations.absoluteHom ((rvUnitNormalize S t).val 0) = 1 := by
  rw [rvUnitNormalize_value]
  split
  · assumption
  · exact map_one _

theorem rvUnitNormalize_of_absolute_one (S : Set M)
    (t : DefSet.univ (rawRVSpace (M := M) 1) S) (h : RVOperations.absoluteHom (t.val 0) = 1) :
    (rvUnitNormalize S t).val 0 = t.val 0 := by
  rw [rvUnitNormalize_value, if_pos h]

end IntegrationInACVF.Section7
