import IntegrationSection6.GammaSchemaNativeRows
import IntegrationSection6.GammaParameterRecoding
import IntegrationSection6.GammaRawElementaryRowCoordinates

/-! Coordinate programs for viewing an RV[e+k] object as a family of
RV[k] objects indexed by the first e volume labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6

def volumeSliceCoordinates (a e k : ℕ) : Fin (a+(e+k)) → Fin ((e+a)+k) :=
  Fin.addCases (fun j => Fin.castAdd k (Fin.natAdd e j))
    (Fin.addCases (fun j => Fin.castAdd k (Fin.castAdd a j)) (Fin.natAdd (e+a)))

theorem volumeSliceCoordinates_append {Y : Type*} {a e k : ℕ}
    (t : Fin e → Y) (x : Fin a → Y) (y : Fin k → Y) :
    Fin.append (Fin.append t x) y ∘ volumeSliceCoordinates a e k = Fin.append x (Fin.append t y) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Function.comp_apply,volumeSliceCoordinates,Fin.addCases_left,Fin.append_left,Fin.append_right]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [Function.comp_apply,volumeSliceCoordinates,Fin.addCases_right,Fin.addCases_left,
        Fin.append_left,Fin.append_right]

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}

def gammaVolumeSliceFormula (U : GammaRVFiniteObject B (e+k)) :
    GammaRelationFormula B e (rvObjectArity U.object) k (fun _ => .rv) :=
  ⟨{z | z ∘ volumeSliceCoordinates (rvObjectArity U.object) e k ∈ gammaRawObjectVolume U.toGammaRVObject ∧
      z ∈ sortedUniverse (Fin.append (Fin.append (fun _ : Fin e => .rv)
        (fun _ : Fin (rvObjectArity U.object) => .rv)) (fun _ : Fin k => .rv))},
    (gammaRawObjectVolume_definable U.toGammaRVObject).preimage_real _
      (volumeSliceCoordinates (rvObjectArity U.object) e k)⟩

theorem gammaVolumeSliceFormula_row (U : GammaRVFiniteObject B (e+k))
    (t : Fin e → RV (M := M)) (x : Fin (rvObjectArity U.object) → RV (M := M))
    (y : Fin k → RV (M := M)) :
    Fin.append (Fin.append (fun j => (t j).val) (fun j => (x j).val)) (fun j => (y j).val) ∈
        (gammaVolumeSliceFormula U).val ↔
      ∃ u : rvObjectDomain U.object, u.val = x ∧ gammaVolumeValue U.toGammaRVObject u = Fin.append t y := by
  change (_ ∈ gammaRawObjectVolume _ ∧ _) ↔ _
  rw [volumeSliceCoordinates_append]
  have hv : Fin.append (fun j => (t j).val) (fun j => (y j).val) =
      (fun j => ((Fin.append t y) j).val) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
  rw [hv,gammaRawObjectVolume_tuple_iff]
  constructor
  · exact And.left
  · intro h
    exact ⟨h,sorted_append_RV _ _ (sorted_append_RV (fun _ : Fin e => .rv)
      (fun j => (t j).val) (fun j => (t j).property) x) y⟩

end IntegrationInACVF.Section6
