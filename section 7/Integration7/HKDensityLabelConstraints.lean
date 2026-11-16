import Integration7.HKConstrainedBijectionCharts
import IntegrationSection6.GammaPreparedFormulaDescent

/-! Exact retained-density equality is a sorted original-base constraint.
Prepared RV recoding keeps it on every represented chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

def densityLabelConstraint (sp : Fin p → SortTag) (δ : Fin a) (ε : Fin b) :
    Set (Fin ((p+a)+b) → M) :=
  {w | w (Fin.castAdd b (Fin.natAdd p δ)) = w (Fin.natAdd (p+a) ε) ∧
    w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv))}

theorem density_label_constraint_definable (δ : Fin a) (ε : Fin b) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv))
      (densityLabelConstraint sp δ ε) := by
  let st := Fin.append (Fin.append sp (fun _ : Fin a => SortTag.rv)) (fun _ : Fin b => .rv)
  apply real_definableOverBase B st
  apply (definableOver_iff_normalized_raw B.real st _).mpr
  have hSort := ((definableOver_iff_normalized_raw B.real st _).mp (sortedUniverse_definable B.real st)).1
  let S : Set M := B.real
  let N := @CanonicalStructure.normalize M sM
  have hEq := @RawClosure.definable_equal_coordinates M N S (Fin ((p+a)+b))
    (Fin.castAdd b (Fin.natAdd p δ)) (Fin.natAdd (p+a) ε)
  letI := N
  exact ⟨hEq.inter hSort,fun _ h => h.2⟩

theorem density_label_constraint_append (δ : Fin a) (ε : Fin b)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (r : Fin a → CanonicalRV.RVSort M) (s : Fin b → CanonicalRV.RVSort M) :
    Fin.append (Fin.append z (rvValues r)) (rvValues s) ∈ densityLabelConstraint sp δ ε ↔ r δ = s ε := by
  change (_ = _ ∧ _) ↔ _
  simp only [Fin.append_left,Fin.append_right]
  exact ⟨fun h => Subtype.ext h.1,fun h =>
    ⟨congrArg Subtype.val h,sorted_append_RV _ _ (sorted_append_RV sp z hz r) s⟩⟩

end IntegrationInACVF.Section7.HK
