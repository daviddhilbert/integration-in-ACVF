import Integration7.GammaRVVolumeSchemata

/-! Specialization retains the complete original-Gamma density graph,
including proper-code invariance, over precisely the named parameter row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeSchema.rowDensity_graph
    (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (hz : F.valid z) :
    GammaGraphDefinable ⟨B.real ∪ Set.range z,B.gamma⟩
      (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 1) =>
        F.rowDensity z x.2 y.2) := by
  let st : Fin (p+(a+1)) → SortTag := Fin.append sp (fun _ : Fin (a+1) => .rv)
  have hV := F.density_definable.preimage_real st (Fin.cast (Nat.add_assoc p a 1))
  have hRow := gamma_tuple_parameter_specialize sp (fun _ : Fin (a+1) => .rv) z hV
  have h := gamma_rv_graph_from_tuple_formula hRow
  apply GammaGraphDefinable.congr h
  intro x y
  change ((Fin.append z (Fin.append (rvValues x.2) (rvValues y.2)) ∘
    Fin.cast (Nat.add_assoc p a 1)) ∈ F.density ∧
      _ ∈ sortedUniverse st) ↔ F.rowDensity z x.2 y.2
  rw [← Fin.append_assoc]
  constructor
  · exact And.left
  · intro hxy
    refine ⟨hxy,fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [st,Fin.append_left] using hz.1.1 i
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [st,Fin.append_right,Fin.append_left,sortEval,iRV,rvValues]
          using (x.2 l).property
      · simpa only [st,Fin.append_right,Fin.append_right,sortEval,iRV,rvValues]
          using (y.2 l).property

end IntegrationInACVF.Section7
