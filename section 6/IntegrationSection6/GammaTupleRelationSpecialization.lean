import IntegrationSection6.GammaRawRVFormulas

/-! Specialize a full tuple relation at its named parameter tuple, keeping
its original-Gamma pure-RV graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

theorem gamma_rv_tuple_relation_specialize (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H) :
    GammaGraphDefinable ⟨B.real ∪ Set.range z,B.gamma⟩
      (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 b) =>
        Fin.append (Fin.append z (fun j => (x.2 j).val)) (fun j => (y.2 j).val) ∈ H) := by
  let st := Fin.append sp (fun _ : Fin (a+b) => SortTag.rv)
  have h := hH.preimage_real st (Fin.cast (Nat.add_assoc p a b))
  have hRow := gamma_tuple_parameter_specialize sp (fun _ : Fin (a+b) => .rv) z h
  have hΓ := gamma_rv_graph_from_tuple_formula hRow
  apply GammaGraphDefinable.congr hΓ
  intro x y
  change ((Fin.append z (Fin.append (fun j => (x.2 j).val) (fun j => (y.2 j).val)) ∘
    Fin.cast (Nat.add_assoc p a b)) ∈ H ∧ _ ∈ sortedUniverse st) ↔ _
  rw [← Fin.append_assoc]
  constructor
  · exact And.left
  · intro hxy
    refine ⟨hxy,fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [st,Fin.append_left] using hz i
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [st,Fin.append_right,Fin.append_left,sortEval,iRV] using (x.2 l).property
      · simpa only [st,Fin.append_right,Fin.append_right,sortEval,iRV] using (y.2 l).property

end IntegrationInACVF.Section6
