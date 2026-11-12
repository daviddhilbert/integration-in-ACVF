import IntegrationSection6.GammaSchemaRowValues

/-! Pure-RV parameter blocks give full original-Gamma joint domain and
volume relations, with no parameter tuple named in the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

theorem GammaFiniteRVSchema.pureRV_domain_definable
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) :
    DefinableOverBase B (fun _ : Fin (p+a) => .rv) F.domain := by
  have hs : Fin.append (fun _ : Fin p => SortTag.rv) (fun _ : Fin a => .rv) = (fun _ => .rv) := by
    funext j
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
  exact hs ▸ F.domain_definable

theorem GammaFiniteRVSchema.pureRV_volume_definable
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) :
    DefinableOverBase B (fun _ : Fin ((p+a)+k) => .rv) F.volume := by
  have hs : Fin.append (Fin.append (fun _ : Fin p => SortTag.rv) (fun _ : Fin a => .rv))
      (fun _ : Fin k => .rv) = (fun _ => .rv) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp only [Fin.append_left,Fin.append_right]
    · simp only [Fin.append_right]
  exact hs ▸ F.volume_definable

theorem GammaFiniteRVSchema.pureRV_domain_graph
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) :
    GammaSetDefinable B {w : Point (M := M) 0 (p+a) | (fun j => (w.2 j).val) ∈ F.domain} :=
  gamma_rv_set_from_tuple_formula F.pureRV_domain_definable

theorem GammaFiniteRVSchema.pureRV_volume_graph
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+a)) (y : Point (M := M) 0 k) =>
      Fin.append (fun j => (w.2 j).val) (fun j => (y.2 j).val) ∈ F.volume) :=
  gamma_rv_graph_from_tuple_formula F.pureRV_volume_definable

end IntegrationInACVF.Section6
