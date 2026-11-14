import Integration7.GammaVolumeIndexedPresentations
import Integration7.GammaVolumeExistentialCertificates

/-! The joint chart of a volume certificate preserves the actual RV
index tuple and retains its full original-base Gamma graph. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}

theorem rvValues_indexed_split (w : Fin (p+a) → RV (M := M)) :
    Fin.append (rvValues (indexedLeft w)) (rvValues (indexedRight w)) = rvValues w := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [indexedLeft,indexedRight,rvValues,Function.comp_apply,Fin.append_left,Fin.append_right]

def indexedVolumeChartRelation
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (x : Fin (p+a) → RV (M := M)) (y : Fin (p+b) → RV (M := M)) : Prop :=
  indexedLeft x = indexedLeft y ∧ Fin.append (rvValues x) (rvValues (indexedRight y)) ∈ H.chart

theorem indexedVolumeChartRelation_chart
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    {x : Fin (p+a) → RV (M := M)} {y : Fin (p+b) → RV (M := M)}
    (h : indexedVolumeChartRelation H x y) :
    Fin.append (Fin.append (rvValues (indexedLeft x)) (rvValues (indexedRight x)))
      (rvValues (indexedRight y)) ∈ H.chart := by
  rw [rvValues_indexed_split]
  exact h.2

theorem indexedVolumeChartRelation_gammaGraph
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv)) :
    GammaGraphDefinable B (fun (x : Point (M := M) 0 (p+a)) (y : Point (M := M) 0 (p+b)) =>
      indexedVolumeChartRelation H x.2 y.2) := by
  have hs : Fin.append (Fin.append (fun _ : Fin p => SortTag.rv) (fun _ : Fin a => .rv))
      (fun _ : Fin b => .rv) = fun _ => .rv := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp only [Fin.append_left,Fin.append_right]
    · simp only [Fin.append_right]
  have hRaw := gamma_rv_graph_from_tuple_formula (hs ▸ H.chart_definable)
  let par := rvCoordinatePointMap (Fin.castAdd a : Fin p → Fin (p+a)) B.real
  let par' := rvCoordinatePointMap (Fin.castAdd b : Fin p → Fin (p+b)) B.real
  let labels := rvCoordinatePointMap (Fin.natAdd p : Fin b → Fin (p+b)) B.real
  let ident := @Map.id M sM _ B.real (PresentedSet.univ (pointSpace (M := M) 0 (p+a)) B.real)
  have h := ((gamma_global_map_graph par).preimage_maps ident par').inter (hRaw.preimage_maps ident labels)
  apply GammaGraphDefinable.congr h
  intro x y
  change (((Fin.elim0,indexedLeft x.2) = (Fin.elim0,indexedLeft y.2)) ∧ _) ↔ _
  exact and_congr ⟨fun he => congrArg Prod.snd he,fun he => Prod.ext (Subsingleton.elim _ _) he⟩ Iff.rfl

end IntegrationInACVF.Section7
