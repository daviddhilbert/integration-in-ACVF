import Integration7.RVDensityRatioGraph
import Integration7.GammaVolumeChartGraphs
import Integration7.GammaVolumeSchemaRestrictions

/-! Pull back a supported coordinate-Jacobian graph to weighted label
pairs, substituting the actual density ratio by its first-order graph. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p d : ℕ}

def weightedPairCoordinateIndices (p d : ℕ) : Fin (p+(d+d)) → Fin (p+((d+1)+(d+1))) :=
  Fin.addCases (Fin.castAdd ((d+1)+(d+1)))
    (Fin.addCases (fun i => Fin.natAdd p (Fin.castAdd (d+1) (Fin.castAdd 1 i)))
      (fun i => Fin.natAdd p (Fin.natAdd (d+1) (Fin.castAdd 1 i))))

def weightedPairDensityIndices (p d : ℕ) : Fin 2 → Fin (p+((d+1)+(d+1))) :=
  ![Fin.natAdd p (Fin.castAdd (d+1) (Fin.natAdd d (0 : Fin 1))),
    Fin.natAdd p (Fin.natAdd (d+1) (Fin.natAdd d (0 : Fin 1)))]

def weightedPairJacobianIndices (p d : ℕ) :
    Fin ((p+(d+d))+1) → Fin ((p+((d+1)+(d+1)))+1) :=
  Fin.addCases (fun i => Fin.castAdd 1 (weightedPairCoordinateIndices p d i))
    (Fin.natAdd (p+((d+1)+(d+1))))

def weightedPairRatioIndices (p d : ℕ) : Fin (2+1) → Fin ((p+((d+1)+(d+1)))+1) :=
  Fin.addCases (fun i => Fin.castAdd 1 (weightedPairDensityIndices p d i))
    (Fin.natAdd (p+((d+1)+(d+1))))

def weightedJacobianFormula (sp : Fin p → SortTag) (J : Set (Fin ((p+(d+d))+1) → M)) :
    Set (Fin (p+((d+1)+(d+1))) → M) :=
  {w | ∃ j : Fin 1 → M,
    (Fin.append w j ∘ weightedPairJacobianIndices p d ∈ J ∧
      Fin.append w j ∈ sortedUniverse
        (Fin.append (Fin.append sp (fun _ : Fin ((d+1)+(d+1)) => .rv)) (fun _ : Fin 1 => .rv))) ∧
    (Fin.append w j ∘ weightedPairRatioIndices p d ∈ rvDensityRatioGraph (M := M) ∧
      Fin.append w j ∈ sortedUniverse
        (Fin.append (Fin.append sp (fun _ : Fin ((d+1)+(d+1)) => .rv)) (fun _ : Fin 1 => .rv)))}

theorem weightedJacobianFormula_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (sp : Fin p → SortTag)
    {J : Set (Fin ((p+(d+d))+1) → M)}
    (hJ : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin (d+d) => .rv)) (fun _ : Fin 1 => .rv)) J) :
    DefinableOverBase B (Fin.append sp (fun _ : Fin ((d+1)+(d+1)) => .rv)) (weightedJacobianFormula sp J) := by
  let st := Fin.append (Fin.append sp (fun _ : Fin ((d+1)+(d+1)) => SortTag.rv)) (fun _ : Fin 1 => .rv)
  exact gamma_family_row_exists_definable _ _
    ((hJ.preimage_real st (weightedPairJacobianIndices p d)).inter
      ((rvDensityRatioGraph_definable hc B).preimage_real st (weightedPairRatioIndices p d)))

theorem weightedJacobianFormula_mem (sp : Fin p → SortTag)
    (J : Set (Fin ((p+(d+d))+1) → M)) (w : Fin (p+((d+1)+(d+1))) → M) :
    w ∈ weightedJacobianFormula sp J ↔ ∃ j : Fin 1 → M,
      Fin.append (w ∘ weightedPairCoordinateIndices p d) j ∈ J ∧
      Fin.append (w ∘ weightedPairDensityIndices p d) j ∈ rvDensityRatioGraph (M := M) ∧
      Fin.append w j ∈ sortedUniverse
        (Fin.append (Fin.append sp (fun _ : Fin ((d+1)+(d+1)) => .rv)) (fun _ : Fin 1 => .rv)) := by
  change (∃ j, _ ∧ _) ↔ _
  apply exists_congr
  intro j
  have hJ : Fin.append w j ∘ weightedPairJacobianIndices p d =
      Fin.append (w ∘ weightedPairCoordinateIndices p d) j := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [weightedPairJacobianIndices,Function.comp_apply,Fin.addCases_left,
        Fin.addCases_right,Fin.append_left,Fin.append_right]
  have hR : Fin.append w j ∘ weightedPairRatioIndices p d =
      Fin.append (w ∘ weightedPairDensityIndices p d) j := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [weightedPairRatioIndices,Function.comp_apply,Fin.addCases_left,
        Fin.addCases_right,Fin.append_left,Fin.append_right]
  rw [hJ,hR]
  tauto

end IntegrationInACVF.Section7
