import Integration7.WeightedPairCoordinates
import Section4.RVCoordinates

/-! On actual RV coordinate-and-density pairs, the first-order formula
substitutes precisely the source density divided by the target density. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {p d : ℕ}

theorem weightedJacobianFormula_typed_iff (sp : Fin p → SortTag)
    (J : Set (Fin ((p+(d+d))+1) → M)) (z : Fin p → M)
    (u v : Fin d → CanonicalRV.RVSort M) (a b : CanonicalRV.RVSort M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ha : a ≠ 0) (hb : b ≠ 0) :
    weightedPairTuple z (rvValues u) (rvValues v) (fun _ : Fin 1 => a.val) (fun _ : Fin 1 => b.val) ∈
        weightedJacobianFormula sp J ↔
      Fin.append (Fin.append z (Fin.append (rvValues u) (rvValues v))) (fun _ : Fin 1 => (a / b).val) ∈ J := by
  have hpair : rvValues ![a,b] = ![a.val,b.val] := by
    funext i
    fin_cases i <;> rfl
  rw [weightedJacobianFormula_mem,weightedPairTuple_coordinates,weightedPairTuple_densities]
  constructor
  · rintro ⟨j,hJ,hR,_⟩
    have hj (i : Fin 1) : iRV (j i) := by
      have h := (hR.1 (Fin.natAdd 2 i)).1
      simpa only [Fin.append_right] using h
    let q : Fin 1 → CanonicalRV.RVSort M := fun i => ⟨j i,hj i⟩
    have hRq : Fin.append (rvValues ![a,b]) (rvValues q) ∈ rvDensityRatioGraph (M := M) := by
      rw [hpair]
      exact hR
    have hq := ((rvDensityRatioGraph_append ![a,b] q).mp hRq).2
    change q 0 = a / b at hq
    have he : j = (fun _ : Fin 1 => (a / b).val) := by
      funext i
      fin_cases i
      exact congrArg Subtype.val hq
    rwa [he] at hJ
  · intro hJ
    refine ⟨(fun _ : Fin 1 => (a / b).val),hJ,?_,?_⟩
    · have h := rvDensityRatioGraph_output a b ha hb
      change Fin.append (rvValues ![a,b]) (fun _ : Fin 1 => (a / b).val) ∈
        rvDensityRatioGraph (M := M) at h
      rwa [hpair] at h
    · have hW := weightedPairTuple_sorted sp z (rvValues u) (rvValues v)
        (fun _ : Fin 1 => a.val) (fun _ : Fin 1 => b.val) hz
        (fun i => (u i).property) (fun i => (v i).property) (fun _ => a.property) (fun _ => b.property)
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hW i
      · simpa only [Fin.append_right,sortEval,iRV] using (a / b).property

end IntegrationInACVF.Section7
