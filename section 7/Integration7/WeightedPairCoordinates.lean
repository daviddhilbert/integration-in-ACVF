import Integration7.GammaVolumeRVValidity

/-! Exact coordinate identities for parameterized pairs of coordinate-
and-density tuples. These connect the first-order formulas to actual points. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

variable {X : Type} {p d : ℕ}

def weightedPairTuple (z : Fin p → X) (u v : Fin d → X) (φ ψ : Fin 1 → X) :
    Fin (p+((d+1)+(d+1))) → X :=
  Fin.append z (Fin.append (Fin.append u φ) (Fin.append v ψ))

theorem weightedPairTuple_coordinates (z : Fin p → X) (u v : Fin d → X) (φ ψ : Fin 1 → X) :
    weightedPairTuple z u v φ ψ ∘ weightedPairCoordinateIndices p d = Fin.append z (Fin.append u v) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [weightedPairTuple,weightedPairCoordinateIndices,Function.comp_apply,
      Fin.addCases_left,Fin.append_left]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [weightedPairTuple,weightedPairCoordinateIndices,Function.comp_apply,
        Fin.addCases_right,Fin.addCases_left,Fin.append_right,Fin.append_left]

theorem weightedPairTuple_densities (z : Fin p → X) (u v : Fin d → X) (φ ψ : Fin 1 → X) :
    weightedPairTuple z u v φ ψ ∘ weightedPairDensityIndices p d = ![φ 0,ψ 0] := by
  funext i
  fin_cases i
  · change weightedPairTuple z u v φ ψ
      (Fin.natAdd p (Fin.castAdd (d+1) (Fin.natAdd d (0 : Fin 1)))) = φ 0
    simp only [weightedPairTuple,Fin.append_right,Fin.append_left]
  · change weightedPairTuple z u v φ ψ
      (Fin.natAdd p (Fin.natAdd (d+1) (Fin.natAdd d (0 : Fin 1)))) = ψ 0
    simp only [weightedPairTuple,Fin.append_right]

theorem weightedPairTuple_source (z : Fin p → X) (u v : Fin d → X) (φ ψ : Fin 1 → X) :
    weightedPairTuple z u v φ ψ ∘ weightedPairSourceIndices p d = Fin.append z (Fin.append u φ) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [weightedPairTuple,weightedPairSourceIndices,Function.comp_apply,
      Fin.addCases_right,Fin.addCases_left,Fin.append_right,Fin.append_left]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem weightedPairTuple_sorted (sp : Fin p → SortTag) (z : Fin p → M)
    (u v : Fin d → M) (φ ψ : Fin 1 → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hu : ∀ i, iRV (u i)) (hv : ∀ i, iRV (v i))
    (hφ : ∀ i, iRV (φ i)) (hψ : ∀ i, iRV (ψ i)) :
    weightedPairTuple z u v φ ψ ∈ sortedUniverse (Fin.append sp (fun _ : Fin ((d+1)+(d+1)) => .rv)) := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [weightedPairTuple,Fin.append_left] using hz i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [weightedPairTuple,Fin.append_right,Fin.append_left,sortEval,iRV] using hu i
      · simpa only [weightedPairTuple,Fin.append_right,Fin.append_left,sortEval,iRV] using hφ i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [weightedPairTuple,Fin.append_right,Fin.append_left,sortEval,iRV] using hv i
      · simpa only [weightedPairTuple,Fin.append_right,sortEval,iRV] using hψ i

end IntegrationInACVF.Section7
