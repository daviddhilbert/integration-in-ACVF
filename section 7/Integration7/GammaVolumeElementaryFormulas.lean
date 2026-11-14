import Integration7.GammaVolumeSchemaBounds
import IntegrationSection6.GammaRawElementarySchemata

/-! Elementary blowup volume formulas use the native last-coordinate
blowup and pull the density back from its original label. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

def elementaryDensityIndices (p a : ℕ) : Fin ((p+a)+1) → Fin ((p+(a+1))+1) :=
  Fin.addCases (fun i => Fin.castAdd 1 (rawElementaryHead p a i)) (Fin.natAdd (p+(a+1)))

theorem elementaryDensityIndices_append {X : Type} {p a : ℕ}
    (z : Fin p → X) (w : Fin (a+1) → X) (ω : Fin 1 → X) :
    Fin.append (Fin.append z w) ω ∘ elementaryDensityIndices p a =
      Fin.append (Fin.append z (w ∘ Fin.castAdd 1)) ω := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [Function.comp_apply,elementaryDensityIndices,rawElementaryHead,
        Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]
  · simp only [Function.comp_apply,elementaryDensityIndices,Fin.addCases_right,Fin.append_right]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaRVVolumeSchema.elementaryDensity (F : GammaRVVolumeSchema B p a k sp) :
    Set (Fin ((p+(a+1))+1) → M) :=
  nonzeroDensityFormula {w |
    (w ∘ elementaryDensityIndices p a ∈ F.density ∧
      w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin (a+1) => .rv)) (fun _ : Fin 1 => .rv))) ∧
    (w ∘ Fin.castAdd 1 ∈ F.object.elementaryDomain ∧
      w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin (a+1) => .rv)) (fun _ : Fin 1 => .rv)))}

theorem GammaRVVolumeSchema.elementaryDensity_definable (F : GammaRVVolumeSchema B p a k sp) :
    DefinableOverBase B
      (Fin.append (Fin.append sp (fun _ : Fin (a+1) => .rv)) (fun _ : Fin 1 => .rv)) F.elementaryDensity :=
  nonzeroDensityFormula_definable ((F.density_definable.preimage_real _ (elementaryDensityIndices p a)).inter
    (F.object.elementaryDomain_definable.preimage_real _ (Fin.castAdd 1)))

def GammaRVVolumeSchema.elementaryFormula (F : GammaRVVolumeSchema B p a k sp) :
    GammaRVVolumeSchema B p (a+1) k sp where
  object := F.object.elementaryFormula (Fin.last k)
  density := F.elementaryDensity
  density_definable := F.elementaryDensity_definable
  density_nonzero _ hw := hw.2

theorem GammaRVVolumeSchema.elementary_rowDensity (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (w : Fin (a+1) → CanonicalRV.RVSort M) (ω : Fin 1 → CanonicalRV.RVSort M) :
    F.elementaryFormula.rowDensity z w ω ↔
      F.rowDensity z (w ∘ Fin.castAdd 1) ω ∧ w ∈ F.elementaryFormula.object.rowDomain z := by
  have hs := sorted_append_RV _ _ (sorted_append_RV sp z hz w) ω
  change Fin.append (Fin.append z (rvValues w)) (rvValues ω) ∈
    nonzeroDensityFormula _ ↔ _
  rw [nonzeroDensityFormula_append]
  change (((_ ∧ _) ∧ (_ ∧ _)) ∧ _) ↔ _
  rw [elementaryDensityIndices_append]
  have hp : Fin.append (Fin.append z (rvValues w)) (rvValues ω) ∘ Fin.castAdd 1 = Fin.append z (rvValues w) :=
    funext (Fin.append_left _ _)
  rw [hp]
  constructor
  · exact fun h => ⟨h.1.1.1,h.1.2.1⟩
  · rintro ⟨hρ,hw⟩
    exact ⟨⟨⟨hρ,hs⟩,hw,hs⟩,F.rowDensity_nonzero z _ ω hρ⟩

end IntegrationInACVF.Section7
