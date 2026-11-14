import Integration7.GammaRVVolumeSchemata

/-! The combined coordinate-and-density graph over the original base.
Its output is the old coordinate tuple followed by the density label. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def weightedVolumeCoordinateIndices (p a d : ℕ) : Fin ((p+a)+d) → Fin ((p+a)+(d+1)) :=
  Fin.addCases (Fin.castAdd (d+1)) (fun j => Fin.natAdd (p+a) (Fin.castAdd 1 j))

def weightedVolumeDensityIndices (p a d : ℕ) : Fin ((p+a)+1) → Fin ((p+a)+(d+1)) :=
  Fin.addCases (Fin.castAdd (d+1)) (fun j => Fin.natAdd (p+a) (Fin.natAdd d j))

def weightedVolumeGraph (F : GammaRVVolumeSchema B p a k sp) : Set (Fin ((p+a)+((k+1)+1)) → M) :=
  {w | (w ∘ weightedVolumeCoordinateIndices p a (k+1) ∈ F.object.volume ∧
    w ∘ weightedVolumeDensityIndices p a (k+1) ∈ F.density) ∧
    w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin ((k+1)+1) => .rv))}

theorem weightedVolumeGraph_definable (F : GammaRVVolumeSchema B p a k sp) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin ((k+1)+1) => .rv))
      (weightedVolumeGraph F) := by
  let st := Fin.append (Fin.append sp (fun _ : Fin a => SortTag.rv)) (fun _ : Fin ((k+1)+1) => .rv)
  have h := (F.object.volume_definable.preimage_real st (weightedVolumeCoordinateIndices p a (k+1))).inter
    (F.density_definable.preimage_real st (weightedVolumeDensityIndices p a (k+1)))
  convert h using 1
  ext w
  change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
  tauto

theorem weightedVolumeGraph_append (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (x : Fin a → M) (u : Fin (k+1) → M) (φ : Fin 1 → M) :
    Fin.append (Fin.append z x) (Fin.append u φ) ∈ weightedVolumeGraph F ↔
      Fin.append (Fin.append z x) u ∈ F.object.volume ∧ Fin.append (Fin.append z x) φ ∈ F.density := by
  let w := Fin.append (Fin.append z x) (Fin.append u φ)
  have hV : w ∘ weightedVolumeCoordinateIndices p a (k+1) = Fin.append (Fin.append z x) u := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp only [w,weightedVolumeCoordinateIndices,Function.comp_apply,Fin.addCases_left,
        Fin.addCases_right,Fin.append_left,Fin.append_right]
  have hD : w ∘ weightedVolumeDensityIndices p a (k+1) = Fin.append (Fin.append z x) φ := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp only [w,weightedVolumeDensityIndices,Function.comp_apply,Fin.addCases_left,
        Fin.addCases_right,Fin.append_left,Fin.append_right]
  change ((_ ∈ F.object.volume ∧ _ ∈ F.density) ∧ _) ↔ _
  rw [hV,hD]
  constructor
  · exact And.left
  · rintro ⟨hV,hD⟩
    refine ⟨⟨hV,hD⟩,?_⟩
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [Fin.append_left] using F.object.volume_definable.proper _ hV (Fin.castAdd (k+1) j)
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.append_left,Fin.append_right] using
          F.object.volume_definable.proper _ hV (Fin.natAdd (p+a) j)
      · simpa only [Fin.append_right] using F.density_definable.proper _ hD (Fin.natAdd (p+a) j)

theorem weightedVolumeGraph_parts (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (x : Fin a → M) (w : Fin ((k+1)+1) → M) :
    Fin.append (Fin.append z x) w ∈ weightedVolumeGraph F ↔
      Fin.append (Fin.append z x) (w ∘ Fin.castAdd 1) ∈ F.object.volume ∧
        Fin.append (Fin.append z x) (w ∘ Fin.natAdd (k+1)) ∈ F.density := by
  have he : Fin.append (w ∘ Fin.castAdd 1) (w ∘ Fin.natAdd (k+1)) = w := Fin.append_castAdd_natAdd
  have h := weightedVolumeGraph_append F z x (w ∘ Fin.castAdd 1) (w ∘ Fin.natAdd (k+1))
  rwa [he] at h

end IntegrationInACVF.Section7
