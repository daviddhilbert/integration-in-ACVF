import IntegrationSection6.GammaFiniteObjectSchemata

/-! Project volume graphs in an original-Gamma tuple family without
changing its parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

def tupleVolumeImage (V : Set (Fin ((p+a)+k) → M)) : Set (Fin (p+k) → M) :=
  {w | ∃ x : Fin a → M, Fin.append (Fin.append (fun i => w (Fin.castAdd k i)) x)
    (fun j => w (Fin.natAdd p j)) ∈ V}

theorem gamma_tuple_volume_image_definable (sp : Fin p → SortTag) (sx : Fin a → SortTag)
    (sy : Fin k → SortTag) {V : Set (Fin ((p+a)+k) → M)}
    (hV : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) V) :
    DefinableOverBase B (Fin.append sp sy) (tupleVolumeImage V) := by
  let W := (fun v => v ∘ swapLastBlockCoordinates p a k) '' V
  have hW : DefinableOverBase B (Fin.append (Fin.append sp sy) sx) W := by
    have h := hV.image_real (swapLastBlockCoordinates p a k)
    rw [append_swapLastBlocks] at h
    exact h
  have h := gamma_family_row_exists_definable (Fin.append sp sy) sx hW
  convert h using 1
  apply Set.ext
  intro w
  apply exists_congr
  intro x
  have he := append_mem_swapLastBlocks_image V (fun i => w (Fin.castAdd k i)) x (fun j => w (Fin.natAdd p j))
  rw [Fin.append_castAdd_natAdd] at he
  exact he.symm

theorem tupleVolumeImage_append_iff (V : Set (Fin ((p+a)+k) → M))
    (z : Fin p → M) (y : Fin k → M) :
    Fin.append z y ∈ tupleVolumeImage V ↔ ∃ x : Fin a → M, Fin.append (Fin.append z x) y ∈ V := by
  simp only [tupleVolumeImage,Set.mem_ofPred_eq,Fin.append_left,Fin.append_right]

theorem GammaFiniteRVSchema.volume_image_definable {sp : Fin p → SortTag} (F : GammaFiniteRVSchema B p a k sp) :
    DefinableOverBase B (Fin.append sp (fun _ : Fin k => .rv))
      (tupleVolumeImage F.volume) :=
  gamma_tuple_volume_image_definable _ _ _ F.volume_definable

end IntegrationInACVF.Section6
