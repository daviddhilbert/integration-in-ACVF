import IntegrationSection6.GammaParameterRecoding
import IntegrationSection6.GammaSchemaFiniteRows

/-! A full sorted relation has a canonical object schema whose domain is
its exact projection. Functionality and finite fibres remain explicit row
obligations; a numerical bound is unnecessary for indexed assembly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaRelationFormula.sourceDomain (R : GammaRelationFormula B p a k sp) : Set (Fin (p+a) → M) :=
  {z | ∃ y : Fin k → M, Fin.append z y ∈ R.val}

theorem GammaRelationFormula.sourceDomain_definable (R : GammaRelationFormula B p a k sp) :
    DefinableOverBase B (Fin.append sp (fun _ : Fin a => .rv)) R.sourceDomain := by
  have h := R.property.image_real (Fin.castAdd k : Fin (p+a) → Fin ((p+a)+k))
  have hs : Fin.append (Fin.append sp (fun _ : Fin a => SortTag.rv)) (fun _ : Fin k => .rv) ∘
      Fin.castAdd k = Fin.append sp (fun _ : Fin a => .rv) := by
    funext j
    exact Fin.append_left _ _ j
  rw [hs] at h
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨Fin.append z y,hy,funext (fun j => Fin.append_left _ _ j)⟩
  · rintro ⟨w,hw,he⟩
    refine ⟨w ∘ Fin.natAdd (p+a),?_⟩
    have hh : Fin.append z (w ∘ Fin.natAdd (p+a)) = w := by
      rw [← he]
      exact Fin.append_castAdd_natAdd
    exact hh.symm ▸ hw

def GammaRelationFormula.graphSchema (R : GammaRelationFormula B p a k sp) : GammaFiniteRVSchema B p a k sp :=
  ⟨R.sourceDomain,R.val,R.sourceDomain_definable,R.property,0⟩

theorem GammaRelationFormula.graphSchema_row_volume (R : GammaRelationFormula B p a k sp)
    (z : Fin p → M) (x : Fin a → RV (M := M)) (y : Fin k → RV (M := M)) :
    R.graphSchema.rowVolume z x y ↔
      Fin.append (Fin.append z (fun j => (x j).val)) (fun j => (y j).val) ∈ R.val := Iff.rfl

theorem GammaRelationFormula.graphSchema_row_domain (R : GammaRelationFormula B p a k sp)
    (z : Fin p → M) (x : Fin a → RV (M := M)) :
    x ∈ R.graphSchema.rowDomain z ↔ ∃ y : Fin k → RV (M := M), R.graphSchema.rowVolume z x y := by
  constructor
  · rintro ⟨y,hy⟩
    have hys (j : Fin k) : iRV (y j) := by
      simpa only [Fin.append_right,sortEval,iRV] using R.property.proper _ hy (Fin.natAdd (p+a) j)
    exact ⟨fun j => ⟨y j,hys j⟩,hy⟩
  · rintro ⟨y,hy⟩
    exact ⟨fun j => (y j).val,hy⟩

end IntegrationInACVF.Section6
