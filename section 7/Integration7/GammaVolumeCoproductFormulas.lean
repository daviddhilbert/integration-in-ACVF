import Integration7.GammaVolumeSchemaRowEquality
import Integration7.NonzeroDensityFormulas
import IntegrationSection6.GammaRawCoproductSchemata

/-! Tagged coproduct formula data for volume objects. The density is
the original density on each summand; no tag changes a volume coordinate.
Finite bounds for valid rows are supplied separately. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def GammaRVVolumeSchema.coprodFormula (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) : GammaRVVolumeSchema B p (1+(a+b)) k sp where
  object := F.object.coprodFormula G.object
  density := nonzeroDensityFormula (F.densityTemplate.coprodFormula G.densityTemplate).volume
  density_definable := nonzeroDensityFormula_definable
    (F.densityTemplate.coprodFormula G.densityTemplate).volume_definable
  density_nonzero _ hw := hw.2

theorem GammaRVVolumeSchema.coprod_rowDensity (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (w : Fin (1+(a+b)) → CanonicalRV.RVSort M) (ω : Fin 1 → CanonicalRV.RVSort M) :
    (F.coprodFormula G).rowDensity z w ω ↔
      (∃ x, F.rowDensity z x ω ∧ @rvLeftTag M N hN a b x = w) ∨
      ∃ y, G.rowDensity z y ω ∧ @rvRightTag M N hN b a y = w := by
  change Fin.append (Fin.append z (rvValues w)) (rvValues ω) ∈
    nonzeroDensityFormula (F.densityTemplate.coprodFormula G.densityTemplate).volume ↔ _
  rw [nonzeroDensityFormula_append]
  change ((F.densityTemplate.coprodFormula G.densityTemplate).rowVolume z w ω ∧ (ω 0).val ≠ iRVZero) ↔ _
  rw [F.densityTemplate.coprod_row_volume_formula G.densityTemplate z hz w ω]
  constructor
  · exact And.left
  · intro h
    refine ⟨h,?_⟩
    rcases h with ⟨x,hx,_⟩ | ⟨y,hy,_⟩
    · exact F.rowDensity_nonzero z x ω hx
    · exact G.rowDensity_nonzero z y ω hy

end IntegrationInACVF.Section7
