import Integration7.GammaVolumeCoproductDensities
import IntegrationSection6.GammaRawCoproductSchemaBridge

/-! Adjust finite coordinate-map metadata without changing any graph or
density. Actual finite coproduct presentations supply a valid bound at
each required row. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaRVVolumeSchema.withBound (F : GammaRVVolumeSchema B p a k sp) (N : ℕ) :
    GammaRVVolumeSchema B p a k sp := {F with object := F.object.withBound N}

theorem GammaRVVolumeSchema.withBound_sameRow (F : GammaRVVolumeSchema B p a k sp)
    (N : ℕ) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) :
    (F.withBound N).sameRow F z := F.sameRow_refl z hz

theorem GammaRVVolumeSchema.exists_valid_coprod_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z) :
    ∃ N : ℕ, ((F.coprodFormula G).withBound N).valid z := by
  obtain ⟨P⟩ := F.object.realize z hF.1
  obtain ⟨Q⟩ := G.object.realize z hG.1
  obtain ⟨N,hN⟩ := F.object.exists_valid_coprod_bound hκ hs hreal hgamma G.object z hF.1.1
    (F.object.valid_row_support hF.1) (G.object.valid_row_support hG.1) P Q
  exact ⟨N,hN,F.coprod_density_valid G z hF hG⟩

end IntegrationInACVF.Section7
