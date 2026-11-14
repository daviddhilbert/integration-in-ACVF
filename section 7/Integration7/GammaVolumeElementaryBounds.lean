import Integration7.GammaVolumeElementaryDensities
import IntegrationSection6.GammaRawElementarySchemaBridge

/-! Original-Gamma admissibility supplies a finite elementary coordinate
map. Its valid bound combines with the proved density pullback to give
an actual valid volume-schema row. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeSchema.exists_valid_elementary_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (hF : F.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      (F.object.rowDomain z) (F.object.rowVolume z))
    (hAd : GammaAdmissible P.toGamma.toGammaRVObject (Fin.last k)) :
    ∃ N : ℕ, (F.elementaryFormula.withBound N).valid z := by
  obtain ⟨N,hN⟩ := F.object.exists_valid_elementary_bound hκ hs h00 hreal hgamma z hF.1.1 P (Fin.last k) hAd
  exact ⟨N,hN,F.elementary_density_valid z hF⟩

end IntegrationInACVF.Section7
