import IntegrationSection6.GammaVolumeSliceUniformity
import IntegrationSection6.GammaUnaryFieldReduction
import IntegrationSection6.GammaVolumeSliceAssembly
import IntegrationSection6.GammaRVIndexedUniformity
import IntegrationSection6.GammaRVParameterFieldBase
import IntegrationSection6.FiniteGammaIsoRealization

/-! Common blowups of all volume slices glue to a common blowup of the
original RV[e+k] objects. In the unary case it suffices to compare the
actual lifts of the slices over the named RV parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}
open FiniteRV

theorem gamma_volume_slice_unary_lift_uniformity_uncountable {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaRVFiniteObject B (e+1))
    (hLift : ∀ t : Fin e → RV (M := M),
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity U.object) 1 ((gammaVolumeSliceSchema U).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema U).rowVolume (fun j => (t j).val)),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity V.object) 1 ((gammaVolumeSliceSchema V).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema V).rowVolume (fun j => (t j).val)),
      Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ P.toGamma.lift Q.toGamma.lift)) :
    GammaIsp hκ.le hs h00 hreal U V := by
  apply gamma_volume_slice_common_uniformity hκ.le hs h00 hreal hgamma U V
  intro t P Q
  obtain ⟨f⟩ := hLift t P Q
  exact corollary_6_11_uncountable_base (B := ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩)
    hκ hs h00 (small_union_range hκ.le B.real hreal (fun j => (t j).val))
    δ hδ hδ1
    P.toGamma Q.toGamma f

end IntegrationInACVF.Section6
