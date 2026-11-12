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

theorem gamma_volume_slice_common_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (U V : GammaRVFiniteObject B (e+k))
    (hCommon : ∀ t : Fin e → RV (M := M),
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity U.object) k ((gammaVolumeSliceSchema U).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema U).rowVolume (fun j => (t j).val)),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity V.object) k ((gammaVolumeSliceSchema V).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema V).rowVolume (fun j => (t j).val)),
      GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (fun j => (t j).val)) P.toGamma Q.toGamma) :
    GammaIsp hκ hs h00 hreal U V := by
  obtain ⟨BP⟩ := gamma_identity_index_presentation_exists B e
  let F := gammaVolumeSliceSchema U
  let G := gammaVolumeSliceSchema V
  let P := F.indexedPresentation_finiteRows BP (fun t _ => gammaVolumeSliceSchema_finiteRows U t)
  let Q := G.indexedPresentation_finiteRows BP (fun t _ => gammaVolumeSliceSchema_finiteRows V t)
  have h := gamma_rv_indexed_common_uniformity hκ hs h00 hreal hgamma F G BP
    (fun t _ => gammaVolumeSliceSchema_finiteRows U t) (fun t _ => gammaVolumeSliceSchema_finiteRows V t)
    (fun t _ => hCommon t) P Q
  exact h.corollary_6_6 (gammaIsoSymm (gammaVolumeSliceAssemblyIso U BP P))
    (gammaIsoSymm (gammaVolumeSliceAssemblyIso V BP Q))

theorem gamma_volume_slice_unary_lift_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (U V : GammaRVFiniteObject B (e+1))
    (hLift : ∀ t : Fin e → RV (M := M),
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity U.object) 1 ((gammaVolumeSliceSchema U).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema U).rowVolume (fun j => (t j).val)),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity V.object) 1 ((gammaVolumeSliceSchema V).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema V).rowVolume (fun j => (t j).val)),
      Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ P.toGamma.lift Q.toGamma.lift)) :
    GammaIsp hκ hs h00 hreal U V := by
  apply gamma_volume_slice_common_uniformity hκ hs h00 hreal hgamma U V
  intro t P Q
  obtain ⟨f⟩ := hLift t P Q
  exact corollary_6_11_gamma (B := ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩)
    hκ hs h00 (small_union_range hκ B.real hreal (fun j => (t j).val))
    δ hδ hδ1 (VFFieldBase.withRVParameters FBase (fun j => (t j).val) (fun j => (t j).property))
    P.toGamma Q.toGamma f

end IntegrationInACVF.Section6
