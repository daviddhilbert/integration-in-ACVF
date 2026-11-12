import IntegrationSection6.GammaFieldBaseReduction
import IntegrationSection6.GammaBlowupBaseReduction
import IntegrationSection6.GammaReducedBaseExtensionIsomorphisms
import IntegrationSection6.FiniteGammaIsoRealization

/-! Unary lift comparison over a small arbitrary base in an uncountably
saturated model. The generated VF field is named internally and then all
of its definable names are eliminated from the actual common blowup. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)}

theorem corollary_6_11_uncountable_base {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaRVFiniteObject B 1) (f : GammaIso B U.lift V.lift) :
    GammaIsp hκ.le hs h00 hreal U V := by
  let C := vfFieldNamedBase B
  let H := vfFieldBaseReduction B
  let UC := gammaFiniteBaseExtension (C := C) U Set.subset_union_left (Set.Subset.refl _)
  let VC := gammaFiniteBaseExtension (C := C) V Set.subset_union_left (Set.Subset.refl _)
  let fC : GammaIso C UC.lift VC.lift :=
    ⟨f.equiv,f.graph.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hC := vfFieldNamedBase_small B hκ hreal
  have h := corollary_6_11_gamma (B := C) hκ.le hs h00 hC δ hδ hδ1 (vfFieldNamedBase_field B) UC VC fC
  have h' := H.common hκ.le hs h00 hreal hC h
  exact h'.corollary_6_6 (gammaReducedBaseExtensionIso H (Set.Subset.refl _) U)
    (gammaReducedBaseExtensionIso H (Set.Subset.refl _) V)

end IntegrationInACVF.Section6.FiniteRV
