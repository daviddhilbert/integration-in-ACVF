import IntegrationSection6.Kernel
import IntegrationSection6.NativeFiniteLiftInvariance

/-! Lemma6.17 for the actual finite categories in every degree, over the
original generated base. No canonical-presentation hypothesis remains. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem lemma_6_17 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ) (hB : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ hs) (U V : GammaRVFiniteObject B k) :
    Nonempty (GammaIso B U.lift V.lift) ↔ GammaIsp hκ hs h00 hreal U V := by
  constructor
  · rintro ⟨e⟩
    exact lemma_6_17_kernel hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 U V e
  · intro H
    exact H.liftIsoNative hB

end IntegrationInACVF.Section6.FiniteRV
