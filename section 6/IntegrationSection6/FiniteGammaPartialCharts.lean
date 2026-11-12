import IntegrationSection6.FiniteGammaBlowups
import IntegrationSection6.FiniteGammaFocusCharts
import IntegrationSection6.FiniteGammaComplementCharts
import IntegrationSection6.FiniteGammaPullbackPartitions
import IntegrationSection6.FiniteGammaPartialFocus

/-! A partial Gamma focus is one Gamma-certified genuine blowup in RV[k].
Both partition charts and the active/complementary comparison graphs are
over the original base; only its real part is bounded by saturation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaPartialFocusImageAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN S n U.object.obj (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U.object.obj)} (D : Focus A i k)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) : GammaObjectAt B S n :=
  gammaPullbackAt U.real_contains D.etaImage
    (GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal D) ⟨hA,hD⟩)
    (gammaPartialFocusStep hκ hs h00 hsmall U.real_contains U.object h D hA hD).target_finite

def gammaPartialFocusBlowupAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN S n U.object.obj (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U.object.obj)} (D : Focus A i k)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    GammaBlowupAt hκ hs h00 hsmall  U (gammaPartialFocusImageAt hκ hs h00 hsmall U h D hA hD) := by
  let LΓ := gammaLogicInput B
  let C := focusActiveSet D
  let E := focusInactiveSet D
  let L := liftLabelLocus C
  have hc := liftLabelLocus_subset h (focusActiveSet_subset D)
  have hAΓ := gamma_focusActiveSet D hA hD
  have hEΓ : GammaSetDefinable B (carrier E) := LΓ.sdiff hA hAΓ
  have hLΓ := (gammaActiveRVObject h D U.real_contains hA hD).domain_graph
  let R := gammaRestrictAt U L hc hLΓ
  let Q := gammaComplementAt U L hLΓ
  have hAd : GammaAdmissible R.toGamma.toGammaRVObject i :=
    gammaActiveRVObject_admissible h D hκ hs hsmall U.real_contains hA hD
  have hAP := (pullback_normalize (carrier A)).mp
    (@PresentsLift.pullback M N hN S n U.object.obj (normalizedPointSet A) h)
  have hCP := focusActiveSet_pullback D hAP
  have hEP := focusInactiveSet_pullback D hAP
  have hpart := partialFocus_source_partition D
  have hd : Disjoint (carrier C) (carrier E) := by
    exact Set.disjoint_left.mpr (fun p hp he => he.2 hp)
  let eC := gammaFullFocusIsoAt hκ hs h00 hsmall  R (focusActiveRVObject_presents h D)
    (activeFocus D) (activeFocus_full D) hAd hAΓ (gamma_activeFocus D hA hD)
  let eE := gammaComplementIsoAt U h hpart hd hCP hEP hLΓ hEΓ
  have hTΓ := GammaPrimitiveDefinable.target LΓ (.centripetal D) ⟨hA,hD⟩
  have hCΓ := GammaPrimitiveDefinable.target LΓ (.centripetal (activeFocus D))
    ⟨hAΓ,gamma_activeFocus D hA hD⟩
  let T := gammaPartialFocusImageAt hκ hs h00 hsmall U h D hA hD
  let A' := gammaFullFocusImageAt hκ hs h00 hsmall  R (focusActiveRVObject_presents h D)
    (activeFocus D) (activeFocus_full D) hAd hAΓ (gamma_activeFocus D hA hD)
  let E' := gammaComplementPresentationAt U h hpart hd hCP hEP hLΓ hEΓ
  let ep := gammaPullbackPartitionIsoAt U.real_contains hTΓ hCΓ hEΓ
    T.object.property A'.object.property E'.object.property
    (partialFocus_image_partition D) (partialFocus_image_disjoint D) ((activeFocus D).etaImage_pullback hCP)
  exact {
    center := R
    remainder := Q
    coordinate := i
    admissible := hAd
    source := (gammaPartitionIsoAt U L hc hLΓ).symm
    result := ep.trans (gammaCoprodIsoAt eC eE) }

end IntegrationInACVF.Section6.FiniteRV
