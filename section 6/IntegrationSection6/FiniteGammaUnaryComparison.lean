import IntegrationSection6.FiniteGammaChartedChains
import IntegrationSection6.FiniteGammaCommonBlowups
import IntegrationSection5.UnaryBijectionPreparation
import IntegrationSection5.UnaryRVCategory

/-! Corollary6.11 in the finite categories: actual common-blowup witnesses
with every chart over the original Gamma base, from checked Section5.2/5.3. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem corollary_6_11_presented {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase B.real) (U V : GammaObjectAt B S 1)
    (f : Map (typedLift U.object.obj) (typedLift V.object.obj)) (hf : Function.Bijective f)
    (hfΓ : GammaGraphDefinable B (pointMapGraph f)) :
    GammaIsp hκ hs h00 hsmall  U.toGamma V.toGamma := by
  have hUΓ : GammaSetDefinable B (carrier (typedLift U.object.obj)) := by
    rw [typedLift_carrier]
    exact U.toGamma.toGammaRVObject.lift_definable
  have hVΓ : GammaSetDefinable B (carrier (typedLift V.object.obj)) := by
    rw [typedLift_carrier]
    exact V.toGamma.toGammaRVObject.lift_definable
  obtain ⟨R,hSR,r,s,C,D,TU,TV,hTU,hTV,hC,hD,hc,hback,hgraph,_⟩ :=
    IntegrationInACVF.Section5.lemma_5_2_gamma_presented hκ hs hsmall h00 δ hδ hδ1 FBase U.real_contains
      f hf hUΓ hVΓ hfΓ
  let fR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M N _ _ S R _ _ f hSR
  let g := IntegrationInACVF.Section5.unaryConjugate TU TV fR
  have hg := IntegrationInACVF.Section5.unaryConjugate_bijective TU TV fR hf
  obtain ⟨e,_,heΓ,_⟩ := IntegrationInACVF.Section5.lemma_5_3 hκ hs hsmall g hg hc hback hC hD hgraph
  have hBR : B.real ⊆ R := fun x hx => hSR (U.real_contains hx)
  have hPU := normalizedPresentsLift_extendBase hSR (normalizedTypedLift_presents U.object.obj)
  have hPV := normalizedPresentsLift_extendBase hSR (normalizedTypedLift_presents V.object.obj)
  let UR := gammaObjectAtExtend U.toGamma hSR
  let VR := gammaObjectAtExtend V.toGamma hSR
  obtain ⟨hCF,hUC⟩ := (gammaChain_charted_pair hκ hs h00 hsmall  hBR TU.chain hTU).1
    (@RVObject.domain M N R 1 UR.object.obj) (@RVObject.volume M N R 1 UR.object.obj) UR.object.property hPU TU.alternating
  obtain ⟨hDF,hVD⟩ := (gammaChain_charted_pair hκ hs h00 hsmall  hBR TV.chain hTV).1
    (@RVObject.domain M N R 1 VR.object.obj) (@RVObject.volume M N R 1 VR.object.obj) VR.object.property hPV TV.alternating
  let A := gammaPullbackAt hBR C (GammaChainDefinable.target B TU.chain hTU) hCF
  let E := gammaPullbackAt hBR D (GammaChainDefinable.target B TV.chain hTV) hDF
  let ei : GammaIsoAt A E := GammaIsoAt.ofAmbient e heΓ
  exact ⟨R,hSR,hSR,TU.length,TV.length,A,E,hUC,hVD,⟨ei⟩⟩

end IntegrationInACVF.Section6.FiniteRV
