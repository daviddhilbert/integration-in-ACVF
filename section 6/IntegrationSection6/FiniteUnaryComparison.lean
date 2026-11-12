import IntegrationSection6.FiniteGammaSpecialChains
import IntegrationSection6.FiniteRVParameterExtension
import IntegrationSection5.UnaryBijectionPreparation
import IntegrationSection5.UnaryRVCategory

/-! The common finite-blowup witnesses underlying6.11, from the actual
Section5 unary preparation and RV isomorphism. The common real presentation
is explicit and is never bounded by saturation. Original-Gamma relation
bookkeeping is separate from this concrete witness construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem unary_common_finite_blowups {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase B.real) (hBS : B.real ⊆ S)
    (U V : @RVFiniteObject M N S 1)
    (f : Map (typedLift U.obj) (typedLift V.obj)) (hf : Function.Bijective f)
    (hUΓ : GammaSetDefinable B (carrier (typedLift U.obj)))
    (hVΓ : GammaSetDefinable B (carrier (typedLift V.obj)))
    (hfΓ : GammaGraphDefinable B (pointMapGraph f)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R,
      @Isp M N hN R 1 (@extendObject M N S R 1 hSR U) (@extendObject M N S R 1 hSR V) := by
  obtain ⟨R,hSR,r,s,C,D,TU,TV,hTU,hTV,hC,hD,hc,hback,hgraph,_⟩ :=
    IntegrationInACVF.Section5.lemma_5_2_gamma_presented hκ hs hsmall h00 δ hδ hδ1 FBase hBS
      f hf hUΓ hVΓ hfΓ
  let fR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M N _ _ S R _ _ f hSR
  let g := IntegrationInACVF.Section5.unaryConjugate TU TV fR
  have hg := IntegrationInACVF.Section5.unaryConjugate_bijective TU TV fR hf
  obtain ⟨e,_,_,_⟩ := IntegrationInACVF.Section5.lemma_5_3 hκ hs hsmall g hg hc hback hC hD hgraph
  have hBR : B.real ⊆ R := fun x hx => hSR (hBS hx)
  have hPU := normalizedPresentsLift_extendBase hSR (normalizedTypedLift_presents U.obj)
  have hPV := normalizedPresentsLift_extendBase hSR (normalizedTypedLift_presents V.obj)
  let UR := @extendObject M N S R 1 hSR U
  let VR := @extendObject M N S R 1 hSR V
  obtain ⟨hCF,hUC⟩ := (gammaChain_blowup_pair hκ hs h00 hsmall hBR TU.chain hTU).1
    (@RVObject.domain M N R 1 UR.obj) (@RVObject.volume M N R 1 UR.obj) UR.property hPU TU.alternating
  obtain ⟨hDF,hVD⟩ := (gammaChain_blowup_pair hκ hs h00 hsmall hBR TV.chain hTV).1
    (@RVObject.domain M N R 1 VR.obj) (@RVObject.volume M N R 1 VR.obj) VR.property hPV TV.alternating
  let a := TU.length
  let b := TV.length
  letI := N
  letI := hN
  exact ⟨R,hSR,a,b,⟨@pullbackObject M sM hM R 1 r C,hCF⟩,
    ⟨@pullbackObject M sM hM R 1 s D,hDF⟩,hUC,hVD,⟨rvFiniteIsoOfAmbient e⟩⟩

end IntegrationInACVF.Section6.FiniteRV
