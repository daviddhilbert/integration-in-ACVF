import IntegrationSection6.CanonicalFocusDiagram
import IntegrationSection6.GammaRVGlobalRestriction
import Section5.GammaLift

/-! Both arrows of the length-one diagram have complete invariant graphs
over the original real/Gamma base. Internal presentation codes are unbounded. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {U : @RVObject M (@CanonicalStructure.normalize M sM) S n}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n (@rvObjectArity M sM S n U)}
variable (h : @PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U (normalizedPointSet A))
variable {i : Fin n} {k : Fin (n+@rvObjectArity M sM S n U)} (D : Focus (canonicalImage A) i k)
variable (hfull : carrier (canonicalImage A) ⊆ D.locus) (hAd : @Admissible M (@CanonicalStructure.normalize M sM) S n U i)
variable (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)

include hA hD in
theorem gamma_canonicalFocusBlowupIso_graph :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (n+(n+@rvObjectArity M sM S n U)))
        (q : Point (M := M) 0 (@rvObjectArity M sM S n U+1)) =>
        ∃ a : rvObjectDomain (originalFocusObject D), a.val = p.2 ∧
          ((@RVHom.map M N S n _ _ (canonicalFocusBlowupIso h D hfull hAd).hom) a).val = q.2) := by
  let L := gammaLogicInput B
  have hC := GammaPrimitiveDefinable.target L (.canonical A) hA
  have hE := GammaPrimitiveDefinable.target L (.centripetal D) ⟨hC,hD⟩
  have hP := gamma_pullback_domain L D.etaImage hE
  apply gamma_rv_graph_of_global_formula (@RVHom.map M N S n _ _ (canonicalFocusBlowupIso h D hfull hAd).hom)
    (@focusRelabelProgram M N hN n (@rvObjectArity M sM S n U) B.real i) hP
  intro a
  exact canonicalFocusBlowupIso_formula h D hfull hAd a

include hA hD in
theorem gamma_canonicalFocusRelabelMap_graph :
    GammaGraphDefinable B (pointMapGraph (canonicalFocusRelabelMap h D hfull hAd)) := by
  let L := gammaLogicInput B
  have hC := GammaPrimitiveDefinable.target L (.canonical A) hA
  have hE := GammaPrimitiveDefinable.target L (.centripetal D) ⟨hC,hD⟩
  have hK := GammaPrimitiveDefinable.target L (.canonical D.etaImage) hE
  apply gamma_map_graph_of_global_formula (canonicalFocusRelabelMap h D hfull hAd)
    (mapRVLabels n B.real (@focusRelabelProgram M N hN n (@rvObjectArity M sM S n U) B.real i)) hK
  intro a
  exact canonicalFocusRelabelMap_formula h D hfull hAd a

end IntegrationInACVF.Section6
