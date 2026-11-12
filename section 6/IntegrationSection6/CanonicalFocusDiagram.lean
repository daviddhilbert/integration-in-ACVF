import IntegrationSection6.CanonicalFocusCoordinates
import IntegrationSection6.TypedRelabeling
import IntegrationSection6.CanonicalFocusSpecial
import IntegrationSection6.RVLabelMap

/-! The actual length-one lift diagram: bijective arrows, identity VF
coordinates, commuting label projection and the quotient-coordinate rule. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {U : @RVObject M (@CanonicalStructure.normalize M sM) S n}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n (@rvObjectArity M sM S n U)}
variable (h : @PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U (normalizedPointSet A))
variable {i : Fin n} {k : Fin (n+@rvObjectArity M sM S n U)} (D : Focus (canonicalImage A) i k)
variable (hfull : carrier (canonicalImage A) ⊆ D.locus) (hAd : @Admissible M (@CanonicalStructure.normalize M sM) S n U i)

def canonicalFocusRelabelMap : Map (canonicalImage D.etaImage) (typedLift (@elementary M N hN S n U i)) :=
  canonicalImageRelabelMap D.etaImage (@elementary M N hN S n U i)
    (@RVHom.map M N S n _ _ (canonicalFocusBlowupIso h D hfull hAd).hom) (canonicalFocusBlowupIso_volume h D hfull hAd)

theorem canonicalFocusRelabelMap_bijective (hA : IsRVPullback (carrier A)) :
    Function.Bijective (canonicalFocusRelabelMap h D hfull hAd) :=
  canonicalImageRelabelMap_bijective D.etaImage
    (D.etaImage_pullback (Primitive.preserves_pullback (.canonical A) hA)) _ _ _
    (@iso_map_bijective M N hN S n _ _ (canonicalFocusBlowupIso h D hfull hAd))

@[simp] theorem canonicalFocusRelabelMap_vf (a : canonicalImage D.etaImage) :
    (canonicalFocusRelabelMap h D hfull hAd a).val.1 = a.val.1 := rfl

@[simp] theorem canonicalFocusRelabelMap_square (a : canonicalImage D.etaImage) :
    (canonicalFocusRelabelMap h D hfull hAd a).val.2 =
      ((@RVHom.map M N S n _ _ (canonicalFocusBlowupIso h D hfull hAd).hom)
        (@liftLabelProjection M N hN S n (originalFocusObject D)
          (canonicalImageLiftMap D.etaImage a))).val := rfl

theorem canonicalFocusRelabelMap_formula (a : canonicalImage D.etaImage) :
    (canonicalFocusRelabelMap h D hfull hAd a).val =
      (mapRVLabels n S (@focusRelabelProgram M N hN n (@rvObjectArity M sM S n U) S i)
        ⟨a.val,Set.mem_univ _⟩).val := by
  change (canonicalImageRelabelMap _ _ _ _ a).val = _
  rw [canonicalImageRelabelMap_value]
  apply congrArg (fun t => (a.val.1,t))
  exact canonicalFocusBlowupIso_formula h D hfull hAd _

end IntegrationInACVF.Section6
