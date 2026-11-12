import IntegrationSection6.GammaFocusDiagram
import IntegrationSection6.GammaElementaryFocus

/-! Lemma6.12 over the original VF/Gamma-generated base. The construction
retains the full focus, special length one, both bijective arrows and their
invariant graphs; all VF coordinates of the relabeling are fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

structure ElementaryLiftDiagram (U : GammaRVObject B n) (i : Fin n) where
  focus : Focus (canonicalTypedLift U.object) i (Fin.castAdd (rvObjectArity U.object) i)
  full : focus.locus = carrier (canonicalTypedLift U.object)
  focus_graph : GammaFocusDefinable B focus
  admissible : @Admissible M (@CanonicalStructure.normalize M sM) U.codes n U.object i

namespace ElementaryLiftDiagram
variable {U : GammaRVObject B n} {i : Fin n} (D : ElementaryLiftDiagram U i)

def special := gammaCanonicalFocusSpecial U.real_contains (typedLift U.object) D.focus
  (gamma_typedLift_definable U) D.focus_graph

@[simp] theorem special_length : D.special.special.length = 1 := rfl

def downIso := canonicalFocusBlowupIso (@normalizedTypedLift_presents M sM hM U.codes n U.object)
  D.focus (by rw [D.full]; exact fun _ h => h) D.admissible

def down := @RVHom.map M N U.codes n _ _ D.downIso.hom

def up := canonicalFocusRelabelMap (@normalizedTypedLift_presents M sM hM U.codes n U.object)
  D.focus (by rw [D.full]; exact fun _ h => h) D.admissible

theorem down_bijective : Function.Bijective D.down :=
  @iso_map_bijective M N hN U.codes n _ _ D.downIso

theorem up_bijective : Function.Bijective D.up :=
  canonicalFocusRelabelMap_bijective (@normalizedTypedLift_presents M sM hM U.codes n U.object)
    D.focus (by rw [D.full]; exact fun _ h => h) D.admissible (typedLift_pullback U.object)

theorem down_graph : GammaGraphDefinable B
    (fun (p : Point (M := M) 0 (n+(n+rvObjectArity U.object)))
      (q : Point (M := M) 0 (rvObjectArity U.object+1)) =>
      ∃ a : rvObjectDomain (originalFocusObject D.focus), a.val = p.2 ∧ (D.down a).val = q.2) :=
  gamma_canonicalFocusBlowupIso_graph (@normalizedTypedLift_presents M sM hM U.codes n U.object)
    D.focus (by rw [D.full]; exact fun _ h => h) D.admissible (gamma_typedLift_definable U) D.focus_graph

theorem up_graph : GammaGraphDefinable B (pointMapGraph D.up) :=
  gamma_canonicalFocusRelabelMap_graph (@normalizedTypedLift_presents M sM hM U.codes n U.object)
    D.focus (by rw [D.full]; exact fun _ h => h) D.admissible (gamma_typedLift_definable U) D.focus_graph

@[simp] theorem up_vf (a : canonicalImage D.focus.etaImage) :
    (D.up a).val.1 = a.val.1 := rfl

@[simp] theorem square (a : canonicalImage D.focus.etaImage) :
    (D.up a).val.2 = (D.down (@liftLabelProjection M N hN U.codes n
      (originalFocusObject D.focus) (canonicalImageLiftMap D.focus.etaImage a))).val := rfl

theorem up_formula (a : canonicalImage D.focus.etaImage) :
    (D.up a).val =
      (mapRVLabels n U.codes (@focusRelabelProgram M N hN n (rvObjectArity U.object) U.codes i)
        ⟨a.val,Set.mem_univ _⟩).val :=
  canonicalFocusRelabelMap_formula (@normalizedTypedLift_presents M sM hM U.codes n U.object)
    D.focus (by rw [D.full]; exact fun _ h => h) D.admissible a

def relabelIso : GammaIso B (carrier (canonicalImage D.focus.etaImage))
    (carrier (typedLift (@elementary M N hN U.codes n U.object i))) where
  equiv := Equiv.ofBijective D.up D.up_bijective
  graph := D.up_graph

def liftIso : GammaIso B (carrier (typedLift U.object))
    (carrier (typedLift (@elementary M N hN U.codes n U.object i))) :=
  D.special.iso (gammaLogicInput B) |>.trans (gammaLogicInput B) D.relabelIso

end ElementaryLiftDiagram

/-- Actual existence of the complete original-Gamma length-one diagram.
Only the original real base is bounded by the saturation cardinal. -/
theorem lemma_6_12 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    {U : GammaRVObject B n} {i : Fin n} (hAd : GammaAdmissible U i) :
    Nonempty (ElementaryLiftDiagram U i) := by
  obtain ⟨D,hD,hΓD⟩ := hAd.exists_canonical_fullFocus hκ hs h00 hsmall hB
  exact ⟨⟨D,hD,hΓD,hAd.ordinary hκ hs h00 hsmall⟩⟩

end IntegrationInACVF.Section6
