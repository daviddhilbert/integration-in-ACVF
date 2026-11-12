import IntegrationSection6.GammaElementaryStructure
import IntegrationSection6.GammaFiniteSlices
import IntegrationSection6.GammaLiftVolumeRecovery
import IntegrationSection6.ElementaryLiftIsomorphism
import IntegrationSection6.FiniteBlowups

/-! Elementary blowups and their length-one diagrams live in RV[k].
The original Gamma base is retained, and only B.real is small. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaAdmissible.elementary_finite_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    {U : GammaRVObject B n} {i : Fin n} (h : GammaAdmissible U i)
    (hU : Map.FiniteFibres (rvObjectVolume U.object)) :
    Map.FiniteFibres (rvObjectVolume (@elementary M N hN U.codes n U.object i)) := by
  let R := U.object
  have hOrd := h.ordinary hκ hs h00 hsmall
  have hf := h.finite_label_slices hκ hs h00 hsmall
  letI := N
  letI := hN
  exact elementary_finite_volume_of_slices R i hOrd hf hU

/-- The geometric construction needs no field-generation hypothesis. -/
def gammaFiniteElementaryBasic {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaRVFiniteObject B n) (i : Fin n)
    (h : GammaAdmissible U.toGammaRVObject i) : GammaRVFiniteObject B n where
  toGammaRVObject := gammaElementaryObject U.toGammaRVObject i
  finite_volume := h.elementary_finite_volume hκ hs h00 hsmall U.finite_volume

def gammaFiniteElementary {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (U : GammaRVFiniteObject B n) (i : Fin n)
    (h : GammaAdmissible U.toGammaRVObject i) : GammaRVFiniteObject B n where
  toGammaRVObject := gammaRVObjectOfLift U.real_contains (@elementary M N hN U.codes n U.object i)
    (elementary_lift_gamma_definable hκ hs h00 hsmall hB h)
  finite_volume := h.elementary_finite_volume hκ hs h00 hsmall U.finite_volume

@[simp] theorem gammaFiniteElementary_object {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (U : GammaRVFiniteObject B n) (i : Fin n)
    (h : GammaAdmissible U.toGammaRVObject i) :
    (gammaFiniteElementary hκ hs h00 hsmall hB U i h).object = @elementary M N hN U.codes n U.object i := rfl

namespace FiniteRV

def ofGamma (U : GammaRVFiniteObject B n) : @RVFiniteObject M N U.codes n :=
  ⟨U.object,U.finite_volume⟩

/-- Lemma6.12 in the requested finite-volume categories. The diagram
contains its length-one special, both bijections, full graphs and square. -/
theorem lemma_6_12 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (U : GammaRVFiniteObject B n) (i : Fin n)
    (h : GammaAdmissible U.toGammaRVObject i) :
    ∃ V : GammaRVFiniteObject B n,
      V.codes = U.codes ∧ HEq V.object (@elementary M N hN U.codes n U.object i) ∧
      Nonempty (ElementaryLiftDiagram U.toGammaRVObject i) ∧
      Nonempty (GammaIso B U.lift V.lift) := by
  let V := gammaFiniteElementary hκ hs h00 hsmall hB U i h
  exact ⟨V,rfl,HEq.rfl,IntegrationInACVF.Section6.lemma_6_12 hκ hs h00 hsmall hB h,
    elementary_lifts_isomorphic hκ hs h00 hsmall hB h⟩

theorem diagram_post_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    {U : GammaRVFiniteObject B n} {i : Fin n} (h : GammaAdmissible U.toGammaRVObject i)
    (D : ElementaryLiftDiagram U.toGammaRVObject i) :
    Map.FiniteFibres (rvObjectVolume (originalFocusObject D.focus)) := by
  have he := h.elementary_finite_volume hκ hs h00 hsmall U.finite_volume
  let e := D.downIso
  letI := N
  letI := hN
  exact (finite_volume_iso e).mpr he

end FiniteRV
end IntegrationInACVF.Section6
