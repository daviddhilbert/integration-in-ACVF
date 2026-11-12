import IntegrationSection6.GammaSchemaNativeRows
import IntegrationSection6.GammaRawElementarySchemaBridge

/-! The generic elementary schema represents the actual native elementary
blowup of every represented admissible row, at arbitrary internal codes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaSchemaRepresents_elementary {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk C.real < κ) (U : GammaRVFiniteObject C k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object) k sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j)) (hF : gammaSchemaRepresents U F z)
    (i : Fin k) (hAd : GammaAdmissible U.toGammaRVObject i) :
    gammaSchemaRepresents (gammaFiniteElementaryBasic hκ hs h00 hsmall U i hAd) (F.elementaryFormula i) z := by
  have hD (x : Fin (rvObjectArity U.object+1) → RV (M := M)) :
      x ∈ (F.elementaryFormula i).rowDomain z ↔
      x ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ U.codes
        (rvObjectDomain (gammaElementaryObject U.toGammaRVObject i).object) := by
    exact (F.elementary_row_domain_formula i z hz x U.codes).trans
      ((and_congr (gammaSchemaRepresents_domain U F z hF _) Iff.rfl).trans
        (@elementary_domain_formula M N hN U.codes k U.object i x).symm)
  apply gammaSchemaRepresents_of_typed _ _ z hD
  intro x y
  have hE := @elementary_graph_formula M N hN U.codes k U.object i x y
  constructor
  · intro hxy
    obtain ⟨hx,v,hv,hg⟩ := (F.elementary_row_volume_formula i z hz x y).mp hxy
    obtain ⟨u,hu,huv⟩ := (gammaSchemaRepresents_volume U F z hF _ v).mp hv
    apply hE.mpr
    refine ⟨(hD x).mp hx,u,hu,?_⟩
    have hp : (@oldVolumeParameterBlowupMap M N hN k U.codes i
        ⟨Fin.append (rvObjectVolume U.object u).val (x ∘ Fin.natAdd (rvObjectArity U.object)),Set.mem_univ _⟩).val =
        (@oldVolumeParameterBlowupMap M N hN k B.real i
          ⟨Fin.append v (x ∘ Fin.natAdd (rvObjectArity U.object)),Set.mem_univ _⟩).val := by
      rw [huv]
      rfl
    exact hp.trans hg
  · intro hxy
    obtain ⟨hx,u,hu,hg⟩ := hE.mp hxy
    apply (F.elementary_row_volume_formula i z hz x y).mpr
    refine ⟨(hD x).mpr hx,(rvObjectVolume U.object u).val,?_,hg⟩
    apply (gammaSchemaRepresents_volume U F z hF _ _).mpr
    exact ⟨u,hu,rfl⟩

end IntegrationInACVF.Section6
