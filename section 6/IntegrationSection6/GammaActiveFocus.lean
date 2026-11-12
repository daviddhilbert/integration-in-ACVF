import IntegrationSection6.GammaFocusLoci
import IntegrationSection6.PartialFocusAdmissibility
import IntegrationSection6.GammaFiniteElementary

/-! The active locus of a partial Gamma focus is a Gamma-definable
admissible RV subobject, with finite volume whenever the source is in RV[k]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {U : @RVObject M (@CanonicalStructure.normalize M sM) S n}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n (@rvObjectArity M sM S n U)}
variable (h : @PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U (normalizedPointSet A))
variable {i : Fin n} {k : Fin (@rvObjectArity M sM S n U)} (D : Focus A i k)

theorem gamma_focusActiveSet (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    GammaSetDefinable B (carrier (focusActiveSet D)) :=
  (gammaLogicInput B).inter hA (GammaFocusDefinable.withoutZero (gammaLogicInput B) D hD).1

theorem gamma_activeFocus (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    GammaFocusDefinable B (activeFocus D) :=
  GammaFocusDefinable.restrict (gammaLogicInput B) D.withoutZero (focusActiveSet_subset D)
    (GammaFocusDefinable.withoutZero (gammaLogicInput B) D hD) (gamma_focusActiveSet D hA hD)

def gammaActiveRVObject (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) : GammaRVObject B n :=
  gammaRVObjectOfLift hBS (focusActiveRVObject h D) (by
    have hg := gamma_focusActiveSet D hA hD
    rw [normalizedPresentsLift_carrier (focusActiveRVObject_presents h D)] at hg
    exact hg)

theorem gammaActiveRVObject_admissible {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    GammaAdmissible (gammaActiveRVObject h D hBS hA hD) i := by
  let R := focusActiveRVObject h D
  have hP := focusActiveRVObject_presents h D
  have hC := gamma_focusActiveSet D hA hD
  have hF := gamma_activeFocus D hA hD
  constructor
  · intro u he
    obtain ⟨p,_,hp⟩ := @PresentsLift.representative M N hN S n R (normalizedPointSet (focusActiveSet D)) hP u
    have hv : (@rv M sM hM (p.val.1 i)).val = (gammaVolumeValue (gammaActiveRVObject h D hBS hA hD) u i).val :=
      congrArg Subtype.val ((rv_normalize _).symm.trans (congrFun hp i))
    have hz : @rv M sM hM (p.val.1 i) = (0 : RV (M := M)) :=
      Subtype.ext (hv.trans (he.trans RVOperations.zero_val.symm))
    exact (@RVOperations.rv_ne_zero M sM hM (p.val.1 i)).mpr
      (activeFocus_field_nonzero D p.val p.property) hz
  · intro u
    have ha := gamma_fullFocus_volume_algebraic hκ hs hsmall hP (activeFocus D) hC hF (activeFocus_full D) u
    obtain ⟨T,hT,hfin,hu⟩ := ha
    exact ⟨T,real_definableAtBase _ .rv T hT,hfin,hu⟩

end IntegrationInACVF.Section6
