import IntegrationSection6.GammaActiveFocus
import IntegrationSection6.PartialFocusPartition
import IntegrationSection6.LiftComplement
import IntegrationSection6.BlowupPresentations
import IntegrationSection6.FiniteRVGeometry

/-! A partial original-Gamma focus is an actual blowup inside RV[k].
The active and complementary objects, and the result, all have finite volume.
The only cardinal bound is on the original B.real. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

structure PartialFocusStep (U : @RVFiniteObject M N S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.obj)}
    {i : Fin n} {k : Fin (rvObjectArity U.obj)} (D : Focus A i k) where
  target_finite : Map.FiniteFibres (rvObjectVolume (originalFocusObject D))
  blowup : @IntegrationInACVF.Section6.Blowup M N hN S n U.obj (originalFocusObject D)

def PartialFocusStep.target {U : @RVFiniteObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.obj)}
    {i : Fin n} {k : Fin (rvObjectArity U.obj)} {D : Focus A i k}
    (E : PartialFocusStep U D) : @RVFiniteObject M N S n :=
  ⟨originalFocusObject D,E.target_finite⟩

def gammaPartialFocusStep {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S) (U : @RVFiniteObject M N S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.obj)}
    (h : @PresentsLift M N hN S n U.obj (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U.obj)} (D : Focus A i k)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    PartialFocusStep U D := by
  have hAP := (pullback_normalize (carrier A)).mp
    (@PresentsLift.pullback M N hN S n U.obj (normalizedPointSet A) h)
  let C := focusActiveSet D
  let E := focusInactiveSet D
  let R := focusActiveRVObject h D
  let L := liftLabelLocus C
  have hc := liftLabelLocus_subset h (focusActiveSet_subset D)
  have hCP := focusActiveSet_pullback D hAP
  have hEP := focusInactiveSet_pullback D hAP
  have hp := partialFocus_source_partition D
  have hd : Disjoint (carrier C) (carrier E) := by
    apply Set.disjoint_left.mpr
    intro p hc he
    exact he.2 hc
  have hAdΓ := gammaActiveRVObject_admissible h D hκ hs hsmall hBS hA hD
  have hAd := hAdΓ.ordinary hκ hs h00 hsmall
  let eC := originalAdmissibleFocusBlowup (focusActiveRVObject_presents h D) (activeFocus D)
    (activeFocus_full D) hAd
  let eE := liftComplementIso h hp hd hCP hEP
  let eT := partialFocusRVSplit D hAP
  have hRF := @RVObject.restrict_finite_volume M N S n U.obj U.property L hc
  have hEF := hAdΓ.elementary_finite_volume hκ hs h00 hsmall hRF
  letI := N
  letI := hN
  let Q := U.obj.restrict (complement U.obj L) (complement_subset U.obj L)
  have hQF : Q.volume.FiniteFibres := U.obj.restrict_finite_volume U.property _ _
  let es : U.obj ≅ rvCoprodObject R Q := (partitionIso U.obj L hc).symm
  let et := eT.trans (rvCoprodIso eC.iso eE)
  have hTF := (finite_volume_iso et).mpr (rvCoprod_finite_volume _ _ hEF hQF)
  exact @PartialFocusStep.mk M sM hM S n U A i k D hTF
    (IntegrationInACVF.Section6.Blowup.of_split i hAd es et)

end IntegrationInACVF.Section6.FiniteRV
