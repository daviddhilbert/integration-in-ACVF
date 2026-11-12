import IntegrationSection6.BlowupPresentations

/-! The complementary coproduct chart has the actual right-tag formula. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem coprodComplementIso_symm_labels (C R : RVObject (M := M) S n) (r : R.domain) :
    ((coprodComplementIso C R).symm.hom.map r).val = rvRightTag C.arity r.val := by
  let V := rvCoprodObject C R
  let A := complement V (rvLeftTagMap C.domain R.arity).image
  let B := (rvRightTagMap R.domain C.arity).image
  let e := rvIsoOfCarrierEq A B (V.restrict A (complement_subset V _)).volume
    (V.restrict B (fun _ h => Or.inr h)).volume (coprod_left_complement C R) (fun _ => rfl)
  have h := congrArg (fun b : B => b.val) (iso_inv_hom_apply e ((rvCoprodRightRestrictionIso C R).hom.map r))
  exact h

end IntegrationInACVF.Section6
