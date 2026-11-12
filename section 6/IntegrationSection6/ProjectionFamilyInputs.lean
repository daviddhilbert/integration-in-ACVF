import IntegrationSection6.VFCoordinateProjections
import IntegrationSection6.GammaCoordinateValues
import IntegrationSection6.DefinableFamilyLifts

/-! The actual total lift, reordered with any selected VF coordinates
first, is a finite-fibre family over the literal coordinate projection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n p a k : ℕ}

theorem VFCoordinateProjection.liftSplit_symm_retained (E : VFCoordinateProjection n p)
    (k : ℕ) (j : Fin p) :
    (E.liftSplit k).symm (Fin.castAdd k (E.retainedIndex j)) = Fin.castAdd (E.discarded+k) j := by
  have h := congrArg (E.liftSplit k).symm (E.liftSplit_prefix k j)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

def projectionFamilyDomain (E : VFCoordinateProjection n p) (A : Set (Point (M := M) n 0))
    (F : GammaFiniteRVSchema B n a k) : Set (Point (M := M) (p+(E.discarded+k)) a) :=
  {q | (q.1 ∘ (E.liftSplit k).symm,q.2) ∈ familyLiftDomain A F}

def projectionFamilyIso (E : VFCoordinateProjection n p) (A : Set (Point (M := M) n 0))
    (hA : GammaSetDefinable B A) (F : GammaFiniteRVSchema B n a k) :
    GammaIso B (familyLiftDomain A F) (projectionFamilyDomain E A F) :=
  gammaVFCoordinateIso (familyLiftDomain A F) (gamma_family_lift_definable A hA F) (E.liftSplit k)

theorem projectionFamily_definable (E : VFCoordinateProjection n p) (A : Set (Point (M := M) n 0))
    (hA : GammaSetDefinable B A) (F : GammaFiniteRVSchema B n a k) :
    GammaSetDefinable B (projectionFamilyDomain E A F) :=
  (projectionFamilyIso E A hA F).target_definable (gammaLogicInput B)

theorem projectionFamily_finite (E : VFCoordinateProjection n p) (A : Set (Point (M := M) n 0))
    (hA : GammaSetDefinable B A) (F : GammaFiniteRVSchema B n a k)
    (hF : ∀ x : A, F.finiteRow (fun j => (x.val.1 j).val)) :
    ∀ z : Fin (p+(E.discarded+k)) → VF (M := M),
      {r : Fin a → RV (M := M) | (z,r) ∈ projectionFamilyDomain E A F}.Finite :=
  fun z => (gammaFamilyLift A hA F hF).finiteFibres (z ∘ (E.liftSplit k).symm)

theorem projectionFamily_base (E : VFCoordinateProjection n p) (A : Set (Point (M := M) n 0))
    (F : GammaFiniteRVSchema B n a k) :
    ∀ q ∈ projectionFamilyDomain E A F, (q.1 ∘ Fin.castAdd (E.discarded+k),Fin.elim0) ∈ E.baseImage A := by
  intro q hq
  refine ⟨⟨((q.1 ∘ (E.liftSplit k).symm) ∘ Fin.castAdd k,Fin.elim0),hq.1⟩,?_⟩
  apply Prod.ext
  · funext j
    change q.1 ((E.liftSplit k).symm (Fin.castAdd k (E.retainedIndex j))) = q.1 (Fin.castAdd (E.discarded+k) j)
    rw [E.liftSplit_symm_retained]
  · rfl

theorem projectionFamilyIso_retained (E : VFCoordinateProjection n p) (A : Set (Point (M := M) n 0))
    (hA : GammaSetDefinable B A) (F : GammaFiniteRVSchema B n a k) (u : familyLiftDomain A F) (j : Fin p) :
    vfAt ((projectionFamilyIso E A hA F).equiv u).val (Fin.castAdd (E.discarded+k) j) =
      vfAt u.val (Fin.castAdd k (E.retainedIndex j)) := by
  have h := congrArg (fun q : Point (M := M) (p+(E.discarded+k)) a =>
    vfAt q (Fin.castAdd (E.discarded+k) j))
    (gammaVFCoordinateIso_value (familyLiftDomain A F) (gamma_family_lift_definable A hA F) (E.liftSplit k) u)
  exact h.trans (congrArg u.val.1 (E.liftSplit_prefix k j))

theorem projectionFamilyIso_symm_retained (E : VFCoordinateProjection n p) (A : Set (Point (M := M) n 0))
    (hA : GammaSetDefinable B A) (F : GammaFiniteRVSchema B n a k) (u : projectionFamilyDomain E A F) (j : Fin p) :
    vfAt ((projectionFamilyIso E A hA F).equiv.symm u).val (Fin.castAdd k (E.retainedIndex j)) =
      vfAt u.val (Fin.castAdd (E.discarded+k) j) := by
  have h := projectionFamilyIso_retained E A hA F ((projectionFamilyIso E A hA F).equiv.symm u) j
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end IntegrationInACVF.Section6
