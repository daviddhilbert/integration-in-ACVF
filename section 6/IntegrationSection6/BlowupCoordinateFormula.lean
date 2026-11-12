import IntegrationSection6.BlowupRelabeling

/-! The relabeling in6.12 has the stated quotient coordinate, including
the absorbing parameter at the centre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem elementaryLift_parameter (U : RVObject (M := M) S n) (i : Fin n)
    (hnz : ∀ u : U.domain, U.value u i ≠ 0) (a : rvLift (elementary U i)) :
    (elementaryParameter U i (liftLabelProjection (elementary U i) a)).val 0 =
      tupleRV a.val.1 i /
        U.value (elementaryProjection U i (liftLabelProjection (elementary U i) a)) i := by
  have he := congrFun (liftLabelProjection_volume (elementary U i) a) i
  rw [elementary_value,blowupValue_same] at he
  exact (eq_div_iff (hnz _)).mpr he

/-- F fixes all VF coordinates and replaces the new RV volume coordinate
by rv(b)/t; this identity is valid also when b=0. -/
theorem fullFocusRelabelLift_parameter {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U : RVObject (M := M) S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
    (h : PresentsLift U A) {i : Fin n} {k : Fin U.arity}
    (D : SpecialTransformations.Section5.Focus A i k)
    (hfull : SpecialTransformations.Section5.carrier A ⊆ D.locus)
    (hnz : ∀ u : U.domain, U.value u i ≠ 0)
    (a : rvLift (fullFocusObject h D hfull hnz)) :
    let b := fullFocusRelabelLift h D hfull hnz hκ hs hsmall a
    (elementaryParameter U i (liftLabelProjection (elementary U i) b)).val 0 =
      tupleRV a.val.1 i /
        U.value (elementaryProjection U i (liftLabelProjection (elementary U i) b)) i := by
  have he := elementaryLift_parameter U i hnz
    (fullFocusRelabelLift h D hfull hnz hκ hs hsmall a)
  rw [fullFocusRelabelLift_vf] at he
  exact he

end IntegrationInACVF.Section6
