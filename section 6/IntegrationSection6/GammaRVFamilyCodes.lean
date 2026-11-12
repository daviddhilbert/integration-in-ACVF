import Section5.GammaPolynomialSupport
import Section5.PolynomialPreparation
import Section5.GammaLiftRelation

/-! Finite RV codes for a Gamma-definable family of RV sets indexed by
VF tuples. Checked polynomial support supplies finitely many leading terms
whose joint values determine the whole RV row, uniformly in all RV inputs.
No saturation or finite-row hypothesis is needed for this coding step. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ}

theorem gamma_rv_family_finite_code (FBase : VFFieldBase B.real)
    (r : Point (M := M) n 0 → Point (M := M) 0 m → Prop) (hr : GammaGraphDefinable B r) :
    ∃ d : ℕ, ∃ g : Map (PresentedSet.univ (pointSpace (M := M) n 0) B.real)
        (PresentedSet.univ (pointSpace (M := M) 0 d) B.real),
      GammaGraphDefinable B (pointMapGraph g) ∧
      ∀ x y, g x = g y → ∀ z, r x.val z ↔ r y.val z := by
  obtain ⟨d,P,hP,hconst⟩ := gammaPolynomialSupportInput_of_fieldBase B FBase r hr
  let A := @PresentedSet.univ M sM (@pointSpace M sM hM n 0) B.real
  let C := @PresentedSet.univ M sM (@pointSpace M sM hM d 0) B.real
  let F := @mvPolynomialTupleMap M sM hM B.real n 0 d A P hP
  let H := @Map.comp M sM _ _ _ B.real _ _ _ (@canonicalMap M sM hM d 0 B.real C) F
  let g := @Map.comp M sM _ _ _ B.real _ _ _ (@pointLabels M sM hM B.real d (d+0)) H
  have hv (x : A) (j : Fin d) :
      (g x).val.2 j = rv (MvPolynomial.eval (vfAt x.val) (P j)) := by
    change (@pointLabels M sM hM B.real d (d+0) (H x)).val.2 j = _
    rw [@pointLabels_snd M sM hM B.real d (d+0)]
    change (canonical (F x).val).2 (Fin.castAdd 0 j) = rv (MvPolynomial.eval (vfAt x.val) (P j))
    rw [canonical_new]
    rfl
  refine ⟨d,g,(gammaLogicInput B).real_map_graph g,?_⟩
  intro x y hxy z
  apply hconst x.val y.val (Subsingleton.elim _ _) ?_ z
  intro j
  exact (hv x j).symm.trans ((congrArg (fun q => q.val.2 j) hxy).trans (hv y j))

end IntegrationInACVF.Section6
