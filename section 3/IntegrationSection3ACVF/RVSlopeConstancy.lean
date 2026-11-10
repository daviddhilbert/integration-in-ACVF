import IntegrationSection3ACVF.RVSlopeOrbits

/-! The RV slope is constant on each actual Gamma value fibre. Integer
orbits make every nonempty coefficient fibre infinite; the checked
finite/cofinite theorem and coefficient uniqueness force constancy. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVSlopeGraph
open IntegrationInACVF.Section3ACVF.RVSlopeFiniteCofinite

namespace IntegrationInACVF.Section3ACVF.RVSlopeConstancy

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem on_value_fibre (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (γ : Values.Gamma (M := M)) {c d : M}
    (hc : (Values.fibre (row A f c) γ).Nonempty)
    (hd : (Values.fibre (row A f d) γ).Nonempty) : c = d := by
  have hiC := RVSlopeOrbits.infinite B h00 δ hδ hδ1 ho hA f hf hfVF hinj c γ hc
  have hiD := RVSlopeOrbits.infinite B h00 δ hδ hδ1 ho hA f hf hfVF hinj d γ hd
  have hbad : {t : CanonicalRV.RVSort M | Values.vrv t = γ.val ∧ t.val ∉ row A f d}.Finite := by
    rcases finite_or_cofinite B hf d γ with h | h
    · exact (hiD h).elim
    · exact h
  obtain ⟨t,htC,htBad⟩ := (hiC.sdiff hbad).nonempty
  have htD : t.val ∈ row A f d := by
    by_contra h
    exact htBad ⟨htC.1,h⟩
  exact RVSlopeFibres.unique B h00 δ hδ hδ1 ho hA f hf hfVF hinj htC.2 htD

end IntegrationInACVF.Section3ACVF.RVSlopeConstancy
