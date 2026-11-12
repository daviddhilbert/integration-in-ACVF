import IntegrationSection6.GammaRVFiniteFamilyCodes
import IntegrationSection6.GammaGlobalRestriction
import Section5.GammaContraction

/-! Simultaneously prepare finitely many full Gamma RV families over a
VF base. A checked finite RV code and Gamma map preparation make every
row constant on each prepared RV-polydisc. -/
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
variable {B : Base (M := M)} {S : Set M} {n k : ℕ}

theorem gamma_prepare_finite_rv_families {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (FBase : VFFieldBase B.real) (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S n 0) (hA : GammaSetDefinable B (carrier A))
    (a : Fin k → ℕ) (r : ∀ i, Point (M := M) n 0 → Point (M := M) 0 (a i) → Prop)
    (hr : ∀ i, GammaGraphDefinable B (r i)) :
    ∃ l : ℕ, ∃ C : DefSet (M := M) S n l, ∃ T : SpecialBijection A C,
      GammaChainDefinable B T.chain ∧ IsRVPullback (carrier C) ∧
      ∀ x y : C, SameRV x.val y.val → ∀ i z,
        r i (T.inverseMap x).val z ↔ r i (T.inverseMap y).val z := by
  obtain ⟨d,g,hg,hrows⟩ := gamma_rv_finite_families_code FBase k a r hr
  let f := postcomposeRealMap (M := M) (sM := sM) (hM := hM) (B := B) (Map.id A) g hBS
  have hf := gamma_map_graph_of_global_formula f g hA (fun _ => rfl)
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have ho := uniformVerticalObstacles hs hsmall v hv
  obtain ⟨l,C,T,_,hT,hC,hfC⟩ := gamma_rvMap_preparation_at_boundary h00 v hv ho
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_fieldBase B FBase) hBS A hA f hf
    none (by intro h; cases h)
  refine ⟨l,C,T,hT,hC,?_⟩
  intro x y hxy i z
  have hv := ((sameRV_iff _ _).mp (hfC x y hxy)).2
  have hcode : g ⟨(T.inverseMap x).val,Set.mem_univ _⟩ = g ⟨(T.inverseMap y).val,Set.mem_univ _⟩ := by
    apply Subtype.ext
    apply Prod.ext (Subsingleton.elim _ _)
    exact hv
  exact hrows _ _ hcode i z

end IntegrationInACVF.Section6
