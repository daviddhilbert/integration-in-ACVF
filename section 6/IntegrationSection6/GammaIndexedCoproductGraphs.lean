import IntegrationSection6.IndexedCoproductEquivalences
import IntegrationSection6.GammaIndexedTagGraphs

/-! The coproduct/index interchange has its full original-Gamma graph,
constructed from the two genuine RV tags and the joint source domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_indexed_coprod_equiv_graph
    (T : Set (Fin p → RV (M := M)))
    (D : (Fin p → RV (M := M)) → Set (Fin a → RV (M := M)))
    (E : (Fin p → RV (M := M)) → Set (Fin b → RV (M := M)))
    (hD : GammaSetDefinable B {u : Point (M := M) 0 (p+a) | u.2 ∈ indexedDomain T D})
    (hE : GammaSetDefinable B {u : Point (M := M) 0 (p+b) | u.2 ∈ indexedDomain T E}) :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+(1+(a+b))))
      (y : Point (M := M) 0 (1+((p+a)+(p+b)))) =>
      ∃ u : indexedDomain T (fun t => graphCoprodDomain (D t) (E t)),
        u.val = w.2 ∧ (indexedCoprodEquiv T D E u).val = y.2) := by
  let L := gammaLogicInput B
  have hNativeL : GammaGraphDefinable B (fun (u : Point (M := M) 0 (p+a))
      (q : Point (M := M) 0 (1+((p+a)+(p+b)))) => @rvLeftTag M N hN (p+a) (p+b) u.2 = q.2) := by
    apply GammaGraphDefinable.congr
      (gamma_rv_graph_from_tuple_formula (rawLeftTagGraph_definable B (p+a) (p+b)))
    intro u q
    exact rawLeftTagGraph_tuple_iff B u.2 q.2
  have hNativeR : GammaGraphDefinable B (fun (u : Point (M := M) 0 (p+b))
      (q : Point (M := M) 0 (1+((p+a)+(p+b)))) => @rvRightTag M N hN (p+b) (p+a) u.2 = q.2) := by
    apply GammaGraphDefinable.congr
      (gamma_rv_graph_from_tuple_formula (rawRightTagGraph_definable B (p+a) (p+b)))
    intro u q
    exact rawRightTagGraph_tuple_iff B u.2 q.2
  have h := L.union_graph
    (L.comp_graph (L.swap_graph (L.restrict_graph hD gamma_indexed_leftTag_graph)) hNativeL)
    (L.comp_graph (L.swap_graph (L.restrict_graph hE gamma_indexed_rightTag_graph)) hNativeR)
  apply GammaGraphDefinable.congr h
  intro w y
  change ((∃ u : Point (M := M) 0 (p+a),
      (u.2 ∈ indexedDomain T D ∧ Fin.append (indexedLeft u.2) (@rvLeftTag M N hN a b (indexedRight u.2)) = w.2) ∧
      @rvLeftTag M N hN (p+a) (p+b) u.2 = y.2) ∨
    ∃ u : Point (M := M) 0 (p+b),
      (u.2 ∈ indexedDomain T E ∧ Fin.append (indexedLeft u.2) (@rvRightTag M N hN b a (indexedRight u.2)) = w.2) ∧
      @rvRightTag M N hN (p+b) (p+a) u.2 = y.2) ↔ _
  constructor
  · rintro (⟨u,⟨hu,hw⟩,hy⟩ | ⟨u,⟨hu,hw⟩,hy⟩)
    · let t : T := ⟨indexedLeft u.2,hu.1⟩
      let x : D t.val := ⟨indexedRight u.2,hu.2⟩
      refine ⟨indexedCoprodLeft T D E t x,hw,?_⟩
      exact (indexedCoprodEquiv_left T D E t x).trans
        ((congrArg (@rvLeftTag M N hN (p+a) (p+b)) Fin.append_castAdd_natAdd).trans hy)
    · let t : T := ⟨indexedLeft u.2,hu.1⟩
      let x : E t.val := ⟨indexedRight u.2,hu.2⟩
      refine ⟨indexedCoprodRight T D E t x,hw,?_⟩
      exact (indexedCoprodEquiv_right T D E t x).trans
        ((congrArg (@rvRightTag M N hN (p+b) (p+a)) Fin.append_castAdd_natAdd).trans hy)
  · rintro ⟨u,hu,hy⟩
    rcases indexedCoprod_cases T D E u with ⟨t,x,rfl⟩ | ⟨t,x,rfl⟩
    · have hdom := ((indexedSigmaEquiv T D).symm ⟨t,x⟩).property
      exact Or.inl ⟨(Fin.elim0,Fin.append t.val x.val),⟨hdom,by
          change Fin.append t.val (@rvLeftTag M N hN a b x.val) = w.2 at hu
          simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hu⟩,
        (indexedCoprodEquiv_left T D E t x).symm.trans hy⟩
    · have hdom := ((indexedSigmaEquiv T E).symm ⟨t,x⟩).property
      exact Or.inr ⟨(Fin.elim0,Fin.append t.val x.val),⟨hdom,by
          change Fin.append t.val (@rvRightTag M N hN b a x.val) = w.2 at hu
          simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hu⟩,
        (indexedCoprodEquiv_right T D E t x).symm.trans hy⟩

end IntegrationInACVF.Section6
