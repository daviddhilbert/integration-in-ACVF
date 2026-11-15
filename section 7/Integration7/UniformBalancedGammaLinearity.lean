import Integration7.UniformBalancedPositionMaps
import Integration7.PreparedUnaryGammaRadiiByLabels

/-! The actual positioning map of a balanced family is Gamma-linear
on each complete old RV-labelled fibre. Its slope may depend on that
fibre, and is never asserted to be constant across the family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}

namespace UniformMixedCellPresentation
variable {A : DefSet (M := M) S 2 m}

set_option maxHeartbeats 1600000 in
theorem centre_gamma_linear_of_row
    (F : UniformMixedCellPresentation G (carrier A)) (a : A) (s : Values.Gamma (M := M))
    (hLin : IntegrationInACVF.Section3ACVF.GammaLinearity.GammaLinear
      (Cells.rawSet (Cells.first (mixedPairFibre F.parameters a))) (Cells.rawMap (F.localPosition a))
      (Cells.rawMap_vf (F.localPosition a) (Cells.first (mixedPairFibre F.parameters a))) s) :
    ∀ b c : A, F.parameters.toFun b = F.parameters.toFun a → F.parameters.toFun c = F.parameters.toFun a →
      Values.vfValueHom (F.centre c-F.centre b) = s.val*Values.vfValueHom (vfAt c.val 1-vfAt b.val 1) := by
  intro b c hb hc
  have hDomain (b : A) (hb : F.parameters.toFun b = F.parameters.toFun a) :
      vfAt b.val 1 ∈ Cells.first (mixedPairFibre F.parameters a) := by
    refine ⟨(vfAt b.val 1,vfAt b.val 0),⟨b,?_,hb⟩,rfl⟩
    funext i
    fin_cases i <;> rfl
  have hh := hLin (vfAt b.val 1) (vfAt c.val 1)
    ⟨vfAt b.val 1,hDomain b hb,rfl⟩ ⟨vfAt c.val 1,hDomain c hc,rfl⟩
  have hB : (⟨Cells.rawMap (F.localPosition a) (vfAt b.val 1).val,
      Cells.rawMap_vf _ _ _ ⟨vfAt b.val 1,hDomain b hb,rfl⟩⟩ : VFType (M := M)) =
      F.localPosition a (vfAt b.val 1) := Subtype.ext (Cells.rawMap_on _ _)
  have hC : (⟨Cells.rawMap (F.localPosition a) (vfAt c.val 1).val,
      Cells.rawMap_vf _ _ _ ⟨vfAt c.val 1,hDomain c hc,rfl⟩⟩ : VFType (M := M)) =
      F.localPosition a (vfAt c.val 1) := Subtype.ext (Cells.rawMap_on _ _)
  change Values.vfValueHom ((_ : VFType (M := M))-(_ : VFType (M := M))) = _ at hh
  rw [hB,hC] at hh
  rw [← F.centre_eq_local_position a b hb,← F.centre_eq_local_position a c hc] at hh
  exact hh

theorem balanced_centre_gamma_linear_on_parameter_fibre
    (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows) (a : A) :
    ∃ s : Values.Gamma (M := M), ∀ b c : A,
      F.parameters.toFun b = F.parameters.toFun a → F.parameters.toFun c = F.parameters.toFun a →
      Values.vfValueHom (F.centre c-F.centre b) = s.val*Values.vfValueHom (vfAt c.val 1-vfAt b.val 1) := by
  obtain ⟨r,_,_,_,_,s,hLin⟩ := hBalanced a
  exact ⟨s,F.centre_gamma_linear_of_row a s hLin⟩

theorem tail_key_source (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S)
    (p : VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) :
    ∃ a : A, p = VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a) := by
  obtain ⟨q,hq⟩ := p.property
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q
  exact ⟨a,Subtype.ext hq.symm⟩

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
