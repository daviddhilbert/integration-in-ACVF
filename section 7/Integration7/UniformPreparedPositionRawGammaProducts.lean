module

public import Integration7.UniformPreparedPositionLabelMaps

@[expose] public section

/-! The actual induced raw RV positioning bijection satisfies the
Gamma product equation with the original cell paradigms. All original
family labels are recovered from explicit suffix coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

set_option maxHeartbeats 1600000 in
theorem raw_gamma_products (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ b : A, (F.vertical.projection b).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (u : rvObjectDomain (pullbackObject P.source)) (hu : u.val (0 : Fin (1+P.sourceArity)) ≠ rv (0 : VF (M := M))) :
    ∃ b : A, ∃ r : RV (M := M),
      u.val ∘ (Fin.natAdd 1 ∘ P.sourceOldLabelIndex) = Fin.append b.val.2 (F.parameters.toFun b) ∧
      Cells.IsBalanced (mixedPairFibre F.parameters b) (F.localPosition b) r
        ((F.vertical.projection b).val.2 F.vertical.paradigm_index) ∧
      Values.vrv r*Values.vrv (show RV (M := M) from (P.rawMap u).val (0 : Fin (1+P.targetArity))) =
        Values.vrv (show RV (M := M) from u.val (0 : Fin (1+P.sourceArity)))*Values.vrv ((F.vertical.projection b).val.2 F.vertical.paradigm_index) := by
  obtain ⟨a,rfl⟩ := rawKeyImage_surjective P.source u
  have hKey : (Map.toImage (rawKeyMap P.source) a).val 0 = rv (vfAt a.val 0) := rfl
  have ha : vfAt a.val 0 ≠ 0 := fun hz => hu (hKey.trans (congrArg rv hz))
  obtain ⟨b,r,hLabels,hBal,hProduct⟩ := P.gamma_products hNonzero a ha
  refine ⟨b,r,?_,hBal,?_⟩
  · funext j
    have hOld := special_oldLabels P.sourceSpecial (P.sourceSpecial.inverseMap a) j
    have hInv := congrArg (fun z : P.source => z.val.2 (P.sourceOldLabelIndex j)) (P.sourceSpecial.apply_inverse a)
    exact (Fin.append_right _ _ _).trans (hInv.symm.trans (hOld.trans (congrFun hLabels j)))
  · have h := rvContractionMap_spec P.conjugateMap P.forwardContractible a
    have hTarget : (P.rawMap (Map.toImage (rawKeyMap P.source) a)).val (0 : Fin (1+P.targetArity)) =
        rv (vfAt (P.conjugateMap a).val 0) := congrArg
      (fun z : rvObjectDomain (pullbackObject P.target) => z.val (0 : Fin (1+P.targetArity))) h
    exact (congrArg (fun z : RV (M := M) => Values.vrv r*Values.vrv z) hTarget).trans hProduct

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
