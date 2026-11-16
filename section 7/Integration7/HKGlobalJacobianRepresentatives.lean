import Integration7.HKGradedAEVolumeJacobians

/-! The global Jacobian operator is the actual family transform on
both zero and positive representatives. The inverse whole-space support
equivalence is compared with its canonical presentation lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
  (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))) (hφ : Function.Bijective φ)

theorem global_jacobian_zero_representative (F : ZeroVFVolumeFamily C (n+1) a) :
    aeVolumeComponentJacobianAddHom hc C φ hφ 0 (Quotient.mk _ ⟨a,F⟩) =
      Quotient.mk _ ⟨a,F.jacobianPushforward φ hφ (fun _ => Set.mem_univ _)⟩ := by
  let E := supportedVolumeComponentUnivEquiv hc C n 0
  let G : SupportedAEZeroVolumeFunction hc C (DefSet.univ _ _) :=
    Quotient.mk _ ⟨a,⟨F,fun _ => Set.mem_univ _⟩⟩
  have hG : E G=Quotient.mk _ ⟨a,F⟩ := rfl
  have hLift : E.symm (Quotient.mk _ ⟨a,F⟩)=G :=
    (congrArg E.symm hG).symm.trans (E.symm_apply_apply G)
  change supportedZeroVolumeFunctionForget hc C _ (supportedZeroVolumeFunctionJacobian hc C φ hφ
    (E.symm (Quotient.mk _ ⟨a,F⟩))) = _
  rw [hLift]
  rfl

theorem global_jacobian_positive_representative (F : SelectedVFVolumeFamily C (n+1) a k) :
    aeVolumeComponentJacobianAddHom hc C φ hφ (k+1) (Quotient.mk _ ⟨a,F⟩) =
      Quotient.mk _ ⟨a,F.jacobianPushforward φ hφ (fun _ => Set.mem_univ _)⟩ := by
  let E := supportedVolumeComponentUnivEquiv hc C n (k+1)
  let G : SupportedAERVVolumeFunction hc C (DefSet.univ _ _) k :=
    Quotient.mk _ ⟨a,⟨F,fun _ => Set.mem_univ _⟩⟩
  have hG : E G=Quotient.mk _ ⟨a,F⟩ := rfl
  have hLift : E.symm (Quotient.mk _ ⟨a,F⟩)=G :=
    (congrArg E.symm hG).symm.trans (E.symm_apply_apply G)
  change supportedVolumeFunctionForget hc C _ (supportedVolumeFunctionJacobian hc C φ hφ
    (E.symm (Quotient.mk _ ⟨a,F⟩))) = _
  rw [hLift]
  rfl

end IntegrationInACVF.Section7.HK
