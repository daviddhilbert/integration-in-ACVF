import IntegrationSection3ACVF.SelfCentredBallProfiles
import IntegrationSection3ACVF.SeparationFunctions

/-! The unnamed-radius open-ball case of 3.4 over real/Gamma bases.
The ambient complete-type set need not be definable. Old ball parameters
are not included in this result's parameter scope. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.OpenCompleteTypeAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem atomic_open_of_infinite_complete_type (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A) (hinf : A.Infinite)
    (i : BallImaginaries.Ball M) (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hi : BallImaginaries.underlying i = gammaBall a α true)
    (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  apply FullBallCoset.atomicWith_to_adjoin B i _
  refine ⟨⟨BallImaginaries.underlying,?_,rfl⟩,?_⟩
  · exact FullBaseAtomicity.OverBase.of_real (BallPresentation.membership_definable B.real)
  · rintro U ⟨P,hP,hPi⟩
    have hProfile := SelfCentredBallProfiles.definable B P hP
    obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
    have hrNZ : r ≠ 0 := by
      intro hz
      have hi : Values.vfValueHom r = Values.infinity := by
        rw [hz,map_zero]
        exact Values.infinity_eq_zero.symm
      exact α.property (hr.symm.trans hi)
    have hConst (x y : VFType (M := M)) (hx : x.val ∈ BallImaginaries.underlying i)
        (hy : y.val ∈ BallImaginaries.underlying i) : x.val ∈ U ↔ y.val ∈ U := by
      have hC := CompleteTypeRVProfiles.constant_on_open_ball B hOnly hA hinf a α
        (hi ▸ hsub) (SelfCentredBallProfiles.profile P) hProfile x y (hi ▸ hx) (hi ▸ hy)
        ![iRv r.val] (fun j => by fin_cases j; exact rv_mem hM r.property)
      change ![x.val,iRv r.val] ∈ SelfCentredBallProfiles.profile P ↔
        ![y.val,iRv r.val] ∈ SelfCentredBallProfiles.profile P at hC
      rw [← hPi]
      exact (SelfCentredBallProfiles.profile_mem P i a r α hi hrNZ hr x hx).symm.trans
        (hC.trans (SelfCentredBallProfiles.profile_mem P i a r α hi hrNZ hr y hy))
    have ha : a.val ∈ BallImaginaries.underlying i :=
      hi.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem a α true
    by_cases haU : a.val ∈ U
    · apply Or.inl
      intro x hx
      exact (hConst a (⟨x,BallImaginaries.underlying_subset_vf i hx⟩ : VFType (M := M)) ha hx).mp haU
    · apply Or.inr
      apply Set.disjoint_left.mpr
      intro x hx hxU
      exact haU ((hConst (⟨x,BallImaginaries.underlying_subset_vf i hx⟩ : VFType (M := M)) a hx ha).mp hxU)

theorem lemma_3_4_open_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ1 : 1 < δ)
    (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hi : BallImaginaries.underlying i = gammaBall a α true)
    (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  have hInf : (BallImaginaries.underlying i).Infinite := by
    rw [hi]
    exact SeparationFunctions.open_infinite h00 δ hδ1 (Or.inr ⟨a,α,rfl⟩)
  exact atomic_open_of_infinite_complete_type B hOnly hA (hInf.mono hsub) i a α hi hsub

end IntegrationInACVF.Section3ACVF.OpenCompleteTypeAtomicity
