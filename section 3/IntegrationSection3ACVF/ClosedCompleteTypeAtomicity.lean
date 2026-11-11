import IntegrationSection3ACVF.ClosedSelfCentredBallProfiles
import IntegrationSection3ACVF.SeparationFunctions

/-! Unnamed closed-ball radii over real/Gamma bases. The ambient
complete-type set need not be definable. Old ball parameters are removed
by the separate full-base finite-hitting argument. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.ClosedCompleteTypeAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem atomic_closed_of_infinite_complete_type (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A) (hinf : A.Infinite)
    (i : BallImaginaries.Ball M) (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hi : BallImaginaries.underlying i = gammaBall a α false)
    (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  apply FullBallCoset.atomicWith_to_adjoin B i _
  refine ⟨⟨BallImaginaries.underlying,?_,rfl⟩,?_⟩
  · exact FullBaseAtomicity.OverBase.of_real (BallPresentation.membership_definable B.real)
  · rintro U ⟨P,hP,hPi⟩
    have hProfile := ClosedSelfCentredBallProfiles.definable B P hP
    obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
    have hConst (x y : VFType (M := M)) (hx : x.val ∈ BallImaginaries.underlying i)
        (hy : y.val ∈ BallImaginaries.underlying i) : x.val ∈ U ↔ y.val ∈ U := by
      have hC := ClosedCompleteTypeRVProfiles.constant_on_closed_ball B hOnly hA hinf a α
        (hi ▸ hsub) (ClosedSelfCentredBallProfiles.profile P) hProfile x y (hi ▸ hx) (hi ▸ hy)
        ![iRv r.val] (fun j => by fin_cases j; exact rv_mem hM r.property)
      change ![x.val,iRv r.val] ∈ ClosedSelfCentredBallProfiles.profile P ↔
        ![y.val,iRv r.val] ∈ ClosedSelfCentredBallProfiles.profile P at hC
      rw [← hPi]
      exact (ClosedSelfCentredBallProfiles.profile_mem P i a r α hi hr x hx).symm.trans
        (hC.trans (ClosedSelfCentredBallProfiles.profile_mem P i a r α hi hr y hy))
    have ha : a.val ∈ BallImaginaries.underlying i :=
      hi.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem a α false
    by_cases haU : a.val ∈ U
    · apply Or.inl
      intro x hx
      exact (hConst a (⟨x,BallImaginaries.underlying_subset_vf i hx⟩ : VFType (M := M)) ha hx).mp haU
    · apply Or.inr
      apply Set.disjoint_left.mpr
      intro x hx hxU
      exact haU ((hConst (⟨x,BallImaginaries.underlying_subset_vf i hx⟩ : VFType (M := M)) a hx ha).mp hxU)

theorem lemma_3_4_closed_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ1 : 1 < δ)
    (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hi : BallImaginaries.underlying i = gammaBall a α false)
    (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  have hOpenInf : (gammaBall a α true).Infinite :=
    SeparationFunctions.open_infinite h00 δ hδ1 (Or.inr ⟨a,α,rfl⟩)
  have hOpenClosed : gammaBall a α true ⊆ gammaBall a α false := by
    rintro x ⟨hx,hval,_⟩
    exact ⟨hx,hval,by simp⟩
  have hInf : (BallImaginaries.underlying i).Infinite := hi.symm ▸ hOpenInf.mono hOpenClosed
  exact atomic_closed_of_infinite_complete_type B hOnly hA (hInf.mono hsub) i a α hi hsub

theorem closed_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ1 : 1 < δ)
    (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (ho : PaperBalls.IsClosedBall (BallImaginaries.underlying i))
    (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  rcases ho with hWhole | ⟨a,ha⟩ | ⟨a,α,hi⟩
  · exact FullGammaRadius.lemma_3_4_whole_field B hA i hWhole hsub
  · exact FullGammaRadius.lemma_3_4_singleton B i (ha.symm ▸ Set.subsingleton_singleton)
  · exact lemma_3_4_closed_gamma_base h00 δ hδ1 B hOnly hA i a α hi hsub

end IntegrationInACVF.Section3ACVF.ClosedCompleteTypeAtomicity
