import IntegrationSection3ACVF.SaturatedBallFamilies
import IntegrationSection3ACVF.AdjoinBall

/-! Applying Lemma 3.2 to the actual identity graph of a ball family. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3ACVF.AtomicBallFamilyChoice

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem identity_graph (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T) :
    FullBaseAtomicity.OverBase B
      ((@BallPresentation.presentation M sM hM).functionPullback T id) := by
  let q := @BallPresentation.presentation M sM hM
  have he := (BallPresentation.presentation_definable (M := M) B.real).2
  have hd := FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hT (Sum.inl : Fin 4 → Fin 4 ⊕ Fin 4))
    (FullBaseAtomicity.OverBase.of_real (B := B) he)
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change ((∃ h : z ∘ Sum.inl ∈ q.codes, q.decode ⟨z ∘ Sum.inl,h⟩ ∈ T) ∧
    (∃ h : z ∘ Sum.inl ∈ q.codes, ∃ h' : z ∘ Sum.inr ∈ q.codes,
      q.decode ⟨z ∘ Sum.inl,h⟩ = q.decode ⟨z ∘ Sum.inr,h'⟩)) ↔
    (∃ h : z ∘ Sum.inl ∈ q.codes, ∃ h' : z ∘ Sum.inr ∈ q.codes,
      q.decode ⟨z ∘ Sum.inl,h⟩ ∈ T ∧ q.decode ⟨z ∘ Sum.inl,h⟩ = q.decode ⟨z ∘ Sum.inr,h'⟩)
  exact ⟨fun ⟨⟨h,ht⟩,⟨_,h',heq⟩⟩ => ⟨h,h',ht,heq⟩,
    fun ⟨h,h',ht,heq⟩ => ⟨⟨h,ht⟩,⟨h,h',heq⟩⟩⟩

theorem atomic_of_nonalgebraic (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T)
    (hdis : T.Pairwise fun i j => Disjoint (BallImaginaries.underlying i)
      (BallImaginaries.underlying j))
    {i : BallImaginaries.Ball M} (hi : i ∈ T) (hna : ¬ FullBaseAtomicity.Algebraic B i) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  exact AdjoinBall.lemma_3_2 B T id hT (identity_graph B T hT) hdis hi hna

theorem exists_atomic {κ : Cardinal} (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary = ∅)
    (hsmall : Cardinal.mk B.real < κ) (T : Set (BallImaginaries.Ball M))
    (hT : FullBaseAtomicity.Family B T) (hInf : T.Infinite)
    (hne : ∀ i ∈ T, (BallImaginaries.underlying i).Nonempty)
    (hdis : T.Pairwise fun i j => Disjoint (BallImaginaries.underlying i)
      (BallImaginaries.underlying j)) :
    ∃ i ∈ T, AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  obtain ⟨i,hi,hna⟩ := SaturatedBallFamilies.exists_nonalgebraic hs B hB hsmall T hT hInf hne hdis
  exact ⟨i,hi,atomic_of_nonalgebraic B T hT hdis hi hna⟩

end IntegrationInACVF.Section3ACVF.AtomicBallFamilyChoice
