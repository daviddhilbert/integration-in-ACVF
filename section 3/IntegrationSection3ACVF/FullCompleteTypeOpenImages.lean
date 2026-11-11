import IntegrationSection3ACVF.FullOpenCompleteTypeAtomicity
import IntegrationSection3ACVF.OpenImages

/-! Lemma3.15 with arbitrary old ball parameters and arbitrary open-ball
radii in a possibly undefinable complete type. Genuine saturation and
smallness of the original real base are explicit. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullCompleteTypeOpenImages

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem lemma_3_15 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A D : Set M} (hA : FullBallCoset.CompleteType B A) (hAD : A ⊆ D)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn D f))
    (hfVF : ∀ x ∈ D, iVF (f x)) (hinj : Set.InjOn f A)
    {b : Set M} (ho : PaperBalls.IsOpenBall b) (hsub : b ⊆ A) :
    PaperBalls.IsOpenBall (f '' b) := by
  have hBall : IsBall b := by
    rcases ho with hvf | ⟨a,α,he⟩
    · exact Or.inl hvf
    · exact he.symm ▸ BallEnlargementGeometry.gammaBall_isBall a α true
  obtain ⟨i,hi⟩ := BallCodeGeometry.encodedBall_coded b hBall
  have hoI : PaperBalls.IsOpenBall (BallImaginaries.underlying i) := hi.symm ▸ ho
  have hsI : BallImaginaries.underlying i ⊆ A := hi.symm ▸ hsub
  have hAtom := FullOpenCompleteTypeAtomicity.lemma_3_4_open hκ hs B hsmall h00 δ hδ1 hA i hoI hsI
  rw [hi] at hAtom
  let C := B.adjoin (Sum.inl i)
  have hδC : FullGammaSyntax.Scalar C {δ} :=
    FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl (Set.subset_insert _ _)
  have hfC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn D f) :=
    FullBaseAtomicity.OverBase.mono hf Set.Subset.rfl (Set.subset_insert _ _)
  have hm := FullBaseAtomicity.OverBase.preimage_comp hAtom.1 (fun _ : Fin 1 => (0 : Fin 2))
  have hGraph : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn b f) := by
    apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hm hfC)
    intro z
    change (z 0 ∈ b ∧ z 0 ∈ D ∧ z 1 = f (z 0)) ↔ (z 0 ∈ b ∧ z 1 = f (z 0))
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hAD (hsub h.1),h.2⟩⟩
  rcases OpenImages.lemma_3_13 C h00 δ hδC hδ1 ho hAtom f hGraph
      (fun x hx => hfVF x (hAD (hsub hx))) with hConstant | hOpen
  · obtain ⟨c,hc⟩ := hConstant
    have hSingle : b.Subsingleton := by
      intro x hx y hy
      exact hinj (hsub hx) (hsub hy) ((hc x hx).trans (hc y hy).symm)
    exact (SeparationFunctions.open_infinite h00 δ hδ1 ho hSingle.finite).elim
  · exact hOpen.2

end IntegrationInACVF.Section3ACVF.FullCompleteTypeOpenImages
