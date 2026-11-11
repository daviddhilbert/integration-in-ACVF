import IntegrationSection3ACVF.OpenCompleteTypeAtomicity
import IntegrationSection3ACVF.OpenImages

/-! Lemma 3.15 over real/Gamma bases, for proper open balls of arbitrary
radius in a possibly undefinable complete-type set. The full interpreted
base with old ball names is a separate remaining extension. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.CompleteTypeOpenImages

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem complete_type_not_contains_vf (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : FullBallCoset.CompleteType B A) (hsub : {x : M | iVF x} ⊆ A) : False := by
  have hz : DefinableAt B.real .vf ({iVFZero} : Set M) :=
    definableClosureAt_function_symbol B.real Fn.vfZero Fin.elim0
      (fun j => j.elim0) (fun j => j.elim0)
  have hZ : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ ({iVFZero} : Set M)} :=
    FullBaseAtomicity.OverBase.of_real
      (((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp hz).1)
  rcases hA {iVFZero} hZ with hAll | hDis
  · have h10 : iVFOne (M := M) = iVFZero := hAll (hsub (1 : VFType (M := M)).property)
    exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext h10)
  · exact Set.disjoint_left.mp hDis (hsub (0 : VFType (M := M)).property) rfl

theorem ordinary_gamma_base (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A D : Set M} (hA : FullBallCoset.CompleteType B A) (hAD : A ⊆ D)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn D f))
    (hfVF : ∀ x ∈ D, iVF (f x)) (hinj : Set.InjOn f A)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (hsub : gammaBall a α true ⊆ A) :
    PaperBalls.IsOpenBall (f '' gammaBall a α true) := by
  obtain ⟨i,hi⟩ := GammaCosetGeometry.gammaBall_coded a α
  have hiSub : BallImaginaries.underlying i ⊆ A := hi.symm ▸ hsub
  have hAtom := OpenCompleteTypeAtomicity.lemma_3_4_open_gamma_base h00 δ hδ1 B hOnly hA i a α hi hiSub
  rw [hi] at hAtom
  let C := B.adjoin (Sum.inl i)
  have hδC : FullGammaSyntax.Scalar C {δ} :=
    FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl (Set.subset_insert _ _)
  have hfC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn D f) :=
    FullBaseAtomicity.OverBase.mono hf Set.Subset.rfl (Set.subset_insert _ _)
  have hm := FullBaseAtomicity.OverBase.preimage_comp hAtom.1 (fun _ : Fin 1 => (0 : Fin 2))
  have hGraph : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (gammaBall a α true) f) := by
    apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hm hfC)
    intro z
    change (z 0 ∈ gammaBall a α true ∧ z 0 ∈ D ∧ z 1 = f (z 0)) ↔
      (z 0 ∈ gammaBall a α true ∧ z 1 = f (z 0))
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hAD (hsub h.1),h.2⟩⟩
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  rcases OpenImages.lemma_3_13 C h00 δ hδC hδ1 ho hAtom f hGraph
      (fun x hx => hfVF x (hAD (hsub hx))) with hc | hImage
  · obtain ⟨c,hc⟩ := hc
    have hOne : (gammaBall a α true).Subsingleton := by
      intro x hx y hy
      exact hinj (hsub hx) (hsub hy) ((hc x hx).trans (hc y hy).symm)
    exact (SeparationFunctions.open_infinite h00 δ hδ1 ho hOne.finite).elim
  · exact hImage.2

theorem lemma_3_15_gamma_base (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A D : Set M} (hA : FullBallCoset.CompleteType B A) (hAD : A ⊆ D)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn D f))
    (hfVF : ∀ x ∈ D, iVF (f x)) (hinj : Set.InjOn f A)
    {b : Set M} (ho : PaperBalls.IsOpenBall b) (hsub : b ⊆ A) :
    PaperBalls.IsOpenBall (f '' b) := by
  rcases ho with hVF | ⟨a,α,rfl⟩
  · exact (complete_type_not_contains_vf B hA (hVF ▸ hsub)).elim
  · exact ordinary_gamma_base B hOnly h00 δ hδ hδ1 hA hAD f hf hfVF hinj a α hsub

end IntegrationInACVF.Section3ACVF.CompleteTypeOpenImages
