import IntegrationSection3ACVF.RealTypeNeighborhoods

/-! The second compactness step in3.19 over a small real parameter base.
The resulting finite cover and all its pieces use the original base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RealOpenImageCovers

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def SendsOpenBalls (U : Set M) (f : M → M) : Prop :=
  ∀ D ⊆ U, PaperBalls.IsOpenBall D → PaperBalls.IsOpenBall (f '' D)

theorem finite_cover {κ : Cardinal} (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary = ∅)
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A) :
    ∃ F : Finset (Set M),
      (∀ U ∈ F, U ⊆ A ∧ FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
        SendsOpenBalls U f) ∧ (∀ a ∈ A, ∃ U ∈ F, a ∈ U) := by
  classical
  let C : Set (Set M) := {U | U ⊆ A ∧
    FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧ SendsOpenBalls U f}
  let p := @ParameterPresentation.presentation M sM hM
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  have hRaw {D : Set M}
      (hd : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ D}) :
      @Set.Definable₁ M B.real LRV N D := by
    letI := N
    exact (ImaginaryParameters.OverBase.empty_iff_real (p := p) hB).mp hd
  have hC (U : Set M) (hU : U ∈ C) : @Set.Definable₁ M B.real LRV N U := hRaw hU.2.1
  have hcover (a : M) (ha : a ∈ A) : ∃ U ∈ C, a ∈ U := by
    obtain ⟨U,haU,hUA,hU,hGood⟩ :=
      RealTypeNeighborhoods.exists_neighborhood hs B hB hsmall h00 δ hδ hδ1 hA f hf hfVF hinj a ha
    exact ⟨U,⟨hUA,hU,hGood⟩,haU⟩
  obtain ⟨F,hF,hFC,hCov⟩ := @Saturated.definable_finite_subcover M N κ
    hs.normalize B.real hsmall A (hRaw hA) C hC hcover
  exact ⟨hF.toFinset,fun U hU => hFC (hF.mem_toFinset.mp hU),
    fun a ha => let ⟨U,hU,haU⟩ := hCov a ha; ⟨U,hF.mem_toFinset.mpr hU,haU⟩⟩

end IntegrationInACVF.Section3ACVF.RealOpenImageCovers
