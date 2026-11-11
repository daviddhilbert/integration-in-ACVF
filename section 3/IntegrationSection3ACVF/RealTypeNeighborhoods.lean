import IntegrationSection3ACVF.TypeNeighborhoodCompactness
import IntegrationSection3ACVF.OpenImageConfigurations
import IntegrationSection3ACVF.CompleteTypeOpenImages
import Section3.NormalizationSaturation

/-! The first compactness step of3.19 over an actual small real base.
The neighborhood is defined over that same base. This does not assert
the still open extension to originally named ball parameters. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.OpenImageConfigurations

namespace IntegrationInACVF.Section3ACVF.RealTypeNeighborhoods

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_neighborhood {κ : Cardinal} (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary = ∅)
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A) (a : M) (ha : a ∈ A) :
    ∃ U : Set M, a ∈ U ∧ U ⊆ A ∧
      FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
      ∀ D ⊆ U, PaperBalls.IsOpenBall D → PaperBalls.IsOpenBall (f '' D) := by
  let T : Set (Set M) := {U | FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U}}
  have hInter (ι : Type) [Finite ι] (U : ι → T) : {x | ∀ i, x ∈ (U i).val} ∈ T :=
    FullBaseAtomicity.OverBase.forall_finite (fun i => (U i).property)
  let C := TypeNeighborhoodCompactness.core T a
  have hCA : C ⊆ A := fun x hx => hx A hA ha
  have hC : FullBallCoset.CompleteType B C := by
    intro U hU
    by_cases haU : a ∈ U
    · exact Or.inl (fun x hx => hx U hU haU)
    · apply Or.inr
      apply Set.disjoint_left.mpr
      intro x hx hxU
      have hn : x ∈ Uᶜ := hx Uᶜ (FullBaseAtomicity.OverBase.compl hU) haU
      exact hn hxU
  have hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ := by
    intro i hi
    exact (Set.notMem_empty i (hB ▸ hi)).elim
  have hNoBad (q : Fin 4 → M) (hq : q ∈ bad A f) : ¬ body q ⊆ C := by
    intro hsub
    obtain ⟨ho,_,hn⟩ := (bad_iff A f q).mp hq
    exact hn (CompleteTypeOpenImages.lemma_3_15_gamma_base B hOnly h00 δ hδ hδ1
      hC hCA f hf hfVF (fun x hx y hy => hinj (hCA hx) (hCA hy)) (body_open q ho) hsub)
  let p := @ParameterPresentation.presentation M sM hM
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  have hRaw {ι : Type} [Finite ι] {D : Set (ι → M)}
      (hd : FullBaseAtomicity.OverBase B D) : @Set.Definable M B.real LRV N ι D := by
    letI := N
    exact (ImaginaryParameters.OverBase.empty_iff_real (p := p) hB).mp hd
  have hDef (U : Set M) (hU : U ∈ T) :
      @Set.Definable M B.real LRV N (Fin 4) {q | q ∈ bad A f ∧ body q ⊆ U} :=
    hRaw ((bad_definable B hA f hf).inter (subset_definable B hU))
  obtain ⟨U,hU,haU,hGood⟩ :=
    @TypeNeighborhoodCompactness.exists_neighborhood M N 4 κ hs.normalize B.real hsmall
      T hInter (bad A f) body hDef a hNoBad
  refine ⟨U ∩ A,⟨haU,ha⟩,fun _ hx => hx.2,FullBaseAtomicity.OverBase.inter hU hA,?_⟩
  intro D hD ho
  by_contra hn
  have hBall : IsBall D := by
    rcases ho with hvf | ⟨c,α,he⟩
    · exact Or.inl hvf
    · exact he.symm ▸ BallEnlargementGeometry.gammaBall_isBall c α true
  obtain ⟨i,hi⟩ := BallCodeGeometry.encodedBall_coded D hBall
  have hOpen : PaperBalls.IsOpenBall (BallImaginaries.underlying i) := hi.symm ▸ ho
  change i ∈ {i | PaperBalls.IsOpenBall (BallImaginaries.underlying i)} at hOpen
  rw [← BallKindPredicates.open_image_eq] at hOpen
  obtain ⟨q,hq,hvalid,hdecode⟩ := hOpen
  change q ∈ BallPresentation.codeDomain at hvalid
  change BallPresentation.decode ⟨q,hvalid⟩ = i at hdecode
  have hBody : body q = D := by
    rw [body_valid (⟨q,hvalid⟩ : BallPresentation.codeDomain),hdecode,hi]
  have hBad : q ∈ bad A f := (bad_iff A f q).mpr
    ⟨hq,fun x hx => (hD (hBody ▸ hx)).2,hBody.symm ▸ hn⟩
  exact hGood q hBad (fun x hx => (hD (hBody ▸ hx)).1)

end IntegrationInACVF.Section3ACVF.RealTypeNeighborhoods
