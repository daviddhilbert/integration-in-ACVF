import IntegrationSection3ACVF.CanonicalHoles
import IntegrationSection3ACVF.FullBallCoset
import IntegrationSection3.AtomicRegions

/-! Uniform definable properties of the canonical positive regions of an
atomic set. The parameter base stays fixed; only the entire family, rather
than any one region or hole, is required to be definable over that base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.AtomicCanonicalRegions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem uniform_property (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (P : Set (BallImaginaries.Ball M)) (hP : FullBaseAtomicity.Family B P) :
    let T := {i | BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧
        region F (BallImaginaries.underlying i) ⊆ A}
    T ⊆ P ∨ Disjoint T P := by
  let U := BallImaginaries.underlying (M := M)
  let C := fun i => region F (U i)
  let T := {i | U i ∈ F ∧ (C i).Nonempty ∧ C i ⊆ A}
  have hT := CanonicalRegions.positive_family_definable B δ hδ hA hF
  have hC := CanonicalRegions.regions_definable B δ hδ hA hF
  have hb := minimal_support_encoded hF
  have hne : ∀ j ∈ T, (C j).Nonempty := fun _ hj => hj.2.1
  have hsub : ∀ j ∈ T, C j ⊆ A := fun _ hj => hj.2.2
  have hdis : T.Pairwise fun j k => Disjoint (C j) (C k) := by
    intro j hj k hk hjk
    exact regions_disjoint encodedBalls_laminar hb hj.1 hk.1
      (fun he => hjk (BallImaginaries.underlying_injective he))
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact AtomicRegions.uniform_property hp hAtomic hT hP hC hne hsub hdis

theorem unpunctured_family_definable (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A) :
    FullBaseAtomicity.Family B {i | holes F (BallImaginaries.underlying i) = ∅} := by
  classical
  let U := BallImaginaries.underlying (M := M)
  let T := {j | ∃ k, U k ∈ holes F (U j)}
  have he : Tᶜ = {j | holes F (U j) = ∅} := by
    ext j
    constructor
    · intro hn
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro b hb
      obtain ⟨k,hk⟩ := BallCodeGeometry.encodedBall_coded b
        (minimal_support_encoded hF b (mem_holes.mp hb).1)
      apply hn
      refine ⟨k,?_⟩
      change U k ∈ holes F (U j)
      rw [hk]
      exact hb
    · intro hempty
      rintro ⟨k,hk⟩
      rw [hempty] at hk
      exact Finset.not_mem_empty _ hk
  have hR := CanonicalHoles.holes_definable B δ hδ hA hF
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hc : FullBaseAtomicity.Family B Tᶜ := by
    letI := CanonicalStructure.normalize (M := M)
    exact RegionFormulas.family_compl hp hq (ImaginaryBaseFamilies.pair_domain hR)
  simpa only [he] using hc

theorem uniform_unpunctured (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    {i j : BallImaginaries.Ball M}
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (hj : BallImaginaries.underlying j ∈ F ∧
      (region F (BallImaginaries.underlying j)).Nonempty ∧ region F (BallImaginaries.underlying j) ⊆ A) :
    holes F (BallImaginaries.underlying i) = ∅ ↔ holes F (BallImaginaries.underlying j) = ∅ := by
  have h := uniform_property B δ hδ hA hAtomic hF _
    (unpunctured_family_definable B δ hδ hA hF)
  rcases h with hall | hnone
  · exact iff_of_true (hall hi) (hall hj)
  · exact iff_of_false (fun h => Set.disjoint_left.mp hnone hi h)
      (fun h => Set.disjoint_left.mp hnone hj h)

end IntegrationInACVF.Section3ACVF.AtomicCanonicalRegions
