import IntegrationSection3ACVF.CanonicalSupportFamily
import IntegrationSection3.RegionFormulas

/-! Positive regions of the canonical ball support over the original base.
The family, rather than a selected enumeration or individual component, is
definable through all real codes of the actual ball imaginaries. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.CanonicalRegions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem regions_definable (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A) :
    FullBaseAtomicity.Relation B (fun i => region F (BallImaginaries.underlying i)) := by
  let U := BallImaginaries.underlying (M := M)
  have hc : ∀ b ∈ F, ∃ k, U k = b := fun b hb =>
    BallCodeGeometry.encodedBall_coded b (minimal_support_encoded hF b hb)
  have he : RegionFormulas.regionFamily (U ⁻¹' (F : Set (Set M))) U =
      fun i => region F (U i) := funext (RegionFormulas.regionFamily_eq_region hc)
  have hT := CanonicalSupportFamily.support_family_definable B δ hδ hA hF
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hd : FullBaseAtomicity.Relation B
      (RegionFormulas.regionFamily (U ⁻¹' (F : Set (Set M))) U) := by
    letI := CanonicalStructure.normalize (M := M)
    exact RegionFormulas.regionFamily_definable hp hq
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hT
  simpa only [he] using hd

theorem positive_family_definable (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A) :
    FullBaseAtomicity.Family B {i | BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧
        region F (BallImaginaries.underlying i) ⊆ A} := by
  let U := BallImaginaries.underlying (M := M)
  have hc : ∀ b ∈ F, ∃ k, U k = b := fun b hb =>
    BallCodeGeometry.encodedBall_coded b (minimal_support_encoded hF b hb)
  have he : RegionFormulas.positiveFamily (U ⁻¹' (F : Set (Set M))) U A =
      {i | U i ∈ F ∧ (region F (U i)).Nonempty ∧ region F (U i) ⊆ A} := by
    rw [RegionFormulas.positiveFamily_eq_preimage hc A]
    rfl
  have hT := CanonicalSupportFamily.support_family_definable B δ hδ hA hF
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hd : FullBaseAtomicity.Family B
      (RegionFormulas.positiveFamily (U ⁻¹' (F : Set (Set M))) U A) := by
    letI := CanonicalStructure.normalize (M := M)
    exact RegionFormulas.positiveFamily_definable hp hq
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hT hA
  simpa only [he] using hd

/-- The canonical positive parents form a finite definable family over the
original real/Gamma/ball base. Their nonempty disjoint punctured regions
partition A. No primitive-type classification or individual definability
of a component is asserted. -/
theorem exists_definable_positive_decomposition (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (A : Set M)
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAVF : A ⊆ {x | iVF x}) :
    ∃ F G : Finset (Set M),
      MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A ∧ G ⊆ F ∧
      FullBaseAtomicity.Family B {i | BallImaginaries.underlying i ∈ G} ∧
      FullBaseAtomicity.Relation B (fun i => region F (BallImaginaries.underlying i)) ∧
      {i : BallImaginaries.Ball M | BallImaginaries.underlying i ∈ G}.Finite ∧
      (∀ b ∈ G, IsBall b ∧ (region F b).Nonempty ∧ region F b ⊆ A) ∧
      (G : Set (Set M)).Pairwise (fun b c => Disjoint (region F b) (region F c)) ∧
      A = {x | ∃ b ∈ G, x ∈ region F b} ∧
      ∀ b ∈ G, (∀ c ∈ holes F b, IsBall c ∧ c ⊂ b) ∧
        (holes F b : Set (Set M)).Pairwise Disjoint := by
  classical
  obtain ⟨F,hF,_⟩ := exists_unique_minimal_support B δ hδ A hA hAVF
  have hb := minimal_support_encoded hF
  have houtside : iRVZero (M := M) ∉ {x | iVF x} := by
    intro h
    have he : SortTag.vf = SortTag.rv :=
      CanonicalStructure.sort_unique hM h (rv_zero_mem hM)
    cases he
  have hcover := MinimalBallSupport.support_covers hF.1.2 hAVF
    (fun b h => isBall_subset_vf b (hb b h)) iRVZero houtside
  let G := F.filter fun b => (region F b).Nonempty ∧ region F b ⊆ A
  have hGF : G ⊆ F := Finset.filter_subset _ _
  refine ⟨F,G,hF,hGF,?_,regions_definable B δ hδ hA hF,?_,?_,?_,?_,?_⟩
  · simpa only [G,Finset.mem_filter] using positive_family_definable B δ hδ hA hF
  · exact G.finite_toSet.preimage BallImaginaries.underlying_injective.injOn
  · intro b h
    exact ⟨hb b (hGF h),(Finset.mem_filter.mp h).2⟩
  · exact (regions_disjoint encodedBalls_laminar hb).mono hGF
  · simpa only [G,Finset.mem_filter,and_assoc] using
      RegionFormulas.positive_regions_cover encodedBalls_laminar hb hF.1.2 hcover
  · intro b _
    exact ⟨fun c hc => ⟨hb c (mem_holes.mp hc).1,(mem_holes.mp hc).2.1⟩,
      holes_disjoint encodedBalls_laminar hb b⟩

end IntegrationInACVF.Section3ACVF.CanonicalRegions
