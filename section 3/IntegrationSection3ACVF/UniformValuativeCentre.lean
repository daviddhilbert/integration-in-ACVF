import IntegrationSection3ACVF.OrdinaryCentreFibres
import IntegrationSection3ACVF.AtomicCanonicalRegions

/-! Constancy of the valuative centre on the canonical positive regions
of an atomic set. Finite ordinary values become individually definable
over the unchanged base; infinity is handled as a separate actual value. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.UniformValuativeCentre

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem uniform_centre (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    {i j : BallImaginaries.Ball M}
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (hj : BallImaginaries.underlying j ∈ F ∧
      (region F (BallImaginaries.underlying j)).Nonempty ∧ region F (BallImaginaries.underlying j) ⊆ A)
    {c d : Values.GammaTop (M := M)}
    (hc : PaperBalls.HasValuativeCentre (BallImaginaries.underlying i) c)
    (hd : PaperBalls.HasValuativeCentre (BallImaginaries.underlying j) d) : c = d := by
  classical
  let U := BallImaginaries.underlying (M := M)
  let T := {k | U k ∈ F ∧ (region F (U k)).Nonempty ∧ region F (U k) ⊆ A}
  have hT : FullBaseAtomicity.Family B T :=
    CanonicalRegions.positive_family_definable B δ hδ hA hF
  have hfinite : T.Finite :=
    (F.finite_toSet.preimage BallImaginaries.underlying_injective.injOn).subset (fun _ h => h.1)
  have hall (k : BallImaginaries.Ball M) (hk : k ∈ T) (γ : Values.Gamma (M := M))
      (hγ : PaperBalls.HasValuativeCentre (U k) γ.val) :
      ∀ l ∈ T, PaperBalls.HasValuativeCentre (U l) γ.val := by
    have hnamed := OrdinaryCentreFibres.value_definable B T hT hfinite hk γ hγ
    have hP := OrdinaryCentreFibres.parent_test_definable B γ hnamed
    have h := AtomicCanonicalRegions.uniform_property B δ hδ hA hAtomic hF _ hP
    rcases h with h | h
    · exact h
    · exact (Set.disjoint_left.mp h hk hγ).elim
  by_cases hc_inf : c = Values.infinity
  · by_cases hd_inf : d = Values.infinity
    · exact hc_inf.trans hd_inf.symm
    · exact ValuativeCentreGeometry.valuativeCentre_unique
        (BallImaginaries.underlying_subset_vf i)
        (encodedBall_nonempty (BallCodeGeometry.underlying_isBall i)) hc
        (hall j hj ⟨d,hd_inf⟩ hd i hi)
  · exact ValuativeCentreGeometry.valuativeCentre_unique
      (BallImaginaries.underlying_subset_vf j)
      (encodedBall_nonempty (BallCodeGeometry.underlying_isBall j))
      (hall i hi ⟨c,hc_inf⟩ hc j hj) hd

theorem exists_common_centre (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A) :
    ∃ c : Values.GammaTop (M := M), ∀ i : BallImaginaries.Ball M,
      (BallImaginaries.underlying i ∈ F ∧
        (region F (BallImaginaries.underlying i)).Nonempty ∧
          region F (BallImaginaries.underlying i) ⊆ A) →
      PaperBalls.HasValuativeCentre (BallImaginaries.underlying i) c := by
  classical
  let T := {i : BallImaginaries.Ball M | BallImaginaries.underlying i ∈ F ∧
    (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A}
  by_cases hT : T.Nonempty
  · obtain ⟨i,hi⟩ := hT
    obtain ⟨c,hc⟩ := ValuativeCentreGeometry.valuativeCentre_exists (BallCodeGeometry.underlying_isBall i)
    refine ⟨c,fun j hj => ?_⟩
    obtain ⟨d,hd⟩ := ValuativeCentreGeometry.valuativeCentre_exists (BallCodeGeometry.underlying_isBall j)
    have he := uniform_centre B δ hδ hA hAtomic hF hi hj hc hd
    rwa [he]
  · exact ⟨Values.infinity,fun j hj => (hT ⟨j,hj⟩).elim⟩

end IntegrationInACVF.Section3ACVF.UniformValuativeCentre
