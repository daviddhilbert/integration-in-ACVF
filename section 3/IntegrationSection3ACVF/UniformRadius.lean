import IntegrationSection3ACVF.OrdinaryRadiusFibres
import IntegrationSection3ACVF.AtomicCanonicalRegions

/-! Constancy of radius on the canonical positive regions of a complete
type. Ordinary values use finite original-base Gamma images. The two
exceptional radii are separated by the checked open/closed-kind tests. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.UniformRadius

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem radius_bottom_iff (D : Set M) :
    PaperBalls.HasRadius D ⊥ ↔ D = {x | iVF x} := by
  constructor
  · rintro (⟨hD,_⟩ | ⟨a,_,h⟩ | ⟨a,γ,s,_,h⟩)
    · exact hD
    · exact (WithBot.coe_ne_bot h.symm).elim
    · exact (WithBot.coe_ne_bot h.symm).elim
  · exact fun hD => Or.inl ⟨hD,rfl⟩

theorem radius_infinity_iff (D : Set M) :
    PaperBalls.HasRadius D (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M)) ↔
      ∃ a : VFType (M := M), D = {a.val} := by
  constructor
  · rintro (⟨_,h⟩ | ⟨a,hD,_⟩ | ⟨a,γ,s,_,h⟩)
    · exact (WithBot.coe_ne_bot h).elim
    · exact ⟨a,hD⟩
    · exact (γ.property (WithBot.coe_inj.mp h).symm).elim
  · rintro ⟨a,hD⟩
    exact Or.inr (Or.inl ⟨a,hD,rfl⟩)

theorem nonordinary_cases (r : PaperBalls.Radius (M := M))
    (hn : ¬ ∃ γ : Values.Gamma (M := M), r = (↑γ.val : PaperBalls.Radius (M := M))) :
    r = ⊥ ∨ r = (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M)) := by
  cases r with
  | none => exact Or.inl rfl
  | some a =>
    by_cases ha : a = Values.infinity
    · exact Or.inr (congrArg (fun c : Values.GammaTop (M := M) => (↑c : PaperBalls.Radius (M := M))) ha)
    · exact (hn ⟨⟨a,ha⟩,rfl⟩).elim

theorem uniform_radius (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    {i j : BallImaginaries.Ball M}
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (hj : BallImaginaries.underlying j ∈ F ∧
      (region F (BallImaginaries.underlying j)).Nonempty ∧ region F (BallImaginaries.underlying j) ⊆ A)
    {r s : PaperBalls.Radius (M := M)}
    (hr : PaperBalls.HasRadius (BallImaginaries.underlying i) r)
    (hs : PaperBalls.HasRadius (BallImaginaries.underlying j) s) : r = s := by
  classical
  let U := BallImaginaries.underlying (M := M)
  let T := {k | U k ∈ F ∧ (region F (U k)).Nonempty ∧ region F (U k) ⊆ A}
  have hT : FullBaseAtomicity.Family B T :=
    CanonicalRegions.positive_family_definable B δ hδ hA hF
  have hfinite : T.Finite :=
    (F.finite_toSet.preimage BallImaginaries.underlying_injective.injOn).subset (fun _ h => h.1)
  have hall (k : BallImaginaries.Ball M) (hk : k ∈ T) (γ : Values.Gamma (M := M))
      (hγ : PaperBalls.HasRadius (U k) (↑γ.val : PaperBalls.Radius (M := M))) :
      ∀ l ∈ T, PaperBalls.HasRadius (U l) (↑γ.val : PaperBalls.Radius (M := M)) := by
    have hnamed := OrdinaryRadiusFibres.value_definable B δ hδ T hT hfinite hk γ hγ
    have hP := OrdinaryRadiusFibres.parent_test_definable B γ hnamed
    have h := AtomicCanonicalRegions.uniform_property B δ hδ hA hAtomic hF _ hP
    rcases h with h | h
    · exact h
    · exact (Set.disjoint_left.mp h hk hγ).elim
  have hspecial (k : BallImaginaries.Ball M) (hk : k ∈ T)
      (l : BallImaginaries.Ball M) (hl : l ∈ T)
      (hkbot : PaperBalls.HasRadius (U k) ⊥)
      (hlinf : PaperBalls.HasRadius (U l)
        (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M))) : False := by
    have hkVF := (radius_bottom_iff (U k)).mp hkbot
    obtain ⟨a,ha⟩ := (radius_infinity_iff (U l)).mp hlinf
    have hkOpen : PaperBalls.IsOpenBall (U k) := Or.inl hkVF
    have h := AtomicCanonicalRegions.uniform_property B δ hδ hA hAtomic hF _
      (BallKindPredicates.open_family_definable B)
    have hlOpen : PaperBalls.IsOpenBall (U l) := by
      rcases h with h | h
      · exact h hl
      · exact (Set.disjoint_left.mp h hk hkOpen).elim
    have hlClosed : PaperBalls.IsClosedBall (U l) := Or.inr (Or.inl ⟨a,ha⟩)
    have hlVF := BallRadiusGeometry.open_closed_only_vf δ hδ hlOpen hlClosed
    exact PaperBallInvariants.singleton_ne_vf a (ha.symm.trans hlVF)
  by_cases hrOrd : ∃ γ : Values.Gamma (M := M), r = (↑γ.val : PaperBalls.Radius (M := M))
  · obtain ⟨γ,hγ⟩ := hrOrd
    have hri : PaperBalls.HasRadius (U i) (↑γ.val : PaperBalls.Radius (M := M)) := by rwa [← hγ]
    exact hγ.trans (PaperBallInvariants.hasRadius_unique δ hδ (hall i hi γ hri j hj) hs)
  · by_cases hsOrd : ∃ γ : Values.Gamma (M := M), s = (↑γ.val : PaperBalls.Radius (M := M))
    · obtain ⟨γ,hγ⟩ := hsOrd
      have hsj : PaperBalls.HasRadius (U j) (↑γ.val : PaperBalls.Radius (M := M)) := by rwa [← hγ]
      exact (PaperBallInvariants.hasRadius_unique δ hδ hr (hall j hj γ hsj i hi)).trans hγ.symm
    · rcases nonordinary_cases r hrOrd with rfl | rfl <;>
        rcases nonordinary_cases s hsOrd with rfl | rfl
      · rfl
      · exact (hspecial i hi j hj hr hs).elim
      · exact (hspecial j hj i hi hs hr).elim
      · rfl

theorem exists_common_radius (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A) :
    ∃ r : PaperBalls.Radius (M := M), ∀ i : BallImaginaries.Ball M,
      (BallImaginaries.underlying i ∈ F ∧
        (region F (BallImaginaries.underlying i)).Nonempty ∧
          region F (BallImaginaries.underlying i) ⊆ A) →
      PaperBalls.HasRadius (BallImaginaries.underlying i) r := by
  classical
  let T := {i : BallImaginaries.Ball M | BallImaginaries.underlying i ∈ F ∧
    (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A}
  by_cases hT : T.Nonempty
  · obtain ⟨i,hi⟩ := hT
    obtain ⟨r,hr⟩ := PaperBallInvariants.hasRadius_exists (BallCodeGeometry.underlying_isBall i)
    refine ⟨r,fun j hj => ?_⟩
    obtain ⟨s,hs⟩ := PaperBallInvariants.hasRadius_exists (BallCodeGeometry.underlying_isBall j)
    have he := uniform_radius B δ hδ hA hAtomic hF hi hj hr hs
    rwa [he]
  · exact ⟨⊥,fun j hj => (hT ⟨j,hj⟩).elim⟩

end IntegrationInACVF.Section3ACVF.UniformRadius
