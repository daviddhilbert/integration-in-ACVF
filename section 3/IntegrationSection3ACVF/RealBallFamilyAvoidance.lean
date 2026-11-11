import IntegrationSection3ACVF.RealTypeNeighborhoods
import IntegrationSection3ACVF.BallFamilyFibreDefinable

/-! Compactness for any real-base ball family whose members are atomic
when contained in a complete type. The geometric premise is explicit here;
the full ACVF consumer supplies it from checked real/Gamma ball atomicity. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.OpenImageConfigurations

namespace IntegrationInACVF.Section3ACVF.RealBallFamilyAvoidance

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finite_cover {κ : Cardinal} (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary = ∅)
    (hsmall : Cardinal.mk B.real < κ)
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T)
    (P : BallImaginaries.Ball M → Set M) (hP : FullBaseAtomicity.Relation B P)
    (hBad : ∀ i ∈ T, Splits (P i) (BallImaginaries.underlying i))
    (hAtomic : ∀ {A : Set M}, FullBallCoset.CompleteType B A →
      ∀ i ∈ T, BallImaginaries.underlying i ⊆ A →
        AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i)) :
    ∃ F : Finset (Set M),
      (∀ U ∈ F, U ⊆ {x | iVF x} ∧
        FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
        ∀ i ∈ T, ¬ BallImaginaries.underlying i ⊆ U) ∧
      ∀ a, iVF a → ∃ U ∈ F, a ∈ U := by
  classical
  let q := @BallPresentation.presentation M sM hM
  let p := @ParameterPresentation.presentation M sM hM
  let VF : Set M := {x | iVF x}
  have hVF : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ VF} :=
    FullBaseAtomicity.OverBase.of_real (((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
      (@definableAt_sort M sM B.real .vf)).1)
  let Tests : Set (Set M) := {U | FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U}}
  have hInter (ι : Type) [Finite ι] (U : ι → Tests) : {x | ∀ i, x ∈ (U i).val} ∈ Tests :=
    FullBaseAtomicity.OverBase.forall_finite (fun i => (U i).property)
  have hLocal (a : M) (ha : a ∈ VF) : ∃ U, a ∈ U ∧ U ⊆ VF ∧
      FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
      ∀ i ∈ T, ¬ BallImaginaries.underlying i ⊆ U := by
    let C := TypeNeighborhoodCompactness.core Tests a
    have hC : FullBallCoset.CompleteType B C := by
      intro U hU
      by_cases haU : a ∈ U
      · exact Or.inl (fun x hx => hx U hU haU)
      · exact Or.inr (Set.disjoint_left.mpr fun x hx hxU =>
          (hx Uᶜ (FullBaseAtomicity.OverBase.compl hU) haU) hxU)
    have hNoBad (c : Fin 4 → M) (hc : c ∈ q.pullback T) : ¬ body c ⊆ C := by
      intro hsub
      obtain ⟨hvalid,hi⟩ := hc
      let i := q.decode ⟨c,hvalid⟩
      have he : body c = BallImaginaries.underlying i := body_valid ⟨c,hvalid⟩
      have hiSub : BallImaginaries.underlying i ⊆ C := he ▸ hsub
      have hAtom := hAtomic hC i hi hiSub
      have hPi := BallFamilyFibreDefinable.fibre_definable B P hP i
      obtain ⟨x,hx,hxP,y,hy,hyP⟩ := hBad i hi
      rcases hAtom.2 (P i) hPi with hAll | hDis
      · exact hyP (hAll hy)
      · exact Set.disjoint_left.mp hDis hx hxP
    let N := @CanonicalStructure.normalize M sM
    letI := sM
    have hRaw {ι : Type} [Finite ι] {D : Set (ι → M)}
        (hd : FullBaseAtomicity.OverBase B D) : @Set.Definable M B.real LRV N ι D := by
      letI := N
      exact (ImaginaryParameters.OverBase.empty_iff_real (p := p) hB).mp hd
    have hDef (U : Set M) (hU : U ∈ Tests) :
        @Set.Definable M B.real LRV N (Fin 4) {c | c ∈ q.pullback T ∧ body c ⊆ U} :=
      hRaw (hT.inter (subset_definable B hU))
    obtain ⟨U,hU,haU,hGood⟩ := @TypeNeighborhoodCompactness.exists_neighborhood M N 4 κ
      hs.normalize B.real hsmall Tests hInter (q.pullback T) body hDef a hNoBad
    refine ⟨U ∩ VF,⟨haU,ha⟩,fun _ hx => hx.2,hU.inter hVF,?_⟩
    intro i hi hsub
    obtain ⟨c,hci⟩ := q.onto i
    have hc : c.val ∈ q.pullback T := ⟨c.property,hci.symm ▸ hi⟩
    apply hGood c.val hc
    intro x hx
    have hxI : x ∈ BallImaginaries.underlying i := by
      have hx' : x ∈ BallImaginaries.underlying (q.decode c) :=
        (Set.ext_iff.mp (body_valid c) x).mp hx
      exact hci ▸ hx'
    exact (hsub hxI).1
  let Good : Set (Set M) := {U | U ⊆ VF ∧
    FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
    ∀ i ∈ T, ¬ BallImaginaries.underlying i ⊆ U}
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  have hRaw {D : Set M} (hd : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ D}) :
      @Set.Definable₁ M B.real LRV N D := by
    letI := N
    exact (ImaginaryParameters.OverBase.empty_iff_real (p := p) hB).mp hd
  have hGood (U : Set M) (hU : U ∈ Good) : @Set.Definable₁ M B.real LRV N U := hRaw hU.2.1
  have hCov (a : M) (ha : a ∈ VF) : ∃ U ∈ Good, a ∈ U := by
    obtain ⟨U,haU,hUVF,hU,hAvoid⟩ := hLocal a ha
    exact ⟨U,⟨hUVF,hU,hAvoid⟩,haU⟩
  obtain ⟨F,hF,hFG,hCover⟩ := @Saturated.definable_finite_subcover M N κ
    hs.normalize B.real hsmall VF (hRaw hVF) Good hGood hCov
  exact ⟨hF.toFinset,fun U hU => hFG (hF.mem_toFinset.mp hU),
    fun a ha => let ⟨U,hU,haU⟩ := hCover a ha; ⟨U,hF.mem_toFinset.mpr hU,haU⟩⟩

end IntegrationInACVF.Section3ACVF.RealBallFamilyAvoidance
