import IntegrationSection3ACVF.AffineHoleGeometry
import IntegrationSection3ACVF.NamedClosedHoleCut

/-! The finite affine graph rules out two maximal open holes in a
canonical positive region. All choices occur in the geometry proof; the
graph itself is definable over the original real/Gamma/ball base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.AffineHoleCut

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "U" => @BallImaginaries.underlying M sM

theorem holes_subsingleton (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ) {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A) :
    ((holes F (BallImaginaries.underlying i) : Finset (Set M)) : Set (Set M)).Subsingleton := by
  intro c hc d hd
  by_contra hcd
  obtain ⟨α,hα,a,hia,hholes⟩ := NamedClosedHoleCut.punctured_parent_shape B δ hδ hδ1
    hA hAtomic hF i hi ⟨c,hc⟩
  have hb := minimal_support_encoded hF
  have hcodes : ∀ b ∈ F, ∃ j, U j = b := fun b hbF =>
    BallCodeGeometry.encodedBall_coded b (hb b hbF)
  obtain ⟨h,hhc⟩ := hcodes c (mem_holes.mp hc).1
  obtain ⟨l,hld⟩ := hcodes d (mem_holes.mp hd).1
  have hh : DefinableHoleRefinement.original F U h i := by
    change U h ∈ holes F (U i)
    rwa [hhc]
  have hl : DefinableHoleRefinement.original F U l i := by
    change U l ∈ holes F (U i)
    rwa [hld]
  have hne : h ≠ l := fun he => hcd (hhc.symm.trans ((congrArg U he).trans hld))
  obtain ⟨N,k,hEk,hnot⟩ := AffineHoleGeometry.exists_additional_hole B h00 δ hδ1 α hα
    F i a hia hholes h l hh hl hne
  let E := AffineHoleGeometry.expansion (M := M) F α N
  let T := {j : BallImaginaries.Ball M | U j ∈ F ∧
    (region F (U j)).Nonempty ∧ region F (U j) ⊆ A}
  have hUballs (j : BallImaginaries.Ball M) : IsBall (U j) := BallCodeGeometry.underlying_isBall j
  have hlam := encodedBalls_laminar (M := M)
  have hnf := encoded_avoids_finite_proper_subballs δ hδ1
  have hproper : ∀ h p k, DefinableHoleRefinement.original F U h p → E h p k → U k ⊂ U p :=
    fun _ _ _ _ he => he.2.2.1
  have hNew : DefinableHoleRefinement.enlarged F U E k i := Or.inr ⟨h,hh,hEk⟩
  have hstrict := DefinableHoleRefinement.body_strict hlam hnf hb hUballs hcodes
    hproper i k hNew hnot
  have hSource := CanonicalSupportFamily.support_family_definable B δ hδ1 hA hF
  have hT := CanonicalRegions.positive_family_definable B δ hδ1 hA hF
  have hE := AffineHoleGeometry.expansion_definable B δ hδ1 hA hF α hα N
  have hEfin := AffineHoleGeometry.additional_names_finite B δ hδ1 α hα F N
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hinj := BallImaginaries.underlying_injective (M := M)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have heq : DefinableHoleRefinement.body F U E i = region F (U i) := by
    letI := CanonicalStructure.normalize (M := M)
    exact DefinableHoleRefinement.body_eq_region hp hq hlam hnf hb
      hinj hUballs hcodes
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm)
      hSource hE hEfin hproper hAtomic hT (fun _ hj => hj) i hi
  exact hstrict.2 heq.symm.subset

end IntegrationInACVF.Section3ACVF.AffineHoleCut
