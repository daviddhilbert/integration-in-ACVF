import IntegrationSection3ACVF.OrdinaryRadiusFibres
import IntegrationSection3ACVF.CanonicalHoles
import IntegrationSection3ACVF.FullBallCoset
import IntegrationSection3ACVF.BallEnlargementGeometry
import IntegrationSection3ACVF.OpenBallConstancy
import IntegrationSection3.DefinableHoleRefinement
import IntegrationSection3.BallInclusionFormulas

/-! Intrinsic actual ACVF geometry. At a named ordinary radius, adjoining
all proper closed supersets of old holes gives an intrinsic finite graph.
The checked generic refinement theorem then forbids a strict enlargement
inside any canonical positive parent. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.NamedClosedHoleCut

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "U" => BallImaginaries.underlying (M := M)

def radiusClass (α : Values.Gamma (M := M)) : Set (BallImaginaries.Ball M) :=
  {k | PaperBalls.IsClosedBall (BallImaginaries.underlying k) ∧
    PaperBalls.HasRadius (BallImaginaries.underlying k) (↑α.val : PaperBalls.Radius (M := M))}

def expansion (F : Finset (Set M)) (α : Values.Gamma (M := M))
    (h p k : BallImaginaries.Ball M) : Prop :=
  BallImaginaries.underlying h ∈ F ∧ k ∈ radiusClass α ∧
    BallImaginaries.underlying h ⊆ BallImaginaries.underlying k ∧
    BallImaginaries.underlying k ⊂ BallImaginaries.underlying p

theorem radiusClass_definable (B : FullBaseAtomicity.Base (M := M))
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α}) :
    FullBaseAtomicity.Family B (radiusClass α) := by
  let D := radiusClass (M := M) α
  have hc := BallKindPredicates.closed_family_definable (M := M) B
  have hr := OrdinaryRadiusFibres.parent_test_definable B α hα
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryBaseFamilies.Family.inter hp hc hr

theorem expansion_definable (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α}) :
    FullBaseAtomicity.OverBase B
      ((ImaginaryParameters.tuplePresentation (@BallPresentation.presentation M sM hM) (Fin 3)).pullback
        {a | expansion F α (a 0) (a 1) (a 2)}) := by
  let E := expansion (M := M) F α
  have hSource := CanonicalSupportFamily.support_family_definable B δ hδ hA hF
  have hD := radiusClass_definable B α hα
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact BallInclusionFormulas.enlargement_definable hp hq
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hSource hD

theorem additional_names_finite (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α})
    (F : Finset (Set M)) (p : BallImaginaries.Ball M) :
    {k | PunctureFormulas.transported
      (DefinableHoleRefinement.original F (BallImaginaries.underlying (M := M)))
      (expansion F α) k p}.Finite := by
  let I := {h : BallImaginaries.Ball M | DefinableHoleRefinement.original F U h p}
  have hI : I.Finite := (holes F (U p)).finite_toSet.preimage
    BallImaginaries.underlying_injective.injOn
  have hf := BallEnlargementGeometry.fixed_radius_enlargements_finite B δ hδ α hα I hI (U p)
  apply hf.subset
  rintro k ⟨h,hh,he⟩
  exact ⟨h,hh,he.2.1.1,he.2.1.2,he.2.2.1,he.2.2.2⟩

theorem no_named_closed_intermediate (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α})
    (i : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (c : Set M) (hc : c ∈ holes F (BallImaginaries.underlying i))
    (k : BallImaginaries.Ball M) (hkClosed : PaperBalls.IsClosedBall (BallImaginaries.underlying k))
    (hkRadius : PaperBalls.HasRadius (BallImaginaries.underlying k) (↑α.val : PaperBalls.Radius (M := M)))
    (hck : c ⊂ BallImaginaries.underlying k)
    (hki : BallImaginaries.underlying k ⊂ BallImaginaries.underlying i) : False := by
  let E := expansion (M := M) F α
  let T := {j : BallImaginaries.Ball M | U j ∈ F ∧
    (region F (U j)).Nonempty ∧ region F (U j) ⊆ A}
  have hb := minimal_support_encoded hF
  have hcodes : ∀ b ∈ F, ∃ j, U j = b := fun b hbF =>
    BallCodeGeometry.encodedBall_coded b (hb b hbF)
  have hUballs (j : BallImaginaries.Ball M) : IsBall (U j) := BallCodeGeometry.underlying_isBall j
  have hlam := encodedBalls_laminar (M := M)
  have hnf := encoded_avoids_finite_proper_subballs δ hδ
  have hinj := BallImaginaries.underlying_injective (M := M)
  have hSource := CanonicalSupportFamily.support_family_definable B δ hδ hA hF
  have hT := CanonicalRegions.positive_family_definable B δ hδ hA hF
  have hE := expansion_definable B δ hδ hA hF α hα
  have hEfin := additional_names_finite B δ hδ α hα F
  have hproper : ∀ h p k, DefinableHoleRefinement.original F U h p → E h p k → U k ⊂ U p :=
    fun _ _ _ _ he => he.2.2.2
  have hNew : DefinableHoleRefinement.enlarged F U E k i := by
    obtain ⟨j,hj⟩ := hcodes c (mem_holes.mp hc).1
    have hold : DefinableHoleRefinement.original F U j i := by
      change U j ∈ holes F (U i)
      rwa [hj]
    refine Or.inr ⟨j,hold,?_,⟨hkClosed,hkRadius⟩,?_,hki⟩
    · rw [hj]
      exact (mem_holes.mp hc).1
    · rw [hj]
      exact hck.1
  have hstrict := DefinableHoleRefinement.body_strict_of_hole_enlargement hlam hnf hb
    hUballs hcodes hproper i k hNew hc hck
  have hParam := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hBallCodes := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let pres := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have heq : DefinableHoleRefinement.body F U E i = region F (U i) := by
    letI := CanonicalStructure.normalize (M := M)
    exact DefinableHoleRefinement.body_eq_region hParam hBallCodes hlam hnf hb hinj
      hUballs hcodes (ImaginaryParameters.OverBase.of_real (p := pres) (B := B) hm)
      hSource hE hEfin hproper hAtomic hT (fun _ hj => hj) i hi
  exact hstrict.2 heq.symm.subset

theorem support_radius_named (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (c : Set M) (hc : c ∈ F) (α : Values.Gamma (M := M))
    (hr : PaperBalls.HasRadius c (↑α.val : PaperBalls.Radius (M := M))) :
    FullGammaSyntax.Scalar B {α} := by
  let S := U ⁻¹' (F : Set (Set M))
  have hS := CanonicalSupportFamily.support_family_definable B δ hδ hA hF
  have hfin : S.Finite := F.finite_toSet.preimage BallImaginaries.underlying_injective.injOn
  obtain ⟨j,hj⟩ := BallCodeGeometry.encodedBall_coded c (minimal_support_encoded hF c hc)
  have hjS : j ∈ S := by
    change U j ∈ F
    rwa [hj]
  have hjR : PaperBalls.HasRadius (U j) (↑α.val : PaperBalls.Radius (M := M)) := by
    rwa [hj]
  exact OrdinaryRadiusFibres.value_definable B δ hδ S hS hfin hjS α hjR

theorem no_ordinary_hole_gap (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (c : Set M) (hc : c ∈ holes F (BallImaginaries.underlying i))
    (α β : Values.Gamma (M := M))
    (hiR : PaperBalls.HasRadius (BallImaginaries.underlying i) (↑α.val : PaperBalls.Radius (M := M)))
    (hcR : PaperBalls.HasRadius c (↑β.val : PaperBalls.Radius (M := M)))
    (hαβ : α < β) : False := by
  have hα := support_radius_named B δ hδ1 hA hF (U i) hi.1 α hiR
  have hβ := support_radius_named B δ hδ1 hA hF c (mem_holes.mp hc).1 β hcR
  obtain ⟨ρ,hρ,hαρ,hρβ⟩ := (FullGammaPoint.named_samples δ hδ hδ1).2.2 α hα β hβ hαβ
  obtain ⟨a,strict,hcEq⟩ := BallEnlargementGeometry.ordinary_presentation β hcR
  obtain ⟨b,other,hiEq⟩ := BallEnlargementGeometry.ordinary_presentation α hiR
  obtain ⟨k,hkEq,hkClosed,hkRadius⟩ := BallEnlargementGeometry.closed_ball_coded a ρ
  have hck : c ⊂ U k := by
    rw [hcEq,hkEq]
    exact BallEnlargementGeometry.gammaBall_strict_enlargement a ρ β hρβ strict
  have haC : a.val ∈ c := by
    rw [hcEq]
    exact BallEnlargementGeometry.gammaBall_centre_mem a β strict
  have haI : a.val ∈ gammaBall b α other := by
    rw [← hiEq]
    exact (mem_holes.mp hc).2.1.1 haC
  have hki : U k ⊂ U i := by
    rw [hkEq,hiEq]
    exact BallEnlargementGeometry.closed_inside_parent δ hδ1 a b α ρ hαρ other haI
  exact no_named_closed_intermediate B δ hδ1 hA hAtomic hF ρ hρ i hi c hc k hkClosed hkRadius hck hki

theorem no_singleton_hole_in_ordinary_parent (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (a : VFType (M := M)) (hc : {a.val} ∈ holes F (BallImaginaries.underlying i))
    (α : Values.Gamma (M := M))
    (hiR : PaperBalls.HasRadius (BallImaginaries.underlying i) (↑α.val : PaperBalls.Radius (M := M))) : False := by
  have hα := support_radius_named B δ hδ1 hA hF (U i) hi.1 α hiR
  obtain ⟨ρ,hρ,hαρ⟩ := (FullGammaPoint.named_samples δ hδ hδ1).2.1 α hα
  obtain ⟨b,other,hiEq⟩ := BallEnlargementGeometry.ordinary_presentation α hiR
  obtain ⟨k,hkEq,hkClosed,hkRadius⟩ := BallEnlargementGeometry.closed_ball_coded a ρ
  have hck : {a.val} ⊂ U k := by
    rw [hkEq]
    exact BallEnlargementGeometry.singleton_strict_enlargement a ρ
  have haI : a.val ∈ gammaBall b α other := by
    rw [← hiEq]
    exact (mem_holes.mp hc).2.1.1 (Set.mem_singleton a.val)
  have hki : U k ⊂ U i := by
    rw [hkEq,hiEq]
    exact BallEnlargementGeometry.closed_inside_parent δ hδ1 a b α ρ hαρ other haI
  exact no_named_closed_intermediate B δ hδ1 hA hAtomic hF ρ hρ i hi {a.val} hc k hkClosed hkRadius hck hki

theorem no_hole_in_vf_parent (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (hiVF : BallImaginaries.underlying i = {x | iVF x})
    (c : Set M) (hc : c ∈ holes F (BallImaginaries.underlying i)) : False := by
  obtain ⟨r,hr⟩ := PaperBallInvariants.hasRadius_exists
    (minimal_support_encoded hF c (mem_holes.mp hc).1)
  rcases hr with ⟨hcVF,_⟩ | ⟨a,hcPoint,_⟩ | ⟨a,β,strict,hcBall,_⟩
  · have hs := (mem_holes.mp hc).2.1
    rw [hcVF,hiVF] at hs
    exact hs.2 Set.Subset.rfl
  · have hOne : FullGammaSyntax.Scalar B {(1 : Values.Gamma (M := M))} := FullGammaPoint.named_one
    obtain ⟨k,hkEq,hkClosed,hkRadius⟩ := BallEnlargementGeometry.closed_ball_coded a 1
    have hck : c ⊂ U k := by
      rw [hcPoint,hkEq]
      exact BallEnlargementGeometry.singleton_strict_enlargement a 1
    have hki : U k ⊂ U i := by
      rw [hkEq,hiVF]
      exact BallEnlargementGeometry.gammaBall_proper_in_vf δ hδ1 a 1 false
    exact no_named_closed_intermediate B δ hδ1 hA hAtomic hF 1 hOne i hi c hc k hkClosed hkRadius hck hki
  · have hcR : PaperBalls.HasRadius c (↑β.val : PaperBalls.Radius (M := M)) :=
      Or.inr (Or.inr ⟨a,β,strict,hcBall,rfl⟩)
    have hβ := support_radius_named B δ hδ1 hA hF c (mem_holes.mp hc).1 β hcR
    obtain ⟨ρ,hρ,hρβ⟩ := (FullGammaPoint.named_samples δ hδ hδ1).1 β hβ
    obtain ⟨k,hkEq,hkClosed,hkRadius⟩ := BallEnlargementGeometry.closed_ball_coded a ρ
    have hck : c ⊂ U k := by
      rw [hcBall,hkEq]
      exact BallEnlargementGeometry.gammaBall_strict_enlargement a ρ β hρβ strict
    have hki : U k ⊂ U i := by
      rw [hkEq,hiVF]
      exact BallEnlargementGeometry.gammaBall_proper_in_vf δ hδ1 a ρ false
    exact no_named_closed_intermediate B δ hδ1 hA hAtomic hF ρ hρ i hi c hc k hkClosed hkRadius hck hki

theorem no_vf_positive_parent (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A) :
    BallImaginaries.underlying i ≠ {x | iVF x} := by
  intro hiVF
  have hEmpty : holes F (BallImaginaries.underlying i) = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr (fun c hc =>
      no_hole_in_vf_parent B δ hδ hδ1 hA hAtomic hF i hi hiVF c hc)
  have hRegion : region F (BallImaginaries.underlying i) = {x | iVF x} := by
    rw [region_eq_sdiff_holes,hEmpty]
    simpa only [Finset.notMem_empty,false_and,exists_false,Set.ofPred_false,Set.sdiff_empty] using hiVF
  have hVFsub : {x | iVF x} ⊆ A := by
    rw [← hRegion]
    exact hi.2.2
  exact OpenBallConstancy.atomic_not_contains_vf B ⟨hA,hAtomic⟩ hVFsub

theorem no_hole_in_singleton_parent {F : Finset (Set M)} {A : Set M}
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i : BallImaginaries.Ball M) (a : VFType (M := M))
    (hiPoint : BallImaginaries.underlying i = {a.val}) :
    holes F (BallImaginaries.underlying i) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hcn := encodedBall_nonempty (minimal_support_encoded hF c (mem_holes.mp hc).1)
  have hsub : c ⊆ {a.val} := by
    rw [← hiPoint]
    exact (mem_holes.mp hc).2.1.1
  have he : c = {a.val} := hcn.subset_singleton_iff.mp hsub
  exact (mem_holes.mp hc).2.1.2 (hiPoint.trans he.symm).subset

theorem hole_maximal_open (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (α : Values.Gamma (M := M))
    (hiR : PaperBalls.HasRadius (BallImaginaries.underlying i) (↑α.val : PaperBalls.Radius (M := M)))
    (c : Set M) (hc : c ∈ holes F (BallImaginaries.underlying i)) :
    ∃ a b : VFType (M := M),
      BallImaginaries.underlying i = gammaBall a α false ∧ c = gammaBall b α true := by
  obtain ⟨b,parentStrict,hiBall⟩ := BallEnlargementGeometry.ordinary_presentation α hiR
  obtain ⟨r,hcR⟩ := PaperBallInvariants.hasRadius_exists
    (minimal_support_encoded hF c (mem_holes.mp hc).1)
  rcases hcR with ⟨hcVF,_⟩ | ⟨a,hcPoint,_⟩ | ⟨a,β,holeStrict,hcBall,_⟩
  · have hrev : U i ⊆ c := by
      rw [hcVF]
      exact BallImaginaries.underlying_subset_vf i
    exact ((mem_holes.mp hc).2.1.2 hrev).elim
  · rw [hcPoint] at hc
    exact (no_singleton_hole_in_ordinary_parent B δ hδ hδ1 hA hAtomic hF i hi a hc α hiR).elim
  · have hcRadius : PaperBalls.HasRadius c (↑β.val : PaperBalls.Radius (M := M)) :=
      Or.inr (Or.inr ⟨a,β,holeStrict,hcBall,rfl⟩)
    have hs : gammaBall a β holeStrict ⊂ gammaBall b α parentStrict := by
      rw [← hcBall,← hiBall]
      exact (mem_holes.mp hc).2.1
    have hαβ := BallEnlargementGeometry.gamma_radius_le_of_subset δ hδ1
      a b α β holeStrict parentStrict hs.1
    have hβα : β ≤ α := le_of_not_gt (fun hgap =>
      no_ordinary_hole_gap B δ hδ hδ1 hA hAtomic hF i hi c hc α β hiR hcRadius hgap)
    have he : α = β := le_antisymm hαβ hβα
    have hsSame : gammaBall a α holeStrict ⊂ gammaBall b α parentStrict := by rwa [← he] at hs
    have hkind := BallEnlargementGeometry.proper_same_radius_kinds a b α holeStrict parentStrict hsSame
    refine ⟨b,a,?_,?_⟩
    · rwa [hkind.2] at hiBall
    · rwa [← he,hkind.1] at hcBall

theorem punctured_parent_shape (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (hne : (holes F (BallImaginaries.underlying i)).Nonempty) :
    ∃ α : Values.Gamma (M := M), FullGammaSyntax.Scalar B {α} ∧
      ∃ a : VFType (M := M), BallImaginaries.underlying i = gammaBall a α false ∧
        ∀ c ∈ holes F (BallImaginaries.underlying i), ∃ b : VFType (M := M), c = gammaBall b α true := by
  obtain ⟨c,hc⟩ := hne
  obtain ⟨r,hiR⟩ := PaperBallInvariants.hasRadius_exists (BallCodeGeometry.underlying_isBall i)
  rcases hiR with ⟨hiVF,_⟩ | ⟨a,hiPoint,_⟩ | ⟨a,α,strict,hiBall,_⟩
  · exact (no_vf_positive_parent B δ hδ hδ1 hA hAtomic hF i hi hiVF).elim
  · have hEmpty := no_hole_in_singleton_parent hF i a hiPoint
    rw [hEmpty] at hc
    exact (Finset.notMem_empty c hc).elim
  · have hRadius : PaperBalls.HasRadius (BallImaginaries.underlying i)
        (↑α.val : PaperBalls.Radius (M := M)) := Or.inr (Or.inr ⟨a,α,strict,hiBall,rfl⟩)
    have hα := support_radius_named B δ hδ1 hA hF (BallImaginaries.underlying i) hi.1 α hRadius
    obtain ⟨a',_,hiClosed,_⟩ := hole_maximal_open B δ hδ hδ1 hA hAtomic hF i hi α hRadius c hc
    refine ⟨α,hα,a',hiClosed,?_⟩
    intro d hd
    obtain ⟨_,b,_,hb⟩ := hole_maximal_open B δ hδ hδ1 hA hAtomic hF i hi α hRadius d hd
    exact ⟨b,hb⟩

end IntegrationInACVF.Section3ACVF.NamedClosedHoleCut
