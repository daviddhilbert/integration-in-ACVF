import IntegrationSection3ACVF.FullGammaSyntax
import IntegrationSection3ACVF.AdjoinBall
import IntegrationSection3ACVF.BallCosetAtomicity
import IntegrationSection3.ImaginaryBaseRanges

/-! Additive ball cosets over a base with genuine Gamma and ball names. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity

namespace IntegrationInACVF.Section3ACVF.FullBallCoset

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev CompleteType (B : FullBaseAtomicity.Base (M := M)) (A : Set M) : Prop :=
  @ImaginaryBaseFamilies.CompleteType LRV M (CanonicalStructure.normalize (M := M))
    (ParameterPresentation.Name (M := M)) (Fin 5)
    (@ParameterPresentation.presentation M sM hM) B A

theorem cosetRelation_definable (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))}) :
    FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ cosetRelation H} := by
  let U := Subtype.val '' (H : Set (VFType (M := M)))
  let R := @DefinableCosets.relation M sM U
  have he := @DefinableCosets.relation_normalize M sM hM U
  have hs := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  have hd : FullBaseAtomicity.OverBase B R := by
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    have hn : B.real.DefinableFun LRV (fun z : Fin 2 → M => iVFNeg (z 1)) := by
      have hf : B.real.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfNeg) :=
        Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 1 Fn.vfNeg)
      exact hf.comp (fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
    have hdiff : B.real.DefinableFun LRV (fun z : Fin 2 → M => iVFAdd (z 0) (iVFNeg (z 1))) := by
      have hf : B.real.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfAdd) :=
        Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 2 Fn.vfAdd)
      exact hf.comp (fun j => by fin_cases j; exact Set.DefinableFun.proj LRV; exact hn)
    have hu := ImaginaryParameters.OverBase.preimage_map hH (fun _ : Fin 1 => hdiff)
    have h0 := ImaginaryParameters.OverBase.preimage_comp
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hs) (fun _ : Fin 1 => (0 : Fin 2))
    have h1 := ImaginaryParameters.OverBase.preimage_comp
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hs) (fun _ : Fin 1 => (1 : Fin 2))
    have hr := ImaginaryParameters.OverBase.inter
      (ImaginaryParameters.OverBase.inter h0 h1 hp) hu hp
    change ImaginaryParameters.OverBase (L := LRV) p B R
    rw [show R = @DefinableCosets.relation M N U from he.symm]
    convert hr using 1
    ext z
    change (iVF (z 0) ∧ iVF (z 1) ∧ _) ↔ ((iVF (z 0) ∧ iVF (z 1)) ∧ _)
    tauto
  convert FullBaseAtomicity.OverBase.preimage_comp hd (![1,0] : Fin 2 → Fin 2) using 1
  ext z
  rfl

theorem cosetFamily_definable (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))}) :
    FullBaseAtomicity.Family B (cosetFamily H) := by
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hr := cosetRelation_definable B H hH
  have hs := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryBaseFamilies.rangeFamily_definable hp hq
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm)
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hs) hr

theorem atomic_coset (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))})
    {A : Set M} (hA : CompleteType B A)
    (i : BallImaginaries.Ball M) (ha : ∃ a : VFType (M := M),
      BallImaginaries.underlying i = cosetBody H a)
    (hsub : BallImaginaries.underlying i ⊆ A) :
    FullBaseAtomicity.AtomicWith B i (BallImaginaries.underlying i) := by
  let T := cosetFamily H
  let C : BallImaginaries.Ball M → Set M :=
    fun j => {x | j ∈ T ∧ x ∈ BallImaginaries.underlying j}
  have hi : i ∈ T := by
    obtain ⟨a,ha⟩ := ha
    exact ⟨a.val,a.property,ha.trans (cosetRelation_fibre H a).symm⟩
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have ht := cosetFamily_definable B H hH
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hc : FullBaseAtomicity.Relation B C := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.restrict hp ht
      (ImaginaryParameters.OverBase.of_real hm)
  have hd := cosetFamily_disjoint H
  have hdis : T.Pairwise fun j k => Disjoint (C j) (C k) := by
    intro j hj k hk hne
    exact Set.disjoint_left.mpr fun x hxj hxk =>
      Set.disjoint_left.mp (hd hj hk hne) hxj.2 hxk.2
  have hCi : C i = BallImaginaries.underlying i := by
    ext x
    exact and_iff_right hi
  have hCA : C i ⊆ A := fun x hx => hsub hx.2
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  have h := ImaginaryBaseFamilies.atomic_below_complete_type hp hq ht hc hdis hA hi hCA
  change ImaginaryBaseFamilies.AtomicWith (L := LRV) p B q i (C i) at h
  rw [hCi] at h
  exact h

theorem atomicWith_to_adjoin (B : FullBaseAtomicity.Base (M := M))
    (i : BallImaginaries.Ball M) (A : Set M) (hat : FullBaseAtomicity.AtomicWith B i A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) A := by
  let B' := B.adjoin (Sum.inl i)
  let U := BallImaginaries.underlying (M := M)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hp := ParameterPresentation.presentation_definable (M := M) B.real
  have hIndex : FullBaseAtomicity.Family B' {i} := by
    have hn : FullBaseAtomicity.OverBase B' (p.pullback {Sum.inl i}) := by
      letI := CanonicalStructure.normalize (M := M)
      exact ImaginaryParameters.OverBase.named_singleton (B := B') hp
        (Set.mem_insert (Sum.inl i) B.imaginary)
    have h := AdjoinBall.restrict_family B' {Sum.inl i} hn
    convert h using 1
    ext D
    simp only [Set.mem_singleton_iff,Set.mem_setOf_eq,Sum.inl.injEq]
  obtain ⟨C,hC,hCi⟩ := hat.1
  change C i = A at hCi
  have hCm : FullBaseAtomicity.Relation B' C := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.mono hC Set.Subset.rfl
      (Set.subset_insert (Sum.inl i) B.imaginary)
  have hd : FullBaseAtomicity.OverBase B'
      {z : Fin 1 → M | ∃ D ∈ ({i} : Set (BallImaginaries.Ball M)), z 0 ∈ C D} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.range
      (ImaginaryBaseFamilies.Relation.restrict (p := p) (B := B') (q := q) hp.1 hIndex hCm)
  letI := CanonicalStructure.normalize (M := M)
  change ImaginaryParameters.IsAtomicOver (L := LRV) p B' (A)
  refine ⟨?_,?_⟩
  · convert hd using 1
    ext z
    change z 0 ∈ A ↔ ∃ D, D = i ∧ z 0 ∈ C D
    rw [← hCi]
    constructor
    · intro hz
      exact ⟨i,rfl,hz⟩
    · rintro ⟨D,hDi,hz⟩
      rw [hDi] at hz
      exact hz
  · intro S hS
    obtain ⟨R,hR,hRi⟩ := (ImaginaryParameters.with_iff_over_adjoin hp (Sum.inl i) S).mpr hS
    have hr := @AdjoinBall.restrict_relation M sM hM B R hR
    exact hat.2 S ⟨(fun D => R (Sum.inl D)),hr,hRi⟩


end IntegrationInACVF.Section3ACVF.FullBallCoset
