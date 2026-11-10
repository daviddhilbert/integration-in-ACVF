import IntegrationSection3ACVF.FullBaseAtomicity

/-! Restrict a full family on the combined imaginary sort to its ball chart. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3ACVF.AdjoinBall

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def embedCode (z : Fin 4 → M) : Fin 5 → M := ![z 0,z 1,z 2,z 3,iVFZero]

theorem embedCode_compatible (z : BallPresentation.codeDomain (M := M)) :
    ∃ h : embedCode z.val ∈ ParameterPresentation.codeDomain,
      ParameterPresentation.decode ⟨embedCode z.val,h⟩ =
        Sum.inl (BallPresentation.decode z) :=
  ⟨(ParameterPresentation.encodeBall z).property,ParameterPresentation.decode_encodeBall z⟩

theorem embedCode_definable (Q : Set M) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 4) (Fin 5) Q embedCode := by
  let E := embedCode (M := M)
  have hz : @iVFZero M (CanonicalStructure.normalize (M := M)) = @iVFZero M sM :=
    @CanonicalStructure.sortZero_normalize M sM .vf
  let N := CanonicalStructure.normalize (M := M)
  have hc : @Set.DefinableFun M LRV N (Fin 4) Q (fun _ => @iVFZero M sM) := by
    rw [← hz]
    letI := N
    exact SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
  letI := N
  intro j
  fin_cases j
  · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV
  · exact hc

theorem restrict_family (B : FullBaseAtomicity.Base (M := M))
    (T : Set (ParameterPresentation.Name (M := M)))
    (hT : FullBaseAtomicity.OverBase B
      ((@ParameterPresentation.presentation M sM hM).pullback T)) :
    FullBaseAtomicity.Family B {D | Sum.inl D ∈ T} := by
  have he := embedCode_definable (M := M) B.real
  have hc := BallPresentation.codeDomain_definable (M := M) B.real
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hcompat := embedCode_compatible (M := M)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  let E := embedCode (M := M)
  letI := CanonicalStructure.normalize (M := M)
  have hd := (ImaginaryParameters.OverBase.of_real hc).inter (hT.preimage_map he) hp
  change ImaginaryParameters.OverBase (L := LRV) p B (q.pullback {D | Sum.inl D ∈ T})
  convert hd using 1
  ext z
  constructor
  · rintro ⟨hz,ht⟩
    obtain ⟨hn,heq⟩ := hcompat ⟨z,hz⟩
    change p.decode ⟨E z,hn⟩ = Sum.inl (q.decode ⟨z,hz⟩) at heq
    refine ⟨hz,hn,?_⟩
    change p.decode ⟨E z,hn⟩ ∈ T
    rw [heq]
    exact ht
  · rintro ⟨hz,hn,ht⟩
    obtain ⟨hn',heq⟩ := hcompat ⟨z,hz⟩
    change p.decode ⟨E z,hn'⟩ = Sum.inl (q.decode ⟨z,hz⟩) at heq
    refine ⟨hz,?_⟩
    change p.decode ⟨E z,hn'⟩ ∈ T at ht
    rw [heq] at ht
    exact ht

theorem restrict_relation (B : FullBaseAtomicity.Base (M := M))
    (R : ParameterPresentation.Name (M := M) → Set M)
    (hR : FullBaseAtomicity.OverBase B
      ((@ParameterPresentation.presentation M sM hM).relationPullback R)) :
    FullBaseAtomicity.Relation B (fun D => R (Sum.inl D)) := by
  have he := embedCode_definable (M := M) B.real
  have hc := BallPresentation.codeDomain_definable (M := M) B.real
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hcompat := embedCode_compatible (M := M)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  let E := embedCode (M := M)
  let F : (Fin 4 ⊕ Fin 1 → M) → (Fin 5 ⊕ Fin 1 → M) :=
    fun z => Sum.elim (E (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hmap : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 4 ⊕ Fin 1) (Fin 5 ⊕ Fin 1) B.real F := by
    letI := CanonicalStructure.normalize (M := M)
    intro j
    cases j with
    | inl j => exact (he j).comp (fun _ => Set.DefinableFun.proj LRV)
    | inr j => exact Set.DefinableFun.proj LRV
  letI := CanonicalStructure.normalize (M := M)
  have hd := (ImaginaryParameters.OverBase.of_real hc).preimage_comp
    (Sum.inl : Fin 4 → Fin 4 ⊕ Fin 1)
  have h := hd.inter (hR.preimage_map hmap) hp
  change ImaginaryParameters.OverBase (L := LRV) p B
    (q.relationPullback (fun D => R (Sum.inl D)))
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz,hr⟩
    obtain ⟨hn,heq⟩ := hcompat ⟨z ∘ Sum.inl,hz⟩
    change p.decode ⟨E (z ∘ Sum.inl),hn⟩ = Sum.inl (q.decode ⟨z ∘ Sum.inl,hz⟩) at heq
    refine ⟨hz,hn,?_⟩
    change z (.inr 0) ∈ R (p.decode ⟨E (z ∘ Sum.inl),hn⟩)
    rw [heq]
    exact hr
  · rintro ⟨hz,hn,hr⟩
    obtain ⟨hn',heq⟩ := hcompat ⟨z ∘ Sum.inl,hz⟩
    change p.decode ⟨E (z ∘ Sum.inl),hn'⟩ = Sum.inl (q.decode ⟨z ∘ Sum.inl,hz⟩) at heq
    refine ⟨hz,?_⟩
    change z (.inr 0) ∈ R (p.decode ⟨E (z ∘ Sum.inl),hn'⟩) at hr
    rw [heq] at hr
    exact hr

abbrev AtomicOver (B : FullBaseAtomicity.Base (M := M)) (A : Set M) : Prop :=
  @ImaginaryParameters.IsAtomicOver LRV M (CanonicalStructure.normalize (M := M))
    (ParameterPresentation.Name (M := M)) (Fin 5)
    (@ParameterPresentation.presentation M sM hM) B A

/-- Lemma 3.2 expressed as atomicity over the exact interpreted base with
the input-ball name adjoined. The base can already contain arbitrary actual
Gamma and ball names, and nonalgebraicity concerns the output-ball name. -/
theorem lemma_3_2 (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (f : BallImaginaries.Ball M → BallImaginaries.Ball M)
    (hT : FullBaseAtomicity.Family B T)
    (hf : FullBaseAtomicity.OverBase B
      ((@BallPresentation.presentation M sM hM).functionPullback T f))
    (hdis : T.Pairwise fun i j => Disjoint (BallImaginaries.underlying (f i))
      (BallImaginaries.underlying (f j)))
    {i : BallImaginaries.Ball M} (hi : i ∈ T) (hna : ¬ FullBaseAtomicity.Algebraic B (f i)) :
    AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying (f i)) := by
  have hat := FullBaseAtomicity.lemma_3_2 B T f hT hf hdis hi hna
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
    have h := restrict_family B' {Sum.inl i} hn
    convert h using 1
    ext D
    simp only [Set.mem_singleton_iff,Set.mem_setOf_eq,Sum.inl.injEq]
  obtain ⟨C,hC,hCi⟩ := hat.1
  have hCm : FullBaseAtomicity.Relation B' C := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.mono hC Set.Subset.rfl
      (Set.subset_insert (Sum.inl i) B.imaginary)
  have hd : FullBaseAtomicity.OverBase B'
      {z : Fin 1 → M | ∃ D ∈ ({i} : Set (BallImaginaries.Ball M)), z 0 ∈ C D} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.range
      (ImaginaryBaseFamilies.Relation.restrict hp.1 hIndex hCm)
  letI := CanonicalStructure.normalize (M := M)
  change ImaginaryParameters.IsAtomicOver (L := LRV) p B' (U (f i))
  refine ⟨?_,?_⟩
  · convert hd using 1
    ext z
    change z 0 ∈ U (f i) ↔ ∃ D, D = i ∧ z 0 ∈ C D
    rw [← hCi]
    exact ⟨fun hz => ⟨i,rfl,hz⟩,fun ⟨D,rfl,hz⟩ => hz⟩
  · intro S hS
    obtain ⟨R,hR,hRi⟩ := (ImaginaryParameters.with_iff_over_adjoin hp (Sum.inl i) S).mpr hS
    have hr := @restrict_relation M sM hM B R hR
    exact hat.2 S ⟨(fun D => R (Sum.inl D)),hr,hRi⟩

end IntegrationInACVF.Section3ACVF.AdjoinBall
