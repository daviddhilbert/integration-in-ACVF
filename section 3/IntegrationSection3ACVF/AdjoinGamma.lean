import IntegrationSection3ACVF.FullGammaSyntax

/-! Full invariant relations after adjoining an actual Gamma name. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.AdjoinGamma

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def embedCode (z : Fin 1 → M) : Fin 5 → M :=
  ![z 0,iVFZero,iVFZero,iVFZero,iVFOne]

theorem embedCode_compatible (z : Fin 1 → M) (hz : NonzeroRV (z 0)) :
    ∃ h : embedCode z ∈ ParameterPresentation.codeDomain,
      ParameterPresentation.decode ⟨embedCode z,h⟩ = Sum.inr (codeValue (z 0)) := by
  have hn : iVFOne (M := M) ≠ iVFZero := by
    intro he
    exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he)
  refine ⟨Or.inr ⟨hn,hz⟩,?_⟩
  change (if h : iVFOne = iVFZero then _ else Sum.inr (codeValue (z 0))) = _
  rw [dite_eq_right hn]

theorem embedCode_definable (Q : Set M) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 1) (Fin 5) Q embedCode := by
  let E := embedCode (M := M)
  have hz : @iVFZero M (CanonicalStructure.normalize (M := M)) = @iVFZero M sM :=
    @CanonicalStructure.sortZero_normalize M sM .vf
  have ho : @iVFOne M (CanonicalStructure.normalize (M := M)) = @iVFOne M sM :=
    @CanonicalStructure.normalize_fun M sM 0 Fn.vfOne Fin.elim0 (fun j => j.elim0)
  let N := CanonicalStructure.normalize (M := M)
  have hzero : @Set.DefinableFun M LRV N (Fin 1) Q (fun _ => @iVFZero M sM) := by
    rw [← hz]
    letI := N
    exact SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
  have hone : @Set.DefinableFun M LRV N (Fin 1) Q (fun _ => @iVFOne M sM) := by
    rw [← ho]
    letI := N
    exact SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfOne Fin.elim0 (fun j => j.elim0))
  letI := N
  intro j
  fin_cases j
  · exact Set.DefinableFun.proj LRV
  · exact hzero
  · exact hzero
  · exact hzero
  · exact hone

def vectorPullback {α : Type} (R : Values.Gamma (M := M) → Set (α → M)) :
    Set (Fin 1 ⊕ α → M) :=
  {z | NonzeroRV (z (.inl 0)) ∧ z ∘ Sum.inr ∈ R (codeValue (z (.inl 0)))}

theorem restrict_vector {α : Type} [Finite α] (B : FullBaseAtomicity.Base (M := M))
    (R : ParameterPresentation.Name (M := M) → Set (α → M))
    (hR : FullBaseAtomicity.OverBase B
      (ImaginaryParameters.vectorPullback (@ParameterPresentation.presentation M sM hM) R)) :
    FullBaseAtomicity.OverBase B (vectorPullback (fun γ => R (Sum.inr γ))) := by
  have he := embedCode_definable (M := M) B.real
  have hcode : FullBaseAtomicity.OverBase B
      {a : Fin 1 → M | NonzeroRV (a 0)} :=
    FullBaseAtomicity.OverBase.of_real (B := B)
      (nonzero_codes_normalized_definable (M := M) B.real)
  have hcompat := embedCode_compatible (M := M)
  let E := embedCode (M := M)
  let d := @ParameterPresentation.decode M sM hM
  let F : (Fin 1 ⊕ α → M) → (Fin 5 ⊕ α → M) :=
    fun z => Sum.elim (E (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hmap : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 1 ⊕ α) (Fin 5 ⊕ α) B.real F := by
    letI := CanonicalStructure.normalize (M := M)
    intro j
    cases j with
    | inl j => exact (he j).comp (fun _ => Set.DefinableFun.proj LRV)
    | inr j => exact Set.DefinableFun.proj LRV
  have hd := FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hcode (Sum.inl : Fin 1 → Fin 1 ⊕ α))
    (FullBaseAtomicity.OverBase.preimage_map hR hmap)
  change FullBaseAtomicity.OverBase B _
  convert hd using 1
  ext z
  constructor
  · rintro ⟨hz,hr⟩
    obtain ⟨hn,heq⟩ := hcompat (z ∘ Sum.inl) hz
    change d ⟨E (z ∘ Sum.inl),hn⟩ = Sum.inr (codeValue (z (.inl 0))) at heq
    refine ⟨hz,hn,?_⟩
    change z ∘ Sum.inr ∈ R (d ⟨E (z ∘ Sum.inl),hn⟩)
    rw [heq]
    exact hr
  · rintro ⟨hz,hn,hr⟩
    obtain ⟨hn',heq⟩ := hcompat (z ∘ Sum.inl) hz
    change d ⟨E (z ∘ Sum.inl),hn'⟩ = Sum.inr (codeValue (z (.inl 0))) at heq
    refine ⟨hz,?_⟩
    change z ∘ Sum.inr ∈ R (d ⟨E (z ∘ Sum.inl),hn'⟩) at hr
    rw [heq] at hr
    exact hr

theorem fibre_definable {α : Type} [Finite α] {B : FullBaseAtomicity.Base (M := M)}
    {R : Values.Gamma (M := M) → Set (α → M)}
    (hR : FullBaseAtomicity.OverBase B (vectorPullback R))
    (γ : Values.Gamma (M := M)) (hγ : FullGammaSyntax.Scalar B {γ}) :
    FullBaseAtomicity.OverBase B (R γ) := by
  have hn := FullBaseAtomicity.OverBase.preimage_comp hγ (Sum.inl : Fin 1 → Fin 1 ⊕ α)
  have hi := FullBaseAtomicity.OverBase.inter hn hR
  have hd := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.preimage_comp hi
      (Sum.swap : Fin 1 ⊕ α → α ⊕ Fin 1))
  convert hd using 1
  ext z
  constructor
  · intro hz
    obtain ⟨t,ht,htγ⟩ := EndpointLogic.codeValue_surjective γ
    have hnt : t ∈ Values.gammaPullback {γ} :=
      (GammaSyntax.mem_gammaPullback_iff {γ} t).mpr ⟨ht,htγ⟩
    refine ⟨![t],hnt,ht,?_⟩
    change z ∈ R (codeValue t)
    rw [htγ]
    exact hz
  · rintro ⟨c,hc,_,hz⟩
    have he : codeValue (c 0) = γ := ((GammaSyntax.mem_gammaPullback_iff {γ} (c 0)).mp hc).2
    change z ∈ R (codeValue (c 0)) at hz
    rw [he] at hz
    exact hz

end IntegrationInACVF.Section3ACVF.AdjoinGamma
