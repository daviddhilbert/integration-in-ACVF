import IntegrationSection3ACVF.BallPresentation

/-!
# Combined genuine Gamma and ball names

The objects are the existing quotients. All real codes of every object are
retained. The proof of interpreted equality uses the actual ball membership
sets and the full RV value fibres, which lie in disjoint real sorts.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3ACVF.ParameterPresentation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev Name := BallImaginaries.Ball M ⊕ Values.Gamma (M := M)

def ballTuple (z : Fin 5 → M) : Fin 4 → M := fun j => z j.castSucc

def codeDomain : Set (Fin 5 → M) :=
  {z | (z 4 = iVFZero ∧ ballTuple z ∈ BallPresentation.codeDomain) ∨
    (z 4 ≠ iVFZero ∧ NonzeroRV (z 0))}

noncomputable def decode (z : codeDomain (M := M)) : Name (M := M) :=
  if h : z.val 4 = iVFZero then
    Sum.inl (BallPresentation.decode
      ⟨ballTuple z.val,(z.property.resolve_right (fun hn => hn.1 h)).2⟩)
  else Sum.inr (codeValue (z.val 0))

def encodeBall (z : BallPresentation.codeDomain (M := M)) : codeDomain (M := M) :=
  ⟨![z.val 0,z.val 1,z.val 2,z.val 3,iVFZero],Or.inl ⟨rfl,by
    have he : ballTuple ![z.val 0,z.val 1,z.val 2,z.val 3,iVFZero] = z.val := by
      funext j; fin_cases j <;> rfl
    rw [he]
    exact z.property⟩⟩

theorem decode_encodeBall (z : BallPresentation.codeDomain (M := M)) :
    decode (encodeBall z) = Sum.inl (BallPresentation.decode z) := by
  have he : ballTuple (encodeBall z).val = z.val := by
    funext j; fin_cases j <;> rfl
  simp only [decode,dif_pos (show (encodeBall z).val 4 = iVFZero from rfl)]
  congr 2
  exact Subtype.ext he

theorem decode_surjective : Function.Surjective (decode (M := M)) := by
  intro i
  cases i with
  | inl D =>
    obtain ⟨z,hz⟩ := BallPresentation.decode_surjective D
    exact ⟨encodeBall z,(decode_encodeBall z).trans (congrArg Sum.inl hz)⟩
  | inr γ =>
    obtain ⟨t,ht,htγ⟩ := EndpointLogic.codeValue_surjective γ
    have hn : iVFOne (M := M) ≠ iVFZero := by
      intro he
      exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he)
    let z : codeDomain (M := M) :=
      ⟨![t,iVFZero,iVFZero,iVFZero,iVFOne],Or.inr ⟨hn,ht⟩⟩
    refine ⟨z,?_⟩
    change (if h : iVFOne = iVFZero then _ else Sum.inr (codeValue t)) = Sum.inr γ
    rw [dif_neg hn,htγ]

noncomputable def presentation : Presentation M (Name (M := M)) (Fin 5) :=
  ⟨codeDomain,decode,decode_surjective⟩

def body : Name (M := M) → Set M :=
  Sum.elim BallImaginaries.underlying (fun γ => Values.gammaPullback {γ})

theorem gamma_membership (t x : M) (ht : NonzeroRV t) :
    x ∈ Values.gammaPullback {codeValue t} ↔ SameScalar t x := by
  constructor
  · intro hx
    have hx0 : NonzeroRV x := ⟨hx.choose,hx.choose_spec.choose⟩
    have he : codeValue x = codeValue t :=
      (gammaPullback_mem_codeValue_iff _ x hx0).mp hx
    exact ⟨ht,hx0,(original_le_codeValue_iff t x ht hx0).mpr he.symm.le,
      (original_le_codeValue_iff x t hx0 ht).mpr he.le⟩
  · intro hx
    apply (gammaPullback_mem_codeValue_iff _ x hx.2.1).mpr
    exact hx.codeValue_eq.symm

theorem body_injective : Function.Injective (body (M := M)) := by
  intro i j he
  cases i with
  | inl D =>
    cases j with
    | inl E => exact congrArg Sum.inl (BallImaginaries.underlying_injective he)
    | inr γ =>
      change BallImaginaries.underlying D = Values.gammaPullback {γ} at he
      obtain ⟨c,hc⟩ := value_surjective γ
      have hr : raw c ∈ Values.gammaPullback {γ} := ⟨raw_rv c,raw_ne_zero c,hc⟩
      have hf := BallImaginaries.underlying_subset_vf D (he.symm ▸ hr)
      exact False.elim (TypedModelMap.not_rv_of_vf hf (raw_rv c))
  | inr γ =>
    cases j with
    | inl D =>
      change Values.gammaPullback {γ} = BallImaginaries.underlying D at he
      obtain ⟨c,hc⟩ := value_surjective γ
      have hr : raw c ∈ Values.gammaPullback {γ} := ⟨raw_rv c,raw_ne_zero c,hc⟩
      have hf := BallImaginaries.underlying_subset_vf D (he ▸ hr)
      exact False.elim (TypedModelMap.not_rv_of_vf hf (raw_rv c))
    | inr δ =>
      change Values.gammaPullback {γ} = Values.gammaPullback {δ} at he
      obtain ⟨c,hc⟩ := value_surjective γ
      have hr : raw c ∈ Values.gammaPullback {γ} := ⟨raw_rv c,raw_ne_zero c,hc⟩
      have hd : raw c ∈ Values.gammaPullback {δ} := he ▸ hr
      have hd' : value c = δ := hd.choose_spec.choose_spec
      exact congrArg Sum.inr (hc.symm.trans hd')

theorem codeDomain_definable (Q : Set M) :
    @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin 5) codeDomain := by
  have hb := BallPresentation.codeDomain_definable (M := M) Q
  have hg := nonzero_codes_normalized_definable (M := M) Q
  let D := codeDomain (M := M)
  have hz : @iVFZero M (CanonicalStructure.normalize (M := M)) = @iVFZero M sM :=
    @CanonicalStructure.sortZero_normalize M sM .vf
  let N := CanonicalStructure.normalize (M := M)
  have hc : @Set.DefinableFun M LRV N (Fin 5) Q (fun _ => @iVFZero M sM) := by
    rw [← hz]
    letI := N
    exact SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
  letI := N
  have he := (@Set.DefinableFun.proj M LRV N (Fin 5) Q 4).ofPred_eq hc
  change Q.Definable LRV D
  convert (he.inter (hb.preimage_comp Fin.castSucc)).union
    (he.compl.inter (hg.preimage_comp (fun _ : Fin 1 => (0 : Fin 5)))) using 1
  ext z
  rfl

theorem membership_definable (Q : Set M) :
    @Presentation.DefinableRelation LRV M (CanonicalStructure.normalize (M := M))
      (Name (M := M)) (Fin 5) presentation Q body := by
  have hb := BallPresentation.membership_definable (M := M) Q
  have hg := same_normalized_definable (M := M) Q (n := 1)
  have hd := codeDomain_definable (M := M) Q
  let p := presentation (M := M)
  let U := body (M := M)
  let b := ballTuple (M := M)
  let UB := BallImaginaries.underlying (M := M)
  let db := @BallPresentation.decode M sM
  have hmem := gamma_membership (M := M)
  let gBody : Values.Gamma (M := M) → Set M := fun γ => Values.gammaPullback {γ}
  let gVal : M → Values.Gamma (M := M) := codeValue
  have hz : @iVFZero M (CanonicalStructure.normalize (M := M)) = @iVFZero M sM :=
    @CanonicalStructure.sortZero_normalize M sM .vf
  let N := CanonicalStructure.normalize (M := M)
  have hc : @Set.DefinableFun M LRV N (Fin 5 ⊕ Fin 1) Q (fun _ => @iVFZero M sM) := by
    rw [← hz]
    letI := N
    exact SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
  letI := N
  have he := (@Set.DefinableFun.proj M LRV N (Fin 5 ⊕ Fin 1) Q (.inl 4)).ofPred_eq hc
  have hball := hb.preimage_comp (Sum.map Fin.castSucc id)
  have hgamma := hg.preimage_comp
    (Sum.elim (fun _ : Fin 1 => (Sum.inl (0 : Fin 5) : Fin 5 ⊕ Fin 1)) Sum.inr)
  change Q.Definable LRV (p.relationPullback U)
  convert (hd.preimage_comp (Sum.inl : Fin 5 → Fin 5 ⊕ Fin 1)).inter
    ((he.inter hball).union (he.compl.inter hgamma)) using 1
  ext z
  constructor
  · rintro ⟨hc,hx⟩
    refine ⟨hc,?_⟩
    by_cases ht : z (.inl 4) = @iVFZero M sM
    · left
      have hbc := (hc.resolve_right (fun h => h.1 ht)).2
      refine ⟨ht,hbc,?_⟩
      change z (.inr 0) ∈ UB (db ⟨b (z ∘ Sum.inl),hbc⟩)
      simpa only [p,presentation,U,body,decode,Function.comp_apply,dite_eq_left ht,Sum.elim_inl] using hx
    · right
      refine ⟨ht,?_⟩
      have hproper := (hc.resolve_left (fun h => ht h.1)).2
      have hx' : z (.inr 0) ∈ gBody (gVal (z (.inl 0))) := by
        simpa only [p,presentation,U,body,decode,Function.comp_apply,dite_eq_right ht,Sum.elim_inr,Sum.elim_inl] using hx
      intro j
      fin_cases j
      exact (hmem _ _ hproper).mp hx'
  · rintro ⟨hc,hx⟩
    refine ⟨hc,?_⟩
    rcases hx with ⟨ht,hb,hx⟩ | ⟨ht,hx⟩
    · change z (.inl 4) = @iVFZero M sM at ht
      have hbc := (hc.resolve_right (fun h => h.1 ht)).2
      change z (.inr 0) ∈ UB (db ⟨b (z ∘ Sum.inl),hbc⟩) at hx
      simpa only [p,presentation,U,body,decode,Function.comp_apply,dite_eq_left ht,Sum.elim_inl] using hx
    · change z (.inl 4) ≠ @iVFZero M sM at ht
      have hproper := (hc.resolve_left (fun h => ht h.1)).2
      have hx' := (hmem _ _ hproper).mpr (hx 0)
      simpa only [p,presentation,U,body,decode,Function.comp_apply,dite_eq_right ht,Sum.elim_inr,Sum.elim_inl] using hx'

theorem presentation_definable (Q : Set M) :
    @Presentation.IsDefinable M (Name (M := M)) (Fin 5) presentation
      LRV (CanonicalStructure.normalize (M := M)) Q := by
  have hi := body_injective (M := M)
  have hc := codeDomain_definable (M := M) Q
  have hm := membership_definable (M := M) Q
  letI := CanonicalStructure.normalize (M := M)
  exact Presentation.isDefinable_of_membership _ _ hi hc hm

end IntegrationInACVF.Section3ACVF.ParameterPresentation
