import IntegrationSection3ACVF.AdjoinGamma
import Section3.GammaBaseTools

/-! Identify the predecessor's actual Gamma-named base with the Gamma-only
instance of the sequel's combined interpreted base. No real representative
is added to either base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaBaseBridge

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def fullBase (G : GammaParameters.Base (M := M)) : FullBaseAtomicity.Base (M := M) :=
  ⟨G.real, (Sum.inr : Values.Gamma (M := M) → ParameterPresentation.Name (M := M)) '' G.gamma⟩

theorem decode_eq_inr_iff (c : ParameterPresentation.codeDomain (M := M))
    (γ : Values.Gamma (M := M)) :
    ParameterPresentation.decode c = Sum.inr γ ↔ c.val 4 ≠ iVFZero ∧ codeValue (c.val 0) = γ := by
  by_cases h : c.val 4 = iVFZero
  · simp only [ParameterPresentation.decode,dif_pos h,Sum.inl_ne_inr,false_iff,not_and]
    exact fun hn => (hn h).elim
  · rw [ParameterPresentation.decode,dif_neg h]
    exact ⟨fun he => ⟨h,Sum.inr.inj he⟩,fun he => congrArg Sum.inr he.2⟩

theorem relation_withTuple (S : Set M) {k n : ℕ} {sn : Fin n → SortTag}
    (R : GammaParameters.Relation (M := M) S k n sn) (γ : Fin k → Values.Gamma (M := M)) :
    @ImaginaryParameters.WithTuple LRV M (CanonicalStructure.normalize (M := M))
      (ParameterPresentation.Name (M := M)) (Fin 5)
      (@ParameterPresentation.presentation M sM hM) S (Fin k) (Fin n)
      (fun i => Sum.inr (γ i)) (R.fibre γ) := by
  let p := @ParameterPresentation.presentation M sM hM
  let F : (Fin k → ParameterPresentation.Name (M := M)) → Set (Fin n → M) :=
    fun names => {b | ∃ δ : Fin k → Values.Gamma (M := M),
      (∀ i, names i = Sum.inr (δ i)) ∧ b ∈ R.fibre δ}
  refine ⟨F,?_,?_⟩
  · let N := @CanonicalStructure.normalize M sM
    let ι := (Fin k × Fin 5) ⊕ Fin n
    have hz : @iVFZero M N = @iVFZero M sM := @CanonicalStructure.sortZero_normalize M sM .vf
    have hzero : @Set.DefinableFun M LRV N ι S (fun _ => @iVFZero M sM) := by
      rw [← hz]
      letI := N
      exact SpecialTransformations.DefinableConstants.constant
        (SpecialTransformations.DefinableConstants.function_symbol
          (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
    have hflags : @Set.Definable M S LRV N ι
        {z | ∀ i : Fin k, z (.inl (i,4)) ≠ @iVFZero M sM} := by
      letI := N
      convert Set.definable_iInter_of_finite (fun i : Fin k =>
        ((@Set.DefinableFun.proj M LRV N ι S (.inl (i,4))).ofPred_eq hzero).compl) using 1
      ext z
      simp only [Set.mem_iInter,Set.mem_compl_iff,Set.mem_ofPred_eq]
    let π : Fin k ⊕ Fin n → ι := Sum.elim (fun i => .inl (i,0)) Sum.inr
    have hR := @GammaParameters.Relation.definable M sM hM S k n sn R
    have hr := @Set.Definable.preimage_comp M S LRV N (Fin k ⊕ Fin n) ι π _ hR
    have hBoth := @Set.Definable.inter M S LRV N ι _ _ hflags hr
    convert hBoth using 1
    ext z
    letI := sM
    constructor
    · rintro ⟨hz,δ,hδ,hb⟩
      have hc (i : Fin k) := (decode_eq_inr_iff
        ⟨(fun j => z (.inl (i,j))),hz i⟩ (δ i)).mp (hδ i)
      have hp : Proper (fun i => z (.inl (i,0))) := by
        intro i
        exact ((hz i).resolve_left (fun h => (hc i).1 h.1)).2
      let t := ofRaw (fun i => z (.inl (i,0))) hp
      have ht : values t = δ := by
        funext i
        exact (codeValue_raw (t i)).symm.trans (hc i).2
      refine ⟨?_,?_⟩
      · simpa only [Set.mem_iInter,Set.mem_compl_iff,Set.mem_ofPred_eq] using (fun i => (hc i).1)
      · exact (R.mem_fibre_iff t δ ht (z ∘ Sum.inr)).mp hb
    · rintro ⟨hflags,hr⟩
      have hn : ∀ i : Fin k, z (.inl (i,4)) ≠ iVFZero := by
        simpa only [Set.mem_iInter,Set.mem_compl_iff,Set.mem_ofPred_eq] using hflags
      have hp : Proper (fun i => z (.inl (i,0))) := (R.proper _ hr).1
      let t := ofRaw (fun i => z (.inl (i,0))) hp
      have hcodes : ∀ i : Fin k, (fun j => z (.inl (i,j))) ∈ ParameterPresentation.codeDomain :=
        fun i => Or.inr ⟨hn i,hp i⟩
      refine ⟨hcodes,values t,?_,?_⟩
      · intro i
        exact (decode_eq_inr_iff ⟨_,hcodes i⟩ (value (t i))).mpr ⟨hn i,codeValue_raw (t i)⟩
      · exact (R.full_preimage t (z ∘ Sum.inr)).mpr hr
  · ext b
    constructor
    · rintro ⟨δ,hδ,hb⟩
      have he : δ = γ := funext (fun i => Sum.inr.inj (hδ i).symm)
      exact he ▸ hb
    · intro hb
      exact ⟨γ,fun _ => rfl,hb⟩

theorem of_gamma (G : GammaParameters.Base (M := M)) {n : ℕ} {sn : Fin n → SortTag}
    {A : Set (Fin n → M)} (hA : GammaParameters.DefinableOverBase G sn A) :
    FullBaseAtomicity.OverBase (fullBase G) A := by
  obtain ⟨k,γ,hγ,R,hRA⟩ := hA
  let names : Fin k → ParameterPresentation.Name (M := M) := fun i => Sum.inr (γ i)
  let F : Finset (ParameterPresentation.Name (M := M)) := Finset.univ.image names
  have hTuple := relation_withTuple G.real R γ
  rw [hRA] at hTuple
  refine ⟨F,?_,?_⟩
  · intro j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact ⟨γ i,hγ i,rfl⟩
  · let π : Fin k → F := fun i => ⟨names i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    have hp := ParameterPresentation.codeDomain_definable (M := M) G.real
    exact @ImaginaryParameters.WithTuple.reindex LRV M (CanonicalStructure.normalize (M := M))
      (ParameterPresentation.Name (M := M)) (Fin 5) (@ParameterPresentation.presentation M sM hM)
      G.real (Fin k) F inferInstance inferInstance (Fin n) inferInstance
      names (Subtype.val : F → ParameterPresentation.Name (M := M)) A hTuple hp π rfl

end IntegrationInACVF.Section4.GammaBaseBridge
