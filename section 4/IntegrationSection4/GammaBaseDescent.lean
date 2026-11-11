import IntegrationSection4.GammaBaseBridge
import Section4.Spaces

/-! Descend full-base definability back to the unchanged Gamma-only base.
Every parameter code is quantified over its full fibre; no chosen real
representative is named in the resulting base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaBaseDescent

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)

def embedTuple {k : ℕ} (t : Fin k → M) : Fin k × Fin 5 → M :=
  fun ij => AdjoinGamma.embedCode (![t ij.1] : Fin 1 → M) ij.2

theorem embedTuple_compatible {k : ℕ} (t : Fin k → M) (ht : Proper t) :
    ∃ hc : embedTuple t ∈ ImaginaryParameters.tupleCodes
        (@ParameterPresentation.presentation M sM hM) (Fin k),
      (ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) (Fin k)).decode
        ⟨embedTuple t,hc⟩ = (fun i => Sum.inr (codeValue (t i))) := by
  choose hc he using fun i => AdjoinGamma.embedCode_compatible (![t i] : Fin 1 → M) (ht i)
  exact ⟨hc,funext he⟩

theorem embedTuple_proper {k : ℕ} (t : Fin k → M)
    (ht : embedTuple t ∈ ImaginaryParameters.tupleCodes
      (@ParameterPresentation.presentation M sM hM) (Fin k)) : Proper t := by
  have hn : iVFOne (M := M) ≠ iVFZero := by
    intro he
    exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he)
  intro i
  have hi := ht i
  change (iVFOne = iVFZero ∧ _) ∨ (iVFOne ≠ iVFZero ∧ NonzeroRV (t i)) at hi
  exact (hi.resolve_left (fun h => hn h.1)).2

theorem withTuple_to_gamma (S : Set M) {k n : ℕ} (γ : Fin k → Values.Gamma (M := M))
    (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hA : @ImaginaryParameters.WithTuple LRV M (CanonicalStructure.normalize (M := M))
      (ParameterPresentation.Name (M := M)) (Fin 5)
      (@ParameterPresentation.presentation M sM hM) S (Fin k) (Fin n)
      (fun i => Sum.inr (γ i)) A)
    (hProper : ∀ b ∈ A, ∀ i, sortEval (sn i) (b i)) :
    GammaParameters.DefinableWith S γ sn A := by
  obtain ⟨R,hR,hRA⟩ := hA
  letI := sM
  let p := @ParameterPresentation.presentation M sM hM
  let F : (Fin k ⊕ Fin n → M) → (Fin k × Fin 5) ⊕ Fin n → M :=
    fun z => Sum.elim (@embedTuple M sM k (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hEmbed := @AdjoinGamma.embedCode_definable M sM hM S
  have hF : @Set.DefinableMap M LRV N (Fin k ⊕ Fin n) ((Fin k × Fin 5) ⊕ Fin n) S F := by
    letI := N
    intro j
    cases j with
    | inl j =>
      exact (hEmbed j.2).comp (show S.DefinableMap LRV
        (fun z : Fin k ⊕ Fin n → M => (![z (.inl j.1)] : Fin 1 → M)) from
          fun i => by fin_cases i; exact Set.DefinableFun.proj LRV)
    | inr j => exact Set.DefinableFun.proj LRV
  have hPull : @Set.Definable M S LRV N (Fin k ⊕ Fin n)
      (F ⁻¹' ImaginaryParameters.vectorPullback (ImaginaryParameters.tuplePresentation p (Fin k)) R) := by
    letI := N
    exact hR.preimage_map hF
  have hSort := @Set.Definable.preimage_comp M S LRV N (Fin n) (Fin k ⊕ Fin n) Sum.inr _
    (@SpecialTransformations.Section4.tuple_domain_definable M sM hM S (Fin n) inferInstance sn)
  let C : Set ((Fin k → M) × (Fin n → M)) :=
    {z | Proper z.1 ∧ (∀ i, sortEval (sn i) (z.2 i)) ∧
      z.2 ∈ R (fun i => Sum.inr (codeValue (z.1 i)))}
  have hC : @Set.Definable M S LRV N (Fin k ⊕ Fin n)
      {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ C} := by
    have hBoth := @Set.Definable.inter M S LRV N (Fin k ⊕ Fin n) _ _ hPull hSort
    convert hBoth using 1
    ext z
    letI := sM
    constructor
    · rintro ⟨ht,hSort,hz⟩
      obtain ⟨hc,he⟩ := embedTuple_compatible (z ∘ Sum.inl) ht
      exact ⟨⟨hc,he.symm ▸ hz⟩,hSort⟩
    · rintro ⟨⟨hc,hz⟩,hSort⟩
      have ht := embedTuple_proper (z ∘ Sum.inl) hc
      obtain ⟨hc',he⟩ := embedTuple_compatible (z ∘ Sum.inl) ht
      exact ⟨ht,hSort,he ▸ hz⟩
  let Q : GammaParameters.Relation (M := M) S k n sn :=
    { carrier := C
      definable := hC
      proper := fun z hz => ⟨hz.1,hz.2.1⟩
      invariant := by
        intro t u htu b
        have he : (fun i => Sum.inr (codeValue (rawTuple t i)) : Fin k → ParameterPresentation.Name (M := M)) =
            (fun i => Sum.inr (codeValue (rawTuple u i))) := by
          funext i
          exact congrArg Sum.inr ((codeValue_raw (t i)).trans
            ((congrFun htu i).trans (codeValue_raw (u i)).symm))
        change (Proper (rawTuple t) ∧ _ ∧ b ∈ R _) ↔ (Proper (rawTuple u) ∧ _ ∧ b ∈ R _)
        rw [he]
        exact and_congr (iff_of_true (rawTuple_proper t) (rawTuple_proper u)) Iff.rfl }
  refine ⟨Q,?_⟩
  ext b
  have he : (fun i => Sum.inr (codeValue (rawTuple (representatives γ) i)) : Fin k → ParameterPresentation.Name (M := M)) =
      (fun i => Sum.inr (γ i)) := by
    funext i
    exact congrArg Sum.inr ((codeValue_raw _).trans (representative_value (γ i)))
  change (Proper (rawTuple (representatives γ)) ∧ (∀ i, sortEval (sn i) (b i)) ∧ b ∈ R _) ↔ b ∈ A
  rw [he,hRA]
  exact ⟨fun h => h.2.2,fun h => ⟨rawTuple_proper _,hProper b h,h⟩⟩

theorem to_gamma (G : GammaParameters.Base (M := M)) {n : ℕ} (sn : Fin n → SortTag)
    (A : Set (Fin n → M)) (hA : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) A)
    (hProper : ∀ b ∈ A, ∀ i, sortEval (sn i) (b i)) : GammaParameters.DefinableOverBase G sn A := by
  obtain ⟨F,hF,hTuple⟩ := hA
  have hNames (j : F) : ∃ γ : Values.Gamma (M := M), Sum.inr γ = j.val ∧ γ ∈ G.gamma := by
    obtain ⟨γ,hγ,he⟩ := hF j.val j.property
    exact ⟨γ,he,hγ⟩
  choose δ hδ hδG using hNames
  let k := Fintype.card F
  let e : F ≃ Fin k := Fintype.equivFin F
  let γ : Fin k → Values.Gamma (M := M) := fun i => δ (e.symm i)
  have hp := ParameterPresentation.codeDomain_definable (M := M) G.real
  have hEq : (fun i : Fin k => Sum.inr (γ i)) ∘ e = (Subtype.val : F → ParameterPresentation.Name (M := M)) := by
    funext j
    exact (congrArg (fun i => Sum.inr (δ i)) (e.symm_apply_apply j)).trans (hδ j)
  have hTuple' := @ImaginaryParameters.WithTuple.reindex LRV M (CanonicalStructure.normalize (M := M))
    (ParameterPresentation.Name (M := M)) (Fin 5) (@ParameterPresentation.presentation M sM hM)
    G.real F (Fin k) inferInstance inferInstance (Fin n) inferInstance
    (Subtype.val : F → ParameterPresentation.Name (M := M)) (fun i => Sum.inr (γ i)) A hTuple hp e hEq
  exact ⟨k,γ,fun i => hδG (e.symm i),withTuple_to_gamma G.real γ sn A hTuple' hProper⟩

end IntegrationInACVF.Section4.GammaBaseDescent
