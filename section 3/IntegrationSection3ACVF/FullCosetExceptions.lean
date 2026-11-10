import IntegrationSection3ACVF.FullBallCoset

/-! The finite coset-exception theorem with arbitrary genuine ball names.
Specialization is used only to prove finiteness. The set-valued graph and
subgroup hypotheses are full invariant preimages over the original base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullCosetExceptions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The powerset-valued function is supplied through its entire real graph,
including all finite RV output arities and absorbing-zero coordinates. -/
theorem finite_bad_cosets (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))})
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hgraph : FullBaseAtomicity.OverBase B (BallFibreConstancy.graph f)) :
    {d : VFType (M := M) ⧸ H | ∃ x y,
      QuotientAddGroup.mk' H x = d ∧ QuotientAddGroup.mk' H y = d ∧ f x ≠ f y}.Finite := by
  let U := Subtype.val '' (H : Set (VFType (M := M)))
  let G := BallFibreConstancy.graph f
  have hU : U ⊆ {x | iVF x} := by
    rintro x ⟨u,_,rfl⟩
    exact u.property
  have hG : ∀ z ∈ G, ∀ i, sortEval (MixedPolynomialSyntax.contextSort i) (z i) := by
    rintro z ⟨x,hx,hz⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · change iVF (z 0)
      rw [← hx]
      exact x.property
    · exact hf x (Fin.tail z) hz j
  have hsH : ∃ E : Set M, E.Finite ∧
      @Set.Definable M (B.real ∪ E) LRV (CanonicalStructure.normalize (M := M))
        (Fin 1) {z | z 0 ∈ U} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.specialize hH
  have hsG : ∃ E : Set M, E.Finite ∧
      @Set.Definable M (B.real ∪ E) LRV (CanonicalStructure.normalize (M := M))
        (Fin (m+1)) G := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.specialize hgraph
  obtain ⟨E,_,hsH⟩ := hsH
  obtain ⟨F,_,hsG⟩ := hsG
  let Q := (B.real ∪ E) ∪ (B.real ∪ F)
  have hdH : DefinableAt Q .vf U :=
    (@definableAt_iff_normalized_raw M sM hM Q .vf U).mpr
      ⟨hsH.mono Set.subset_union_left,hU⟩
  have hdG : DefinableOver Q MixedPolynomialSyntax.contextSort G :=
    (@definableOver_iff_normalized_raw M sM hM Q (m+1) MixedPolynomialSyntax.contextSort G).mpr
      ⟨hsG.mono Set.subset_union_right,hG⟩
  exact AdditiveCosets.lemma_3_18_1 h00 Q H hdH f hf hdG

end IntegrationInACVF.Section3ACVF.FullCosetExceptions
