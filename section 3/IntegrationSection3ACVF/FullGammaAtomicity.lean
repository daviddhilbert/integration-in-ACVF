import IntegrationSection3ACVF.FullGammaPoint
import IntegrationSection3ACVF.AdjoinGamma
import IntegrationSection3ACVF.AdjoinBall

/-! Lemma 3.3 with additional genuine ball names in the original base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullGammaAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev AtomicTuple (B : FullBaseAtomicity.Base (M := M)) {n : ℕ}
    (A : Set (Fin n → M)) : Prop :=
  @ImaginaryParameters.IsAtomicTupleOver LRV M (CanonicalStructure.normalize (M := M))
    (ParameterPresentation.Name (M := M)) (Fin 5)
    (@ParameterPresentation.presentation M sM hM) B (Fin n) A

def cutParameters {n : ℕ} (A : Set (Fin n → M))
    (R : Values.Gamma (M := M) → Set (Fin n → M)) : Set (Values.Gamma (M := M)) :=
  {γ | Splits (R γ) A}

theorem cutParameters_definable {B : FullBaseAtomicity.Base (M := M)} {n : ℕ}
    {A : Set (Fin n → M)} (hA : FullBaseAtomicity.OverBase B A)
    {R : Values.Gamma (M := M) → Set (Fin n → M)}
    (hR : FullBaseAtomicity.OverBase B (AdjoinGamma.vectorPullback R)) :
    FullGammaSyntax.Scalar B (cutParameters A R) := by
  have hp : FullBaseAtomicity.OverBase B {a : Fin 1 → M | NonzeroRV (a 0)} :=
    FullBaseAtomicity.OverBase.of_real (B := B)
      (nonzero_codes_normalized_definable (M := M) B.real)
  have ha := FullBaseAtomicity.OverBase.preimage_comp hA (Sum.inr : Fin n → Fin 1 ⊕ Fin n)
  have hpc := FullBaseAtomicity.OverBase.preimage_comp hp (Sum.inl : Fin 1 → Fin 1 ⊕ Fin n)
  have hy := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter ha hR)
  have hn := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.inter hpc ha) (FullBaseAtomicity.OverBase.compl hR))
  change FullBaseAtomicity.OverBase B {a : Fin 1 → M | a 0 ∈ Values.gammaPullback (cutParameters A R)}
  convert FullBaseAtomicity.OverBase.inter hy hn using 1
  ext a
  change (a 0 ∈ Values.gammaPullback (cutParameters A R)) ↔
    ((∃ x : Fin n → M, x ∈ A ∧ NonzeroRV (a 0) ∧ x ∈ R (codeValue (a 0))) ∧
      ∃ y : Fin n → M, (NonzeroRV (a 0) ∧ y ∈ A) ∧
        ¬ (NonzeroRV (a 0) ∧ y ∈ R (codeValue (a 0))))
  rw [GammaSyntax.mem_gammaPullback_iff]
  change (NonzeroRV (a 0) ∧ Splits (R (codeValue (a 0))) A) ↔ _
  constructor
  · rintro ⟨hp,x,hx,hxr,y,hy,hyn⟩
    exact ⟨⟨x,hx,hp,hxr⟩,y,⟨hp,hy⟩,fun h => hyn h.2⟩
  · rintro ⟨⟨x,hx,hp,hxr⟩,y,⟨_,hy⟩,hn⟩
    exact ⟨hp,x,hx,hxr,y,hy,fun h => hn ⟨hp,h⟩⟩

theorem lemma_3_3_one (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {n : ℕ} {A : Set (Fin n → M)} (hA : AtomicTuple B A) (γ : Values.Gamma (M := M)) :
    AtomicTuple (B.adjoin (Sum.inr γ)) A := by
  have hAm : FullBaseAtomicity.OverBase (B.adjoin (Sum.inr γ)) A :=
    FullBaseAtomicity.OverBase.mono hA.1 Set.Subset.rfl (Set.subset_insert _ _)
  refine ⟨hAm,?_⟩
  intro S hS
  obtain ⟨R,hR,hRi⟩ := (FullBaseAtomicity.OverBase.adjoin_iff (B := B) (Sum.inr γ) S).mp hS
  let P : Values.Gamma (M := M) → Set (Fin n → M) := fun η => R (Sum.inr η)
  have hP : FullBaseAtomicity.OverBase B (AdjoinGamma.vectorPullback P) :=
    AdjoinGamma.restrict_vector B R hR
  have hbad := cutParameters_definable hA.1 hP
  have hcut : ¬ Splits S A := by
    intro hc
    have hne : (cutParameters A P).Nonempty := by
      refine ⟨γ,?_⟩
      change Splits (R (Sum.inr γ)) A
      rw [hRi]
      exact hc
    obtain ⟨γ',hγ',hdγ'⟩ := FullGammaPoint.gamma_definable_point h00 δ hδ hδ1
      (cutParameters A P) hbad hne
    have hf := AdjoinGamma.fibre_definable hP γ' hdγ'
    rcases hA.2 (P γ') hf with hw | hd
    · obtain ⟨x,hx,hxr,y,hy,hyn⟩ := hγ'
      exact hyn (hw hy)
    · obtain ⟨x,hx,hxr,y,hy,hyn⟩ := hγ'
      exact Set.disjoint_left.mp hd hx hxr
  by_cases hw : A ⊆ S
  · exact Or.inl hw
  · obtain ⟨y,hy,hyn⟩ := Set.not_subset.mp hw
    exact Or.inr (Set.disjoint_left.mpr fun x hx hxr => hcut ⟨x,hx,hxr,y,hy,hyn⟩)

def withGammaFinset (B : FullBaseAtomicity.Base (M := M))
    (G : Finset (Values.Gamma (M := M))) : FullBaseAtomicity.Base (M := M) :=
  ⟨B.real,B.imaginary ∪ (Sum.inr : Values.Gamma (M := M) → ParameterPresentation.Name (M := M)) ''
    (G : Set (Values.Gamma (M := M)))⟩

theorem lemma_3_3_finset (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {n : ℕ} {A : Set (Fin n → M)} (hA : AtomicTuple B A)
    (G : Finset (Values.Gamma (M := M))) : AtomicTuple (withGammaFinset B G) A := by
  classical
  induction G using Finset.induction_on with
  | empty =>
    simpa only [withGammaFinset,Finset.coe_empty,Set.image_empty,Set.union_empty] using hA
  | @insert γ G hγ ih =>
    let C := withGammaFinset B G
    have hdC : FullGammaSyntax.Scalar C {δ} :=
      FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl Set.subset_union_left
    have h := lemma_3_3_one h00 C δ hdC hδ1 ih γ
    have he : C.adjoin (Sum.inr γ) = withGammaFinset B (insert γ G) := by
      change (⟨B.real,insert (Sum.inr γ)
        (B.imaginary ∪ (Sum.inr : Values.Gamma (M := M) → ParameterPresentation.Name (M := M)) ''
          (G : Set (Values.Gamma (M := M))))⟩ : FullBaseAtomicity.Base (M := M)) = _
      congr 1
      ext x
      simp only [Finset.coe_insert,Set.image_insert_eq,Set.mem_insert_iff,Set.mem_union]
      tauto
    rw [he] at h
    exact h

noncomputable def withGammaTuple (B : FullBaseAtomicity.Base (M := M)) {k : ℕ}
    (γ : Fin k → Values.Gamma (M := M)) : FullBaseAtomicity.Base (M := M) := by
  classical
  exact withGammaFinset B (Finset.univ.image γ)

/-- Lemma 3.3 over a base already containing arbitrary actual Gamma and
ball names, in every finite real tuple arity (hence every mixed VF/RV arity).
The standing original-base definable nontrivial value is explicit. -/
theorem lemma_3_3 (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {n : ℕ} {A : Set (Fin n → M)} (hA : AtomicTuple B A)
    {k : ℕ} (γ : Fin k → Values.Gamma (M := M)) : AtomicTuple (withGammaTuple B γ) A := by
  classical
  exact lemma_3_3_finset h00 B δ hδ hδ1 hA (Finset.univ.image γ)

theorem lemma_3_3_unary (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    {k : ℕ} (γ : Fin k → Values.Gamma (M := M)) :
    AdjoinBall.AtomicOver (withGammaTuple B γ) A := by
  have ht : AtomicTuple B {z : Fin 1 → M | z 0 ∈ A} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.unary_tuple_atomic_iff.mpr hA
  have h := lemma_3_3 h00 B δ hδ hδ1 ht γ
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.unary_tuple_atomic_iff.mp h

end IntegrationInACVF.Section3ACVF.FullGammaAtomicity
