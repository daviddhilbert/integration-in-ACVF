import IntegrationSection3ACVF.FullBaseDefinability
import Section3.FibreEnumerations

/-! Full interpreted-base version of the proved MIT
Section3/FibreEnumerations enumeration formula at pinned revision
9cc9760892092dd34cfad4a6dee655843c52f30c. Every imaginary code is retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.RawClosure.Tuple
open SpecialTransformations.Section3.RawClosure
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullFibreEnumerations

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem exists_finite (B : FullBaseAtomicity.Base (M := M))
    {α τ : Type} [Finite α] [Finite τ] (A : τ → Set (α → M))
    (hA : ∀ t, FullBaseAtomicity.OverBase B (A t)) :
    FullBaseAtomicity.OverBase B {z | ∃ t, z ∈ A t} := by
  have h := FullBaseAtomicity.OverBase.compl
    (FullBaseAtomicity.OverBase.forall_finite (fun t => FullBaseAtomicity.OverBase.compl (hA t)))
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_forall,not_not]

theorem definable (B : FullBaseAtomicity.Base (M := M))
    (R : Set ((Fin n → M) × M))
    (hR : FullBaseAtomicity.OverBase B
      {z : Fin n ⊕ Fin 1 → M | (z ∘ Sum.inl,z (.inr 0)) ∈ R}) (k : ℕ) :
    FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin k → M |
      Enumerates R k (z ∘ Sum.inl) (z ∘ Sum.inr)} := by
  let ι := Fin n ⊕ Fin k
  have hmem (i : Fin k) : FullBaseAtomicity.OverBase B
      {z : ι → M | (z ∘ Sum.inl,z (.inr i)) ∈ R} :=
    FullBaseAtomicity.OverBase.preimage_comp hR (Sum.map id (fun _ : Fin 1 => i))
  have heq (i j : ι ⊕ Fin 1) : FullBaseAtomicity.OverBase B
      {z : ι ⊕ Fin 1 → M | z i = z j} := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact definable_equal_coordinates B.real i j
  have hne (p : Fin k × Fin k) : FullBaseAtomicity.OverBase B
      {z : ι → M | p.1 = p.2 ∨ z (.inr p.1) ≠ z (.inr p.2)} := by
    by_cases hp : p.1 = p.2
    · have hu : FullBaseAtomicity.OverBase B (Set.univ : Set (ι → M)) := by
        apply FullBaseAtomicity.OverBase.of_real
        letI := @CanonicalStructure.normalize M sM
        exact Set.definable_univ
      apply FullBaseAtomicity.OverBase.congr hu
      intro z
      simp only [Set.mem_univ,Set.mem_ofPred_eq,hp,true_or]
    · have he : FullBaseAtomicity.OverBase B {z : ι → M | z (.inr p.1) = z (.inr p.2)} := by
        apply FullBaseAtomicity.OverBase.of_real
        letI := @CanonicalStructure.normalize M sM
        exact definable_equal_coordinates B.real (Sum.inr p.1 : ι) (Sum.inr p.2 : ι)
      apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.compl he)
      intro z
      simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,hp,false_or]
  have hrel := FullBaseAtomicity.OverBase.preimage_comp hR
    (Sum.elim (fun i : Fin n => (Sum.inl (Sum.inl i) : ι ⊕ Fin 1)) Sum.inr)
  have hAny : FullBaseAtomicity.OverBase B
      {z : ι ⊕ Fin 1 → M | ∃ i : Fin k, z (.inl (.inr i)) = z (.inr 0)} := by
    have h := FullBaseAtomicity.OverBase.compl (FullBaseAtomicity.OverBase.forall_finite
      (fun i : Fin k => FullBaseAtomicity.OverBase.compl (heq (.inl (.inr i)) (.inr 0))))
    apply FullBaseAtomicity.OverBase.congr h
    intro z
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_forall,not_not]
  have hcov := FullBaseAtomicity.OverBase.forall_block
    (FullBaseAtomicity.OverBase.union (FullBaseAtomicity.OverBase.compl hrel) hAny)
  have hfull := FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.inter (FullBaseAtomicity.OverBase.forall_finite hne)
      (FullBaseAtomicity.OverBase.forall_finite hmem)) hcov
  apply FullBaseAtomicity.OverBase.congr hfull
  intro z
  change (((∀ p : Fin k × Fin k, p.1 = p.2 ∨ z (.inr p.1) ≠ z (.inr p.2)) ∧
    (∀ i : Fin k, (z ∘ Sum.inl,z (.inr i)) ∈ R)) ∧
    (∀ b : Fin 1 → M, ¬ (z ∘ Sum.inl,b 0) ∈ R ∨ ∃ i : Fin k, z (.inr i) = b 0)) ↔
      Enumerates R k (z ∘ Sum.inl) (z ∘ Sum.inr)
  constructor
  · rintro ⟨⟨hinj,hm⟩,hcover⟩
    refine ⟨fun i j he => (hinj (i,j)).resolve_right (fun hn => hn he),hm,?_⟩
    intro b hb
    exact (hcover ![b]).resolve_left (fun hn => hn hb)
  · rintro ⟨hinj,hm,hcover⟩
    refine ⟨⟨fun p => or_iff_not_imp_left.mpr (fun hp => hinj.ne hp),hm⟩,?_⟩
    intro b
    by_cases hb : (z ∘ Sum.inl,b 0) ∈ R
    · exact Or.inr (hcover (b 0) hb)
    · exact Or.inl hb

end IntegrationInACVF.Section3ACVF.FullFibreEnumerations
