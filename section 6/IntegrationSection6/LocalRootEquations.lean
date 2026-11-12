import IntegrationSection6.PolynomialFocus
import IntegrationSection6.FocusRootDomains
import Section4.PolynomialZero
import Section3.SortedBoolean

/-! Convert the checked local Hensel section into a whole-fibre validity
witness for an equation definable over the original VF/Gamma-generated base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7

namespace IntegrationInACVF.Section6

variable {M Γ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ]

theorem exists_originalBase_localRootSet {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {r n : ℕ} (f : Fin r ↪ Fin n) (j : Fin n) (hj : j ∉ Set.range f)
    (t : Fin n → RVCalc.RV v) (ht : ∀ i, t i ≠ none)
    (halg : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun i => (CanonicalRV.equiv v hv (t (f i))).val), B.gamma⟩
      .rv (CanonicalRV.equiv v hv (t j)).val) :
    ∃ R : Set (Fin n → M), B.real.Definable LRV R ∧
      (@Set.Definable M B.real LRV (@CanonicalStructure.normalize M sM) (Fin n) R) ∧
      rawRV v hv t ∈ rootDomain R j := by
  let E := vfDefinableClosureFieldBase B
  obtain ⟨P,hP⟩ := exists_originalPolynomial_focus hκ hs h00 B hsmall hB v hv f j hj t ht halg
  let R := PolynomialZero.zeroSet E P
  have hSorted : DefinableOver B.real (fun _ => .vf) R :=
    PolynomialZero.zeroSet_named_definable B.real E
      (fun c => (mem_generatedBase_vfField B hB c.val).mp c.property) P
  refine ⟨R,hSorted.raw_definable,
    ((definableOver_iff_normalized_raw B.real _ _).mp hSorted).1,?_⟩
  intro a ha
  let aVF : Fin n → VFType (M := M) := fun i => ⟨a i,(ha i).1⟩
  have haVF : aVF ∈ RVFibre v t := (rawVF_mem_rawTupleFibre_iff v hv t aVF).mp ha
  apply (existsUnique_rawTupleFibre_iff v hv t
    (fun b => b ∈ R ∧ ∀ i, i ≠ j → b i = a i)).mp
  apply (existsUnique_congr (fun b => ?_)).mp (hP aVF haVF)
  apply and_congr_right
  intro hb
  apply and_congr
  · change (P.map E.subtype).eval b = 0 ↔ rawVF b ∈ PolynomialZero.zeroSet E P
    rw [eval_map]
    exact ⟨fun h => ⟨fun i => (b i).property,h⟩,fun ⟨_,h⟩ => h⟩
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    exact Subtype.ext_iff

end IntegrationInACVF.Section6
