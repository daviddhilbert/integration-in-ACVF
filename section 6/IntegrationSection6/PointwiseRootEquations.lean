import IntegrationSection6.LocalRootEquations
import IntegrationSection6.RootCoordinateExtension
import IntegrationSection6.RootDomainNormalization
import IntegrationSection6.ZeroCoordinateAlgebraicity
import IntegrationSection6.NonzeroCoordinates

/-! Pointwise focus equations for every admissible RV tuple, including
zero unchanged coordinates, over the original generated parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7

namespace IntegrationInACVF.Section6

variable {M Γ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ]

theorem exists_pointwise_rootEquation {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) (j : Fin n) (hj : t j ≠ 0)
    (halg : AlgebraicAtBase ⟨coordinateBase B.real j t,B.gamma⟩ .rv (t j).val) :
    ∃ R : Set (Fin n → M),
      @Set.Definable M B.real LRV (@CanonicalStructure.normalize M sM) (Fin n) R ∧
      rvValues t ∈ @rootDomain M (@CanonicalStructure.normalize M sM) n R j := by
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  obtain ⟨r,f,l,hfl,hnz,hzero⟩ := exists_nonzero_coordinate_embedding t j hj
  have halg' : AlgebraicAtBase ⟨coordinateBase B.real (f l) t,B.gamma⟩ .rv (t (f l)).val := by
    simpa only [hfl] using halg
  have hrem := gammaAlgebraic_remove_zero_coordinates hκ hs h00 B hsmall f l t hzero halg'
  let e := CanonicalRV.equiv v hv
  let s : Fin (r+1) → RVCalc.RV v := fun i => e.symm (t (f i))
  have hnone : e none = (0 : CanonicalRV.RVSort M) := by
    rw [← RVCalc.rv_zero,CanonicalRV.equiv_rv,RVOperations.rv_zero]
  have hs0 (i : Fin (r+1)) : s i ≠ none := by
    intro he
    apply hnz i
    exact (e.apply_symm_apply (t (f i))).symm.trans ((congrArg e he).trans hnone)
  let g : Fin r ↪ Fin (r+1) := ⟨l.succAbove,Fin.succAbove_right_injective⟩
  have hlg : l ∉ Set.range g := by
    rintro ⟨i,hi⟩
    exact Fin.succAbove_ne l i hi
  have hlocal : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun i : Fin r => (e (s (g i))).val),B.gamma⟩
      .rv (e (s l)).val := by
    simpa only [s,g,Function.Embedding.coeFn_mk,Equiv.apply_symm_apply] using hrem
  obtain ⟨R,_,hR,hgood⟩ := exists_originalBase_localRootSet hκ hs h00 B hsmall hB
    v hv g l hlg s hs0 hlocal
  have hkey : rawRV v hv s = rvValues t ∘ f := by
    funext i
    exact congrArg Subtype.val (e.apply_symm_apply (t (f i)))
  have hgoodN : rvValues t ∘ f ∈ @rootDomain M N (r+1) R l := by
    rw [rootDomain_normalize]
    rwa [hkey] at hgood
  let R' : Set (Fin n → M) := {b | b ∘ f ∈ R}
  refine ⟨R',@Set.Definable.preimage_comp M B.real LRV N _ _ f _ hR,?_⟩
  have hext := @rootDomain_extend M N n (r+1) f l R (rvValues t) hgoodN
  simpa only [hfl] using hext

end IntegrationInACVF.Section6
