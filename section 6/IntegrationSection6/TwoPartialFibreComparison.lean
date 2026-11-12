import IntegrationSection6.VFPrefixStandardPresentations
import IntegrationSection6.TwoCoordinateExchange

/-! Two partial contractions in opposite orders compare fibrewise after
freezing every remaining VF coordinate. Their actual restricted programs
and RV presentations are supplied by the prefix restriction construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a l r : ℕ}

theorem gamma_two_partial_fibre_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (hBS : B.real ⊆ S)
    {U W : DefSet (M := M) S (n+2) a} {V : DefSet (M := M) S n l} {Z : DefSet (M := M) S n r}
    (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    (T : PartialContractionProgram S n (n := 2) U V) (E : PartialContractionProgram S n (n := 2) W Z)
    (hT : GammaPartialProgramDefinable B T) (hE : GammaPartialProgramDefinable B E)
    (x : Fin n → VF (M := M))
    (h58 : Section5TwoOrderInput ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ hκ.le hs
      (small_union_range hκ.le B.real hreal (fun j => (x j).val)))
    (hSource : vfPrefixFibre (p := 2) W x =
      vfPermutationImage (vfPrefixFibre (p := 2) U x) (Equiv.swap (0 : Fin 2) (0 : Fin 1).succ))
    (P : SelectedLabelFibrePresentation B V (partialSelectedIndex T (Fin.elim0 : Fin 0 → Fin a)) x)
    (Q : SelectedLabelFibrePresentation B Z (partialSelectedIndex E (Fin.elim0 : Fin 0 → Fin a)) x) :
    GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma := by
  let A := vfPrefixFibre (p := 2) U x
  have hA := gamma_vfPrefixFibre (p := 2) U hU x
  have hfinA : ∀ y : Fin 2 → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier A}.Finite :=
    fun y => hfinU (vfPrefixTuple x y)
  obtain ⟨C,hC,⟨eP⟩⟩ := prefixPartialTwoStandardComparison hκ.le hs hreal hBS T hT x A (Equiv.refl _)
    (vfPermutationImage_id_eq A).symm hA hfinA P
  obtain ⟨D,hD,⟨eQ⟩⟩ := prefixPartialTwoStandardComparison hκ.le hs hreal hBS E hE x A
    (Equiv.swap (0 : Fin 2) (0 : Fin 1).succ) hSource hA hfinA Q
  have h := lemma_6_16_two (B := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩) hκ hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val))
    hgamma δ hδ hδ1 h58 (Set.union_subset_union hBS (Set.Subset.refl _)) A hA hfinA
    (by decide) C D hC hD
  exact h.corollary_6_6 eP eQ

end IntegrationInACVF.Section6.FiniteRV
