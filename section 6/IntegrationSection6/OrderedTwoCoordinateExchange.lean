import IntegrationSection6.TwoPartialFibreComparison

/-! Higher-arity first-two-coordinate exchange for actual ordered programs.
The source fibre identity is a literal coordinate permutation, and the
only unfinished input is the explicitly authorized Section5.8 theorem. -/
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

theorem gamma_ordered_two_exchange {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (hBS : B.real ⊆ S)
    {U W : DefSet (M := M) S (n+2) a} {V : DefSet (M := M) S 0 l} {Z : DefSet (M := M) S 0 r}
    (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    (hfinW : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier W}.Finite)
    (h58 : ∀ x : Fin n → VF (M := M),
      Section5TwoOrderInput ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ hκ.le hs
        (small_union_range hκ.le B.real hreal (fun j => (x j).val)))
    (hSource : ∀ x : Fin n → VF (M := M), vfPrefixFibre (p := 2) W x =
      vfPermutationImage (vfPrefixFibre (p := 2) U x) (Equiv.swap (0 : Fin 2) (0 : Fin 1).succ))
    (T : OrderedContractionProgram S U V) (E : OrderedContractionProgram S W Z)
    (hT : GammaProgramDefinable B T) (hE : GammaProgramDefinable B E)
    (P : GammaSelectedRVPresentation B V (orderedSelectedIndex T (Fin.elim0 : Fin 0 → Fin a)))
    (Q : GammaSelectedRVPresentation B Z (orderedSelectedIndex E (Fin.elim0 : Fin 0 → Fin a))) :
    GammaIsp hκ.le hs h00 hreal P.toGamma Q.toGamma := by
  cases T with
  | step T tail =>
    cases tail with
    | step T2 tail2 =>
      cases E with
      | step E etail =>
        cases etail with
        | step E2 etail2 =>
          let PT : PartialContractionProgram S n (n := 2) U T2.contractedSet :=
            .step T (.step T2 (.zero _))
          let PE : PartialContractionProgram S n (n := 2) W E2.contractedSet :=
            .step E (.step E2 (.zero _))
          have hPT : GammaPartialProgramDefinable B PT :=
            ⟨hT.1,hT.2.1,hT.2.2.1,hT.2.2.2.1,gamma_headImage T2.target hT.2.2.2.1⟩
          have hPE : GammaPartialProgramDefinable B PE :=
            ⟨hE.1,hE.2.1,hE.2.2.1,hE.2.2.2.1,gamma_headImage E2.target hE.2.2.2.1⟩
          exact lemma_6_14_ordered hκ hs h00 hreal hgamma δ hδ hδ1
            T2.contractedSet E2.contractedSet
            (gamma_headImage T2.target hT.2.2.2.1) (gamma_headImage E2.target hE.2.2.2.1)
            (partialSelectedIndex PT (Fin.elim0 : Fin 0 → Fin a))
            (partialSelectedIndex PE (Fin.elim0 : Fin 0 → Fin a))
            (partial_selected_fibres_finite hκ.le hs hreal PT hPT Fin.elim0 (empty_selected_fibres U hfinU))
            (partial_selected_fibres_finite hκ.le hs hreal PE hPE Fin.elim0 (empty_selected_fibres W hfinW))
            (fun x LP LQ => gamma_two_partial_fibre_comparison hκ hs h00 hreal hgamma δ hδ hδ1 hBS
              hU hfinU PT PE hPT hPE x (h58 x) (hSource x) LP LQ)
            tail2 etail2 hT.2.2.2.2 hE.2.2.2.2 P Q

end IntegrationInACVF.Section6.FiniteRV
