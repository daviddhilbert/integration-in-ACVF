module

public import Integration7.CompletedVFParameterTwoOrderInputs
public import IntegrationSection6.CoordinateExchange

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Ordinary first-two contraction exchange over the standing generated
base follows from the completed Section5 theorem. This retains every
ordinary RV label, including zero labels, and has no open two-order input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a l r : ℕ}

theorem generated_ordered_two_exchange {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (hBS : B.real ⊆ S)
    {U W : DefSet (M := M) S (n+2) a} {V : DefSet (M := M) S 0 l} {Z : DefSet (M := M) S 0 r}
    (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    (hfinW : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier W}.Finite)
    (hSource : ∀ x : Fin n → VF (M := M), vfPrefixFibre (p := 2) W x =
      vfPermutationImage (vfPrefixFibre (p := 2) U x) (Equiv.swap (0 : Fin 2) (0 : Fin 1).succ))
    (T : OrderedContractionProgram S U V) (E : OrderedContractionProgram S W Z)
    (hT : GammaProgramDefinable B T) (hE : GammaProgramDefinable B E)
    (P : GammaSelectedRVPresentation B V (orderedSelectedIndex T (Fin.elim0 : Fin 0 → Fin a)))
    (Q : GammaSelectedRVPresentation B Z (orderedSelectedIndex E (Fin.elim0 : Fin 0 → Fin a))) :
    GammaIsp hκ.le hs h00 hreal P.toGamma Q.toGamma :=
  gamma_ordered_two_exchange hκ hs h00 hreal hgamma δ hδ hδ1 hBS hU hfinU hfinW
    (fun x => completed_vf_parameter_two_order_input hκ hs h00 B hreal hgamma hGenerated δ hδ hδ1 x)
    hSource T E hT hE P Q

theorem generated_ordinary_first_two_exchange {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S (n+2) a) (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    {σ : Equiv.Perm (Fin (n+2))}
    (T : StandardContraction U σ) (E : StandardContraction U ((swapFirstTwo n).trans σ))
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal (gammaFiniteContraction hκ.le hs hreal hBS hU hfinU T hT)
      (gammaFiniteContraction hκ.le hs hreal hBS hU hfinU E hE) :=
  lemma_6_16_uncountable hκ hs h00 hreal hgamma δ hδ hδ1 hBS
    (fun x => completed_vf_parameter_two_order_input hκ hs h00 B hreal hgamma hGenerated δ hδ hδ1 x)
    U hU hfinU T E hT hE

theorem generated_ordinary_first_two_exchange_of_order {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S (n+2) a) (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    {σ υ : Equiv.Perm (Fin (n+2))} (hOrder : υ = (swapFirstTwo n).trans σ)
    (T : StandardContraction U σ) (E : StandardContraction U υ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal (gammaFiniteContraction hκ.le hs hreal hBS hU hfinU T hT)
      (gammaFiniteContraction hκ.le hs hreal hBS hU hfinU E hE) := by
  subst υ
  exact generated_ordinary_first_two_exchange hκ hs h00 hreal hgamma hGenerated δ hδ hδ1 hBS
    U hU hfinU T E hT hE
end IntegrationInACVF.Section7
