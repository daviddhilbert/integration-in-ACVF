import IntegrationSection6.ArbitraryContractionOrders
import IntegrationSection6.GammaContractionExtensionIsomorphisms

/-! Arbitrary-order comparison for the actual normalized RV[n+k]
contraction objects, in every internal real presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a k : ℕ}

theorem gamma_selected_contractions_all_orders_univ {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ.le hs)
    (U : DefSet (M := M) Set.univ n a) (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ υ : Equiv.Perm (Fin n)} (C : StandardContraction U σ) (E : StandardContraction U υ)
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal
      (gammaFiniteSelectedContraction hκ.le hs hreal (Set.subset_univ _) hU ρ hfin C hC)
      (gammaFiniteSelectedContraction hκ.le hs hreal (Set.subset_univ _) hU ρ hfin E hE) := by
  obtain ⟨P⟩ := gammaSelectedRVPresentation_exists C.target (gamma_program_final_set C.program hC)
    (orderedSelectedIndex C.program ρ)
    (ordered_selected_fibres_finite hκ.le hs hreal C.program hC ρ (vfPermutation_selected_finite U σ ρ hfin))
  obtain ⟨Q⟩ := gammaSelectedRVPresentation_exists E.target (gamma_program_final_set E.program hE)
    (orderedSelectedIndex E.program ρ)
    (ordered_selected_fibres_finite hκ.le hs hreal E.program hE ρ (vfPermutation_selected_finite U υ ρ hfin))
  have H := gamma_contraction_order_independent hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 n
    U hU ρ hfin σ υ C E hC hE P Q
  have H' := H.corollary_6_6
    (gammaIsoSymm (gammaContractionPresentationIso hκ.le hs hreal (Set.subset_univ _) hU ρ hfin C hC P))
    (gammaIsoSymm (gammaContractionPresentationIso hκ.le hs hreal (Set.subset_univ _) hU ρ hfin E hE Q))
  have H'' := H'.castDegree (orderedVolumeDegree_eq n k)
  simpa only [gammaCastDegree_symm] using H''

theorem gamma_selected_contractions_all_orders {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ.le hs) (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S n a) (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ υ : Equiv.Perm (Fin n)} (C : StandardContraction U σ) (E : StandardContraction U υ)
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal
      (gammaFiniteSelectedContraction hκ.le hs hreal hBS hU ρ hfin C hC)
      (gammaFiniteSelectedContraction hκ.le hs hreal hBS hU ρ hfin E hE) := by
  have H := gamma_selected_contractions_all_orders_univ hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58
    (extendBase U (Set.subset_univ _)) hU ρ hfin
    (extendStandardContraction C (Set.subset_univ _)) (extendStandardContraction E (Set.subset_univ _))
    (gamma_extendStandardContraction C (Set.subset_univ _) hC) (gamma_extendStandardContraction E (Set.subset_univ _) hE)
  exact H.corollary_6_6
    (gammaSelectedContractionExtensionIso hκ.le hs hreal hBS (Set.subset_univ _) hU ρ hfin C hC)
    (gammaSelectedContractionExtensionIso hκ.le hs hreal hBS (Set.subset_univ _) hU ρ hfin E hE)

theorem gamma_finite_contractions_all_orders {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ.le hs) (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S n a) (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    {σ υ : Equiv.Perm (Fin n)} (C : StandardContraction U σ) (E : StandardContraction U υ)
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal (gammaFiniteContraction hκ.le hs hreal hBS hU hfin C hC)
      (gammaFiniteContraction hκ.le hs hreal hBS hU hfin E hE) :=
  (gamma_selected_contractions_all_orders hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 hBS U hU
    Fin.elim0 (empty_selected_fibres U hfin) C E hC hE).corollary_6_6
      (gammaIsoSymm (gammaEmptySelectedContractionIso hκ.le hs hreal hBS hU hfin C hC))
      (gammaIsoSymm (gammaEmptySelectedContractionIso hκ.le hs hreal hBS hU hfin E hE))

end IntegrationInACVF.Section6.FiniteRV
