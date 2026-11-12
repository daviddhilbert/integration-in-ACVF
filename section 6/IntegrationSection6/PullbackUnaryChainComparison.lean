import IntegrationSection6.PullbackContractionComparison
import IntegrationSection6.UnaryChainContractions
import IntegrationSection6.GammaUnaryChainUnivRealization

/-! Actual finite RV data of pullbacks are Isp-equivalent whenever the
pullbacks are joined by a Gamma relatively unary chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b : ℕ}

theorem gamma_pullback_unary_chain_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ.le hs)
    (U : DefSet (M := M) Set.univ (n+1) a) (V : DefSet (M := M) Set.univ (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hUP : IsRVPullback (carrier U)) (hVP : IsRVPullback (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U)))
    (hVF : Map.FiniteFibres (rvObjectVolume (pullbackObject V)))
    (T : GammaUnaryChain B (n+1) (carrier U) (carrier V)) :
    GammaIsp hκ.le hs h00 hreal (gammaPullbackAt (Set.subset_univ _) U hU hUF).toGamma
      (gammaPullbackAt (Set.subset_univ _) V hV hVF).toGamma := by
  have Ht := gammaUnaryChain_univ_realization T hU hV
  have hUeq : gammaDefSetUniv (carrier U) hU = U := defSet_eq_of_carrier_eq rfl
  have hVeq : gammaDefSetUniv (carrier V) hV = V := defSet_eq_of_carrier_eq rfl
  rw [hUeq,hVeq] at Ht
  obtain ⟨t,ht⟩ := Ht
  obtain ⟨C,hC,_,_,_⟩ := standard_contraction_exists_with_natural_graph hs h00 B hreal FBase
    (Set.subset_univ _) U hU (Equiv.refl _)
  obtain ⟨E,hE,_,_,_⟩ := standard_contraction_exists_with_natural_graph hs h00 B hreal FBase
    (Set.subset_univ _) V hV (Equiv.refl _)
  have H1 := gamma_pullback_contraction_comparison hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58
    (Set.subset_univ _) U hU hUP hfinU hUF C hC
  have H2 := gamma_unary_chain_contractions hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58
    t ht hU hV hfinU hfinV C E hC hE
  have H3 := gamma_pullback_contraction_comparison hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58
    (Set.subset_univ _) V hV hVP hfinV hVF E hE
  exact H1.trans (H2.trans H3.symm)

end IntegrationInACVF.Section6.FiniteRV
