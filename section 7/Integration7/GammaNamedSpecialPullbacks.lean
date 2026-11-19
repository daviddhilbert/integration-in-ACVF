import Integration7.GammaNamedVolumeTransport
import Integration7.GammaNamedPullbackComparisons
import Integration7.SpecialPullbackVolumeComparisons
import Section5.GammaRestriction

/-! Gamma-named special pullbacks: the coordinate-density volume object of
the target of a Gamma special bijection, and its comparison with the source
pullback. The unary factor chain of a Gamma special chain is a Gamma unary
chain; its Gamma volume data comes from the Gamma volume-transport input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a b : ℕ}

theorem gamma_special_unary_chain (hn : 0 < n) {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (t : Chain S n A B) (ht : GammaChainDefinable G t) :
    GammaUnaryChainDefinable G (specialUnaryChain hn t) := by
  induction t with
  | nil A => exact ht
  | cons p tail ih => exact ⟨GammaPrimitiveDefinable.graph (gammaLogicInput G) p ht.1,ih ht.2⟩

namespace GammaNamed

def specialPullbackVolumeGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable G T.chain) (hBP : IsRVPullback (carrier B))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    GammaVolumeObjects G (C.base : Set M) n :=
  pullbackCoordinateGammaObject hc C hGC B (GammaChainDefinable.target G T.chain hT)
    (special_pullback_volume_finite C G.gamma T hBP hfinA) (suffixIndex (special_chain_rvArity_le T.chain) δ)
    (special_retained_density_nonzero T δ hδ)

theorem special_pullback_volume_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (hTransport : GammaVolumeTransportInput hc G (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable G T.chain)
    (hAP : IsRVPullback (carrier A)) (hBP : IsRVPullback (carrier B))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ p, ω.value p = p.val.2 δ)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C hGC A (GammaChainDefinable.source G T.chain hT) hAF δ hδ)
      (specialPullbackVolumeGammaObject hc C G hGC T hT hBP hfinA δ hδ) := by
  have hA := GammaChainDefinable.source G T.chain hT
  have hB := GammaChainDefinable.target G T.chain hT
  let π := specialRetainedVolumeForm hc T δ hδ
  let t := specialUnaryChain (Nat.zero_lt_succ n) T.chain
  have hDensity : ∀ p, ω.value p = π.value ((rawSpecialMap hc T.toMap) p) := by
    intro p
    rw [hω]
    exact (special_oldLabels T ⟨p.val,p.property⟩ δ).symm
  have hπ : ∀ p, π.value p = p.val.2 (suffixIndex (special_chain_rvArity_le T.chain) δ) := fun _ => rfl
  have hData : gammaUnaryChainVolumeData hc G t ω π := by
    apply gamma_unary_chain_volume_data_of_composite hc C (Nat.zero_lt_succ n) hTransport t
      (gamma_special_unary_chain _ T.chain hT) ω π (gamma_coordinate_volume_density_graph hc hA ω δ hω)
    rw [specialUnaryChain_toMap]
    exact (special_preserves_volume hc C (Nat.zero_lt_succ n) T ω π hDensity).1
  exact pullback_unary_chain_volume_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A B hA hB hAP hBP hfinA (special_target_finite_labels C G.gamma T hfinA) hAF
    (special_pullback_volume_finite C G.gamma T hBP hfinA)
    ω π δ (suffixIndex (special_chain_rvArity_le T.chain) δ) hω hπ t
    (gamma_special_unary_chain _ T.chain hT) hData

end GammaNamed
end IntegrationInACVF.Section7
