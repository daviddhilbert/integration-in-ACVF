import Integration7.SpecialRetainedVolumeChains
import Integration7.PullbackCoordinateGammaObjects
import IntegrationSection6.GammaFiniteMixedBijections

/-! Finite RV volume data of an actual special-prepared pullback,
with its literal transported density coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem special_target_finite_labels (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : SpecialBijection A B)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite :=
  finite_rv_fibres_of_gamma_bijection (B := (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) C.uncountable.le
    C.saturated C.small T.toMap T.bijective
    ((gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_map_graph T.toMap) hfinA

theorem special_pullback_volume_finite (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : SpecialBijection A B) (hBP : IsRVPullback (carrier B))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M (@CanonicalStructure.normalize M sM)
      _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject B)) :=
  pullbackObject_finiteVolume B hBP (special_target_finite_labels C Ξ T hfinA)

def specialPullbackVolumeGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : SpecialBijection A B) (hBP : IsRVPullback (carrier B))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    GammaVolumeObjects (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (C.base : Set M) n :=
  pullbackCoordinateGammaObject hc C (Set.Subset.refl _) B
    ((gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_set _ (setDefinable B))
    (special_pullback_volume_finite C Ξ T hBP hfinA) (suffixIndex (special_chain_rvArity_le T.chain) δ)
    (special_retained_density_nonzero T δ hδ)

end IntegrationInACVF.Section7
