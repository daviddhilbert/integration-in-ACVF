import Integration7.SelectedDefinableFamilyLiftBijections
import Integration7.VolumeFamilyRealizationIdentifications
import Integration7.PositiveVFVolumeAdditiveStructure

/-! Integration of the actual tagged family sum is additive. The proof
uses its full VF volume bijection to the coproduct, followed by the checked
additive integration equivalence. Arithmetic degree identifications are
explicit; no unsigned coordinate permutation is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

private theorem degree_add_heq {A : ℕ → Type} [∀ j, Add (A j)]
    {i j : ℕ} (h : i=j) {x y : A i} {u v : A j} (hx : HEq x u) (hy : HEq y v) :
    HEq (x+y) (u+v) := by
  cases h
  cases hx
  cases hy
  rfl

private theorem degree_zero_heq {A : ℕ → Type} [∀ j, Zero (A j)]
    {i j : ℕ} (h : i=j) : HEq (0 : A i) (0 : A j) := by
  cases h
  rfl

theorem selected_family_canonical_integral_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated (selectedVolumeFamilySum F G) =
      selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F +
        selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated G := by
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := (n+1)+k)
  have hClass : positiveVFVolumeIsoClass hc C (selectedVolumeFamilySum F G).fullLift =
      positiveVFVolumeIsoClass hc C F.fullLift + positiveVFVolumeIsoClass hc C G.fullLift :=
    (positiveVFVolumeIsoClass_eq_iff hc C).mpr ⟨VFVolumeIso.of_bijection (selectedFamilySumLiftBijection hc F G)⟩
  have hIntegral := (congrArg E hClass).trans (E.map_add _ _)
  have hF := selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F
  have hG := selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 G
  have hSum := selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (selectedVolumeFamilySum F G)
  exact eq_of_heq (hSum.trans ((heq_of_eq hIntegral).trans
    (degree_add_heq (family_realization_degree_eq n k) hF.symm hG.symm)))

theorem selected_zero_family_full_lift_empty (C : BaseContext M) (n k : ℕ) :
    (selectedZeroVolumeFamily C n k).fullLift.domain =
      DefSet.empty (rawMixedSpace (M := M) (n+(k+1)) (k+1)) (C.base : Set M) := by
  apply DefSet.eq_of_carrier_eq
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact ((mem_selected_rv_vf_tail_lift (selectedZeroVolumeFamily C n k).domain id p).mp hp).1

theorem selected_family_canonical_integral_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n k : ℕ) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated (selectedZeroVolumeFamily C (n+1) k) = 0 := by
  let F := selectedZeroVolumeFamily C (n+1) k
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := (n+1)+k)
  have hSmall : vfDim (rawRVSpace (M := M) 1) F.fullLift.domain < ((n+1)+k)+1 := by
    rw [selected_zero_family_full_lift_empty]
    exact (Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
      (.rv (k+1))).trans_lt (Nat.zero_lt_succ _)
  have hClass := positiveVFVolumeIsoClass_small hc C F.fullLift hSmall
  have hIntegral := (congrArg E hClass).trans
    (positive_volume_integration_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1)
  have hF := selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F
  exact eq_of_heq (hF.trans ((heq_of_eq hIntegral).trans
    (degree_zero_heq (A := PositiveVolumeBlowupClasses hc C) (family_realization_degree_eq n k))))

end IntegrationInACVF.Section7
