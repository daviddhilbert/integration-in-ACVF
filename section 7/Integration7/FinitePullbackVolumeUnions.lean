module

public import Integration7.NativeFiniteMixedUnions
public import Integration7.PullbackCoordinateGammaObjects
public import Integration7.GammaVolumePullbackPartitions
public import Integration7.CommonContextVolumePartitions
public import Integration7.GammaTermContextVolumeGeometry
public import IntegrationSection6.FinitePullbackSubsets

@[expose] public section

/-! Actual volume objects of finite pullback unions and their binary
partition isomorphisms, all over the original real context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ} {ι : Type}

def finitePullbackVolumePiece (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a) (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (i : ι) :
    GammaVolumeObjects (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (C.base : Set M) n :=
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  pullbackCoordinateGammaObject hc C (Set.Subset.refl _) (D i)
    ((gammaLogicInput G).real_set _ (setDefinable (D i))) (pullback_finite_of_subset (hDU i) hUF)
    δ (fun p => hδ ⟨p.val,hDU i p.property⟩)

def finitePullbackVolumeUnion (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a) (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (F : Finset ι) :
    GammaVolumeObjects (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (C.base : Set M) n :=
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedFiniteUnion D F
  let hAU := native_mixed_union_subset D hDU F
  pullbackCoordinateGammaObject hc C (Set.Subset.refl _) A
    ((gammaLogicInput G).real_set _ (setDefinable A)) (pullback_finite_of_subset hAU hUF)
    δ (fun p => hδ ⟨p.val,hAU p.property⟩)

theorem finite_pullback_volume_union_split [DecidableEq ι]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a) (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hDP : ∀ i, IsRVPullback (carrier (D i)))
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (i : ι) (F : Finset ι) (hi : i ∉ F) :
    CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      (GammaVolumeObjects.coprod (finitePullbackVolumePiece hc C Ξ U hUF D hDU δ hδ i)
        (finitePullbackVolumeUnion hc C Ξ U hUF D hDU δ hδ F))
      (finitePullbackVolumeUnion hc C Ξ U hUF D hDU δ hδ (insert i F)) := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedFiniteUnion D (insert i F)
  let R := nativeMixedFiniteUnion D F
  let hAU := native_mixed_union_subset D hDU (insert i F)
  let hRU := native_mixed_union_subset D hDU F
  have hPart : carrier A = carrier (D i) ∪ carrier R := native_mixed_union_insert D i F
  let e := pullbackVolumePartitionIso hc C A (D i) R
    (pullback_finite_of_subset hAU hUF) (pullback_finite_of_subset (hDU i) hUF)
    (pullback_finite_of_subset hRU hUF) hPart (native_mixed_union_disjoint D hDisj i F hi) (hDP i)
    δ (fun p => hδ ⟨p.val,hAU p.property⟩)
  have hBase : (C.base : Set M) = (Substructure.closure LRV G.real : Set M) := by
    change (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M)
    rw [Substructure.closure_eq]
  have he : e.GammaDefinable G := e.gamma_of_term_context hc C hBase
  exact CommonContextVolumeEquivalent.of_iso e he

end IntegrationInACVF.Section7
