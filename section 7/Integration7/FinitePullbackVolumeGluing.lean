module

public import Integration7.FinitePullbackVolumeUnions
public import Integration7.EmptyPullbackVolumeObjects
public import IntegrationSection5.RelativeSpecialRestriction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Common forward volume blowups of finite pullback partition pieces
assemble into common forward volume blowups of the whole objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ} {ι : Type}

theorem finite_pullback_volume_unions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (hVF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject V)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a)
    (E : ι → DefSet (M := M) (C.base : Set M) (n+1) b)
    (hDU : ∀ i, carrier (D i) ⊆ carrier U) (hEV : ∀ i, carrier (E i) ⊆ carrier V)
    (hDdisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hEdisj : ∀ i j, i ≠ j → Disjoint (carrier (E i)) (carrier (E j)))
    (hDP : ∀ i, IsRVPullback (carrier (D i))) (hEP : ∀ i, IsRVPullback (carrier (E i)))
    (δ : Fin a) (ε : Fin b) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero)
    (hε : ∀ p : V, (p.val.2 ε).val ≠ iRVZero)
    (hPieces : ∀ i, CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      (finitePullbackVolumePiece hc C Ξ U hUF D hDU δ hδ i)
      (finitePullbackVolumePiece hc C Ξ V hVF E hEV ε hε i)) (F : Finset ι) :
    CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      (finitePullbackVolumeUnion hc C Ξ U hUF D hDU δ hδ F)
      (finitePullbackVolumeUnion hc C Ξ V hVF E hEV ε hε F) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    apply CommonContextVolumeEquivalent.of_empty_essential hc C
    · exact pullback_volume_essential_empty hc (nativeMixedFiniteUnion D ∅)
        (pullback_finite_of_subset (native_mixed_union_subset D hDU ∅) hUF) δ
        (fun p => hδ ⟨p.val,native_mixed_union_subset D hDU ∅ p.property⟩) (native_mixed_union_empty D)
    · exact pullback_volume_essential_empty hc (nativeMixedFiniteUnion E ∅)
        (pullback_finite_of_subset (native_mixed_union_subset E hEV ∅) hVF) ε
        (fun p => hε ⟨p.val,native_mixed_union_subset E hEV ∅ p.property⟩) (native_mixed_union_empty E)
  | insert i F hi ih =>
    have hLeft := finite_pullback_volume_union_split hc C Ξ U hUF D hDU hDdisj hDP δ hδ i F hi
    have hRight := finite_pullback_volume_union_split hc C Ξ V hVF E hEV hEdisj hEP ε hε i F hi
    exact (hLeft.symm hc).trans hc (((hPieces i).coprod hc ih).trans hc hRight)

theorem finite_pullback_volume_union_covers
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a) (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (F : Finset ι)
    (hCover : carrier U = nativeMixedFiniteUnionSet D F) :
    finitePullbackVolumeUnion hc C Ξ U hUF D hDU δ hδ F =
      pullbackCoordinateGammaObject hc C (Set.Subset.refl _) U
        ((gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_set _ (setDefinable U)) hUF δ hδ := by
  have he : nativeMixedFiniteUnion D F = U := defSet_eq_of_carrier_eq hCover.symm
  cases he
  rfl

theorem finite_pullback_volume_partition_gluing
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (hVF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject V)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a)
    (E : ι → DefSet (M := M) (C.base : Set M) (n+1) b)
    (hDU : ∀ i, carrier (D i) ⊆ carrier U) (hEV : ∀ i, carrier (E i) ⊆ carrier V)
    (hDdisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hEdisj : ∀ i j, i ≠ j → Disjoint (carrier (E i)) (carrier (E j)))
    (hDP : ∀ i, IsRVPullback (carrier (D i))) (hEP : ∀ i, IsRVPullback (carrier (E i)))
    (δ : Fin a) (ε : Fin b) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero)
    (hε : ∀ p : V, (p.val.2 ε).val ≠ iRVZero)
    (hPieces : ∀ i, CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      (finitePullbackVolumePiece hc C Ξ U hUF D hDU δ hδ i)
      (finitePullbackVolumePiece hc C Ξ V hVF E hEV ε hε i))
    (F : Finset ι) (hUcover : carrier U = nativeMixedFiniteUnionSet D F)
    (hVcover : carrier V = nativeMixedFiniteUnionSet E F) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) U ((gammaLogicInput G).real_set _ (setDefinable U)) hUF δ hδ)
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) V ((gammaLogicInput G).real_set _ (setDefinable V)) hVF ε hε) := by
  have h := finite_pullback_volume_unions_compare hc C Ξ U V hUF hVF D E hDU hEV hDdisj hEdisj hDP hEP
    δ ε hδ hε hPieces F
  rw [finite_pullback_volume_union_covers hc C Ξ U hUF D hDU δ hδ F hUcover,
    finite_pullback_volume_union_covers hc C Ξ V hVF E hEV ε hε F hVcover] at h
  exact h

end IntegrationInACVF.Section7
