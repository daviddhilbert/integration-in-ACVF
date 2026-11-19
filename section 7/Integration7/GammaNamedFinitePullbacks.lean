import Integration7.GammaNamedSpecialPullbacks
import Integration7.FinitePullbackVolumeGluing

/-! Gamma-named finite pullback unions: pieces and unions of a finite family
of Gamma pullback domains, binary partition isomorphisms with Gamma graphs,
and gluing of piecewise Gamma-named common-context equivalences. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M}
variable {n a b : ℕ} {ι : Type}

theorem gamma_empty_point_set : GammaSetDefinable G (∅ : Set (Point (M := M) n a)) := by
  have hU := (gammaLogicInput G).real_set _ (setDefinable (PresentedSet.univ (pointSpace (M := M) n a) G.real))
  have h := (gammaLogicInput G).sdiff hU hU
  rw [Set.diff_self] at h
  exact h

theorem gamma_native_mixed_union (D : ι → DefSet (M := M) S n a)
    (hD : ∀ i, GammaSetDefinable G (carrier (D i))) (F : Finset ι) :
    GammaSetDefinable G (nativeMixedFiniteUnionSet D F) := by
  classical
  induction F using Finset.induction_on with
  | empty => rw [native_mixed_union_empty]; exact gamma_empty_point_set
  | insert i F hi ih => rw [native_mixed_union_insert]; exact (gammaLogicInput G).union (hD i) ih

namespace GammaNamed

def finitePullbackVolumePiece (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a) (hD : ∀ i, GammaSetDefinable G (carrier (D i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (i : ι) :
    GammaVolumeObjects G (C.base : Set M) n :=
  pullbackCoordinateGammaObject hc C hGC (D i) (hD i) (pullback_finite_of_subset (hDU i) hUF)
    δ (fun p => hδ ⟨p.val,hDU i p.property⟩)

def finitePullbackVolumeUnion (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a) (hD : ∀ i, GammaSetDefinable G (carrier (D i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (F : Finset ι) :
    GammaVolumeObjects G (C.base : Set M) n :=
  let A := nativeMixedFiniteUnion D F
  let hAU := native_mixed_union_subset D hDU F
  pullbackCoordinateGammaObject hc C hGC A (gamma_native_mixed_union D hD F)
    (pullback_finite_of_subset hAU hUF) δ (fun p => hδ ⟨p.val,hAU p.property⟩)

theorem finite_pullback_volume_union_split [DecidableEq ι]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a) (hD : ∀ i, GammaSetDefinable G (carrier (D i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hDP : ∀ i, IsRVPullback (carrier (D i)))
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (i : ι) (F : Finset ι) (hi : i ∉ F) :
    CommonContextVolumeEquivalent G C
      (GammaVolumeObjects.coprod (finitePullbackVolumePiece hc C G hGC U hUF D hD hDU δ hδ i)
        (finitePullbackVolumeUnion hc C G hGC U hUF D hD hDU δ hδ F))
      (finitePullbackVolumeUnion hc C G hGC U hUF D hD hDU δ hδ (insert i F)) := by
  let A := nativeMixedFiniteUnion D (insert i F)
  let R := nativeMixedFiniteUnion D F
  let hAU := native_mixed_union_subset D hDU (insert i F)
  let hRU := native_mixed_union_subset D hDU F
  have hPart : carrier A = carrier (D i) ∪ carrier R := native_mixed_union_insert D i F
  let e := pullbackVolumePartitionIso hc C A (D i) R
    (pullback_finite_of_subset hAU hUF) (pullback_finite_of_subset (hDU i) hUF)
    (pullback_finite_of_subset hRU hUF) hPart (native_mixed_union_disjoint D hDisj i F hi) (hDP i)
    δ (fun p => hδ ⟨p.val,hAU p.property⟩)
  have he : e.GammaDefinable G := gamma_pullback_volume_partition hc C A (D i) R _ _ _ hPart
    (native_mixed_union_disjoint D hDisj i F hi) (hDP i) δ _ hGC
    (gamma_native_mixed_union D hD _) (hD i) (gamma_native_mixed_union D hD F)
  exact CommonContextVolumeEquivalent.of_iso e he

theorem finite_pullback_volume_unions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (hVF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject V)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a)
    (E : ι → DefSet (M := M) (C.base : Set M) (n+1) b)
    (hD : ∀ i, GammaSetDefinable G (carrier (D i))) (hE : ∀ i, GammaSetDefinable G (carrier (E i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U) (hEV : ∀ i, carrier (E i) ⊆ carrier V)
    (hDdisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hEdisj : ∀ i j, i ≠ j → Disjoint (carrier (E i)) (carrier (E j)))
    (hDP : ∀ i, IsRVPullback (carrier (D i))) (hEP : ∀ i, IsRVPullback (carrier (E i)))
    (δ : Fin a) (ε : Fin b) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero)
    (hε : ∀ p : V, (p.val.2 ε).val ≠ iRVZero)
    (hPieces : ∀ i, CommonContextVolumeEquivalent G C
      (finitePullbackVolumePiece hc C G hGC U hUF D hD hDU δ hδ i)
      (finitePullbackVolumePiece hc C G hGC V hVF E hE hEV ε hε i)) (F : Finset ι) :
    CommonContextVolumeEquivalent G C
      (finitePullbackVolumeUnion hc C G hGC U hUF D hD hDU δ hδ F)
      (finitePullbackVolumeUnion hc C G hGC V hVF E hE hEV ε hε F) := by
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
    have hLeft := finite_pullback_volume_union_split hc C G hGC U hUF D hD hDU hDdisj hDP δ hδ i F hi
    have hRight := finite_pullback_volume_union_split hc C G hGC V hVF E hE hEV hEdisj hEP ε hε i F hi
    exact (hLeft.symm hc).trans hc (((hPieces i).coprod hc ih).trans hc hRight)

theorem finite_pullback_volume_union_covers
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hU : GammaSetDefinable G (carrier U))
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a) (hD : ∀ i, GammaSetDefinable G (carrier (D i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (F : Finset ι)
    (hCover : carrier U = nativeMixedFiniteUnionSet D F) :
    finitePullbackVolumeUnion hc C G hGC U hUF D hD hDU δ hδ F =
      pullbackCoordinateGammaObject hc C hGC U hU hUF δ hδ := by
  have he : nativeMixedFiniteUnion D F = U := defSet_eq_of_carrier_eq hCover.symm
  cases he
  rfl

theorem finite_pullback_volume_partition_gluing
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject U)))
    (hVF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject V)))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a)
    (E : ι → DefSet (M := M) (C.base : Set M) (n+1) b)
    (hD : ∀ i, GammaSetDefinable G (carrier (D i))) (hE : ∀ i, GammaSetDefinable G (carrier (E i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U) (hEV : ∀ i, carrier (E i) ⊆ carrier V)
    (hDdisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hEdisj : ∀ i j, i ≠ j → Disjoint (carrier (E i)) (carrier (E j)))
    (hDP : ∀ i, IsRVPullback (carrier (D i))) (hEP : ∀ i, IsRVPullback (carrier (E i)))
    (δ : Fin a) (ε : Fin b) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero)
    (hε : ∀ p : V, (p.val.2 ε).val ≠ iRVZero)
    (hPieces : ∀ i, CommonContextVolumeEquivalent G C
      (finitePullbackVolumePiece hc C G hGC U hUF D hD hDU δ hδ i)
      (finitePullbackVolumePiece hc C G hGC V hVF E hE hEV ε hε i))
    (F : Finset ι) (hUcover : carrier U = nativeMixedFiniteUnionSet D F)
    (hVcover : carrier V = nativeMixedFiniteUnionSet E F) :
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C hGC U hU hUF δ hδ)
      (pullbackCoordinateGammaObject hc C hGC V hV hVF ε hε) := by
  have h := finite_pullback_volume_unions_compare hc C G hGC U V hUF hVF D E hD hE hDU hEV hDdisj hEdisj
    hDP hEP δ ε hδ hε hPieces F
  rw [finite_pullback_volume_union_covers hc C G hGC U hU hUF D hD hDU δ hδ F hUcover,
    finite_pullback_volume_union_covers hc C G hGC V hV hVF E hE hEV ε hε F hVcover] at h
  exact h

end GammaNamed
end IntegrationInACVF.Section7
