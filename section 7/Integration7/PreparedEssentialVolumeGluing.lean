module

public import Integration7.PreparedVolumeGeometryContexts
public import Integration7.GammaEssentialIndexedVolumeUniformity
public import IntegrationSection6.GammaPreparedIndexValues

@[expose] public section

/-! Finite volume witnesses prepared over VF parameters assemble to
actual common forward blowups over a finite-volume RV key base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a b d k : ℕ}
variable {A : DefSet (M := M) S p 0} {Z : DefSet (M := M) S p l}

theorem prepared_volume_essential_geometry_gluing
    {κ : Cardinal} (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf))
    (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (J : Finset (GammaVolumeCommonSchema F G))
    (T : SpecialBijection A Z) (hT : GammaChainDefinable B T.chain)
    (hF : ∀ x : A, F.valid (rawVFParameter x.val))
    (hG : ∀ x : A, G.valid (rawVFParameter x.val))
    (hFA : ∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val))
    (hGA : ∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val))
    (hCover : ∀ x : Z, (∀ j, (rv (x.val.1 j)).val ≠ iRVZero) → ∃ W ∈ J,
      ((GammaVolumeParameterRecode.prepared T hT).commonWithFrozenParameters W).valid (rawPreparedKey x.val))
    (C : BaseContext M) (BP : PreparedIndexPresentation B Z)
    (P : ((GammaVolumeParameterRecode.prepared T hT).volumeObject F).IndexedPresentation BP)
    (Q : ((GammaVolumeParameterRecode.prepared T hT).volumeObject G).IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent B (D.base : Set M) (p+k)
        ⟨(P.inContext hc C hP).toObject.extend hCD,(P.gamma_object hc C hP).extend hCD⟩
        ⟨(Q.inContext hc C hQ).toObject.extend hCD,(Q.gamma_object hc C hQ).extend hCD⟩ := by
  let D := GammaVolumeParameterRecode.prepared T hT
  have hDF : ∀ t ∈ preparedKeyDomain Z, (D.volumeObject F).valid (rvValues t) := by
    intro t ht
    obtain ⟨x,rfl⟩ := ht
    exact D.volumeObject_valid F _ _ (fun j => ((flatKey x.val).2 j).property) (hFA x) (hF (T.inverseMap x))
  have hDG : ∀ t ∈ preparedKeyDomain Z, (D.volumeObject G).valid (rvValues t) := by
    intro t ht
    obtain ⟨x,rfl⟩ := ht
    exact D.volumeObject_valid G _ _ (fun j => ((flatKey x.val).2 j).property) (hGA x) (hG (T.inverseMap x))
  apply gamma_indexed_volume_uniformity_on_essential_indices hc
    hκ hs hreal hgamma (D.volumeObject F) (D.volumeObject G) BP hDF hDG ?_ C P Q hP hQ hB
  intro t ht hNZ
  obtain ⟨x,rfl⟩ := ht
  have hNZ' : ∀ j, (rv (x.val.1 j)).val ≠ iRVZero := by
    intro j
    have hv := congrFun (PreparedIndexPresentation.totalVolume_eq Z BP (flatKey x.val).2 ⟨x,rfl⟩) j
    intro hz
    apply hNZ j
    calc
      (BP.totalVolume (flatKey x.val).2 j).val =
          ((flatKey x.val).2 (Fin.castAdd l j)).val := congrArg Subtype.val hv
      _ = (rv (x.val.1 j)).val := by simp only [flatKey,Fin.append_left,key]
      _ = iRVZero := hz
  obtain ⟨W,hW,hvalid⟩ := hCover x hNZ'
  exact ⟨D.commonWithFrozenParameters W,hvalid⟩

end IntegrationInACVF.Section7
