import Integration7.GammaPreparedVolumeWitnessCover
import Integration7.IndexedVolumeFiniteWitnessGluing

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

theorem gamma_prepared_volume_witness_gluing
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf))
    (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (J : Finset {H : GammaVolumeCommonSchema F G // H.NoAuxiliary})
    (T : SpecialBijection A Z) (hT : GammaChainDefinable B T.chain)
    (hF : ∀ x : A, F.valid (rawVFParameter x.val))
    (hG : ∀ x : A, G.valid (rawVFParameter x.val))
    (hFA : ∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val))
    (hGA : ∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val))
    (hCover : ∀ x : Z, ∃ W ∈ J,
      ((GammaVolumeParameterRecode.prepared T hT).common W.val W.property).valid (rawPreparedKey x.val))
    (C : BaseContext M) {K : Set (Fin (p+l) → RV (M := M))}
    {R : (Fin (p+l) → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B (p+l) d K R)
    (hK : ∀ t ∈ K, ∃ x : Z, (flatKey x.val).2 = t)
    (P : ((GammaVolumeParameterRecode.prepared T hT).volumeObject F).IndexedPresentation BP)
    (Q : ((GammaVolumeParameterRecode.prepared T hT).volumeObject G).IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      VolumeBlowupEquivalent
        ((P.inContext hc C hP).toObject.extend hCD)
        ((Q.inContext hc C hQ).toObject.extend hCD) := by
  let D := GammaVolumeParameterRecode.prepared T hT
  let J' := J.image (fun W => D.common W.val W.property)
  have hDF : ∀ t ∈ K, (D.volumeObject F).valid (rvValues t) := by
    intro t ht
    obtain ⟨x,rfl⟩ := hK t ht
    exact D.volumeObject_valid F _ _ (fun j => ((flatKey x.val).2 j).property) (hFA x) (hF (T.inverseMap x))
  have hDG : ∀ t ∈ K, (D.volumeObject G).valid (rvValues t) := by
    intro t ht
    obtain ⟨x,rfl⟩ := hK t ht
    exact D.volumeObject_valid G _ _ (fun j => ((flatKey x.val).2 j).property) (hGA x) (hG (T.inverseMap x))
  apply gamma_volume_common_finite_indexed_glue hc (D.volumeObject F) (D.volumeObject G) J' C BP
    hDF hDG ?_ P Q hP hQ hBP hB
  intro t ht
  obtain ⟨x,rfl⟩ := hK t ht
  obtain ⟨W,hW,hvalid⟩ := hCover x
  exact ⟨D.common W.val W.property,Finset.mem_image.mpr ⟨W,hW,rfl⟩,hvalid⟩

end IntegrationInACVF.Section7
