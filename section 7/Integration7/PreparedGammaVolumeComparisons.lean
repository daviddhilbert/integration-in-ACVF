import Integration7.PreparedVolumeGeometryGammaGluing
import Integration7.GammaVFPreparedVolumeUniformity
import IntegrationSection6.GammaVFParameterBases
import IntegrationSection6.GammaPreparedIndexPresentation

/-! Pointwise common volume blowups over named VF parameters give one
preparation and actual common blowups of the assembled positive objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a b k : ℕ}

def HasPreparedGammaVolumeCommonComparison
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S p 0)
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf))
    (G : GammaRVVolumeSchema B p b k (fun _ => .vf)) : Prop :=
    ∃ l : ℕ, ∃ Z : DefSet (M := M) S p l, ∃ T : SpecialBijection A Z,
      ∃ hT : GammaChainDefinable B T.chain, ∃ hZ : IsRVPullback (carrier Z),
      ∃ BP : PreparedIndexPresentation B Z,
        (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
          (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
        (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
          (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
        (∀ t ∈ preparedKeyDomain Z,
          ((GammaVolumeParameterRecode.prepared T hT).volumeObject F).valid (rvValues t)) ∧
        (∀ t ∈ preparedKeyDomain Z,
          ((GammaVolumeParameterRecode.prepared T hT).volumeObject G).valid (rvValues t)) ∧
        ∀ (C : BaseContext M)
          (P : ((GammaVolumeParameterRecode.prepared T hT).volumeObject F).IndexedPresentation BP)
          (Q : ((GammaVolumeParameterRecode.prepared T hT).volumeObject G).IndexedPresentation BP)
          (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)),
          BP.codes ⊆ (C.base : Set M) → B.real ⊆ (C.base : Set M) →
          ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
            GammaVolumeBlowupEquivalent B (D.base : Set M) (p+k)
              ⟨(P.inContext hc C hP).toObject.extend hCD,(P.gamma_object hc C hP).extend hCD⟩
              ⟨(Q.inContext hc C hQ).toObject.extend hCD,(Q.gamma_object hc C hQ).extend hCD⟩

theorem HasPreparedGammaVolumeCommonComparison.toOrdinary
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S p 0)
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf))
    (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (h : HasPreparedGammaVolumeCommonComparison hc A F G) : HasPreparedVolumeCommonComparison hc A F G := by
  obtain ⟨l,Z,T,hT,hZ,BP,hFA,hGA,hDF,hDG,hComparison⟩ := h
  refine ⟨l,Z,T,hT,hZ,BP,hFA,hGA,hDF,hDG,?_⟩
  intro C P Q hP hQ hBP hB
  obtain ⟨D,hCD,h⟩ := hComparison C P Q hP hQ hBP hB
  exact ⟨D,hCD,h.toOrdinary hc D B⟩

end IntegrationInACVF.Section7
