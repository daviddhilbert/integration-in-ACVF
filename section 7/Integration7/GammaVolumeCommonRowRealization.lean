module

public import Integration7.GammaVolumeBlowupRowRealization

@[expose] public section

/-! Common formula witnesses realize as full original-Gamma geometric
chains on specified named rows. Exact chain lengths and the final
comparison chart survive all finite internal context extensions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaVolumeChainSchema.realizeOnGamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
    {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp} {r : ℕ}
    (H : GammaVolumeChainSchema F G r) (z : Fin p → M) (hz : H.valid z)
    (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (hU : VolumeObjectGamma U ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hV : VolumeObjectGamma V ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hB : B.real ⊆ (C.base : Set M)) (hzC : Set.range z ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      ∃ W : GammaVolumeObjects ⟨B.real ∪ Set.range z,B.gamma⟩ (D.base : Set M) k,
        GammaIteratedVolumeBlowup ⟨B.real ∪ Set.range z,B.gamma⟩ (D.base : Set M) k r
          ⟨U.extend hCD,hU.extend hCD⟩ W ∧
        ∃ e : RVVolumeIso W.val (V.extend hCD), e.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ := by
  cases H with
  | iso chart =>
    obtain ⟨D,hCD,e,he⟩ := chart.realizeOnGamma hc C z hz.1
      (PU.congr (GammaRVVolumeSchema.sameRow_symm hz.2.1))
      (PV.congr (GammaRVVolumeSchema.sameRow_symm hz.2.2)) hU hV hB hzC
    exact ⟨D,hCD,⟨U.extend hCD,hU.extend hCD⟩,.refl _,e,he⟩
  | step W head tail =>
    obtain ⟨P⟩ := W.realize z hz.1
    obtain ⟨D,hCD,hP⟩ := P.exists_containingContext C
      (fun _ hx => hx.elim (fun h => hB h) (fun h => hzC h))
    let A := (P.inContext hc D hP).toObject
    have hA : RVVolumeSchemaRow A W z := P.inContext_schemaRow hc D W z hz.1 hP
    have hAΓ := P.gamma_object hc D hP
    obtain ⟨D₁,hDD₁,b,hb⟩ := head.realizeOnGamma hc D z hz.2.1 (PU.extend hCD) hA
      (hU.extend hCD) hAΓ (hB.trans hCD) (hzC.trans hCD)
    obtain ⟨D₂,hD₁D₂,Y,hY,eY,heY⟩ := GammaVolumeChainSchema.realizeOnGamma hc D₁ tail z hz.2.2
      (hA.extend hDD₁) ((PV.extend hCD).extend hDD₁)
      (hAΓ.extend hDD₁) ((hV.extend hCD).extend hDD₁)
      (hB.trans (hCD.trans hDD₁)) (hzC.trans (hCD.trans hDD₁))
    exact ⟨D₂,hCD.trans (hDD₁.trans hD₁D₂),Y,
      .step (V := ⟨(A.extend hDD₁).extend hD₁D₂,(hAΓ.extend hDD₁).extend hD₁D₂⟩)
        ⟨b.extend hD₁D₂,hb.extend hD₁D₂⟩ hY,eY,heY⟩
termination_by r

theorem GammaVolumeCommonSchema.realizeOnGamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
    {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp}
    (H : GammaVolumeCommonSchema F G) (z : Fin p → M) (hz : H.valid z)
    (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (hU : VolumeObjectGamma U ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hV : VolumeObjectGamma V ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hB : B.real ⊆ (C.base : Set M)) (hzC : Set.range z ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent ⟨B.real ∪ Set.range z,B.gamma⟩ (D.base : Set M) k
        ⟨U.extend hCD,hU.extend hCD⟩ ⟨V.extend hCD,hV.extend hCD⟩ := by
  rcases hz with ⟨hF,hG,hL,hR,hLC,hRC,hCmp,hCmpL,hCmpR⟩
  obtain ⟨P⟩ := H.leftObject.realize z hL
  obtain ⟨Q⟩ := H.rightObject.realize z hR
  have hReal : B.real ∪ Set.range z ⊆ (C.base : Set M) :=
    fun _ hx => hx.elim (fun h => hB h) (fun h => hzC h)
  obtain ⟨D₀,hCD₀,hP₀⟩ := P.exists_containingContext C hReal
  obtain ⟨D,hD₀D,hQ⟩ := Q.exists_containingContext D₀ (hReal.trans hCD₀)
  let hCD := hCD₀.trans hD₀D
  let hP := hP₀.trans hD₀D
  let A := (P.inContext hc D hP).toObject
  let R := (Q.inContext hc D hQ).toObject
  have hAP := P.inContext_schemaRow hc D H.leftObject z hL hP
  have hRP := Q.inContext_schemaRow hc D H.rightObject z hR hQ
  have hAΓ := P.gamma_object hc D hP
  have hRΓ := Q.gamma_object hc D hQ
  obtain ⟨D₁,hDD₁,L,hLeft,eL,heL⟩ := H.leftChain.realizeOnGamma hc D z hLC
    (PU.extend hCD) hAP (hU.extend hCD) hAΓ (hB.trans hCD) (hzC.trans hCD)
  obtain ⟨D₂,hD₁D₂,Z,hRight,eR,heR⟩ := H.rightChain.realizeOnGamma hc D₁ z hRC
    ((PV.extend hCD).extend hDD₁) (hRP.extend hDD₁)
    ((hV.extend hCD).extend hDD₁) (hRΓ.extend hDD₁)
    (hB.trans (hCD.trans hDD₁)) (hzC.trans (hCD.trans hDD₁))
  let hDD₂ := hDD₁.trans hD₁D₂
  obtain ⟨D₃,hD₂D₃,e,he⟩ := H.comparison.realizeOnGamma hc D₂ z hCmp
    ((hAP.extend hDD₂).congr (GammaRVVolumeSchema.sameRow_symm hCmpL))
    ((hRP.extend hDD₂).congr (GammaRVVolumeSchema.sameRow_symm hCmpR))
    (hAΓ.extend hDD₂) (hRΓ.extend hDD₂) (hB.trans (hCD.trans hDD₂)) (hzC.trans (hCD.trans hDD₂))
  let c := (((eL.extend hD₁D₂).extend hD₂D₃).trans hc D₃ e).trans hc D₃ ((eR.extend hD₂D₃).symm hc D₃)
  exact ⟨D₃,hCD.trans (hDD₂.trans hD₂D₃),H.leftLength,H.rightLength,
    (L.extend hD₁D₂).extend hD₂D₃,Z.extend hD₂D₃,
    (hLeft.extend hD₁D₂).extend hD₂D₃,hRight.extend hD₂D₃,c,
    (((heL.extend hD₁D₂).extend hD₂D₃).trans hc D₃ _ he).trans hc D₃ _
      ((heR.extend hD₂D₃).symm hc D₃ _)⟩

end IntegrationInACVF.Section7
