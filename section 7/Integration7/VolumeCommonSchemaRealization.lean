import Integration7.VolumeChainSchemaRealization

/-! A valid common-volume-blowup formula witness gives actual common
forward blowups, with both specified lengths and the volume comparison. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaVolumeCommonSchema.realizeOn
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
    {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp}
    (H : GammaVolumeCommonSchema F G) (z : Fin p → M) (hz : H.valid z)
    (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (hB : B.real ⊆ (C.base : Set M)) (hzC : Set.range z ⊆ (C.base : Set M)) :
    ∃ (T : BaseContext M) (hCT : (C.base : Set M) ⊆ (T.base : Set M))
      (L R : PositiveRVVolumeObject (M := M) (T.base : Set M) k),
      IteratedVolumeBlowup H.leftLength (U.extend hCT) L ∧
      IteratedVolumeBlowup H.rightLength (V.extend hCT) R ∧ Nonempty (RVVolumeIso L R) := by
  rcases hz with ⟨hF,hG,hL,hR,hLC,hRC,hCmp,hCmpL,hCmpR⟩
  obtain ⟨P⟩ := H.leftObject.realize z hL
  obtain ⟨Q⟩ := H.rightObject.realize z hR
  obtain ⟨D₀,hCD₀,hP₀⟩ := P.exists_containingContext C
    (fun _ hx => hx.elim (fun hx => hB hx) (fun hx => hzC hx))
  obtain ⟨D,hD₀D,hQ⟩ := Q.exists_containingContext D₀
    (fun _ hx => hCD₀ (hx.elim (fun hx => hB hx) (fun hx => hzC hx)))
  let hCD := hCD₀.trans hD₀D
  let A := (P.inContext hc D (hP₀.trans hD₀D)).toObject
  let R := (Q.inContext hc D hQ).toObject
  have hA : RVVolumeSchemaRow A H.leftObject z :=
    P.inContext_schemaRow hc D H.leftObject z hL (hP₀.trans hD₀D)
  have hRP : RVVolumeSchemaRow R H.rightObject z :=
    Q.inContext_schemaRow hc D H.rightObject z hR hQ
  obtain ⟨D₁,hDD₁,L',hL',⟨eL⟩⟩ := GammaVolumeChainSchema.realizeOn
    (U := U.extend hCD) (V := A) hc D H.leftChain z hLC (PU.extend hCD) hA
    (hB.trans hCD) (hzC.trans hCD)
  obtain ⟨D₂,hD₁D₂,R',hR',⟨eR⟩⟩ := GammaVolumeChainSchema.realizeOn
    (U := (V.extend hCD).extend hDD₁) (V := R.extend hDD₁) hc D₁ H.rightChain z hRC
    ((PV.extend hCD).extend hDD₁) (hRP.extend hDD₁)
    (hB.trans (hCD.trans hDD₁)) (hzC.trans (hCD.trans hDD₁))
  obtain ⟨D₃,hD₂D₃,e,_⟩ := GammaRVVolumeIsoCertificateSchema.realizeOn
    (U := (A.extend hDD₁).extend hD₁D₂) (V := (R.extend hDD₁).extend hD₁D₂)
    hc D₂ H.comparison z hCmp
    (((hA.extend hDD₁).extend hD₁D₂).congr (GammaRVVolumeSchema.sameRow_symm hCmpL))
    (((hRP.extend hDD₁).extend hD₁D₂).congr (GammaRVVolumeSchema.sameRow_symm hCmpR))
    (hB.trans (hCD.trans (hDD₁.trans hD₁D₂)))
    (hzC.trans (hCD.trans (hDD₁.trans hD₁D₂)))
  exact ⟨D₃,hCD.trans (hDD₁.trans (hD₁D₂.trans hD₂D₃)),
    (L'.extend hD₁D₂).extend hD₂D₃,R'.extend hD₂D₃,
    (hL'.extend hD₁D₂).extend hD₂D₃,hR'.extend hD₂D₃,
    ⟨(((eL.extend hD₁D₂).extend hD₂D₃).trans hc D₃ e).trans hc D₃
      ((eR.extend hD₂D₃).symm hc D₃)⟩⟩

end IntegrationInACVF.Section7
