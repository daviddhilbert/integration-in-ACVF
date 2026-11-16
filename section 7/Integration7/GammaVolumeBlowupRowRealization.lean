module

public import Integration7.GammaVolumeCertificateRowRealization
public import Integration7.VolumeBlowupSchemaRealization
public import Integration7.VolumeChainSchemaRealization
public import Integration7.GammaCanonicalElementaryGraphs

@[expose] public section

/-! A valid blowup formula realizes on arbitrary Gamma endpoint rows
with its center algebraic over the original named Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeBlowupSchema.realizeOnGamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
    {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp}
    (H : GammaRVVolumeBlowupSchema F G) (z : Fin p → M) (hz : H.valid z)
    (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (hU : VolumeObjectGamma U ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hV : VolumeObjectGamma V ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hB : B.real ⊆ (C.base : Set M)) (hzC : Set.range z ⊆ (C.base : Set M)) :
    ∃ (T : BaseContext M) (hCT : (C.base : Set M) ⊆ (T.base : Set M)),
      ∃ b : VolumeBlowup (U.extend hCT) (V.extend hCT),
        b.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ := by
  rcases hz with ⟨hF,hG,hA,hR,hAd,hS,hT,hSF,hSA,hTG,hTA⟩
  let Bz : Base (M := M) := ⟨B.real ∪ Set.range z,B.gamma⟩
  have hReal : Bz.real ⊆ (C.base : Set M) := fun _ hx => hx.elim (fun h => hB h) (fun h => hzC h)
  obtain ⟨P⟩ := H.center.realize z hA
  obtain ⟨Q⟩ := H.remainder.realize z hR
  obtain ⟨D₀,hCD₀,hP₀⟩ := P.exists_containingContext C hReal
  obtain ⟨D,hD₀D,hQ⟩ := Q.exists_containingContext D₀ (hReal.trans hCD₀)
  let hCD := hCD₀.trans hD₀D
  let hP := hP₀.trans hD₀D
  let A := (P.inContext hc D hP).toObject
  let R := (Q.inContext hc D hQ).toObject
  have hAP : RVVolumeSchemaRow A H.center z := P.inContext_schemaRow hc D H.center z hA hP
  have hRP : RVVolumeSchemaRow R H.remainder z := Q.inContext_schemaRow hc D H.remainder z hR hQ
  have hAdΓ := H.admissibility.admissible z hAd P.finite
  have hAPAd : BlowupAdmissible A := P.blowupAdmissibleInContext hc D hP hAdΓ
  have hAΓ : VolumeObjectGamma A Bz := P.gamma_object hc D hP
  have hRΓ : VolumeObjectGamma R Bz := Q.gamma_object hc D hQ
  have hCenter : GammaBlowupCenter A Bz := fun u => hAdΓ.algebraic ⟨u.val,u.property⟩
  let A' := elementaryVolumeObject D A hAPAd
  have hA'Γ : VolumeObjectGamma A' Bz := hAΓ.elementary_canonical hc D A hAPAd
  have hA'P : RVVolumeSchemaRow A' H.center.elementaryFormula z := hAP.elementary D hA hAPAd
  have hAS : RVVolumeSchemaRow (A.coprod R) H.sourceChart.target z :=
    (hAP.coprod hRP hF.1.1).congr (GammaRVVolumeSchema.sameRow_symm hSA)
  have hAT : RVVolumeSchemaRow (A'.coprod R) H.resultChart.target z :=
    (hA'P.coprod hRP hF.1.1).congr (GammaRVVolumeSchema.sameRow_symm hTA)
  obtain ⟨D₁,hDD₁,eS,heS⟩ := H.sourceChart.realizeOnGamma hc D z hS
    ((PU.extend hCD).congr (GammaRVVolumeSchema.sameRow_symm hSF)) hAS
    (hU.extend hCD) (hAΓ.coprod hRΓ) (hB.trans hCD) (hzC.trans hCD)
  obtain ⟨D₂,hD₁D₂,eT,heT⟩ := H.resultChart.realizeOnGamma hc D₁ z hT
    (((PV.extend hCD).extend hDD₁).congr (GammaRVVolumeSchema.sameRow_symm hTG)) (hAT.extend hDD₁)
    ((hV.extend hCD).extend hDD₁) ((hA'Γ.coprod hRΓ).extend hDD₁)
    (hB.trans (hCD.trans hDD₁)) (hzC.trans (hCD.trans hDD₁))
  let b : VolumeBlowup (U.extend (hCD.trans (hDD₁.trans hD₁D₂)))
      (V.extend (hCD.trans (hDD₁.trans hD₁D₂))) := {
    locus := (A.extend hDD₁).extend hD₁D₂
    complement := (R.extend hDD₁).extend hD₁D₂
    blownLocus := (A'.extend hDD₁).extend hD₁D₂
    elementary := ((elementaryVolumeBlowup D A hAPAd).extend hDD₁).extend hD₁D₂
    sourceIso := eS.extend hD₁D₂
    targetIso := eT }
  exact ⟨D₂,hCD.trans (hDD₁.trans hD₁D₂),b,
    ⟨(hAΓ.extend hDD₁).extend hD₁D₂,(hRΓ.extend hDD₁).extend hD₁D₂,
      (hA'Γ.extend hDD₁).extend hD₁D₂,gamma_canonical_full_packed_chart hc D A hAPAd hAΓ,
      (hCenter.extend hDD₁).extend hD₁D₂,heS.extend hD₁D₂,heT⟩⟩

end IntegrationInACVF.Section7
