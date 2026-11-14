import Integration7.GammaVolumeBlowupSchemata
import Integration7.GammaVolumeAdmissibilityContexts
import Integration7.VolumeCertificateContextRealization
import Integration7.VolumeSchemaCoproductSemantics
import Integration7.VolumeSchemaElementarySemantics
import Integration7.VolumeExtensionCoherence

/-! A valid finite formula witness realizes an actual volume blowup of
any interpreted endpoints, after a finite internal parameter extension. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeBlowupSchema.realizeOn
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
    {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp}
    (H : GammaRVVolumeBlowupSchema F G) (z : Fin p → M) (hz : H.valid z)
    (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (hB : B.real ⊆ (C.base : Set M)) (hzC : Set.range z ⊆ (C.base : Set M)) :
    ∃ (T : BaseContext M) (hCT : (C.base : Set M) ⊆ (T.base : Set M)),
      Nonempty (VolumeBlowup (U.extend hCT) (V.extend hCT)) := by
  rcases hz with ⟨hF,hG,hA,hR,hAd,hS,hT,hSF,hSA,hTG,hTA⟩
  obtain ⟨P⟩ := H.center.realize z hA
  obtain ⟨Q⟩ := H.remainder.realize z hR
  obtain ⟨EP,hEP,hPcodes⟩ := P.finite.finite_extra
  obtain ⟨EQ,hEQ,hQcodes⟩ := Q.finite.finite_extra
  let D := finiteVolumeParameterContext C (EP ∪ EQ) (hEP.union hEQ)
  have hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ hx => finiteVolumeParameterContext_contains C _ _ (Or.inl hx)
  have hReal : B.real ∪ Set.range z ⊆ (D.base : Set M) :=
    fun _ hx => hCD (hx.elim (fun hx => hB hx) (fun hx => hzC hx))
  have hP : P.finite.codes ⊆ (D.base : Set M) := by
    rw [hPcodes]
    rintro x (hx | hx)
    · exact hReal hx
    · exact finiteVolumeParameterContext_contains C _ _ (Or.inr (Or.inl hx))
  have hQ : Q.finite.codes ⊆ (D.base : Set M) := by
    rw [hQcodes]
    rintro x (hx | hx)
    · exact hReal hx
    · exact finiteVolumeParameterContext_contains C _ _ (Or.inr (Or.inr hx))
  let A := (P.inContext hc D hP).toObject
  let R := (Q.inContext hc D hQ).toObject
  have hAP : RVVolumeSchemaRow A H.center z := P.inContext_schemaRow hc D H.center z hA hP
  have hRP : RVVolumeSchemaRow R H.remainder z := Q.inContext_schemaRow hc D H.remainder z hR hQ
  have hAPAd : BlowupAdmissible A := P.blowupAdmissibleInContext hc D hP
    (H.admissibility.admissible z hAd P.finite)
  let A' := elementaryVolumeObject D A hAPAd
  have hA'P : RVVolumeSchemaRow A' H.center.elementaryFormula z := hAP.elementary D hA hAPAd
  have hAS : RVVolumeSchemaRow (A.coprod R) H.sourceChart.target z :=
    (hAP.coprod hRP hF.1.1).congr (GammaRVVolumeSchema.sameRow_symm hSA)
  have hAT : RVVolumeSchemaRow (A'.coprod R) H.resultChart.target z :=
    (hA'P.coprod hRP hF.1.1).congr (GammaRVVolumeSchema.sameRow_symm hTA)
  obtain ⟨D₁,hDD₁,eS,_⟩ := GammaRVVolumeIsoCertificateSchema.realizeOn
    (U := U.extend hCD) (V := A.coprod R) hc D H.sourceChart z hS
    ((PU.extend hCD).congr (GammaRVVolumeSchema.sameRow_symm hSF)) hAS
    (hB.trans hCD) (hzC.trans hCD)
  obtain ⟨D₂,hD₁D₂,eT,_⟩ := GammaRVVolumeIsoCertificateSchema.realizeOn
    (U := (V.extend hCD).extend hDD₁) (V := (A'.coprod R).extend hDD₁)
    hc D₁ H.resultChart z hT
    (((PV.extend hCD).extend hDD₁).congr (GammaRVVolumeSchema.sameRow_symm hTG)) (hAT.extend hDD₁)
    (hB.trans (hCD.trans hDD₁)) (hzC.trans (hCD.trans hDD₁))
  refine ⟨D₂,hCD.trans (hDD₁.trans hD₁D₂),⟨{
    locus := (A.extend hDD₁).extend hD₁D₂
    complement := (R.extend hDD₁).extend hD₁D₂
    blownLocus := (A'.extend hDD₁).extend hD₁D₂
    elementary := ((elementaryVolumeBlowup D A hAPAd).extend hDD₁).extend hD₁D₂
    sourceIso := eS.extend hD₁D₂
    targetIso := eT }⟩⟩

end IntegrationInACVF.Section7
