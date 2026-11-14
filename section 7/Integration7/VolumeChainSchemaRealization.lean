import Integration7.GammaVolumeChainSchemata
import Integration7.VolumeBlowupSchemaRealization

/-! Valid formula chains realize exactly their encoded number of actual
blowups, followed by a volume isomorphism of the endpoint. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaVolumeGraphPresentation.exists_containingContext {a n : ℕ}
    {D : Set (Fin a → RV (M := M))}
    {R : (Fin a → RV (M := M)) → (Fin n → RV (M := M)) → Prop}
    {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}
    (C : BaseContext M) (P : GammaVolumeGraphPresentation B a n D R W)
    (hB : B.real ⊆ (C.base : Set M)) :
    ∃ T : BaseContext M, (C.base : Set M) ⊆ (T.base : Set M) ∧ P.finite.codes ⊆ (T.base : Set M) := by
  obtain ⟨E,hE,hcodes⟩ := P.finite.finite_extra
  refine ⟨finiteVolumeParameterContext C E hE,
    (fun _ hx => finiteVolumeParameterContext_contains C E hE (Or.inl hx)),?_⟩
  rw [hcodes]
  rintro x (hx | hx)
  · exact finiteVolumeParameterContext_contains C E hE (Or.inl (hB hx))
  · exact finiteVolumeParameterContext_contains C E hE (Or.inr hx)

theorem GammaVolumeChainSchema.realizeOn
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
    {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp} {r : ℕ}
    (H : GammaVolumeChainSchema F G r) (z : Fin p → M) (hz : H.valid z)
    (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (hB : B.real ⊆ (C.base : Set M)) (hzC : Set.range z ⊆ (C.base : Set M)) :
    ∃ (T : BaseContext M) (hCT : (C.base : Set M) ⊆ (T.base : Set M))
      (W : PositiveRVVolumeObject (M := M) (T.base : Set M) k),
      IteratedVolumeBlowup r (U.extend hCT) W ∧ Nonempty (RVVolumeIso W (V.extend hCT)) := by
  cases H with
  | iso chart =>
    obtain ⟨T,hCT,e,_⟩ := GammaRVVolumeIsoCertificateSchema.realizeOn
      (U := U) (V := V) hc C chart z hz.1
      (PU.congr (GammaRVVolumeSchema.sameRow_symm hz.2.1))
      (PV.congr (GammaRVVolumeSchema.sameRow_symm hz.2.2)) hB hzC
    exact ⟨T,hCT,U.extend hCT,.refl _,⟨e⟩⟩
  | step W head tail =>
    obtain ⟨P⟩ := W.realize z hz.1
    obtain ⟨D,hCD,hP⟩ := P.exists_containingContext C
      (fun _ hx => hx.elim (fun hx => hB hx) (fun hx => hzC hx))
    let A := (P.inContext hc D hP).toObject
    have hA : RVVolumeSchemaRow A W z := P.inContext_schemaRow hc D W z hz.1 hP
    obtain ⟨D₁,hDD₁,⟨b⟩⟩ := GammaRVVolumeBlowupSchema.realizeOn
      (U := U.extend hCD) (V := A) hc D head z hz.2.1 (PU.extend hCD) hA
      (hB.trans hCD) (hzC.trans hCD)
    obtain ⟨D₂,hD₁D₂,Y,hY,eY⟩ := GammaVolumeChainSchema.realizeOn
      (U := A.extend hDD₁) (V := (V.extend hCD).extend hDD₁) hc D₁ tail z hz.2.2
      (hA.extend hDD₁) ((PV.extend hCD).extend hDD₁)
      (hB.trans (hCD.trans hDD₁)) (hzC.trans (hCD.trans hDD₁))
    exact ⟨D₂,hCD.trans (hDD₁.trans hD₁D₂),Y,.step ⟨b.extend hD₁D₂⟩ hY,eY⟩
termination_by r

end IntegrationInACVF.Section7
