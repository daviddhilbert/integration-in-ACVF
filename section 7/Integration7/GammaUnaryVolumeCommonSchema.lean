module

public import Integration7.GammaUnarySpecialVolumeSchemata
public import Integration7.GammaUnaryPullbackVolumeComparison
public import Integration7.VolumeSchemaRowExtension
public import Integration7.UnarySmallContextPreparation
public import Integration7.UnaryVolumeChainCorollary
public import Integration7.UnaryPullbackVolumeComparison
public import Integration7.SpecialVolumeConjugacy
public import Integration7.LiteralRVVolumeForms
public import Integration7.PositiveVolumeParameterExtension

@[expose] public section

/-! The unary common-volume-blowup comparison has a finite formula
witness over the original Gamma base. The preparation context is allowed
to contain additional internal RV representative codes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (carrier extendBase GammaSetDefinable GammaGraphDefinable GammaChainDefinable pointMapGraph rvObjectArity)
open SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

set_option maxHeartbeats 1600000 in
theorem gamma_unary_volume_common_schema {κ : Cardinal}
    {B₀ : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B₀.real < κ) (hgamma : Cardinal.mk B₀.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hPC : B₀.real ∪ Set.range z ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B₀.gamma) (hγ1 : 1 < γ)
    (FBase : VFFieldBase (B₀.real ∪ Set.range z))
    (F G : @RVFiniteObject M N (C.base : Set M) 1)
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    (π : VolumeForm (canonicalFiniteRVObject hc G).obj.domain)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1
      (@RVObject.arity M N (C.base : Set M) 1 F.obj))
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1
      (@RVObject.arity M N (C.base : Set M) 1 G.obj))
    (hA : @Section6.PresentsLift M N hN (C.base : Set M) 1 F.obj (Section6.normalizedPointSet A))
    (hB : @Section6.PresentsLift M N hN (C.base : Set M) 1 G.obj (Section6.normalizedPointSet B))
    (δ : Fin (@RVObject.arity M N (C.base : Set M) 1 F.obj))
    (ε : Fin (@RVObject.arity M N (C.base : Set M) 1 G.obj))
    (hω : ∀ u, ω.value u = u.val δ) (hπ : ∀ u, π.value u = u.val ε)
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (hAΓ : GammaSetDefinable ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ (carrier A)) (hBΓ : GammaSetDefinable ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ (carrier B))
    (hfΓ : GammaGraphDefinable ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ (pointMapGraph f))
    (hMeasure : PreservesVFVolume (literalRVVolumeForm hc F ω A hA)
      (literalRVVolumeForm hc G π B hB) (rawSpecialMap hc f))    (L : GammaRVVolumeSchema B₀ p (rvObjectArity F.obj) 0 sp)
    (R : GammaRVVolumeSchema B₀ p (rvObjectArity G.obj) 0 sp)
    (hL : L.valid z) (hR : R.valid z)
    (PL : RVVolumeSchemaRow
      (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) L z)
    (PR : RVVolumeSchemaRow
      (⟨canonicalFiniteRVObject hc G,π⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) 0) R z) :
    ∃ H : GammaVolumeCommonSchema L R, H.valid z := by
  obtain ⟨D, hCD, r, s, A', B', TA, TB, hTA, hTB, hA', hB', hcon, hback, hgΓ, _⟩ :=
    unary_bijection_preparation_in_context C ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ hPC γ hγ hγ1 FBase f hf hAΓ hBΓ hfΓ
  let FD := @Section6.FiniteRV.extendObject M N (C.base : Set M) (D.base : Set M) 1 hCD F
  let GD := @Section6.FiniteRV.extendObject M N (C.base : Set M) (D.base : Set M) 1 hCD G
  let AD := extendBase A hCD
  let BD := extendBase B hCD
  let fD : SpecialTransformations.Section5.Map AD BD :=
    @SpecialTransformations.DefinableGeometry.Map.extend LRV M N
      (SpecialTransformations.Section5.pointSpace 1 (@RVObject.arity M N (C.base : Set M) 1 F.obj))
      (SpecialTransformations.Section5.pointSpace 1 (@RVObject.arity M N (C.base : Set M) 1 G.obj))
      (C.base : Set M) (D.base : Set M) A B f hCD
  have hAD := Section6.normalizedPresentsLift_extendBase hCD hA
  have hBD := Section6.normalizedPresentsLift_extendBase hCD hB
  have hωD : ∀ u, (ω.extend hCD).value u = u.val δ :=
    fun u => hω ⟨u.val, u.property⟩
  have hπD : ∀ u, (π.extend hCD).value u = u.val ε :=
    fun u => hπ ⟨u.val, u.property⟩
  obtain ⟨hAF, hδA, WA, hWA, ⟨eA⟩⟩ :=
    corollary_6_10_unary_volume hc D FD (ω.extend hCD) hAD δ hωD TA
  obtain ⟨hBF, hεB, WB, hWB, ⟨eB⟩⟩ :=
    corollary_6_10_unary_volume hc D GD (π.extend hCD) hBD ε hπD TB
  let ωD := literalRVVolumeForm hc FD (ω.extend hCD) AD hAD
  let πD := literalRVVolumeForm hc GD (π.extend hCD) BD hBD
  let θA := rawPullbackVolumeForm hc A' hA' hAF (TA.chain.labelIndex δ) hδA
  let θB := rawPullbackVolumeForm hc B' hB' hBF (TB.chain.labelIndex ε) hεB
  have hmD : PreservesVFVolume ωD πD (rawSpecialMap hc fD) :=
    hMeasure.extend hCD
  have hωT : ∀ p, ωD.value p = θA.value ((rawSpecialMap hc TA.toMap) p) :=
    special_retained_volume_density hc TA hA' hAF δ hδA ωD
      (literalRVVolumeForm_density hc FD (ω.extend hCD) AD hAD δ hωD)
  have hπT : ∀ p, πD.value p = θB.value ((rawSpecialMap hc TB.toMap) p) :=
    special_retained_volume_density hc TB hB' hBF ε hεB πD
      (literalRVVolumeForm_density hc GD (π.extend hCD) BD hBD ε hπD)
  have hm := unary_volume_conjugate hc D TA TB fD hf ωD πD θA θB hωT hπT hmD
  let g := IntegrationInACVF.Section5.unaryConjugate TA TB fD
  have hg := IntegrationInACVF.Section5.unaryConjugate_bijective TA TB fD hf
  let e := unaryPullbackVolumeIso hc D ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ (hPC.trans hCD) A' B' hA' hB' hAF hBF
    (TA.chain.labelIndex δ) (TB.chain.labelIndex ε) hδA hεB g hg hcon hback hgΓ hm
  have hA'Γ := GammaChainDefinable.target ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ TA.chain hTA
  have hB'Γ := GammaChainDefinable.target ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ TB.chain hTB
  let AΓ := Section6.FiniteRV.gammaPullbackAt (hPC.trans hCD) A' hA'Γ hAF
  let BΓ := Section6.FiniteRV.gammaPullbackAt (hPC.trans hCD) B' hB'Γ hBF
  let VA := pullbackCoordinateVolumeObject hc A' hAF (TA.chain.labelIndex δ) hδA
  let VB := pullbackCoordinateVolumeObject hc B' hBF (TB.chain.labelIndex ε) hεB
  obtain ⟨LA,hLA,PA⟩ := gamma_canonical_label_object_promotion hc D hκ hs hreal hgamma z hz
    AΓ VA.form (Fin.natAdd 1 (TA.chain.labelIndex δ)) (fun _ => rfl)
  obtain ⟨LB,hLB,PB⟩ := gamma_canonical_label_object_promotion hc D hκ hs hreal hgamma z hz
    BΓ VB.form (Fin.natAdd 1 (TB.chain.labelIndex ε)) (fun _ => rfl)
  let FΓ := Section6.FiniteRV.gammaLiteralAt (hPC.trans hCD) FD hAD hAΓ
  let GΓ := Section6.FiniteRV.gammaLiteralAt (hPC.trans hCD) GD hBD hBΓ
  let U : PositiveRVVolumeObject (M := M) (D.base : Set M) 0 := ⟨canonicalFiniteRVObject hc FD,ω.extend hCD⟩
  let V : PositiveRVVolumeObject (M := M) (D.base : Set M) 0 := ⟨canonicalFiniteRVObject hc GD,π.extend hCD⟩
  obtain ⟨HA,hHA⟩ := (gamma_unary_special_volume_schema_pair hc D hκ hs hreal hgamma z hz
    (hPC.trans hCD) TA.chain hTA).1 (@RVObject.domain M N (D.base : Set M) 1 FD.obj)
      (@RVObject.volume M N (D.base : Set M) 1 FD.obj) FD.property (ω.extend hCD) hAD δ hωD TA.alternating
      hAF hδA U (RVVolumeIso.refl hc D U)
      (gamma_volume_refl hc D U (canonical_gamma_object_volume_graph hc FΓ))
      L LA hL hLA (PL.extend hCD) PA
  obtain ⟨HB,hHB⟩ := (gamma_unary_special_volume_schema_pair hc D hκ hs hreal hgamma z hz
    (hPC.trans hCD) TB.chain hTB).1 (@RVObject.domain M N (D.base : Set M) 1 GD.obj)
      (@RVObject.volume M N (D.base : Set M) 1 GD.obj) GD.property (π.extend hCD) hBD ε hπD TB.alternating
      hBF hεB V (RVVolumeIso.refl hc D V)
      (gamma_volume_refl hc D V (canonical_gamma_object_volume_graph hc GΓ))
      R LB hR hLB (PR.extend hCD) PB
  have heΓ := unaryPullbackVolumeIso_gamma hc D ⟨B₀.real ∪ Set.range z,B₀.gamma⟩ (hPC.trans hCD)
    A' B' hA' hB' hAF hBF (TA.chain.labelIndex δ) (TB.chain.labelIndex ε) hδA hεB
    g hg hcon hback hgΓ hm hA'Γ
  obtain ⟨I,hIS,hIT,hI,_⟩ := gamma_volume_row_comparison_promotion_free hc hκ hs hreal hgamma
    D z hz LA LB hLA hLB PA PB e heΓ
  let H : GammaVolumeCommonSchema L R := {
    leftArity := 1+r
    rightArity := 1+s
    leftObject := LA
    rightObject := LB
    leftLength := TA.length
    rightLength := TB.length
    leftChain := HA
    rightChain := HB
    comparison := I }
  refine ⟨H,hL,hR,hLA,hLB,hHA,hHB,hI,?_,?_⟩
  · rw [hIS]; exact LA.sameRow_refl z hz
  · rw [hIT]; exact LB.sameRow_refl z hz

end IntegrationInACVF.Section7
