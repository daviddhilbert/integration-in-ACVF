module

public import Integration7.GammaVolumeLiftChartRealization
public import Integration7.GammaUnaryVolumeCommonSchema
public import Integration7.RawVFVolumeComposition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Two retained-density lift charts from the same mixed source give
a finite original-Gamma common-volume-blowup witness. The VF components
may move, provided each follows a checked Jacobian-one map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b c : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 1600000 in
theorem gamma_unary_common_from_lift_charts {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hBC : B.real ∪ Set.range z ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (FBase : VFFieldBase (B.real ∪ Set.range z))
    (U V : GammaRVFiniteObject ⟨B.real ∪ Set.range z,B.gamma⟩ 1)
    (hUC : U.codes ⊆ (C.base : Set M)) (hVC : V.codes ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {ZU : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    {ZV : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 c}
    (eU : GammaIso ⟨B.real ∪ Set.range z,B.gamma⟩ (carrier A) U.lift)
    (eV : GammaIso ⟨B.real ∪ Set.range z,B.gamma⟩ (carrier A) V.lift)
    (gU : SpecialTransformations.Section5.Map A ZU) (gV : SpecialTransformations.Section5.Map A ZV)
    (hJU : VFAlmostEverywhere (rawSpecialSet hc A) (fun p => HasMixedVFJacobianAt (rawSpecialMap hc gU) p 1))
    (hJV : VFAlmostEverywhere (rawSpecialSet hc A) (fun p => HasMixedVFJacobianAt (rawSpecialMap hc gV) p 1))
    (hVFU : ∀ q : A, (eU.equiv q).val.1 = (gU q).val.1)
    (hVFV : ∀ q : A, (eV.equiv q).val.1 = (gV q).val.1)
    (δ : Fin a) (εU : Fin (rvObjectArity U.object)) (εV : Fin (rvObjectArity V.object))
    (hεU : ∀ u : rvObjectDomain U.object, (u.val εU).val ≠ iRVZero)
    (hεV : ∀ v : rvObjectDomain V.object, (v.val εV).val ≠ iRVZero)
    (hLabelU : ∀ q : A, (eU.equiv q).val.2 εU = q.val.2 δ)
    (hLabelV : ∀ q : A, (eV.equiv q).val.2 εV = q.val.2 δ)
    (ω : VolumeForm (rawSpecialSet hc A)) (hDensity : ∀ q, ω.value q = q.val.2 δ)
    (F : GammaRVVolumeSchema B p (rvObjectArity U.object) 0 sp)
    (G : GammaRVVolumeSchema B p (rvObjectArity V.object) 0 sp)
    (hF : F.valid z) (hG : G.valid z)
    (PF : RVVolumeSchemaRow (gammaCoordinateDensityObject (e := 0) (k := 0) hc C U hUC εU hεU) F z)
    (PG : RVVolumeSchemaRow (gammaCoordinateDensityObject (e := 0) (k := 0) hc C V hVC εV hεV) G z) :
    ∃ H : GammaVolumeCommonSchema F G, H.valid z := by
  obtain ⟨D,hCD,hUD,fU,hfU,hΓU,hValU,hmU⟩ := gamma_volume_lift_chart_realization hc C hBC U hUC
    eU gU hJU hVFU δ εU hεU hLabelU ω hDensity
  let AD := extendBase A hCD
  let gVD := @Map.extend LRV M N _ _ (C.base : Set M) (D.base : Set M) A ZV gV hCD
  obtain ⟨E,hDE,hVE,fV,hfV,hΓV,hValV,hmV⟩ := gamma_volume_lift_chart_realization hc D (hBC.trans hCD)
    V (hVC.trans hCD) (A := AD) eV gVD (hJV.extend hCD)
    (fun q => hVFV ⟨q.val,q.property⟩) δ εV hεV (fun q => hLabelV ⟨q.val,q.property⟩)
    (ω.extend hCD) (fun q => hDensity ⟨q.val,q.property⟩)
  let hCE := hCD.trans hDE
  let hUE := hUD.trans hDE
  let UE := FiniteRV.gammaObjectAtExtend U hUE
  let VE := FiniteRV.gammaObjectAtExtend V hVE
  let ΩU := gammaCoordinateDensityObject (e := 0) (k := 0) hc E U hUE εU hεU
  let ΩV := gammaCoordinateDensityObject (e := 0) (k := 0) hc E V hVE εV hεV
  let AE := extendBase AD hDE
  let fUE : SpecialTransformations.Section5.Map AE (typedLift UE.object.obj) :=
    @Map.extend LRV M N _ _ (D.base : Set M) (E.base : Set M) _ _ fU hDE
  have hfUE : Function.Bijective fUE := hfU
  let fUi := SpecialTransformations.Section5.Map.inverse fUE hfUE
  let f := SpecialTransformations.Section5.Map.comp fV fUi
  have hfUi := inverse_map_bijective fUE hfUE
  have hf : Function.Bijective f := hfV.comp hfUi
  have hfΓ : GammaGraphDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ (pointMapGraph f) :=
    gamma_composition_graph fUi fV (gamma_inverse_map_graph fUE hfUE hΓU) hΓV
  let πU := literalRVVolumeForm hc UE.object ΩU.form (typedLift UE.object.obj) (normalizedTypedLift_presents UE.object.obj)
  let πV := literalRVVolumeForm hc VE.object ΩV.form (typedLift VE.object.obj) (normalizedTypedLift_presents VE.object.obj)
  have hmUE : PreservesVFVolume ((ω.extend hCD).extend hDE) πU (rawSpecialMap hc fUE) := hmU.extend hDE
  have hmi : PreservesVFVolume πU ((ω.extend hCD).extend hDE) (rawSpecialMap hc fUi) :=
    preservesVFVolume_inverse hc E Nat.one_pos ((ω.extend hCD).extend hDE) πU
      (rawSpecialMap hc fUE) hfUE hmUE
  have hm : PreservesVFVolume πU πV (rawSpecialMap hc f) :=
    preservesVFVolume_comp hc E Nat.one_pos πU ((ω.extend hCD).extend hDE) πV
      (rawSpecialMap hc fUi) (rawSpecialMap hc fV) hfUi.1 hmi hmV
  have hUΓ : GammaSetDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ (carrier (typedLift UE.object.obj)) := by
    rw [typedLift_carrier]
    exact UE.toGamma.toGammaRVObject.lift_definable
  have hVΓ : GammaSetDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ (carrier (typedLift VE.object.obj)) := by
    rw [typedLift_carrier]
    exact VE.toGamma.toGammaRVObject.lift_definable
  exact gamma_unary_volume_common_schema hc E hκ hs hreal hgamma z hz (hBC.trans hCE) γ hγ hγ1 FBase
    UE.object VE.object ΩU.form ΩV.form (typedLift UE.object.obj) (typedLift VE.object.obj)
    (normalizedTypedLift_presents UE.object.obj) (normalizedTypedLift_presents VE.object.obj)
    εU εV (fun _ => rfl) (fun _ => rfl) f hf hUΓ hVΓ hfΓ hm F G hF hG
    (PF.extend hCE) (PG.extend hCE)

end IntegrationInACVF.Section7
