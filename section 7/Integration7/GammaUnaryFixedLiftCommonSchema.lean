module

public import Integration7.GammaUnaryVolumeCommonSchema
public import Integration7.GammaVolumeSliceDensityAssembly
public import Integration7.FiniteVolumeParameterContexts
public import IntegrationSection6.GammaRVRealization

@[expose] public section

/-! A VF-fixed, density-preserving original-Gamma isomorphism of unary
lifts supplies a finite common-volume-blowup witness. Only finitely many
internal real representative codes are added to a genuine small context. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

private theorem gamma_iso_congr_value {n m u w : ℕ}
    {P : Base (M := M)} {A A' : Set (Point (M := M) n m)} {D D' : Set (Point (M := M) u w)}
    (e : GammaIso P A D) (hA : A = A') (hD : D = D') (a : A') :
    ((e.congr hA hD).equiv a).val =
      (e.equiv ⟨a.val,by rw [hA]; exact a.property⟩).val := by
  cases hA
  cases hD
  rfl

set_option maxHeartbeats 1600000 in
theorem gamma_unary_fixed_lift_common_schema {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (FBase : VFFieldBase (B.real ∪ Set.range z))
    (U V : GammaRVFiniteObject ⟨B.real ∪ Set.range z,B.gamma⟩ 1)
    (hUC : U.codes ⊆ (C.base : Set M)) (hVC : V.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object)) (ε : Fin (rvObjectArity V.object))
    (hδ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (hε : ∀ v : rvObjectDomain V.object, (v.val ε).val ≠ iRVZero)
    (e : GammaIso ⟨B.real ∪ Set.range z,B.gamma⟩ U.lift V.lift)
    (hVF : ∀ u, (e.equiv u).val.1 = u.val.1)
    (hLabel : ∀ u, (e.equiv u).val.2 ε = u.val.2 δ)
    (L : GammaRVVolumeSchema B p (rvObjectArity U.object) 0 sp)
    (R : GammaRVVolumeSchema B p (rvObjectArity V.object) 0 sp)
    (hL : L.valid z) (hR : R.valid z)
    (PL : RVVolumeSchemaRow (gammaCoordinateDensityObject (e := 0) (k := 0) hc C U hUC δ hδ) L z)
    (PR : RVVolumeSchemaRow (gammaCoordinateDensityObject (e := 0) (k := 0) hc C V hVC ε hε) R z) :
    ∃ H : GammaVolumeCommonSchema L R, H.valid z := by
  let e' := e.congr (typedLift_carrier U.object).symm (typedLift_carrier V.object).symm
  obtain ⟨d,t,hr⟩ := e'.graph.real_specialize
  let E := Set.range (rawTuple t)
  let D := finiteVolumeParameterContext C E (Set.finite_range _)
  have hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ hx => finiteVolumeParameterContext_contains C E (Set.finite_range _) (Or.inl hx)
  have hBase : B.real ∪ Set.range z ⊆ (D.base : Set M) := U.real_contains.trans (hUC.trans hCD)
  have hQD : (B.real ∪ Set.range z) ∪ Set.range (rawTuple t) ⊆ (D.base : Set M) := by
    intro x hx
    rcases hx with hx | hx
    · exact hBase hx
    · exact finiteVolumeParameterContext_contains C E (Set.finite_range _) (Or.inr hx)
  let UD := FiniteRV.gammaObjectAtExtend U (hUC.trans hCD)
  let VD := FiniteRV.gammaObjectAtExtend V (hVC.trans hCD)
  let A := typedLift UD.object.obj
  let A' := typedLift VD.object.obj
  let f : SpecialTransformations.Section5.Map A A' :=
    @Map.mk LRV M N _ _ (D.base : Set M) _ _ e'.equiv
      (@Space.RelationDefinable.mono LRV M N
        (@pointSpace M sM hM 1 (rvObjectArity U.object))
        (@pointSpace M sM hM 1 (rvObjectArity V.object))
        ((B.real ∪ Set.range z) ∪ Set.range (rawTuple t)) (D.base : Set M) _ hr hQD)
  have hfValue (a : A) : (f a).val =
      (e.equiv ⟨a.val,(Set.ext_iff.mp (typedLift_carrier U.object) a.val).mp a.property⟩).val :=
    gamma_iso_congr_value e (typedLift_carrier U.object).symm (typedLift_carrier V.object).symm a
  let Ω := gammaCoordinateDensityObject (e := 0) (k := 0) hc D U (hUC.trans hCD) δ hδ
  let Θ := gammaCoordinateDensityObject (e := 0) (k := 0) hc D V (hVC.trans hCD) ε hε
  have hA := normalizedTypedLift_presents UD.object.obj
  have hA' := normalizedTypedLift_presents VD.object.obj
  have hAΓ : GammaSetDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ (carrier A) := by
    rw [typedLift_carrier]
    exact UD.toGamma.toGammaRVObject.lift_definable
  have hA'Γ : GammaSetDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ (carrier A') := by
    rw [typedLift_carrier]
    exact VD.toGamma.toGammaRVObject.lift_definable
  have hm : PreservesVFVolume (literalRVVolumeForm hc UD.object Ω.form A hA)
      (literalRVVolumeForm hc VD.object Θ.form A' hA') (rawSpecialMap hc f) := by
    apply (vfJacobianOne_of_preservesVF hc D Nat.one_pos (rawSpecialMap hc f) (by
      intro u
      change (f ⟨u.val,u.property⟩).val.1 = u.val.1
      rw [hfValue]
      exact hVF ⟨u.val,(Set.ext_iff.mp (typedLift_carrier U.object) u.val).mp u.property⟩)).mono
    intro u hJ
    refine ⟨1,hJ,?_⟩
    rw [RVOperations.rv_one,mul_one]
    change u.val.2 δ = (f ⟨u.val,u.property⟩).val.2 ε
    rw [hfValue]
    exact (hLabel ⟨u.val,(Set.ext_iff.mp (typedLift_carrier U.object) u.val).mp u.property⟩).symm
  exact gamma_unary_volume_common_schema hc D hκ hs hreal hgamma z hz hBase γ hγ hγ1 FBase
    UD.object VD.object Ω.form Θ.form A A' hA hA' δ ε (fun _ => rfl) (fun _ => rfl)
    f e'.equiv.bijective hAΓ hA'Γ e'.graph hm L R hL hR (PL.extend hCD) (PR.extend hCD)

end IntegrationInACVF.Section7
