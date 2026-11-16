module

public import Integration7.CanonicalGammaVolumeIsomorphisms
public import Integration7.FiniteVolumeParameterContexts
public import Integration7.GradedVolumeProducts
public import IntegrationSection6.FiniteGammaIsoRealization

@[expose] public section

/-! A full coordinate-preserving finite Gamma isomorphism is an actual
unit-density RV volume isomorphism in a small containing context. Its
full original-Gamma graph survives the internal representative choices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open SpecialTransformations.Section7
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaUnitVolumeObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B (k+1)) (hUC : U.codes ⊆ (C.base : Set M)) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
  ⟨canonicalFiniteRVObject hc (FiniteRV.gammaObjectAtExtend U hUC).object,VolumeForm.one _⟩

@[simp] theorem gammaUnitVolumeObject_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B (k+1)) (hUC : U.codes ⊆ (C.base : Set M))
    (u : (gammaUnitVolumeObject hc C U hUC).underlying.obj.domain) :
    (gammaUnitVolumeObject hc C U hUC).form.value u = 1 := rfl

set_option maxHeartbeats 1600000 in
theorem gamma_unit_volume_iso_realization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : GammaRVFiniteObject B (k+1))
    (hUC : U.codes ⊆ (C.base : Set M)) (hVC : V.codes ⊆ (C.base : Set M))
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (hVolume : ∀ u, gammaVolumeValue V.toGammaRVObject (e.equiv u) = gammaVolumeValue U.toGammaRVObject u) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ f : RVVolumeIso ((gammaUnitVolumeObject hc C U hUC).extend hCD)
      ((gammaUnitVolumeObject hc C V hVC).extend hCD), f.GammaDefinable B := by
  obtain ⟨r,t,hReal⟩ := gamma_rv_relation_real_specialize e.graph
  let D := finiteVolumeParameterContext C (Set.range (rawTuple t)) (Set.finite_range _)
  have hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ hx => finiteVolumeParameterContext_contains C _ (Set.finite_range _) (Or.inl hx)
  have hBD : B.real ∪ Set.range (rawTuple t) ⊆ (D.base : Set M) := by
    rintro z (hz | hz)
    · exact hCD (hUC (U.real_contains hz))
    · exact finiteVolumeParameterContext_contains C _ (Set.finite_range _) (Or.inr hz)
  let A := FiniteRV.gammaObjectAtExtend U (hUC.trans hCD)
  let Z := FiniteRV.gammaObjectAtExtend V (hVC.trans hCD)
  let F : @Map LRV M N _ _ (D.base : Set M)
      (rvObjectDomain A.object.obj) (rvObjectDomain Z.object.obj) :=
    @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ (D.base : Set M) _ _ e.equiv
      (@SpecialTransformations.DefinableGeometry.Space.RelationDefinable.mono LRV M N
        (@rawRVSpace M N (rvObjectArity U.object)) (@rawRVSpace M N (rvObjectArity V.object))
        (B.real ∪ Set.range (rawTuple t)) (D.base : Set M) _ hReal hBD)
  have hw (u : rvObjectDomain A.object.obj) :
      @rvWeight M N (k+1) (@RVObject.value M N (D.base : Set M) (k+1) A.object.obj u) =
      @rvWeight M N (k+1) (@RVObject.value M N (D.base : Set M) (k+1) Z.object.obj (F u)) :=
    (FiniteRV.rawWeight_eq_normalized_weight (gammaVolumeValue U.toGammaRVObject u)).symm.trans
      ((e.weight u).trans (FiniteRV.rawWeight_eq_normalized_weight (gammaVolumeValue V.toGammaRVObject (e.equiv u))))
  let ei : FiniteRV.GammaIsoAt A Z := {
    iso := @FiniteRV.isoOfDefinableBijection M N (D.base : Set M) (k+1) A.object Z.object F e.equiv.bijective hw
    graph := e.graph }
  have hCoord : ∀ u, (canonicalFiniteRVObject hc Z.object).obj.value
      (finiteIsoMap (canonicalFiniteRVIso hc ei.iso) u) = (canonicalFiniteRVObject hc A.object).obj.value u := by
    intro u
    funext j
    apply Subtype.ext
    exact congrArg Subtype.val (congrFun (hVolume ⟨u.val,u.property⟩) j)
  let ω := ((gammaUnitVolumeObject hc C U hUC).extend hCD).form
  let π := ((gammaUnitVolumeObject hc C V hVC).extend hCD).form
  have hForm : ∀ u, π.value (finiteIsoMap (canonicalFiniteRVIso hc ei.iso) u) = ω.value u := fun _ => rfl
  exact ⟨D,hCD,canonicalGammaVolumeIso hc D A Z ω π ei hCoord hForm,
    canonicalGammaVolumeIso_gamma hc D A Z ω π ei hCoord hForm⟩

end IntegrationInACVF.Section7
