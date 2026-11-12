import IntegrationSection6.GammaElementaryDomains
import IntegrationSection6.GammaRVProductGraphs

/-! Complete Gamma graphs for elementary blowups directly from the actual
RV product and multiplication. Field generation is needed only to lift
these objects by special bijections, not to define the blowup relation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

def elementaryOldVolumeParamMap (U : RVObject (M := M) S n) (i : Fin n) :=
  (@rvPack M sM S n 1
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M sM (@SpecialTransformations.Section4.rawRVSpace M sM n) S)
    (positiveRV S)).comp ((U.volume.comp (elementaryProjection U i)).pair (elementaryParameter U i))

theorem elementaryOldVolumeParamMap_value (U : RVObject (M := M) S n) (i : Fin n) (a : (elementary U i).domain) :
    (elementaryOldVolumeParamMap U i a).val =
      Fin.append (U.value (elementaryProjection U i a)) (elementaryParameter U i a).val := rfl

def oldVolumeParameterBlowupMap (S : Set M) (i : Fin n) :=
  let P := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M sM (@SpecialTransformations.Section4.rawRVSpace M sM (n+1)) S
  (blowupValueMap S i).comp
    (((@selectRVTuple M sM S (n+1) n (Fin.castAdd 1) P).pair
      (@selectRVTuple M sM S (n+1) 1 (Fin.natAdd n) P)).toUniv)

theorem elementaryVolume_oldProgram (U : RVObject (M := M) S n) (i : Fin n) (a : (elementary U i).domain) :
    (elementary U i).value a =
      (oldVolumeParameterBlowupMap S i ⟨(elementaryOldVolumeParamMap U i a).val,Set.mem_univ _⟩).val := by
  change blowupValue i (U.value (elementaryProjection U i a)) ((elementaryParameter U i a).val 0) =
    blowupValue i (fun j => (elementaryOldVolumeParamMap U i a).val (Fin.castAdd 1 j))
      ((elementaryOldVolumeParamMap U i a).val (Fin.natAdd n 0))
  rw [elementaryOldVolumeParamMap_value]
  simp only [Fin.append_left,Fin.append_right]

variable {B : Base (M := M)}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_elementaryOldVolumeParam_graph (U : GammaRVObject B n) (i : Fin n) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 (rvObjectArity U.object+1)) (q : Point (M := M) 0 (n+1)) =>
      ∃ a : rvObjectDomain (@elementary M N hN U.codes n U.object i), a.val = p.2 ∧
        (@elementaryOldVolumeParamMap M N hN U.codes n U.object i a).val = q.2) := by
  let F := @elementaryOldVolumeParamMap M N hN U.codes n U.object i
  apply gamma_rv_graph_append_id F U.volume_graph (gamma_elementary_domain U i)
  intro p q
  constructor
  · rintro ⟨a,ha,hq⟩
    have hp := @elementaryProjection_labels M N hN U.codes n U.object i a
    have hm := (@elementaryOldVolumeParamMap_value M N hN U.codes n U.object i a).symm.trans hq
    rw [@elementaryParameter_labels M N hN U.codes n U.object i a] at hm
    refine ⟨ha ▸ a.property,⟨@elementaryProjection M N hN U.codes n U.object i a,?_,?_⟩,?_⟩
    · exact hp.trans (funext fun t => congrFun ha (Fin.castAdd 1 t))
    · funext t
      exact (Fin.append_left _ _ t).symm.trans (congrFun hm (Fin.castAdd 1 t))
    · funext t
      exact (congrFun ha (Fin.natAdd (rvObjectArity U.object) t)).symm.trans
        ((Fin.append_right _ _ t).symm.trans (congrFun hm (Fin.natAdd n t)))
  · rintro ⟨hp,⟨u,hu,hv⟩,hpar⟩
    let a : rvObjectDomain (@elementary M N hN U.codes n U.object i) := ⟨p.2,hp⟩
    have hpu : @elementaryProjection M N hN U.codes n U.object i a = u :=
      Subtype.ext ((@elementaryProjection_labels M N hN U.codes n U.object i a).trans hu.symm)
    refine ⟨a,rfl,?_⟩
    rw [@elementaryOldVolumeParamMap_value M N hN U.codes n U.object i a,
      @elementaryParameter_labels M N hN U.codes n U.object i a,hpu]
    funext t
    cases t using Fin.addCases with
    | left t => simpa only [Fin.append_left,RVObject.value] using congrFun hv t
    | right t => simpa only [Fin.append_right] using congrFun hpar t

theorem gamma_elementary_volume (U : GammaRVObject B n) (i : Fin n) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 (rvObjectArity U.object+1)) (q : Point (M := M) 0 n) =>
      ∃ a : rvObjectDomain (@elementary M N hN U.codes n U.object i), a.val = p.2 ∧
        (rvObjectVolume (@elementary M N hN U.codes n U.object i) a).val = q.2) := by
  let L := gammaLogicInput B
  let F := @elementaryOldVolumeParamMap M N hN U.codes n U.object i
  let G := @oldVolumeParameterBlowupMap M N hN n B.real i
  let P := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N (n+1)) B.real
  have hG := gamma_rv_graph_of_global_formula G G (gamma_rv_set_of_real P) (fun _ => rfl)
  have h := L.comp_graph (gamma_elementaryOldVolumeParam_graph U i) hG
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨z,⟨a,ha,hz⟩,⟨v,hv,hq⟩⟩
    have he : v.val = (F a).val := hv.trans hz.symm
    refine ⟨a,ha,?_⟩
    exact (@elementaryVolume_oldProgram M N hN U.codes n U.object i a).trans
      ((congrArg (fun x => (G ⟨x,Set.mem_univ _⟩).val) he).symm.trans hq)
  · rintro ⟨a,ha,hq⟩
    exact ⟨(Fin.elim0,(F a).val),⟨a,ha,rfl⟩,⟨(F a).val,Set.mem_univ _⟩,rfl,
      (@elementaryVolume_oldProgram M N hN U.codes n U.object i a).symm.trans hq⟩

def gammaElementaryObject (U : GammaRVObject B n) (i : Fin n) : GammaRVObject B n where
  codes := U.codes
  real_contains := U.real_contains
  object := @elementary M N hN U.codes n U.object i
  domain_graph := gamma_elementary_domain U i
  volume_graph := gamma_elementary_volume U i

end IntegrationInACVF.Section6
