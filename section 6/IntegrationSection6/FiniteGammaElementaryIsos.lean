import IntegrationSection6.FiniteGammaElementaryAt
import IntegrationSection6.FiniteGammaChartLaws
import IntegrationSection6.ElementaryCoordinates
import IntegrationSection6.GammaRVProductGraphs

/-! Lemma6.3 over the original Gamma base, exclusively in RV[k].
Finite volume supplies both morphism image conditions, so no bound on
the internal real code presentation is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {U V : GammaObjectAt B S n}

theorem isoAtMap_weight (e : GammaIsoAt U V) (u : rvObjectDomain U.object.obj) :
    @rvWeight M N n (@RVObject.value M N S n U.object.obj u) =
      @rvWeight M N n (@RVObject.value M N S n V.object.obj (isoAtMap e.iso u)) := by
  let E := isoAtAmbient e.iso
  let A := U.object.obj
  let C := V.object.obj
  let f := isoAtMap e.iso
  let g := isoAtMap e.iso.symm
  have hi := isoAtMap_inv_hom e.iso u
  letI := N
  letI := hN
  have h := E.hom.volumetric u
  have h' := E.inv.volumetric (f u)
  change rvWeight (C.value (f u)) ≤ rvWeight (A.value (g (f u))) at h'
  rw [hi] at h'
  exact Nat.le_antisymm h h'

theorem gamma_elementaryMap_graph {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (i j : Fin n)
    (hU : GammaAdmissible U.toGamma.toGammaRVObject i)
    (hV : GammaAdmissible V.toGamma.toGammaRVObject j) (e : GammaIsoAt U V) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj+1))
        (q : Point (M := M) 0 (rvObjectArity V.object.obj+1)) =>
        ∃ a : rvObjectDomain (gammaElementaryAt hκ hs h00 hsmall  U i hU).object.obj,
          a.val = p.2 ∧ (@elementaryMap M N hN S n U.object.obj V.object.obj i j (isoAtMap e.iso) a).val = q.2) := by
  let W := gammaElementaryAt hκ hs h00 hsmall  U i hU
  let Z := gammaElementaryAt hκ hs h00 hsmall  V j hV
  let f := isoAtMap e.iso
  let F := @elementaryMap M N hN S n U.object.obj V.object.obj i j f
  apply gamma_rv_graph_append_id F e.graph W.domain_graph
  intro p q
  constructor
  · rintro ⟨a,ha,hq⟩
    have hp := @elementaryProjection_labels M N hN S n U.object.obj i a
    have hm := (@elementaryMap_labels M N hN S n U.object.obj V.object.obj i j f a).symm.trans hq
    refine ⟨ha ▸ a.property,⟨@elementaryProjection M N hN S n U.object.obj i a,?_,?_⟩,?_⟩
    · exact hp.trans (funext fun t => congrFun ha (Fin.castAdd 1 t))
    · funext t
      exact (Fin.append_left _ _ t).symm.trans (congrFun hm (Fin.castAdd 1 t))
    · funext t
      exact (congrFun ha (Fin.natAdd (rvObjectArity U.object.obj) t)).symm.trans
        ((Fin.append_right _ _ t).symm.trans (congrFun hm (Fin.natAdd (rvObjectArity V.object.obj) t)))
  · rintro ⟨hp,⟨u,hu,hv⟩,hpar⟩
    let a : rvObjectDomain W.object.obj := ⟨p.2,hp⟩
    have hpu : @elementaryProjection M N hN S n U.object.obj i a = u :=
      Subtype.ext ((@elementaryProjection_labels M N hN S n U.object.obj i a).trans hu.symm)
    refine ⟨a,rfl,?_⟩
    rw [@elementaryMap_labels M N hN S n U.object.obj V.object.obj i j f a,hpu]
    funext t
    cases t using Fin.addCases with
    | left t => simpa only [Fin.append_left] using congrFun hv t
    | right t => simpa only [Fin.append_right] using congrFun hpar t

def gammaElementaryIsoAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (i j : Fin n)
    (hU : GammaAdmissible U.toGamma.toGammaRVObject i)
    (hV : GammaAdmissible V.toGamma.toGammaRVObject j) (e : GammaIsoAt U V) :
    GammaIsoAt (gammaElementaryAt hκ hs h00 hsmall  U i hU)
      (gammaElementaryAt hκ hs h00 hsmall  V j hV) := by
  let W := gammaElementaryAt hκ hs h00 hsmall  U i hU
  let Z := gammaElementaryAt hκ hs h00 hsmall  V j hV
  let f := isoAtMap e.iso
  let E := isoAtAmbient e.iso
  let F := @elementaryMap M N hN S n U.object.obj V.object.obj i j f
  have hF := @elementaryMap_bijective M N hN S n U.object.obj V.object.obj i j f
    (@iso_map_bijective M N hN S n U.object.obj V.object.obj E)
  have hW : ∀ a : rvObjectDomain W.object.obj,
      @rvWeight M N n (@RVObject.value M N S n W.object.obj a) =
        @rvWeight M N n (@RVObject.value M N S n Z.object.obj (F a)) := by
    let A := U.object.obj
    let C := V.object.obj
    have hu := hU.ordinary hκ hs h00 hsmall
    have hv := hV.ordinary hκ hs h00 hsmall
    have he := isoAtMap_weight e
    letI := N
    letI := hN
    intro a
    let u := elementaryProjection A i a
    let s := (elementaryParameter A i a).val 0
    have h1 := blowupValue_weight_balance i (A.value u) s (hu.nonzero u)
    have h2 := blowupValue_weight_balance j (C.value (f u)) s (hv.nonzero (f u))
    change rvWeight ((IntegrationInACVF.Section6.elementary A i).value a) =
      rvWeight ((IntegrationInACVF.Section6.elementary C j).value (elementaryMap i j f a))
    rw [elementary_value,elementary_value,elementaryMap_projection,elementaryMap_parameter]
    exact Nat.add_right_cancel (h1.trans ((he u).trans h2.symm))
  exact {
    iso := @isoOfDefinableBijection M N S n W.object Z.object F hF hW
    graph := gamma_elementaryMap_graph hκ hs h00 hsmall  i j hU hV e }

end IntegrationInACVF.Section6.FiniteRV
