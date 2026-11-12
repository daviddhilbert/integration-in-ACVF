import IntegrationSection6.GammaRVKeyGraphs
import IntegrationSection6.FiniteGammaAmbientIsos
import IntegrationSection6.FiniteGammaElementaryAt
import IntegrationSection6.OriginalFocusCoordinates

/-! Full-focus comparisons in RV[k] retain the original-Gamma graph.
The graph is the inverse of the injective elementary key graph; no
internal real presentation names are added to the original base. -/
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

 theorem gamma_elementaryKey_graph {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S n) (i : Fin n)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj+1))
        (q : Point (M := M) 0 (n+rvObjectArity U.object.obj)) =>
        ∃ u : rvObjectDomain (gammaElementaryAt hκ hs h00 hsmall  U i hAd).object.obj,
          u.val = p.2 ∧ (@elementaryKeyMap M N hN S n U.object.obj i u).val = q.2) := by
  let W := gammaElementaryAt hκ hs h00 hsmall  U i hAd
  let Q := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
    (@rawRVSpace M N (rvObjectArity U.object.obj+1)) B.real
  let H := @selectRVTuple M N B.real (rvObjectArity U.object.obj+1) (rvObjectArity U.object.obj) (Fin.castAdd 1) Q
  apply gamma_volume_key_graph W H (fun u => (@elementaryKeyMap M N hN S n U.object.obj i u).val)
  intro u
  rw [@elementaryKeyMap_value M N hN S n U.object.obj i u]
  apply congrArg (Fin.append _)
  have he := @elementary_labels M N hN S n U.object.obj i u
  funext j
  exact (Fin.append_left _ _ j).symm.trans (congrFun he (Fin.castAdd 1 j)).symm

 def gammaFullFocusImageAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN S n U.object.obj (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U.object.obj)} (D : Focus A i k)
    (hfull : carrier A ⊆ D.locus) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) : GammaObjectAt B S n := by
  let e := originalAdmissibleFocusBlowup h D hfull (hAd.ordinary hκ hs h00 hsmall)
  let E := @IntegrationInACVF.Section6.ElementaryBlowup.iso M N hN S n U.object.obj (originalFocusObject D) e
  let W := gammaElementaryAt hκ hs h00 hsmall  U i hAd
  have hfin := (@finite_volume_iso M N hN S n (originalFocusObject D) W.object.obj E).mpr W.object.property
  exact gammaPullbackAt U.real_contains D.etaImage
    (GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal D) ⟨hA,hD⟩) hfin

 def gammaFullFocusIsoAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN S n U.object.obj (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U.object.obj)} (D : Focus A i k)
    (hfull : carrier A ⊆ D.locus) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    GammaIsoAt (gammaFullFocusImageAt hκ hs h00 hsmall  U h D hfull hAd hA hD)
      (gammaElementaryAt hκ hs h00 hsmall  U i hAd) := by
  let e := originalAdmissibleFocusBlowup h D hfull (hAd.ordinary hκ hs h00 hsmall)
  let E := @IntegrationInACVF.Section6.ElementaryBlowup.iso M N hN S n U.object.obj (originalFocusObject D) e
  apply GammaIsoAt.ofAmbient E
  apply GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph
    (gamma_elementaryKey_graph hκ hs h00 hsmall  U i hAd))
  let forward := @RVHom.map M N S n (originalFocusObject D) _ E.hom
  let backward := @RVHom.map M N S n _ (originalFocusObject D) E.inv
  intro p q
  constructor
  · rintro ⟨b,hb,hkey⟩
    have ha : p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain (originalFocusObject D)) := by
      have ht := @originalAdmissibleFocusBlowup_key M sM hM S n U.object.obj A h i k D hfull
        (hAd.ordinary hκ hs h00 hsmall) (backward b)
      have hinv := @iso_inv_hom_apply M N hN S n _ _ E b
      rw [hinv] at ht
      exact (ht.symm.trans hkey) ▸ (backward b).property
    let a : rvObjectDomain (originalFocusObject D) := ⟨p.2,ha⟩
    have he : forward a = b := by
      apply @elementaryKeyMap_injective M N hN S n U.object.obj i (hAd.ordinary hκ hs h00 hsmall)
      apply Subtype.ext
      exact (@originalAdmissibleFocusBlowup_key M sM hM S n U.object.obj A h i k D hfull
        (hAd.ordinary hκ hs h00 hsmall) a).trans hkey.symm
    exact ⟨a,rfl,(congrArg (fun b : rvObjectDomain (gammaElementaryAt hκ hs h00 hsmall  U i hAd).object.obj => b.val) he).trans hb⟩
  · rintro ⟨a,ha,hq⟩
    exact ⟨forward a,hq,
      (@originalAdmissibleFocusBlowup_key M sM hM S n U.object.obj A h i k D hfull
        (hAd.ordinary hκ hs h00 hsmall) a).trans ha⟩

end IntegrationInACVF.Section6.FiniteRV
