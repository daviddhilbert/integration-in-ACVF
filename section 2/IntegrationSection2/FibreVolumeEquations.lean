import IntegrationSection2.ConcreteVolumeForms
import IntegrationSection2.FixedLabelLift

/-! On a fixed label fibre the two lifted forms are constant, so the
measure equation fixes the actual RV class of the VF Jacobian. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section2.ConcreteVolumeForms

namespace IntegrationInACVF.Section2.FibreVolumeEquations

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
  {U V : RVFiniteObject (M := M) S k}

theorem ratio (e : U.obj ≅ V.obj) (ω : RVForm U) (π : RVForm V)
    (f : Map (rvLift U.obj) (rvLift V.obj))
    (hlabel : ∀ p : rvLift U.obj, e.hom.map.graph p.val.2 (f p).val.2)
    (u : U.obj.domain) (p : FixedLabelLift.source e u) (J : VFType (M := M))
    (hMeasure : liftedValue ω ⟨p.val,((FixedLabelLift.source_mem e u p.val).mp p.property).1⟩ =
      liftedValue π (f ⟨p.val,((FixedLabelLift.source_mem e u p.val).mp p.property).1⟩) *
        CanonicalRV.encodedRv J) :
    CanonicalRV.encodedRv J = value ω u / value π (e.hom.map u) := by
  let q : rvLift U.obj := ⟨p.val,((FixedLabelLift.source_mem e u p.val).mp p.property).1⟩
  have hs : liftLabelMap U.obj q = u :=
    Subtype.ext ((FixedLabelLift.source_mem e u p.val).mp p.property).2
  have ht : liftLabelMap V.obj (f q) = e.hom.map u := by
    apply Subtype.ext
    exact ((e.hom.map.graph_apply (liftLabelMap U.obj q) (f q).val.2).mp (hlabel q)).symm.trans
      (congrArg Subtype.val (congrArg e.hom.map hs))
  have he : value ω u = value π (e.hom.map u) * CanonicalRV.encodedRv J := by
    change liftedValue ω q = liftedValue π (f q) * CanonicalRV.encodedRv J at hMeasure
    simpa only [liftedValue_eq,hs,ht] using hMeasure
  apply (eq_div_iff (value_ne_zero π (e.hom.map u))).mpr
  exact (mul_comm _ _).trans he.symm

theorem gamma_equation_of_ratio {u : U.obj.domain} {w : V.obj.domain}
    (ω : RVForm U) (π : RVForm V) (a b : Fin k → VFType (M := M))
    (hU : ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ i, (V.obj.value w i).val ≠ iRVZero)
    (ha : tupleRV a = U.obj.value u) (hb : tupleRV b = V.obj.value w)
    (c : VFType (M := M)) (hc : CanonicalRV.encodedRv c = value ω u / value π w)
    (hval : Values.vfValueHom c =
      (∏ i, Values.vfValueHom (b i)) / ∏ i, Values.vfValueHom (a i)) :
    gammaValue ω u = gammaValue π w * rvGammaJacobian (U.obj.value u) (V.obj.value w) hU hV := by
  have hvolume (t : Fin k → CanonicalRV.RVSort M) (ht : ∀ i, (t i).val ≠ iRVZero) :
      (rvVolumeGamma t ht).val = ∏ i, RVOperations.vrvHom (t i) :=
    map_prod Values.gammaValHom (fun i => Values.gammaOf (t i) (ht i)) Finset.univ
  have hw : (gammaValue ω u).val = RVOperations.vrvHom (value ω u) := rfl
  have hp : (gammaValue π w).val = RVOperations.vrvHom (value π w) := rfl
  have hnonzero : RVOperations.vrvHom (value π w) ≠ 0 :=
    (map_ne_zero RVOperations.vrvHom).mpr (value_ne_zero π w)
  apply Subtype.ext
  rw [Values.gamma_val_mul,rvGammaJacobian,div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv]
  rw [hvolume,hvolume,hw,hp]
  have hv : RVOperations.vrvHom (value ω u) / RVOperations.vrvHom (value π w) =
      (∏ i, RVOperations.vrvHom (V.obj.value w i)) / ∏ i, RVOperations.vrvHom (U.obj.value u i) := by
    have he := congrArg RVOperations.vrvHom hc
    rw [map_div₀] at he
    have hvb : (∏ i, Values.vfValueHom (b i)) = ∏ i, RVOperations.vrvHom (V.obj.value w i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact congrArg RVOperations.vrvHom (congrFun hb i)
    have hva : (∏ i, Values.vfValueHom (a i)) = ∏ i, RVOperations.vrvHom (U.obj.value u i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact congrArg RVOperations.vrvHom (congrFun ha i)
    exact he.symm.trans (hval.trans (by rw [hvb,hva]))
  exact (div_eq_iff hnonzero).mp hv |>.trans (by rw [div_eq_mul_inv];ac_rfl)

end IntegrationInACVF.Section2.FibreVolumeEquations
