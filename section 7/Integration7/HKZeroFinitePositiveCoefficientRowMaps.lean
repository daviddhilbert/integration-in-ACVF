import Integration7.FiniteVolumeCoefficientFamilies
import Integration7.HKZeroFamilyFiniteProductBijections
import Integration7.HKZeroFamilyPositiveCoefficients
import Integration7.OrdinaryFamilyPositiveCoefficientRows
import Integration7.DefinableVolumeFamilySelectionRows

/-! Deleting the functional density-graph label gives a genuine row bijection for a weighted-zero family times a positive coefficient. The original VF density determines the deleted label uniquely. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (F : ZeroVFVolumeFamily C (n+1) a)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (σ : Fin (p+1) → Fin d) (ε : Fin d)
variable (hR : ∀ t : Fin (p+1) → RV (M := M),
  {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)
variable (x : Fin (n+1) → VFType (M := M))

private def densityGraphProduct := finiteVolumeCoefficientFamily hc C F.fullVFObject.densityGraph.domain
  F.fullVFObject.densityGraph.finite_labels F.fullVFObject.densityGraph.form R σ ε hR hε
private def coefficient := nativeCoordinateDensityVolumeObject hc C R σ ε hR hε

def zeroFinitePositiveCoefficientRowProjection :
    Map ((densityGraphProduct hc C F R σ ε hR hε).rowInContext x).underlying.obj.domain
      ((F.mulConstant (coefficient hc C R σ ε hR hε)).rowInContext x).underlying.obj.domain := by
  let ι : Fin (a+d) → Fin ((a+1)+d) :=
    Fin.append (m := a) (n := d) (Fin.castAdd d ∘ Fin.castAdd 1) (Fin.natAdd (a+1))
  let f : Map ((densityGraphProduct hc C F R σ ε hR hε).rowInContext x).underlying.obj.domain
      (DefSet.univ (rawRVSpace (M := M) (a+d)) ((vfParameterVolumeContext C x).base : Set M)) :=
    (rvCoordinateSelectMap ((vfParameterVolumeContext C x).base : Set M) ι).restrict (Set.subset_univ _)
  refine f.corestrict ?_
  intro r
  have h := (mem_mixed_rv_factor_domain F.fullVFObject.densityGraph.domain (rawVolumeContractionLabels hc R) x r.val).mp r.property
  let q : F.fullVFObject.densityGraph.domain := ⟨(x,r.val ∘ Fin.castAdd d),h.1⟩
  let s := densityGraphProjection F.fullVFObject.form q
  have hs := s.property
  rw [densityGraphProjection_value] at hs
  apply (mem_mixed_rv_factor_domain F.domain (rawVolumeContractionLabels hc R) x (r.val ∘ ι)).mpr
  have hL : (r.val ∘ ι) ∘ Fin.castAdd d = (r.val ∘ Fin.castAdd d) ∘ Fin.castAdd 1 := by
    funext i
    simp only [Function.comp_apply,ι,Fin.append_left]
  have hU : (r.val ∘ ι) ∘ Fin.natAdd a = r.val ∘ Fin.natAdd (a+1) := by
    funext i
    simp only [Function.comp_apply,ι,Fin.append_right]
  exact ⟨hL ▸ hs,hU ▸ h.2⟩

theorem zero_finite_positive_coefficient_row_projection_value
    (r : ((densityGraphProduct hc C F R σ ε hR hε).rowInContext x).underlying.obj.domain) :
    (zeroFinitePositiveCoefficientRowProjection hc C F R σ ε hR hε x r).val =
      r.val ∘ Fin.append (m := a) (n := d) (Fin.castAdd d ∘ Fin.castAdd 1) (Fin.natAdd (a+1)) := rfl

theorem zero_finite_positive_coefficient_row_projection_bijective :
    Function.Bijective (zeroFinitePositiveCoefficientRowProjection hc C F R σ ε hR hε x) := by
  let ι : Fin (a+d) → Fin ((a+1)+d) :=
    Fin.append (m := a) (n := d) (Fin.castAdd d ∘ Fin.castAdd 1) (Fin.natAdd (a+1))
  constructor
  · intro r s he
    have hv := congrArg Subtype.val he
    change r.val ∘ ι=s.val ∘ ι at hv
    let graphPoint := fun t : ((densityGraphProduct hc C F R σ ε hR hε).rowInContext x).underlying.obj.domain =>
      (⟨(x,t.val ∘ Fin.castAdd d),
        ((mem_mixed_rv_factor_domain F.fullVFObject.densityGraph.domain
          (rawVolumeContractionLabels hc R) x t.val).mp t.property).1⟩ : F.fullVFObject.densityGraph.domain)
    have hBase : densityGraphProjection F.fullVFObject.form (graphPoint r) =
        densityGraphProjection F.fullVFObject.form (graphPoint s) := by
      apply Subtype.ext
      rw [densityGraphProjection_value,densityGraphProjection_value]
      change (x,(r.val ∘ Fin.castAdd d) ∘ Fin.castAdd 1) =
        (x,(s.val ∘ Fin.castAdd d) ∘ Fin.castAdd 1)
      refine Prod.ext (show x=x from rfl) ?_
      funext j
      have h := congrFun hv (Fin.castAdd d j)
      simpa only [Function.comp_apply,ι,Fin.append_left] using h
    have hOne (t : ((densityGraphProduct hc C F R σ ε hR hε).rowInContext x).underlying.obj.domain) :
        t.val (Fin.castAdd d (Fin.last a)) =
          F.form.value (densityGraphProjection F.fullVFObject.form (graphPoint t)) :=
      (densityGraphPullback_form_last F.fullVFObject.form (graphPoint t)).symm
    apply Subtype.ext
    funext i
    refine Fin.addCases (m := a+1) (n := d) (fun j => ?_) (fun j => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · exact (hOne r).trans ((congrArg F.form.value hBase).trans (hOne s).symm)
      · have h := congrFun hv (Fin.castAdd d j)
        have hcast : Fin.castAdd 1 j=j.castSucc := Fin.ext rfl
        simpa only [Function.comp_apply,ι,Fin.append_left,hcast] using h
    · have h := congrFun hv (Fin.natAdd a j)
      simpa only [Function.comp_apply,ι,Fin.append_right] using h
  · intro r
    have hr := (mem_mixed_rv_factor_domain F.domain (rawVolumeContractionLabels hc R) x r.val).mp r.property
    let q : F.domain := ⟨(x,r.val ∘ Fin.castAdd d),hr.1⟩
    let g := (appendDensityMap F.fullVFObject.form).toImage q
    let labels := Fin.append (m := a+1) (n := d) g.val.2 (r.val ∘ Fin.natAdd a)
    have hx : g.val.1=x := rfl
    have hG : (x,g.val.2) ∈ F.fullVFObject.densityGraph.domain.carrier := by
      have h := g.property
      change (g.val.1,g.val.2) ∈ F.fullVFObject.densityGraph.domain.carrier at h
      rw [hx] at h
      exact h
    have hLabels : (x,labels) ∈ (mixedRVFactorDomain F.fullVFObject.densityGraph.domain (rawVolumeContractionLabels hc R)).carrier := by
      apply (mem_mixed_rv_factor_domain _ _ x labels).mpr
      simpa only [labels,Function.comp_def,Fin.append_left,Fin.append_right] using And.intro hG hr.2
    refine ⟨⟨labels,hLabels⟩,Subtype.ext ?_⟩
    change labels ∘ ι=r.val
    funext i
    refine Fin.addCases (m := a) (n := d) (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply,ι,Fin.append_left,labels]
      change Fin.append (m := a) (n := 1) (r.val ∘ Fin.castAdd d) (F.fullVFObject.form.map q).val (Fin.castAdd 1 j)=r.val (Fin.castAdd d j)
      rw [Fin.append_left]
      rfl
    · simp only [Function.comp_apply,ι,Fin.append_right,labels]
end IntegrationInACVF.Section7.HK
