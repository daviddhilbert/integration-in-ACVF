module

public import Integration7.ActualVolumeObjectPromotion

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Exact original-Gamma coordinate and density graphs suffice for object
promotion in any genuine context. No naming assumption on the whole context
is needed; the three graph certificates supply the original-base data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem gamma_volume_object_promotion_from_graphs {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hD : SpecialTransformations.Section5.GammaSetDefinable ⟨B.real ∪ Set.range z,B.gamma⟩
      {p : SpecialTransformations.Section5.Point (M := M) 0 U.underlying.obj.arity |
        p.2 ∈ U.underlying.obj.domain.carrier})
    (hV : SpecialTransformations.Section5.GammaGraphDefinable ⟨B.real ∪ Set.range z,B.gamma⟩
      (fun (x : SpecialTransformations.Section5.Point (M := M) 0 U.underlying.obj.arity)
        (y : SpecialTransformations.Section5.Point (M := M) 0 (k+1)) =>
          U.underlying.obj.volume.graph x.2 y.2))
    (hω : SpecialTransformations.Section5.GammaGraphDefinable ⟨B.real ∪ Set.range z,B.gamma⟩
      (fun (x : SpecialTransformations.Section5.Point (M := M) 0 U.underlying.obj.arity)
        (y : SpecialTransformations.Section5.Point (M := M) 0 1) => U.form.map.graph x.2 y.2)) :
    ∃ F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp,
      F.valid z ∧ RVVolumeSchemaRow U F z := by
  obtain ⟨R⟩ := exists_gammaFiniteGraphPresentation hD hV (by
    intro x
    refine ⟨(U.underlying.obj.volume x).val,⟨x,rfl,rfl⟩,?_⟩
    intro y hy
    exact ((Map.graph_apply U.underlying.obj.volume x y).mp hy).symm) (by
    intro y
    apply (U.underlying.property ⟨y,Set.mem_univ _⟩).subset
    intro x hx
    exact Subtype.ext ((Map.graph_apply U.underlying.obj.volume x y).mp hx))
  obtain ⟨P⟩ := exists_gammaVolumeGraphPresentation R hω (by
    intro x
    refine ⟨(U.form.map x).val,⟨x,rfl,rfl⟩,?_⟩
    intro y hy
    exact ((Map.graph_apply U.form.map x y).mp hy).symm) (by
    rintro x y ⟨u,rfl,_⟩
    exact u.property) (by
    rintro x y ⟨u,rfl,rfl⟩
    exact (rv_nonzero_iff_raw _).mp (U.form.nonzero u))
  obtain ⟨F,hF,_,hV,hW⟩ := gamma_sorted_volume_object_promotion hκ hs hreal hgamma sp z hz P
  refine ⟨F,hF,⟨?_,?_⟩⟩
  · intro x t
    change Fin.append (Fin.append z (rvValues x)) (rvValues t) ∈ F.object.volume ↔ _
    rw [hV,gammaRawObjectVolume_append_iff]
    constructor
    · rintro ⟨u,hx,ht⟩
      exact ((P.canonicalData_volume_iff hc x t).mp ⟨⟨u.val,u.property⟩,
        funext (fun i => Subtype.ext (congrFun hx i)),
        funext (fun i => Subtype.ext (congrFun ht i))⟩).2
    · intro h
      obtain ⟨u,hu,ht⟩ := (P.canonicalData_volume_iff hc x t).mpr
        ⟨by obtain ⟨v,rfl,_⟩ := h; exact v.property,h⟩
      exact ⟨⟨u.val,u.property⟩,funext (fun i => congrArg Subtype.val (congrFun hu i)),
        funext (fun i => congrArg Subtype.val (congrFun ht i))⟩
  · intro x ω
    change Fin.append (Fin.append z (rvValues x)) (rvValues ω) ∈ F.density ↔ _
    rw [hW,gammaRawObjectVolume_append_iff]
    constructor
    · rintro ⟨u,hx,hω⟩
      exact (P.canonicalData_density_iff hc x ω).mp ⟨⟨u.val,u.property⟩,
        funext (fun i => Subtype.ext (congrFun hx i)),
        funext (fun i => Subtype.ext (congrFun hω i))⟩
    · intro h
      obtain ⟨u,hx,hω⟩ := (P.canonicalData_density_iff hc x ω).mpr h
      exact ⟨⟨u.val,u.property⟩,funext (fun i => congrArg Subtype.val (congrFun hx i)),
        funext (fun i => congrArg Subtype.val (congrFun hω i))⟩

end IntegrationInACVF.Section7
