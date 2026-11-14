import Integration7.TermContextGammaGraphs
import Integration7.PromotedVolumeSchemaRows

/-! Actual volume objects over the term context of the original named
parameters promote with their exact coordinate and density graphs. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem PositiveRVVolumeObject.gammaPresentationInTermContext
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hBase : (C.base : Set M) = (Substructure.closure LRV B.real : Set M)) :
    Nonempty (GammaVolumeGraphPresentation B U.underlying.obj.arity (k+1)
      U.underlying.obj.domain.carrier U.underlying.obj.volume.graph U.form.map.graph) := by
  have hD := U.underlying.obj.domain.definable
  have hV := rawRVRelationFormula_definable U.underlying.obj.volume.graph_definable
  have hD' := Eq.mp (congrArg (fun S : Set M => S.Definable LRV
    ((rawRVSpace (M := M) U.underlying.obj.arity).preimage U.underlying.obj.domain.carrier)) hBase) hD
  have hV' := Eq.mp (congrArg (fun S : Set M => S.Definable LRV
    (rawRVRelationFormula U.underlying.obj.volume.graph)) hBase) hV
  obtain ⟨P⟩ := realFiniteMap_gammaPresentation hc U.underlying.obj.domain U.underlying.obj.volume
    U.underlying.property (definable_termClosure_iff.mp hD') (definable_termClosure_iff.mp hV')
  apply exists_gammaVolumeGraphPresentation P
    (gammaGraph_of_termContext hc C B hBase U.form.map.graph_definable)
  · intro x
    refine ⟨(U.form.map x).val,⟨x,rfl,rfl⟩,?_⟩
    intro y hy
    exact ((Map.graph_apply U.form.map x y).mp hy).symm
  · rintro x y ⟨u,rfl,_⟩
    exact u.property
  · rintro x y ⟨u,rfl,rfl⟩
    exact (rv_nonzero_iff_raw _).mp (U.form.nonzero u)

theorem gamma_volume_actual_object_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hBase : (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range z) : Set M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    ∃ F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp,
      F.valid z ∧ RVVolumeSchemaRow U F z := by
  obtain ⟨P⟩ := U.gammaPresentationInTermContext (B := ⟨B.real ∪ Set.range z,B.gamma⟩) hc C hBase
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
