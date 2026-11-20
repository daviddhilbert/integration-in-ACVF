import Integration7.FieldBaseUnarySpecialPreparations
import IntegrationSection5.GammaHeadPreparation
import IntegrationSection6.GammaVFFieldClosureBases
import Integration7.DefinablyClosedVolumeContexts

/-! **Gamma unary special preparations over a field-named base.** Any Gamma base whose VF part is a
field and which lies in a context gives Gamma special preparations (with Gamma chains) of unary
sources that are Gamma over it. The VF field closure of a row base lies in the definably closed
extension of any context containing the row base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {a : ℕ}

/-- A Gamma special preparation of a Gamma unary source over a field-named base. -/
theorem gamma_field_unary_special_preparation (C : BaseContext M) (P : Base (M := M))
    (FBase : VFFieldBase P.real) (hPC : P.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) 1 a) (hA : GammaSetDefinable P (carrier A)) :
    ∃ b : ℕ, ∃ B : DefSet (M := M) (C.base : Set M) 1 b, ∃ T : SpecialBijection A B,
      GammaChainDefinable P T.chain ∧ IsRVPullback (carrier B) := by
  let L := gammaLogicInput P
  let X := PresentedSet.univ (pointSpace (M := M) 1 a) P.real
  let f := constantRVMap A 0
  have hf : GammaGraphDefinable P (pointMapGraph f) := by
    apply GammaGraphDefinable.congr (L.restrict_graph hA (L.real_map_graph (constantRVMap X 0)))
    intro p q
    constructor
    · rintro ⟨hp,x,hx,hq⟩
      exact ⟨⟨p,hp⟩,rfl,hq⟩
    · rintro ⟨u,rfl,hq⟩
      exact ⟨u.property,⟨u.val,Set.mem_univ _⟩,rfl,hq⟩
  have hsmall : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
  obtain ⟨b,B,T,_,hT,hB,_⟩ := gamma_map_preparation_at_boundary
    C.model00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles C.saturated hsmall Values.presentationValuation Values.presentation_compatible)
    L (gammaPolynomialSupportInput_of_fieldBase P FBase) hPC A hA f hf none (by intro h; cases h)
  exact ⟨b,B,T,hT,hB⟩

/-- The VF field closure of a base inside a context lies in its definably closed extension. -/
theorem vf_field_names_subset_definably_closed (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) (hB : B.real ⊆ (C.base : Set M)) :
    vfFieldNames B ⊆ ((definablyClosedVolumeContext hc C).base : Set M) := by
  rintro _ ⟨y,rfl⟩
  have hle : vfParameterField B.real ≤ (definablyClosedVolumeContextField hc C).field :=
    Subfield.closure_le.mpr (fun v hv => ((definablyClosedVolumeContextField hc C).mem_iff v).mpr
      (definably_closed_volume_context_contains hc C (hB hv)))
  exact ((definablyClosedVolumeContextField hc C).mem_iff y.val).mp (hle y.property)

theorem vf_field_named_base_subset_definably_closed (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) (hB : B.real ⊆ (C.base : Set M)) :
    (vfFieldNamedBase B).real ⊆ ((definablyClosedVolumeContext hc C).base : Set M) :=
  Set.union_subset (hB.trans (definably_closed_volume_context_contains hc C))
    (vf_field_names_subset_definably_closed hc C B hB)

end IntegrationInACVF.Section7
