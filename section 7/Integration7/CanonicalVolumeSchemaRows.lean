import Integration7.VolumeSchemaRowSemantics
import Integration7.GammaVolumeSchemaRealization
import Integration7.EssentialFiniteVolumeSchemata

/-! A schema's canonical real presentation interprets its exact coordinate
and density graphs in any containing base context. The essential domain is
exactly the schema's nonzero-coordinate restriction. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem GammaVolumeGraphPresentation.inContext_schemaRow
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (hz : F.valid z)
    (P : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      (F.object.rowDomain z) (F.object.rowVolume z) (F.rowDensity z))
    (hP : P.finite.codes ⊆ (C.base : Set M)) :
    RVVolumeSchemaRow (P.inContext hc C hP).toObject F z := by
  constructor
  · intro x t
    change F.object.rowVolume z x t ↔ ∃ u : P.finite.domain,
      u.val = x ∧ (P.finite.volume u).val = t
    constructor
    · intro h
      exact (P.finite.graph_iff x t).mpr ⟨hz.1.2.2.1 _ _ h,h⟩
    · intro h
      exact ((P.finite.graph_iff x t).mp h).2
  · intro x ω
    change F.rowDensity z x ω ↔ ∃ u : P.finite.domain,
      u.val = x ∧ (@VolumeForm.map M (@CanonicalStructure.normalize M sM)
        (@CanonicalStructure.normalized_model M sM hM) _ P.finite.codes P.finite.domain P.form u).val = ω
    exact (P.density_iff x ω).symm

theorem RVVolumeSchemaRow.essential_domain_iff
    {S : Set M} {U : PositiveRVVolumeObject (M := M) S k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp} {z : Fin p → M}
    (P : RVVolumeSchemaRow U F z) (x : Fin U.underlying.obj.arity → CanonicalRV.RVSort M) :
    x ∈ (essentialFiniteVolumeSchema F.object).rowDomain z ↔
      x ∈ U.essential.obj.domain.carrier := by
  rw [essentialFiniteVolumeSchema_rowDomain]
  constructor
  · rintro ⟨t,ht,hn⟩
    obtain ⟨u,rfl,rfl⟩ := (P.volume_iff x t).mp ht
    exact (mem_rvEssentialLabels U.underlying.obj u).mpr hn
  · intro hx
    let u : U.essential.obj.domain := ⟨x,hx⟩
    exact ⟨U.essential.obj.value u,P.volume_at u,U.essential_nonzero u⟩

end IntegrationInACVF.Section7
