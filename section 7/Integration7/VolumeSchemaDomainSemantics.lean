import Integration7.CanonicalVolumeSchemaRows

/-! A valid coordinate schema has exactly the domain of every actual
object interpreting its coordinate graph, including zero-coordinate rows. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem RVVolumeSchemaRow.domain_iff {U : PositiveRVVolumeObject (M := M) S k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp} {z : Fin p → M}
    (P : RVVolumeSchemaRow U F z) (hF : F.valid z)
    (x : Fin U.underlying.obj.arity → CanonicalRV.RVSort M) :
    x ∈ F.object.rowDomain z ↔ x ∈ U.underlying.obj.domain.carrier := by
  constructor
  · intro hx
    obtain ⟨t,ht,_⟩ := hF.1.2.1 (rvValues x) hx
    have htRV (i) : iRV (t i) := by
      simpa only [Fin.append_right,sortEval,iRV] using F.object.volume_definable.proper _ ht
        (Fin.natAdd (p+U.underlying.obj.arity) i)
    let tt : Fin (k+1) → CanonicalRV.RVSort M := fun i => ⟨t i,htRV i⟩
    obtain ⟨u,rfl,_⟩ := (P.volume_iff x tt).mp ht
    exact u.property
  · intro hx
    let u : U.underlying.obj.domain := ⟨x,hx⟩
    exact hF.1.2.2.1 _ _ ((P.volume_iff x (U.underlying.obj.value u)).mpr ⟨u,rfl,rfl⟩)

end IntegrationInACVF.Section7
