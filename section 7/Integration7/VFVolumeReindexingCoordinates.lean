module

public import Integration7.VFVolumeDegreeReindexing

@[expose] public section

/-! Literal VF coordinate formulas for an arithmetic degree cast. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a b : ℕ}

theorem mem_vf_volume_reindex_degree
    (U : PositiveVFVolumeObject (M := M) S b) (h : a=b)
    (x : Fin (a+1) → VFType (M := M)) (r : Fin U.arity → CanonicalRV.RVSort M) :
    (x,r) ∈ (U.reindexDegree h).domain.carrier ↔
      (x ∘ (finCongr (congrArg Nat.succ h)).symm,r) ∈ U.domain.carrier := by
  cases h
  rfl

theorem vf_volume_reindex_degree_density
    (U : PositiveVFVolumeObject (M := M) S b) (h : a=b) (q : (U.reindexDegree h).domain) :
    (U.reindexDegree h).form.value q = U.form.value
      ⟨(q.val.1 ∘ (finCongr (congrArg Nat.succ h)).symm,q.val.2),
        (mem_vf_volume_reindex_degree U h q.val.1 q.val.2).mp q.property⟩ := by
  cases h
  rfl

end IntegrationInACVF.Section7
