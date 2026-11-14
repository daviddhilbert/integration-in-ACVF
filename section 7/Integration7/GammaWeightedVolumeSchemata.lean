import Integration7.GammaWeightedVolumeGraphs

/-! The auxiliary coordinate-and-density tuple is a finite schema with
the original reverse-fibre bound. It is used to encode Gamma weight; the
original volume degree is unchanged in the volume-isomorphism criterion. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def weightedVolumeSchema (F : GammaRVVolumeSchema B p a k sp) : GammaFiniteRVSchema B p a ((k+1)+1) sp where
  domain := F.object.domain
  volume := weightedVolumeGraph F
  domain_definable := F.object.domain_definable
  volume_definable := weightedVolumeGraph_definable F
  bound := F.object.bound

theorem weightedVolumeSchema_valid (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) : (weightedVolumeSchema F).valid z := by
  refine ⟨hz.1.1,?_,?_,?_⟩
  · intro x hx
    obtain ⟨u,hu,hunique⟩ := hz.1.2.1 x hx
    obtain ⟨φ,hφ,hφunique⟩ := hz.2.2.1 x hx
    refine ⟨Fin.append u φ,(weightedVolumeGraph_append F z x u φ).mpr ⟨hu,hφ⟩,?_⟩
    intro w hw
    have hparts := (weightedVolumeGraph_parts F z x w).mp hw
    exact (show Fin.append (w ∘ Fin.castAdd 1) (w ∘ Fin.natAdd (k+1)) = w from
      Fin.append_castAdd_natAdd).symm.trans
      (congrArg₂ Fin.append (hunique (w ∘ Fin.castAdd 1) hparts.1)
        (hφunique (w ∘ Fin.natAdd (k+1)) hparts.2))
  · intro x w hw
    exact hz.1.2.2.1 x (w ∘ Fin.castAdd 1) ((weightedVolumeGraph_parts F z x w).mp hw).1
  · intro w hw
    obtain ⟨hfin,hbound⟩ := hz.1.2.2.2 (w ∘ Fin.castAdd 1) (fun i => hw (Fin.castAdd 1 i))
    have hsub : {x : Fin a → M | Fin.append (Fin.append z x) w ∈ weightedVolumeGraph F} ⊆
        {x : Fin a → M | Fin.append (Fin.append z x) (w ∘ Fin.castAdd 1) ∈ F.object.volume} :=
      fun x hx => ((weightedVolumeGraph_parts F z x w).mp hx).1
    exact ⟨hfin.subset hsub,(Set.ncard_le_ncard hsub hfin).trans hbound⟩

@[simp] theorem weightedVolumeSchema_rowDomain (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) :
    (weightedVolumeSchema F).rowDomain z = F.object.rowDomain z := rfl

theorem weightedVolumeSchema_rowVolume (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M)
    (x : Fin a → CanonicalRV.RVSort M) (w : Fin ((k+1)+1) → CanonicalRV.RVSort M) :
    (weightedVolumeSchema F).rowVolume z x w ↔
      F.object.rowVolume z x (w ∘ Fin.castAdd 1) ∧ F.rowDensity z x (w ∘ Fin.natAdd (k+1)) :=
  weightedVolumeGraph_parts F z (rvValues x) (rvValues w)

end IntegrationInACVF.Section7
