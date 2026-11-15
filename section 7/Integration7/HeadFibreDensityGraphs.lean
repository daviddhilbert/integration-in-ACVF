import Integration7.SelectedVolumeHeadFibres
import Integration7.HeadCoordinateFibreContraction
import Integration7.NativeVolumeDomains

/-! Taking the actual density graph commutes with freezing the VF tail.
The equality retains both the old labels and the actual density value. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a k : ℕ}

theorem volume_density_graph_mem_iff {A : DefSet (rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) (x : Fin n → VFType (M := M)) (r : Fin (a+1) → CanonicalRV.RVSort M) :
    (x,r) ∈ (volumeDensityGraph ω).carrier ↔
      ∃ h : (x,r ∘ Fin.castAdd 1) ∈ A.carrier,
        r (Fin.last a) = ω.value ⟨(x,r ∘ Fin.castAdd 1),h⟩ := by
  constructor
  · intro hq
    let q : volumeDensityGraph ω := ⟨(x,r),hq⟩
    let p := densityGraphProjection ω q
    have hp : p.val = (x,r ∘ Fin.castAdd 1) := densityGraphProjection_value ω q
    have hA : (x,r ∘ Fin.castAdd 1) ∈ A.carrier := hp ▸ p.property
    refine ⟨hA,?_⟩
    have he : p = ⟨(x,r ∘ Fin.castAdd 1),hA⟩ := Subtype.ext hp
    have h := densityGraphPullback_form_last ω q
    change ω.value p = r (Fin.last a) at h
    rw [he] at h
    exact h.symm
  · rintro ⟨hA,hr⟩
    let p : A := ⟨(x,r ∘ Fin.castAdd 1),hA⟩
    refine ⟨p,Prod.ext rfl ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ j
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact (Fin.append_right _ _ 0).trans hr.symm

theorem head_fibre_density_graph_domain {C : BaseContext M}
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M)) :
    (F.headFibre x).densityGraph.domain.carrier = (F.densityGraph.headFibre x).domain.carrier := by
  ext p
  rcases p with ⟨y,r⟩
  change (y,r) ∈ (volumeDensityGraph (F.headFibre x).form).carrier ↔
    (Fin.cons (y 0) x,r) ∈ (volumeDensityGraph F.form).carrier
  rw [volume_density_graph_mem_iff,volume_density_graph_mem_iff]
  rfl

end IntegrationInACVF.Section7
