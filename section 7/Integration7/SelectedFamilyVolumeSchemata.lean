import Integration7.GammaSelectedVolumeSchemata
import Integration7.SelectedVolumeRowContexts
import Integration7.NativeVolumeDomains
import Integration7.UniformVolumeSchemaBounds
import Integration7.VolumeSchemaRowSemantics
import IntegrationSection6.GammaVFParameterBases

/-! The actual density graph of a selected VF volume family has a full
coordinate-and-density schema. Its rows are the genuine named fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (Point RV VF GammaSetDefinable gammaLogicInput carrier setDefinable)
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.densityGraphSchema
    (hc : CanonicalStructure.IsCanonical (M := M)) (Ξ : Set (Values.Gamma (M := M)))
    (F : SelectedVFVolumeFamily C n a k) :
    GammaRVVolumeSchema (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) n (a+1) k (fun _ => .vf) :=
  gammaSelectedVolumeSchema (nativeMixedVolumeDomain hc F.densityGraph.domain)
    ((gammaLogicInput _).real_set _ (setDefinable _)) F.densityGraph.selected (Fin.last a)

theorem SelectedVFVolumeFamily.densityGraph_label_nonzero
    (F : SelectedVFVolumeFamily C n a k)
    (q : (Fin n → VF (M := M)) × (Fin (a+1) → RV (M := M))) (hq : q ∈ F.densityGraph.domain.carrier) :
    (q.2 (Fin.last a)).val ≠ iRVZero := by
  have hn := F.densityGraph.form.nonzero ⟨q,hq⟩
  rw [← F.densityGraph_form_last ⟨q,hq⟩]
  exact fun he => hn (Subtype.ext (he.trans RVOperations.zero_val.symm))

theorem SelectedVFVolumeFamily.densityGraphSchema_rows
    (hc : CanonicalStructure.IsCanonical (M := M)) (Ξ : Set (Values.Gamma (M := M)))
    (F : SelectedVFVolumeFamily C n a k) (x : Fin n → VF (M := M)) :
    RVVolumeSchemaRow (F.densityGraph.rowInContext x) (F.densityGraphSchema hc Ξ) (fun j => (x j).val) := by
  let U := nativeMixedVolumeDomain hc F.densityGraph.domain
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hU : GammaSetDefinable B (carrier U) := (gammaLogicInput B).real_set _ (setDefinable U)
  constructor
  · intro r t
    change (gammaSelectedLabelSchema U hU F.densityGraph.selected).rowVolume _ r t ↔ _
    rw [gammaSelectedLabelSchema_volume]
    exact ⟨fun h => ⟨⟨r,h.1⟩,rfl,h.2⟩,by rintro ⟨u,rfl,rfl⟩; exact ⟨u.property,rfl⟩⟩
  · intro r y
    change (gammaSelectedVolumeSchema U hU F.densityGraph.selected (Fin.last a)).rowDensity _ r y ↔ _
    rw [gammaSelectedVolumeSchema_density U hU F.densityGraph.selected (Fin.last a)
      (fun q hq => F.densityGraph_label_nonzero q hq)]
    constructor
    · rintro ⟨hr,hy⟩
      refine ⟨⟨r,hr⟩,rfl,?_⟩
      funext i
      have hd := F.densityGraph_form_last ⟨(x,r),hr⟩
      have hi := congrFun hy i
      fin_cases i
      exact hd.trans hi
    · rintro ⟨u,rfl,rfl⟩
      refine ⟨u.property,?_⟩
      funext i
      fin_cases i
      exact (F.densityGraph_form_last ⟨(x,u.val),u.property⟩).symm

theorem SelectedVFVolumeFamily.densityGraphSchema_uniform_bound
    (hc : CanonicalStructure.IsCanonical (M := M)) (Ξ : Set (Values.Gamma (M := M)))
    (hΞ : Cardinal.mk Ξ < C.κ) (F : SelectedVFVolumeFamily C n a k) :
    ∃ N : ℕ, ∀ x : Fin n → VF (M := M),
      ((F.densityGraphSchema hc Ξ).withBound N).valid (fun j => (x j).val) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let U := nativeMixedVolumeDomain hc F.densityGraph.domain
  have hU : GammaSetDefinable B (carrier U) := (gammaLogicInput B).real_set _ (setDefinable U)
  let A := SpecialTransformations.Section5.PresentedSet.univ
    (SpecialTransformations.Section5.pointSpace (M := M) n 0) (C.base : Set M)
  have hA : GammaSetDefinable B (carrier A) := (gammaLogicInput B).real_set _ (setDefinable A)
  obtain ⟨N,hN⟩ := (F.densityGraphSchema hc Ξ).uniform_valid_bound C.uncountable.le C.saturated
    C.small hΞ (rawVFParameter '' carrier A) (gamma_raw_vf_parameter_base hA)
    (by
      rintro z ⟨x,hx,rfl⟩
      exact gammaSelectedLabelSchema_finiteRows U hU F.densityGraph.selected
        F.densityGraph.finite_selected x.1)
    (by
      rintro z ⟨x,hx,rfl⟩
      exact gammaSelectedVolumeSchema_density_valid U hU F.densityGraph.selected (Fin.last a)
        (fun q hq => F.densityGraph_label_nonzero q hq) x.1)
  exact ⟨N,fun x => hN _ ⟨(x,Fin.elim0),Set.mem_univ _,rfl⟩⟩

end IntegrationInACVF.Section7
