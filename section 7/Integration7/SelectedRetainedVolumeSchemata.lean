module

public import Integration7.SelectedFamilyVolumePreparation
public import Integration7.SelectedDensityGraphRowMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A selected family whose density is already an old label has its
own actual volume schema. Appending a density graph gives the same named
row through the genuine density-graph volume isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV VF gammaLogicInput carrier setDefinable)
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.retainedSchema (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k) (δ : Fin a) :
    GammaRVVolumeSchema (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) n a k (fun _ => .vf) :=
  gammaSelectedVolumeSchema (nativeMixedVolumeDomain hc F.domain)
    ((gammaLogicInput _).real_set _ (setDefinable _)) F.selected δ

private theorem label_nonzero (F : SelectedVFVolumeFamily C n a k) (δ : Fin a)
    (hForm : ∀ q : F.domain, F.form.value q=q.val.2 δ) :
    ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero := by
  intro q hq
  exact (rv_nonzero_iff_raw _).mp (fun h => F.form.nonzero ⟨q,hq⟩ ((hForm ⟨q,hq⟩).trans h))

theorem SelectedVFVolumeFamily.retainedSchema_rows (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k) (δ : Fin a)
    (hForm : ∀ q : F.domain, F.form.value q=q.val.2 δ) (x : Fin n → VF (M := M)) :
    RVVolumeSchemaRow (F.rowInContext x) (F.retainedSchema hc Ξ δ) (fun j => (x j).val) := by
  let U := nativeMixedVolumeDomain hc F.domain
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hU := (gammaLogicInput B).real_set _ (setDefinable U)
  constructor
  · intro r t
    change (gammaSelectedLabelSchema U hU F.selected).rowVolume _ r t ↔ _
    rw [gammaSelectedLabelSchema_volume]
    exact ⟨fun h => ⟨⟨r,h.1⟩,rfl,h.2⟩,by rintro ⟨u,rfl,rfl⟩; exact ⟨u.property,rfl⟩⟩
  · intro r y
    change (gammaSelectedVolumeSchema U hU F.selected δ).rowDensity _ r y ↔ _
    rw [gammaSelectedVolumeSchema_density U hU F.selected δ (label_nonzero F δ hForm)]
    constructor
    · rintro ⟨hr,hy⟩
      refine ⟨⟨r,hr⟩,rfl,?_⟩
      funext i
      have hd := hForm ⟨(x,r),hr⟩
      have hi := congrFun hy i
      fin_cases i
      exact hd.trans hi
    · rintro ⟨u,rfl,rfl⟩
      refine ⟨u.property,?_⟩
      funext i
      fin_cases i
      exact (hForm ⟨(x,u.val),u.property⟩).symm

theorem SelectedVFVolumeFamily.retainedSchema_uniform_bound (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (F : SelectedVFVolumeFamily C n a k) (δ : Fin a)
    (hForm : ∀ q : F.domain, F.form.value q=q.val.2 δ) :
    ∃ N : ℕ, ∀ x : Fin n → VF (M := M), ((F.retainedSchema hc Ξ δ).withBound N).valid (fun j => (x j).val) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let U := nativeMixedVolumeDomain hc F.domain
  have hU := (gammaLogicInput B).real_set _ (setDefinable U)
  let A := SpecialTransformations.Section5.PresentedSet.univ
    (SpecialTransformations.Section5.pointSpace (M := M) n 0) (C.base : Set M)
  have hA := (gammaLogicInput B).real_set _ (setDefinable A)
  obtain ⟨N,hN⟩ := (F.retainedSchema hc Ξ δ).uniform_valid_bound C.uncountable.le C.saturated
    C.small hΞ (rawVFParameter '' carrier A) (gamma_raw_vf_parameter_base hA)
    (by rintro z ⟨x,hx,rfl⟩; exact gammaSelectedLabelSchema_finiteRows U hU F.selected F.finite_selected x.1)
    (by rintro z ⟨x,hx,rfl⟩; exact gammaSelectedVolumeSchema_density_valid U hU F.selected δ (label_nonzero F δ hForm) x.1)
  exact ⟨N,fun x => hN _ ⟨(x,Fin.elim0),Set.mem_univ _,rfl⟩⟩

theorem selected_retained_densityGraph_named_common (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k) (δ : Fin a)
    (hForm : ∀ q : F.domain, F.form.value q=q.val.2 δ) (NF NG : ℕ) (x : Fin n → VF (M := M)) :
    ((F.retainedSchema hc Ξ δ).withBound NF).commonInNamedContext
      ((F.densityGraphSchema hc Ξ).withBound NG) (fun j => (x j).val) := by
  refine ⟨vfParameterVolumeContext C x,rfl,F.rowInContext x,F.densityGraph.rowInContext x,rfl,rfl,?_,?_,
    VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x) (F.densityGraphRowIso hc x)⟩
  · exact (F.retainedSchema_rows hc Ξ δ hForm x).congr
      (GammaRVVolumeSchema.sameRow_symm ((F.retainedSchema hc Ξ δ).withBound_sameRow NF _ (fun j => (x j).property)))
  · exact (F.densityGraphSchema_rows hc Ξ x).congr
      (GammaRVVolumeSchema.sameRow_symm ((F.densityGraphSchema hc Ξ).withBound_sameRow NG _ (fun j => (x j).property)))
end IntegrationInACVF.Section7
