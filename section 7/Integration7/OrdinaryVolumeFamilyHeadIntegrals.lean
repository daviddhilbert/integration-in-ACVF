module

public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.VolumeDensityGraphs
public import Integration7.VolumeFamilyHeadIntegrals
public import Integration7.EmptySelectedVolumeCharts
public import IntegrationSection5.GammaHeadPreparation

@[expose] public section

/-! Contracting one VF coordinate of an ordinary finite-label family
creates its first volume coordinate. The density is the retained unit
label of the actual VF realization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a : ℕ}

theorem OrdinaryVFVolumeFamily.densityGraph_label_one
    (F : OrdinaryVFVolumeFamily C (n+1) a)
    (q : F.fullVFObject.densityGraph.domain) : q.val.2 (Fin.last a) = 1 :=
  (densityGraph_form_last F.fullVFObject q).symm

theorem OrdinaryVFVolumeFamily.densityGraph_label_nonzero
    (F : OrdinaryVFVolumeFamily C (n+1) a) :
    ∀ p ∈ F.fullVFObject.densityGraph.domain.carrier,
      (p.2 (Fin.last a)).val ≠ iRVZero := by
  intro p hp
  apply (rv_nonzero_iff_raw _).mp
  rw [F.densityGraph_label_one ⟨p,hp⟩]
  exact one_ne_zero

def OrdinaryVFVolumeFamily.headIntegral
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : OrdinaryVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)) :
    SelectedVFVolumeFamily C n (1+T.arity) 0 :=
  nativeCoordinateVolumeFamily hc T.contractedSet
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (a+1)))
    (head_selected_fibres_finite C.uncountable.le C.saturated C.small T
      ((gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_map_graph T.map)
      ((gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_set _ (setDefinable T.target))
      Fin.elim0 (empty_selected_volume_finite _ F.fullVFObject.densityGraph.finite_labels))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a)))
    (head_retained_density_nonzero T (Fin.last a) F.densityGraph_label_nonzero)

@[simp] theorem OrdinaryVFVolumeFamily.headIntegral_selected
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : OrdinaryVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)) :
    (F.headIntegral hc Ξ T).selected 0 = 0 := rfl

theorem OrdinaryVFVolumeFamily.headIntegral_density_one
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : OrdinaryVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (q : (F.headIntegral hc Ξ T).domain) : (F.headIntegral hc Ξ T).form.value q = 1 := by
  obtain ⟨p,hp⟩ := T.contractionMap_surjective ⟨q.val,q.property⟩
  have hold : (T.contractionMap p).val.2
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a))) =
      p.val.2 (Fin.last a) := by
    change (headKeyMap T.target (T.map p)).val.2 _ = _
    rw [headKeyMap_apply]
    simpa only [headKey,Fin.append_right] using specialRelative_oldLabels T.special p (Fin.last a)
  rw [hp] at hold
  exact hold.trans (F.densityGraph_label_one ⟨p.val,p.property⟩)

def ordinaryFamilyHeadPreparation
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (F : OrdinaryVFVolumeFamily C (n+1) a) :
    HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain
  exact Classical.choose (gamma_head_preparation C.saturated C.model00 B C.small
    (generatedBaseVFField hGenerated) (Set.Subset.refl _) A
    ((gammaLogicInput B).real_set _ (setDefinable A)))

end IntegrationInACVF.Section7
